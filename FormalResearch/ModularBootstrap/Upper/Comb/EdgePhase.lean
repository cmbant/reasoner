module

public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Reference Blaschke Comb I: Edge Phase and Euler--Maclaurin Decomposition (Lemma K3)

Formalizes Lemma K3 (`cmb:K3`) of `CFT/modular_bootstrap/paper/comb_estimates.tex`
(lines 103--137):

* `logRefComb`: convergent logarithm $\log B^{(f)}(b) = i\pi + \varphi_{\chi_f}(b) +
  \sum_{k \ge f + 1} (\varphi_{\chi_k + i\varepsilon_k}(b) + \varphi_{\chi_k - i\varepsilon_k}(b))$
  on $\mathcal N = \{b : |\operatorname{Im} b - 1/2| \le 1/4\}$, with
  `cexp (logRefComb c' f η₀ b) = refComb c' f η₀ b`.
* `phi0`, `barPhi`, `deltaDetComb`, `emRem`, `phi1Comb`: the asymptotic edge phase
  $\Phi_0(b) = \int_{\xi_*}^\infty \rho_U(y)\varphi_y(b)\,dy$ and the decomposition
  $\log B^{(f)}(b) = c'\Phi_0(b) + \Phi_1^{(f)}(b)$, where
  $\Phi_1^{(f)} = i\pi - 2 n_1 \bar\varphi^{(f)} + \Delta_{\mathrm{det}}^{(f)} + R_{\mathrm{EM}}^{(f)}$,
  with second-order Euler--Maclaurin remainder `emRem`.
* `re_phi1Comb_eq_zero_of_im_half`: $\operatorname{Re} \Phi_1^{(f)}(b) = 0$ on
  $E_+ = \{\operatorname{Im} b = 1/2\}$.
* Derivative identities and bounds for $i = 0, 1, 2$ (`edgePhase_bounds`):
  uniformly in $f \ge 1$, $\eta_0 \in [0, 1/4]$, $b \in \mathcal N$ for large $c'$,
  $\|\partial_b^i \Delta_{\mathrm{det}}^{(f)}(b)\| + \|\partial_b^i R_{\mathrm{EM}}^{(f)}(b)\| \le C\lambda$,
  $\|\partial_b^i \Phi_1^{(f)}(b)\| \le C n_1$, and
  $\|\partial_b^i (\bar\varphi^{(f)}(b) - \varphi_{\xi_*}(b))\| \le C n_1^{2/3} \lambda$.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: Open-strip kernel and `phiZeta` derivative package -/

/-- Open strip neighbourhood of `combN` strictly inside `combNOpen`: $|\operatorname{Im} b - 1/2| < 17/64$. -/
def combNMid : Set ℂ := {b : ℂ | |b.im - 1 / 2| < 17 / 64}

lemma combN_subset_combNMid : combN ⊆ combNMid := fun b hb =>
  lt_of_le_of_lt (show |b.im - 1 / 2| ≤ 1 / 4 from hb) (by norm_num)

lemma combNMid_subset_combNOpen : combNMid ⊆ combNOpen := fun b hb =>
  lt_trans (show |b.im - 1 / 2| < 17 / 64 from hb) (by norm_num)

lemma isOpen_combNMid : IsOpen combNMid :=
  isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const

private lemma ofReal_add_I_mul_mem_combZ {x y : ℝ} (hx : 0 ≤ x) (hy : |y| ≤ 1 / 8) :
    (x : ℂ) + (y : ℂ) * Complex.I ∈ combZ :=
  ⟨by simpa using hx, by simpa using hy⟩

private lemma ofReal_sub_I_mul_mem_combZ {x y : ℝ} (hx : 0 ≤ x) (hy : |y| ≤ 1 / 8) :
    (x : ℂ) - (y : ℂ) * Complex.I ∈ combZ :=
  ⟨by simpa using hx, by simpa using hy⟩

private lemma ofReal_mem_combZ {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ∈ combZ :=
  ⟨by simpa using hx, by simp⟩

private lemma ofReal_mem_combZOpen {x : ℝ} (hx : -1 / 4 < x) : (x : ℂ) ∈ combZOpen :=
  ⟨by simpa using hx, by simp⟩

private lemma ofReal_add_I_mul_mem_combZOpen {x y : ℝ} (hx : -1 / 4 < x) (hy : |y| ≤ 1 / 8) :
    (x : ℂ) + (y : ℂ) * Complex.I ∈ combZOpen :=
  ⟨by simpa using hx, by simpa using lt_of_le_of_lt hy (by norm_num : (1 / 8 : ℝ) < 5 / 32)⟩

private lemma ofReal_sub_I_mul_mem_combZOpen {x y : ℝ} (hx : -1 / 4 < x) (hy : |y| ≤ 1 / 8) :
    (x : ℂ) - (y : ℂ) * Complex.I ∈ combZOpen :=
  ⟨by simpa using hx, by simpa using lt_of_le_of_lt hy (by norm_num : (1 / 8 : ℝ) < 5 / 32)⟩

private lemma continuousAt_rhoUDeriv {y : ℝ} (hy : xiStar < y) : ContinuousAt rhoUDeriv y := by
  have hpi := Real.pi_pos
  have hs : 1 < Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
  have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
  have hsh : ContinuousAt (fun t : ℝ => Real.sinh (π * t)) y :=
    Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
  have hch : ContinuousAt (fun t : ℝ => Real.cosh (π * t)) y :=
    Real.continuous_cosh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
  have hden : ContinuousAt (fun t : ℝ => √(Real.sinh (π * t) ^ 2 - 1)) y :=
    ((hsh.pow 2).sub continuousAt_const).sqrt
  exact continuousAt_const.mul (hch.div hden (Real.sqrt_ne_zero'.mpr hsq))

private lemma comb_sinh_norm_ge {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1 / 2) :
    ∃ c > 0, ∀ w : ℂ, s₀ ≤ w.im → w.im ≤ 1 - s₀ →
      c * Real.exp (π * |w.re|) ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
  have hpi := Real.pi_pos
  have hsin_pos : 0 < Real.sin (π * s₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hsin_le : ∀ θ : ℝ, π * s₀ ≤ θ → θ ≤ π * (1 - s₀) → Real.sin (π * s₀) ≤ Real.sin θ := by
    intro θ hθ1 hθ2
    rcases le_or_gt θ (π / 2) with h | h
    · exact Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ hθ1
    · rw [← Real.sin_pi_sub θ]
      exact Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
  set c := min (Real.sin (π * s₀) * Real.exp (-π)) (1 / 4)
  refine ⟨c, lt_min (by positivity) (by norm_num), fun w hw1 hw2 => ?_⟩
  have hns : ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 =
      Real.sinh (π * w.re) ^ 2 + Real.sin (π * w.im) ^ 2 := by
    have hw : (π : ℂ) * w = ((π * w.re : ℝ) : ℂ) + ((π * w.im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp) (by simp)
    rw [Complex.sq_norm, hw, complex_sinh_normSq]
  rcases le_or_gt |w.re| 1 with hre | hre
  · have hsin_ge : Real.sin (π * s₀) ≤ |Real.sin (π * w.im)| :=
      (hsin_le (π * w.im) (by nlinarith) (by nlinarith)).trans (le_abs_self _)
    have hnorm_ge : Real.sin (π * s₀) ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
      have hsq : Real.sin (π * s₀) ^ 2 ≤ ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 := by
        nlinarith [sq_nonneg (Real.sinh (π * w.re)), sq_abs (Real.sin (π * w.im)),
          pow_le_pow_left₀ hsin_pos.le hsin_ge 2]
      nlinarith [norm_nonneg (Complex.sinh ((π : ℂ) * w))]
    have hexp_le : c * Real.exp (π * |w.re|) ≤ Real.sin (π * s₀) := by
      have h1 : Real.exp (π * |w.re|) ≤ Real.exp π := Real.exp_le_exp.mpr (by nlinarith)
      calc c * Real.exp (π * |w.re|) ≤ c * Real.exp π := by gcongr
        _ ≤ (Real.sin (π * s₀) * Real.exp (-π)) * Real.exp π := by
            gcongr; exact min_le_left _ _
        _ = Real.sin (π * s₀) := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    exact hexp_le.trans hnorm_ge
  · have hsh_ge : (1 / 4 : ℝ) * Real.exp (π * |w.re|) ≤ |Real.sinh (π * w.re)| := by
      have h1 : Real.pi * 1 < Real.pi * |w.re| := mul_lt_mul_of_pos_left hre hpi
      have h2 : (1 / 2 : ℝ) * Real.exp (π * |w.re|) ≤ Real.exp (π * |w.re|) - Real.exp (-(π * |w.re|)) := by
        have h3 : Real.exp (-(π * |w.re|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have h4 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
        have h5 : (2 : ℝ) ≤ Real.exp (π * |w.re|) :=
          h4.trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three]))
        linarith
      have h3 : (1 / 4 : ℝ) * Real.exp (π * |w.re|) ≤ Real.sinh (π * |w.re|) := by
        rw [Real.sinh_eq]; linarith
      have habs : |Real.sinh (π * w.re)| = Real.sinh (π * |w.re|) := by
        rcases le_or_gt 0 w.re with hw_re | hw_re
        · rw [abs_of_nonneg hw_re, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
        · have hneg : π * w.re < 0 := mul_neg_of_pos_of_neg hpi hw_re
          rw [abs_of_neg (Real.sinh_neg_iff.mpr hneg), ← Real.sinh_neg,
            show -(π * w.re) = π * |w.re| by rw [abs_of_neg hw_re]; ring]
      rw [habs]; exact h3
    have hnorm_ge : |Real.sinh (π * w.re)| ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
      have hsq : |Real.sinh (π * w.re)| ^ 2 ≤ ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 := by
        rw [hns, sq_abs]; linarith [sq_nonneg (Real.sin (π * w.im))]
      nlinarith [norm_nonneg (Complex.sinh ((π : ℂ) * w)), abs_nonneg (Real.sinh (π * w.re))]
    exact ((mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le).trans hsh_ge).trans hnorm_ge

private lemma comb_sinhKernel_differentiableOn :
    DifferentiableOn ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} := by
  intro w hw
  have hs₀ : 0 < min (w.im / 2) ((1 - w.im) / 2) := lt_min (by linarith [hw.1]) (by linarith [hw.2])
  have hs₁ : min (w.im / 2) ((1 - w.im) / 2) < 1 / 2 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [hw.2])
  obtain ⟨c, hc, hne⟩ := comb_sinh_norm_ge hs₀ hs₁
  have h_ne : Complex.sinh ((π : ℂ) * w) ≠ 0 := by
    intro h0
    have := hne w (min_le_left _ _ |>.trans (by linarith [hw.1]))
      (by linarith [min_le_right (w.im / 2) ((1 - w.im) / 2), hw.2])
    rw [h0, norm_zero] at this
    linarith [mul_pos hc (Real.exp_pos (π * |w.re|))]
  unfold sinhKernel
  exact ((differentiableAt_const _).div
    (Complex.differentiable_sinh.differentiableAt.comp w (by fun_prop)) h_ne).differentiableWithinAt

private lemma comb_sinhKernel_iteratedDeriv_bound {k : ℕ} :
    ∃ C > 0, ∀ w : ℂ, 1 / 16 ≤ w.im → w.im ≤ 15 / 16 →
      ‖iteratedDeriv k sinhKernel w‖ ≤ C * Real.exp (-π * |w.re|) := by
  set s₀ : ℝ := 1 / 32
  have hs₀ : 0 < s₀ := by norm_num
  obtain ⟨c, hc, hne⟩ := comb_sinh_norm_ge hs₀ (by norm_num)
  set C₀ := π / c
  set C := (k.factorial : ℝ) * C₀ * Real.exp (π * s₀) / s₀ ^ k
  refine ⟨C, by positivity, fun w hw1 hw2 => ?_⟩
  have hsub : Metric.closedBall w s₀ ⊆ {z : ℂ | 0 < z.im ∧ z.im < 1} := by
    intro z hz
    have him : |z.im - w.im| ≤ 1 / 32 :=
      (Complex.abs_im_le_norm (z - w)).trans (mem_closedBall_iff_norm.mp hz)
    have h1 : s₀ ≤ z.im := by dsimp [s₀]; linarith [(abs_le.mp him).1]
    have h2 : z.im ≤ 1 - s₀ := by dsimp [s₀]; linarith [(abs_le.mp him).2]
    exact ⟨lt_of_lt_of_le hs₀ h1, lt_of_le_of_lt h2 (by dsimp [s₀]; norm_num)⟩
  have hdiff : DiffContOnCl ℂ sinhKernel (Metric.ball w s₀) :=
    ⟨comb_sinhKernel_differentiableOn.mono (Metric.ball_subset_closedBall.trans hsub),
      by rw [closure_ball w hs₀.ne']; exact (comb_sinhKernel_differentiableOn.mono hsub).continuousOn⟩
  have hsphere : ∀ z ∈ Metric.sphere w s₀,
      ‖sinhKernel z‖ ≤ C₀ * Real.exp (π * s₀) * Real.exp (-π * |w.re|) := by
    intro z hz
    have hzw : ‖z - w‖ = s₀ := mem_sphere_iff_norm.mp hz
    have him : |z.im - w.im| ≤ 1 / 32 := (Complex.abs_im_le_norm (z - w)).trans hzw.le
    have hre : |z.re - w.re| ≤ s₀ := (Complex.abs_re_le_norm (z - w)).trans hzw.le
    have hge := hne z (by dsimp [s₀]; linarith [(abs_le.mp him).1])
      (by dsimp [s₀]; linarith [(abs_le.mp him).2])
    have h1 : ‖sinhKernel z‖ ≤ C₀ * Real.exp (-π * |z.re|) := by
      unfold sinhKernel
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, div_le_iff₀
        (lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) hge)]
      calc π = C₀ * c := by dsimp [C₀]; field_simp [hc.ne']
        _ = C₀ * (Real.exp (-π * |z.re|) * Real.exp (π * |z.re|) * c) := by
            rw [← Real.exp_add, show -π * |z.re| + π * |z.re| = 0 by ring, Real.exp_zero, one_mul]
        _ = C₀ * Real.exp (-π * |z.re|) * (c * Real.exp (π * |z.re|)) := by ring
        _ ≤ C₀ * Real.exp (-π * |z.re|) * ‖Complex.sinh ((π : ℂ) * z)‖ := by gcongr
    have hre_lb : |w.re| - s₀ ≤ |z.re| := by
      have : |w.re| - |z.re| ≤ |w.re - z.re| := abs_sub_abs_le_abs_sub _ _
      rw [abs_sub_comm] at this
      linarith
    have hexp_le : Real.exp (-π * |z.re|) ≤ Real.exp (π * s₀) * Real.exp (-π * |w.re|) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    calc ‖sinhKernel z‖ ≤ C₀ * Real.exp (-π * |z.re|) := h1
      _ ≤ C₀ * (Real.exp (π * s₀) * Real.exp (-π * |w.re|)) := by gcongr
      _ = C₀ * Real.exp (π * s₀) * Real.exp (-π * |w.re|) := by ring
  exact (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hs₀ hdiff hsphere).trans_eq
    (by dsimp [C]; ring)

/-- Unified $(i, j)$-derivative formula for $\partial_b^i \partial_\zeta^j \varphi_\zeta(b)$
matching `phiZeta` when `i + j = 0` and `iteratedDeriv_phiZeta_eq` when `1 ≤ i + j`. -/
noncomputable def combPhiDeriv (i j : ℕ) (ζ b : ℂ) : ℂ :=
  if i + j = 0 then phiZeta ζ b
  else (-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b - ζ) +
    iteratedDeriv (i + j - 1) sinhKernel (b + ζ)

lemma combPhiDeriv_zero (ζ b : ℂ) : combPhiDeriv 0 0 ζ b = phiZeta ζ b := by
  simp [combPhiDeriv]

private lemma combNMid_im_range {b ζ : ℂ} (hb : b ∈ combNMid) (hζ : |ζ.im| ≤ 1 / 8) (t : ℝ) :
    1 / 16 ≤ (b - (ζ + (t : ℂ))).im ∧ (b - (ζ + (t : ℂ))).im ≤ 15 / 16 ∧
      1 / 16 ≤ (b + (ζ + (t : ℂ))).im ∧ (b + (ζ + (t : ℂ))).im ≤ 15 / 16 := by
  have hb' := abs_le.mp (show |b.im - 1 / 2| ≤ 17 / 64 from le_of_lt hb)
  have hζ' := abs_le.mp hζ
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero]
  norm_num at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma re_dist_le_sub_add {ζ b : ℂ} (hζ : 0 ≤ ζ.re) :
    abs (ζ.re - |b.re|) ≤ |(b - ζ).re| ∧ abs (ζ.re - |b.re|) ≤ |(b + ζ).re| := by
  constructor
  · simp only [Complex.sub_re]
    rcases le_or_gt 0 b.re with h | h
    · rw [abs_of_nonneg h, abs_sub_comm]
    · rw [abs_of_neg h, sub_neg_eq_add]
      have h1 : |ζ.re + b.re| ≤ ζ.re - b.re := by rw [abs_le]; constructor <;> linarith
      calc |ζ.re + b.re| ≤ ζ.re - b.re := h1
        _ ≤ |ζ.re - b.re| := le_abs_self _
        _ = |b.re - ζ.re| := abs_sub_comm _ _
  · simp only [Complex.add_re]
    rcases le_or_gt 0 b.re with h | h
    · rw [abs_of_nonneg h]
      have : |ζ.re - b.re| ≤ b.re + ζ.re := by rw [abs_le]; constructor <;> linarith
      exact this.trans (le_abs_self _)
    · rw [abs_of_neg h, sub_neg_eq_add, add_comm]

lemma integrable_exp_neg_pi_abs : Integrable (fun t : ℝ => Real.exp (-π * |t|)) volume := by
  have hpi := Real.pi_pos
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-π * t)) (Ioi 0) volume :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have h_ici : IntegrableOn (fun t : ℝ => Real.exp (-π * t)) (Ici 0) volume :=
    (integrableOn_exp_mul_Ioi (by linarith : -π < 0) (-1)).mono_set (fun t ht => by
      have ht0 : 0 ≤ t := ht
      change -1 < t; linarith)
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (π * t)) (Iic 0) volume := by
    have heq : (fun t : ℝ => Real.exp (π * t)) = (fun t : ℝ => Real.exp (-π * (-t))) := by
      ext t; ring_nf
    rw [heq]
    have hcomp : IntegrableOn (fun t : ℝ => Real.exp (-π * (-t))) (Neg.neg ⁻¹' Ici 0) volume :=
      (Measure.measurePreserving_neg volume).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding |>.mpr h_ici
    have hpre : (Neg.neg ⁻¹' Ici (0 : ℝ)) = Iic (0 : ℝ) := by ext x; simp
    rwa [hpre] at hcomp
  rw [← integrableOn_univ, show (univ : Set ℝ) = Ioi 0 ∪ Iic 0 from Ioi_union_Iic.symm]
  exact (h1.congr_fun (fun t ht => by rw [abs_of_nonneg ht.out.le]) measurableSet_Ioi).union
    (h2.congr_fun (fun t ht => by rw [abs_of_nonpos ht]; ring_nf) measurableSet_Iic)

lemma integral_exp_neg_pi_abs : ∫ t : ℝ, Real.exp (-π * |t|) = 2 / π := by
  have hpi := Real.pi_pos
  have hiic : IntegrableOn (fun t : ℝ => Real.exp (-π * |t|)) (Iic 0) volume :=
    integrable_exp_neg_pi_abs.integrableOn
  have hioi : IntegrableOn (fun t : ℝ => Real.exp (-π * |t|)) (Ioi 0) volume :=
    integrable_exp_neg_pi_abs.integrableOn
  have huniv : ∫ t : ℝ, Real.exp (-π * |t|) =
      (∫ t in Iic (0 : ℝ), Real.exp (-π * |t|)) + ∫ t in Ioi (0 : ℝ), Real.exp (-π * |t|) := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
      MeasureTheory.setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hiic hioi]
  have v1 : ∫ t in Ioi (0 : ℝ), Real.exp (-π * |t|) = 1 / π := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [abs_of_nonneg ht.out.le],
      integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
    ring
  have v2 : ∫ t in Iic (0 : ℝ), Real.exp (-π * |t|) = 1 / π := by
    have hcomp : ∫ t in Iic (0 : ℝ), Real.exp (-π * |t|) =
        ∫ t in Ici (0 : ℝ), Real.exp (-π * |t|) := by
      have hpre : (Iic (0 : ℝ)) = Neg.neg ⁻¹' Ici (0 : ℝ) := by ext x; simp
      rw [hpre]
      have hs := (Measure.measurePreserving_neg volume).setIntegral_preimage_emb
        (Homeomorph.neg ℝ).measurableEmbedding (fun t : ℝ => Real.exp (-π * |t|)) (Ici 0)
      simpa [abs_neg] using hs
    rw [hcomp, integral_Ici_eq_integral_Ioi, v1]
  rw [huniv, v1, v2]; ring

/-- Uniform bounds on `combPhiDeriv i j ζ b` over the open strip `combNMid × combZ` for `i + j ≤ 4`. -/
theorem combPhiDeriv_bound :
    ∃ C > 0,
      (∀ (i j : ℕ), 1 ≤ i + j → i + j ≤ 4 → ∀ {ζ b : ℂ}, b ∈ combNMid → ζ ∈ combZ →
        ‖combPhiDeriv i j ζ b‖ ≤ C * Real.exp (-π * abs (ζ.re - |b.re|))) ∧
      (∀ (i j : ℕ), i + j ≤ 4 → ∀ {ζ b : ℂ}, b ∈ combNMid → ζ ∈ combZ →
        ‖combPhiDeriv i j ζ b‖ ≤ C * min 1 (Real.exp (-π * (ζ.re - |b.re|)))) := by
  have hpi := Real.pi_pos
  obtain ⟨C₀, hC₀, hbd0⟩ := comb_sinhKernel_iteratedDeriv_bound (k := 0)
  obtain ⟨C₁, hC₁, hbd1⟩ := comb_sinhKernel_iteratedDeriv_bound (k := 1)
  obtain ⟨C₂, hC₂, hbd2⟩ := comb_sinhKernel_iteratedDeriv_bound (k := 2)
  obtain ⟨C₃, hC₃, hbd3⟩ := comb_sinhKernel_iteratedDeriv_bound (k := 3)
  set M := max (max C₀ C₁) (max C₂ C₃)
  set C := max (2 * M) (max (4 * C₀ / π) (2 * C₀ / π))
  have hM : 0 < M := by positivity
  have hbd_ij : ∀ (i j : ℕ), 1 ≤ i + j → i + j ≤ 4 → ∀ {ζ b : ℂ}, b ∈ combNMid → ζ ∈ combZ →
      ‖combPhiDeriv i j ζ b‖ ≤ 2 * M * Real.exp (-π * abs (ζ.re - |b.re|)) := by
    intro i j hij1 hij4 ζ b hb hζ
    unfold combPhiDeriv
    rw [if_neg (by omega)]
    have him := combNMid_im_range hb hζ.2 0
    simp only [Complex.ofReal_zero, add_zero] at him
    have hbd_k : ∀ k : ℕ, k ≤ 3 → ∀ w : ℂ, 1 / 16 ≤ w.im → w.im ≤ 15 / 16 →
        ‖iteratedDeriv k sinhKernel w‖ ≤ M * Real.exp (-π * |w.re|) := by
      intro k hk w hw1 hw2
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · exact (hbd0 w hw1 hw2).trans (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_left _ _)) (Real.exp_pos _).le)
      · exact (hbd1 w hw1 hw2).trans (mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_left _ _)) (Real.exp_pos _).le)
      · exact (hbd2 w hw1 hw2).trans (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_pos _).le)
      · exact (hbd3 w hw1 hw2).trans (mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_pos _).le)
    have h1 := hbd_k (i + j - 1) (by omega) (b - ζ) him.1 him.2.1
    have h2 := hbd_k (i + j - 1) (by omega) (b + ζ) him.2.2.1 him.2.2.2
    obtain ⟨hd1, hd2⟩ := re_dist_le_sub_add hζ.1
    have he1 : Real.exp (-π * |(b - ζ).re|) ≤ Real.exp (-π * abs (ζ.re - |b.re|)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he2 : Real.exp (-π * |(b + ζ).re|) ≤ Real.exp (-π * abs (ζ.re - |b.re|)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc ‖(-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b - ζ) +
            iteratedDeriv (i + j - 1) sinhKernel (b + ζ)‖
        ≤ ‖(-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b - ζ)‖ +
            ‖iteratedDeriv (i + j - 1) sinhKernel (b + ζ)‖ := norm_add_le _ _
      _ = ‖iteratedDeriv (i + j - 1) sinhKernel (b - ζ)‖ +
            ‖iteratedDeriv (i + j - 1) sinhKernel (b + ζ)‖ := by
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      _ ≤ M * Real.exp (-π * |(b - ζ).re|) + M * Real.exp (-π * |(b + ζ).re|) := add_le_add h1 h2
      _ ≤ M * Real.exp (-π * abs (ζ.re - |b.re|)) + M * Real.exp (-π * abs (ζ.re - |b.re|)) := by gcongr
      _ = 2 * M * Real.exp (-π * abs (ζ.re - |b.re|)) := by ring
  refine ⟨C, by positivity, fun i j hij1 hij4 {ζ b} hb hζ => ?_, fun i j hij4 {ζ b} hb hζ => ?_⟩
  · exact (hbd_ij i j hij1 hij4 hb hζ).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · rcases eq_or_ne (i + j) 0 with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
      rw [combPhiDeriv_zero]
      have h_pt : ∀ t : ℝ,
          ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖ ≤
            C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
              Real.exp (-π * |(b + (ζ + (t : ℂ))).re|)) := by
        intro t
        have him := combNMid_im_range hb hζ.2 t
        have h1 := hbd0 (b - (ζ + (t : ℂ))) him.1 him.2.1
        have h2 := hbd0 (b + (ζ + (t : ℂ))) him.2.2.1 him.2.2.2
        simp only [iteratedDeriv_zero] at h1 h2
        calc ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖
            ≤ ‖sinhKernel (b - (ζ + (t : ℂ)))‖ + ‖sinhKernel (b + (ζ + (t : ℂ)))‖ := norm_sub_le _ _
          _ ≤ C₀ * Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
                C₀ * Real.exp (-π * |(b + (ζ + (t : ℂ))).re|) := add_le_add h1 h2
          _ = C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
                Real.exp (-π * |(b + (ζ + (t : ℂ))).re|)) := by ring
      have h_cont_fn : Continuous fun t : ℝ =>
          sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ))) := by
        refine Continuous.sub ?_ ?_
        · exact comb_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop) fun t =>
            ⟨by linarith [(combNMid_im_range hb hζ.2 t).1],
              by linarith [(combNMid_im_range hb hζ.2 t).2.1]⟩
        · exact comb_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop) fun t =>
            ⟨by linarith [(combNMid_im_range hb hζ.2 t).2.2.1],
              by linarith [(combNMid_im_range hb hζ.2 t).2.2.2]⟩
      have hdom1_int : Integrable (fun t : ℝ =>
          C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
            Real.exp (-π * |(b + (ζ + (t : ℂ))).re|))) volume := by
        have ha : Integrable (fun t : ℝ => Real.exp (-π * |t - (b.re - ζ.re)|)) volume :=
          integrable_exp_neg_pi_abs.comp_sub_right _
        have hb_int : Integrable (fun t : ℝ => Real.exp (-π * |t - (-b.re - ζ.re)|)) volume :=
          integrable_exp_neg_pi_abs.comp_sub_right _
        have heq1_pt : ∀ t : ℝ, |(b - (ζ + (t : ℂ))).re| = |t - (b.re - ζ.re)| := fun t => by
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
          rw [show b.re - (ζ.re + t) = -(t - (b.re - ζ.re)) by ring, abs_neg]
        have heq2_pt : ∀ t : ℝ, |(b + (ζ + (t : ℂ))).re| = |t - (-b.re - ζ.re)| := fun t => by
          simp only [Complex.add_re, Complex.ofReal_re]
          rw [show b.re + (ζ.re + t) = t - (-b.re - ζ.re) by ring]
        have hdom' : Integrable (fun t : ℝ =>
            C₀ * (Real.exp (-π * |t - (b.re - ζ.re)|) + Real.exp (-π * |t - (-b.re - ζ.re)|))) volume :=
          (ha.add hb_int).const_mul C₀
        exact hdom'.congr (Eventually.of_forall fun t => by simp only [heq1_pt t, heq2_pt t])
      have hint_fn_norm : IntegrableOn (fun t : ℝ =>
          ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖) (Ioi (0 : ℝ)) := by
        refine hdom1_int.integrableOn.mono' h_cont_fn.norm.aestronglyMeasurable
          (Eventually.of_forall fun t => ?_)
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact h_pt t
      have h_int_val1 : ∫ t in Ioi (0 : ℝ), C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
            Real.exp (-π * |(b + (ζ + (t : ℂ))).re|)) ≤ 4 * C₀ / π := by
        have ha : Integrable (fun t : ℝ => Real.exp (-π * |t - (b.re - ζ.re)|)) volume :=
          integrable_exp_neg_pi_abs.comp_sub_right _
        have hb_int : Integrable (fun t : ℝ => Real.exp (-π * |t - (-b.re - ζ.re)|)) volume :=
          integrable_exp_neg_pi_abs.comp_sub_right _
        have heq1_pt : ∀ t : ℝ, |(b - (ζ + (t : ℂ))).re| = |t - (b.re - ζ.re)| := fun t => by
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
          rw [show b.re - (ζ.re + t) = -(t - (b.re - ζ.re)) by ring, abs_neg]
        have heq2_pt : ∀ t : ℝ, |(b + (ζ + (t : ℂ))).re| = |t - (-b.re - ζ.re)| := fun t => by
          simp only [Complex.add_re, Complex.ofReal_re]
          rw [show b.re + (ζ.re + t) = t - (-b.re - ζ.re) by ring]
        calc ∫ t in Ioi (0 : ℝ), C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
              Real.exp (-π * |(b + (ζ + (t : ℂ))).re|))
            ≤ ∫ t : ℝ, C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
                Real.exp (-π * |(b + (ζ + (t : ℂ))).re|)) :=
              setIntegral_le_integral hdom1_int (Eventually.of_forall fun _ => by positivity)
          _ = ∫ t : ℝ, C₀ * (Real.exp (-π * |t - (b.re - ζ.re)|) +
                Real.exp (-π * |t - (-b.re - ζ.re)|)) :=
              integral_congr_ae (Eventually.of_forall fun t => by simp only [heq1_pt t, heq2_pt t])
          _ = 4 * C₀ / π := by
              rw [integral_const_mul, integral_add ha hb_int,
                integral_sub_right_eq_self (fun u : ℝ => Real.exp (-π * |u|)) (b.re - ζ.re),
                integral_sub_right_eq_self (fun u : ℝ => Real.exp (-π * |u|)) (-b.re - ζ.re),
                integral_exp_neg_pi_abs]
              ring
      have hle1 : ‖phiZeta ζ b‖ ≤ C := by
        unfold phiZeta
        calc ‖∫ t in Ioi (0 : ℝ), (sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ))))‖
            ≤ ∫ t in Ioi (0 : ℝ), ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t in Ioi (0 : ℝ), C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
                Real.exp (-π * |(b + (ζ + (t : ℂ))).re|)) :=
              setIntegral_mono_on hint_fn_norm hdom1_int.integrableOn measurableSet_Ioi
                fun t _ => h_pt t
          _ ≤ 4 * C₀ / π := h_int_val1
          _ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
      rcases le_or_gt ζ.re |b.re| with hle | hlt
      · rwa [min_eq_left (Real.one_le_exp (by nlinarith)), mul_one]
      · rw [min_eq_right (Real.exp_le_one_iff.mpr (by nlinarith))]
        have hdom2 : IntegrableOn (fun t : ℝ => 2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) *
            Real.exp (-π * t)) (Ioi (0 : ℝ)) :=
          (integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul _
        have hpt2 : ∀ t ∈ Ioi (0 : ℝ),
            ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖ ≤
              2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by
          intro t ht
          have ht0 : 0 ≤ t := ht.le
          have h1 : ζ.re - |b.re| + t ≤ |(b - (ζ + (t : ℂ))).re| := by
            rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
            calc ζ.re - |b.re| + t ≤ ζ.re + t - b.re := by linarith [le_abs_self b.re]
              _ ≤ |b.re - (ζ.re + t)| := by
                rw [abs_sub_comm]
                exact (le_of_eq (by ring)).trans (le_abs_self (ζ.re + t - b.re))
          have h2 : ζ.re - |b.re| + t ≤ |(b + (ζ + (t : ℂ))).re| := by
            rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]
            calc ζ.re - |b.re| + t ≤ b.re + (ζ.re + t) := by linarith [neg_le_abs b.re]
              _ ≤ |b.re + (ζ.re + t)| := le_abs_self _
          have e1 : Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) ≤
              Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
          have e2 : Real.exp (-π * |(b + (ζ + (t : ℂ))).re|) ≤
              Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
          calc ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖
              ≤ C₀ * (Real.exp (-π * |(b - (ζ + (t : ℂ))).re|) +
                  Real.exp (-π * |(b + (ζ + (t : ℂ))).re|)) := h_pt t
            _ ≤ C₀ * (Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) +
                  Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t)) := by gcongr
            _ = 2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by ring
        calc ‖phiZeta ζ b‖
            ≤ ∫ t in Ioi (0 : ℝ), ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖ := by
                unfold phiZeta; exact norm_integral_le_integral_norm _
          _ ≤ ∫ t in Ioi (0 : ℝ), 2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) :=
                setIntegral_mono_on hint_fn_norm hdom2 measurableSet_Ioi hpt2
          _ = (2 * C₀ / π) * Real.exp (-π * (ζ.re - |b.re|)) := by
                rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith : -π < 0) 0,
                  mul_zero, Real.exp_zero]; ring
          _ ≤ C * Real.exp (-π * (ζ.re - |b.re|)) := by
                gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
    · have h1 := hbd_ij i j (Nat.pos_of_ne_zero hpos) hij4 hb hζ
      have h_le1 : Real.exp (-π * abs (ζ.re - |b.re|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (ζ.re - |b.re|)])
      have h_le2 : Real.exp (-π * abs (ζ.re - |b.re|)) ≤ Real.exp (-π * (ζ.re - |b.re|)) :=
        Real.exp_le_exp.mpr (by nlinarith [le_abs_self (ζ.re - |b.re|)])
      calc ‖combPhiDeriv i j ζ b‖
          ≤ 2 * M * Real.exp (-π * abs (ζ.re - |b.re|)) := h1
        _ ≤ C * Real.exp (-π * abs (ζ.re - |b.re|)) := by gcongr; exact le_max_left _ _
        _ ≤ C * min 1 (Real.exp (-π * (ζ.re - |b.re|))) := by gcongr; exact le_min h_le1 h_le2

lemma hasDerivAt_combPhiDeriv_b {i j : ℕ} {ζ b : ℂ} (hb : b ∈ combNOpen) (hζ : ζ ∈ combZOpen) :
    HasDerivAt (fun b' => combPhiDeriv i j ζ b') (combPhiDeriv (i + 1) j ζ b) b := by
  rcases eq_or_ne (i + j) 0 with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
    simpa [combPhiDeriv] using hasDerivAt_phiZeta_b hb hζ
  · have hpos' : ¬(i + 1 + j = 0) := by omega
    simp only [combPhiDeriv, hpos, hpos', ↓reduceIte]
    rw [show (i + 1 + j - 1) = (i + j - 1) + 1 by omega]
    have hopenS : IsOpen {w : ℂ | 0 < w.im ∧ w.im < 1} :=
      (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have han : AnalyticOnNhd ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} :=
      comb_sinhKernel_differentiableOn.analyticOnNhd hopenS
    have hdiff_k : DifferentiableOn ℂ (iteratedDeriv (i + j - 1) sinhKernel)
        {w : ℂ | 0 < w.im ∧ w.im < 1} := by
      rw [iteratedDeriv_eq_iterate]
      exact (han.iterated_deriv (i + j - 1)).differentiableOn
    have hb_im := abs_lt.mp (show |b.im - 1 / 2| < 9 / 32 from hb)
    have hζ_im := abs_lt.mp hζ.2
    have hb1 : 0 < (b - ζ).im ∧ (b - ζ).im < 1 := by
      simp only [Complex.sub_im]; constructor <;> linarith
    have hb2 : 0 < (b + ζ).im ∧ (b + ζ).im < 1 := by
      simp only [Complex.add_im]; constructor <;> linarith
    have hd1 : HasDerivAt (iteratedDeriv (i + j - 1) sinhKernel)
        (iteratedDeriv (i + j - 1 + 1) sinhKernel (b - ζ)) (b - ζ) := by
      rw [iteratedDeriv_succ]
      exact ((hdiff_k _ hb1).differentiableAt (hopenS.mem_nhds hb1)).hasDerivAt
    have hd2 : HasDerivAt (iteratedDeriv (i + j - 1) sinhKernel)
        (iteratedDeriv (i + j - 1 + 1) sinhKernel (b + ζ)) (b + ζ) := by
      rw [iteratedDeriv_succ]
      exact ((hdiff_k _ hb2).differentiableAt (hopenS.mem_nhds hb2)).hasDerivAt
    have hd := ((hd1.comp b ((hasDerivAt_id b).sub_const ζ)).const_mul ((-1 : ℂ) ^ j)).add
      (hd2.comp b ((hasDerivAt_id b).add_const ζ))
    exact hd.congr_deriv (by ring)

lemma hasDerivAt_combPhiDeriv_zeta {i j : ℕ} {ζ b : ℂ} (hb : b ∈ combNOpen) (hζ : ζ ∈ combZOpen) :
    HasDerivAt (fun ζ' => combPhiDeriv i j ζ' b) (combPhiDeriv i (j + 1) ζ b) ζ := by
  rcases eq_or_ne (i + j) 0 with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
    simpa [combPhiDeriv] using hasDerivAt_phiZeta_zeta hb hζ
  · have hpos' : ¬(i + (j + 1) = 0) := by omega
    simp only [combPhiDeriv, hpos, hpos', ↓reduceIte]
    rw [show (i + (j + 1) - 1) = (i + j - 1) + 1 by omega]
    have hopenS : IsOpen {w : ℂ | 0 < w.im ∧ w.im < 1} :=
      (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have han : AnalyticOnNhd ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} :=
      comb_sinhKernel_differentiableOn.analyticOnNhd hopenS
    have hdiff_k : DifferentiableOn ℂ (iteratedDeriv (i + j - 1) sinhKernel)
        {w : ℂ | 0 < w.im ∧ w.im < 1} := by
      rw [iteratedDeriv_eq_iterate]
      exact (han.iterated_deriv (i + j - 1)).differentiableOn
    have hb_im := abs_lt.mp (show |b.im - 1 / 2| < 9 / 32 from hb)
    have hζ_im := abs_lt.mp hζ.2
    have hb1 : 0 < (b - ζ).im ∧ (b - ζ).im < 1 := by
      simp only [Complex.sub_im]; constructor <;> linarith
    have hb2 : 0 < (b + ζ).im ∧ (b + ζ).im < 1 := by
      simp only [Complex.add_im]; constructor <;> linarith
    have hd1 : HasDerivAt (iteratedDeriv (i + j - 1) sinhKernel)
        (iteratedDeriv (i + j - 1 + 1) sinhKernel (b - ζ)) (b - ζ) := by
      rw [iteratedDeriv_succ]
      exact ((hdiff_k _ hb1).differentiableAt (hopenS.mem_nhds hb1)).hasDerivAt
    have hd2 : HasDerivAt (iteratedDeriv (i + j - 1) sinhKernel)
        (iteratedDeriv (i + j - 1 + 1) sinhKernel (b + ζ)) (b + ζ) := by
      rw [iteratedDeriv_succ]
      exact ((hdiff_k _ hb2).differentiableAt (hopenS.mem_nhds hb2)).hasDerivAt
    have hd := ((hd1.comp ζ ((hasDerivAt_id ζ).const_sub b)).const_mul ((-1 : ℂ) ^ j)).add
      (hd2.comp ζ ((hasDerivAt_id ζ).const_add b))
    exact hd.congr_deriv (by rw [pow_succ]; ring)

lemma iteratedDeriv_combPhiDeriv_b (i j : ℕ) {ζ b : ℂ} (hb : b ∈ combNOpen) (hζ : ζ ∈ combZOpen) :
    iteratedDeriv i (fun b' => combPhiDeriv 0 j ζ b') b = combPhiDeriv i j ζ b := by
  induction i generalizing b with
  | zero => simp
  | succ i ih =>
    have h_ev : (fun b' => iteratedDeriv i (fun w => combPhiDeriv 0 j ζ w) b') =ᶠ[𝓝 b]
        fun b' => combPhiDeriv i j ζ b' := by
      filter_upwards [isOpen_combNOpen.mem_nhds hb] with b' hb'
      exact ih hb'
    rw [iteratedDeriv_succ, h_ev.deriv_eq]
    exact (hasDerivAt_combPhiDeriv_b hb hζ).deriv

/-! ### Section 2: Averaging and detuning perturbation bounds for `combPhiDeriv` -/

/-- Dependence of `∂_b^i φ_y` on the site `y`: `‖∂_b^i φ_y - ∂_b^i φ_x‖ ≤ C (y - x)` for `0 ≤ x ≤ y`, on `combNMid`,
`i ≤ 2`. -/
lemma combPhiDeriv_sub_le :
    ∃ C > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {x y : ℝ} {b : ℂ}, 0 ≤ x → x ≤ y → b ∈ combNMid →
      ‖combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (x : ℂ) b‖ ≤ C * (y - x) := by
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  refine ⟨C, hC, fun i hi x y b hx hxy hb => ?_⟩
  have hdiff : ∀ t ∈ Icc x y,
      HasDerivWithinAt (fun u : ℝ => combPhiDeriv i 0 (u : ℂ) b)
        (combPhiDeriv i 1 (t : ℂ) b) (Icc x y) t := by
    intro t ht
    have ht_nn : 0 ≤ t := hx.trans ht.1
    have hζ : (t : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith)
    have hc := (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0)
      (combNMid_subset_combNOpen hb) hζ).comp_ofReal
    exact (hc.congr_deriv (by ring)).hasDerivWithinAt
  have hnorm : ∀ t ∈ Ico x y, ‖combPhiDeriv i 1 (t : ℂ) b‖ ≤ C := by
    intro t ht
    have hζ : (t : ℂ) ∈ combZ := ofReal_mem_combZ (hx.trans ht.1)
    calc ‖combPhiDeriv i 1 (t : ℂ) b‖
        ≤ C * min 1 (Real.exp (-π * (t - |b.re|))) := hbd i 1 (by omega) hb hζ
      _ ≤ C * 1 := by gcongr; exact min_le_left _ _
      _ = C := mul_one C
  exact norm_image_sub_le_of_norm_deriv_le_segment' hdiff hnorm y (right_mem_Icc.mpr hxy)

lemma combPhiDeriv_sub_xiStar_le :
    ∃ C > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {y : ℝ} {b : ℂ}, xiStar ≤ y → b ∈ combNMid →
      ‖combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (xiStar : ℂ) b‖ ≤ C * (y - xiStar) := by
  obtain ⟨C, hC, h⟩ := combPhiDeriv_sub_le
  exact ⟨C, hC, fun i hi y b hy hb => h i hi xiStar_pos.le hy hb⟩

lemma combPhiDeriv_detune_bound :
    ∃ C > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {χ ε : ℝ} {b : ℂ},
      0 ≤ χ → |ε| ≤ 1 / 8 → b ∈ combNMid →
      ‖combPhiDeriv i 0 ((χ : ℂ) + (ε : ℂ) * Complex.I) b +
          combPhiDeriv i 0 ((χ : ℂ) - (ε : ℂ) * Complex.I) b -
          2 * combPhiDeriv i 0 (χ : ℂ) b‖ ≤
        C * ε ^ 2 * Real.exp (-π * abs (χ - |b.re|)) := by
  obtain ⟨C, hC, hbd_exp, _⟩ := combPhiDeriv_bound
  refine ⟨C, hC, fun i hi χ ε b hχ hε hb => ?_⟩
  let h : ℝ → ℂ := fun s =>
    combPhiDeriv i 0 ((χ : ℂ) + (s : ℂ) * Complex.I) b +
    combPhiDeriv i 0 ((χ : ℂ) - (s : ℂ) * Complex.I) b -
    2 * combPhiDeriv i 0 (χ : ℂ) b
  let h' : ℝ → ℂ := fun s =>
    Complex.I * (combPhiDeriv i 1 ((χ : ℂ) + (s : ℂ) * Complex.I) b -
      combPhiDeriv i 1 ((χ : ℂ) - (s : ℂ) * Complex.I) b)
  have hderiv : ∀ s : ℝ, |s| ≤ 1 / 8 → HasDerivAt h (h' s) s := by
    intro s hs
    have hζ1 := ofReal_add_I_mul_mem_combZOpen (by linarith : (-1 / 4 : ℝ) < χ) hs
    have hζ2 := ofReal_sub_I_mul_mem_combZOpen (by linarith : (-1 / 4 : ℝ) < χ) hs
    have hl1 : HasDerivAt (fun t : ℝ => (χ : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
      have hof : HasDerivAt (fun t : ℝ => ((t : ℂ) * Complex.I)) ((Complex.ofRealCLM 1) * Complex.I) s :=
        Complex.ofRealCLM.hasDerivAt.mul_const Complex.I
      exact ((hasDerivAt_const s (χ : ℂ)).add hof).congr_deriv (by simp)
    have hl2 : HasDerivAt (fun t : ℝ => (χ : ℂ) - (t : ℂ) * Complex.I) (-Complex.I) s := by
      have hof : HasDerivAt (fun t : ℝ => ((t : ℂ) * Complex.I)) ((Complex.ofRealCLM 1) * Complex.I) s :=
        Complex.ofRealCLM.hasDerivAt.mul_const Complex.I
      exact ((hasDerivAt_const s (χ : ℂ)).sub hof).congr_deriv (by simp)
    have hd1 := HasDerivAt.scomp_of_eq s
      (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0) (combNMid_subset_combNOpen hb) hζ1) hl1 rfl
    have hd2 := HasDerivAt.scomp_of_eq s
      (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0) (combNMid_subset_combNOpen hb) hζ2) hl2 rfl
    have htot := (hd1.add hd2).sub_const (2 * combPhiDeriv i 0 (χ : ℂ) b)
    exact htot.congr_deriv (by dsimp [h']; simp [smul_eq_mul]; ring)
  have h_pair_bound : ∀ s : ℝ, |s| ≤ 1 / 8 →
      ‖h' s‖ ≤ 2 * C * |s| * Real.exp (-π * abs (χ - |b.re|)) := by
    intro s hs
    let g : ℝ → ℂ := fun t => combPhiDeriv i 1 ((χ : ℂ) + (t : ℂ) * Complex.I) b
    have hg_deriv : ∀ t ∈ Icc (-|s|) |s|,
        HasDerivWithinAt g (Complex.I * combPhiDeriv i 2 ((χ : ℂ) + (t : ℂ) * Complex.I) b)
          (Icc (-|s|) |s|) t := by
      intro t ht
      have ht_abs : |t| ≤ 1 / 8 := (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans hs
      have hζt := ofReal_add_I_mul_mem_combZOpen (by linarith : (-1 / 4 : ℝ) < χ) ht_abs
      have hl : HasDerivAt (fun u : ℝ => (χ : ℂ) + (u : ℂ) * Complex.I) Complex.I t := by
        have hof : HasDerivAt (fun u : ℝ => ((u : ℂ) * Complex.I)) ((Complex.ofRealCLM 1) * Complex.I) t :=
          Complex.ofRealCLM.hasDerivAt.mul_const Complex.I
        exact ((hasDerivAt_const t (χ : ℂ)).add hof).congr_deriv (by simp)
      exact ((HasDerivAt.scomp_of_eq t
        (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 1) (combNMid_subset_combNOpen hb) hζt)
        hl rfl).congr_deriv (by simp [smul_eq_mul])).hasDerivWithinAt
    have hg_norm : ∀ t ∈ Ico (-|s|) |s|,
        ‖Complex.I * combPhiDeriv i 2 ((χ : ℂ) + (t : ℂ) * Complex.I) b‖ ≤
          C * Real.exp (-π * abs (χ - |b.re|)) := by
      intro t ht
      have ht_abs : |t| ≤ 1 / 8 := (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans hs
      have hζt : (χ : ℂ) + (t : ℂ) * Complex.I ∈ combZ := ofReal_add_I_mul_mem_combZ hχ ht_abs
      rw [norm_mul, Complex.norm_I, one_mul]
      have h1 := hbd_exp i 2 (by omega) (by omega) hb hζt
      simpa using h1
    have hdiff_sub : ‖g s - g (-s)‖ ≤ 2 * C * |s| * Real.exp (-π * abs (χ - |b.re|)) := by
      have hm := norm_image_sub_le_of_norm_deriv_le_segment' hg_deriv hg_norm |s|
        (right_mem_Icc.mpr (by linarith [abs_nonneg s]))
      have hm2 : ‖g |s| - g (-|s|)‖ ≤ 2 * C * |s| * Real.exp (-π * abs (χ - |b.re|)) :=
        hm.trans_eq (by ring)
      rcases le_or_gt 0 s with hs0 | hs0
      · have hs' : |s| = s := abs_of_nonneg hs0
        calc ‖g s - g (-s)‖ = ‖g |s| - g (-|s|)‖ := by rw [hs']
          _ ≤ 2 * C * |s| * Real.exp (-π * abs (χ - |b.re|)) := hm2
      · have hs' : |s| = -s := abs_of_neg hs0
        have hm3 : ‖g (-s) - g s‖ ≤ 2 * C * |s| * Real.exp (-π * abs (χ - |b.re|)) := by
          simpa [hs', neg_neg] using hm2
        exact (norm_sub_rev (g s) (g (-s))).trans_le hm3
    have heq : ‖h' s‖ = ‖g s - g (-s)‖ := by
      dsimp [h', g]
      rw [norm_mul, Complex.norm_I, one_mul]
      congr 1; push_cast; ring
    exact heq ▸ hdiff_sub
  have h0 : h 0 = 0 := by dsimp [h]; simp; ring
  have h_even : h (-ε) = h ε := by dsimp [h]; push_cast; ring
  have hcont_h' : ContinuousOn h' (Icc 0 |ε|) := by
    intro s hs
    have hs_abs : |s| ≤ 1 / 8 := by rw [abs_of_nonneg hs.1]; exact hs.2.trans hε
    have hζ1 := ofReal_add_I_mul_mem_combZOpen (by linarith : (-1 / 4 : ℝ) < χ) hs_abs
    have hζ2 := ofReal_sub_I_mul_mem_combZOpen (by linarith : (-1 / 4 : ℝ) < χ) hs_abs
    have hl1 : HasDerivAt (fun t : ℝ => (χ : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
      have hof : HasDerivAt (fun t : ℝ => ((t : ℂ) * Complex.I)) ((Complex.ofRealCLM 1) * Complex.I) s :=
        Complex.ofRealCLM.hasDerivAt.mul_const Complex.I
      exact ((hasDerivAt_const s (χ : ℂ)).add hof).congr_deriv (by simp)
    have hl2 : HasDerivAt (fun t : ℝ => (χ : ℂ) - (t : ℂ) * Complex.I) (-Complex.I) s := by
      have hof : HasDerivAt (fun t : ℝ => ((t : ℂ) * Complex.I)) ((Complex.ofRealCLM 1) * Complex.I) s :=
        Complex.ofRealCLM.hasDerivAt.mul_const Complex.I
      exact ((hasDerivAt_const s (χ : ℂ)).sub hof).congr_deriv (by simp)
    have hc1 : ContinuousAt (fun t : ℝ => combPhiDeriv i 1 ((χ : ℂ) + (t : ℂ) * Complex.I) b) s :=
      ContinuousAt.comp (f := fun t : ℝ => (χ : ℂ) + (t : ℂ) * Complex.I)
        (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 1)
          (combNMid_subset_combNOpen hb) hζ1).continuousAt hl1.continuousAt
    have hc2 : ContinuousAt (fun t : ℝ => combPhiDeriv i 1 ((χ : ℂ) - (t : ℂ) * Complex.I) b) s :=
      ContinuousAt.comp (f := fun t : ℝ => (χ : ℂ) - (t : ℂ) * Complex.I)
        (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 1)
          (combNMid_subset_combNOpen hb) hζ2).continuousAt hl2.continuousAt
    exact (continuousAt_const.mul (hc1.sub hc2)).continuousWithinAt
  have hint : IntervalIntegrable h' volume 0 |ε| := hcont_h'.intervalIntegrable_of_Icc (abs_nonneg ε)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := |ε|)
    (fun s hs => hderiv s (by
      rw [Set.uIcc_of_le (abs_nonneg ε)] at hs
      rw [abs_of_nonneg hs.1]
      exact hs.2.trans hε)) hint
  rw [h0, sub_zero] at hftc
  have hnorm_h_abs : ‖h |ε|‖ ≤ C * ε ^ 2 * Real.exp (-π * abs (χ - |b.re|)) := by
    rw [← hftc]
    have hle_int : ∫ s in (0 : ℝ)..|ε|, ‖h' s‖ ≤
        ∫ s in (0 : ℝ)..|ε|, 2 * C * s * Real.exp (-π * abs (χ - |b.re|)) := by
      refine intervalIntegral.integral_mono_on (abs_nonneg ε)
        (hcont_h'.norm.intervalIntegrable_of_Icc (abs_nonneg ε))
        ((continuous_const.mul continuous_id |>.mul continuous_const).intervalIntegrable _ _)
        fun s hs => by
          have hs_abs : |s| ≤ 1 / 8 := by rw [abs_of_nonneg hs.1]; exact hs.2.trans hε
          simpa [abs_of_nonneg hs.1] using h_pair_bound s hs_abs
    have hval : ∫ s in (0 : ℝ)..|ε|, 2 * C * s * Real.exp (-π * abs (χ - |b.re|)) =
        C * ε ^ 2 * Real.exp (-π * abs (χ - |b.re|)) := by
      have heq : (fun s : ℝ => 2 * C * s * Real.exp (-π * abs (χ - |b.re|))) =
          fun s : ℝ => (2 * C * Real.exp (-π * abs (χ - |b.re|))) * s := by ext s; ring
      rw [heq, intervalIntegral.integral_const_mul, integral_id]
      simp [sq_abs]; ring
    exact (intervalIntegral.norm_integral_le_integral_norm (abs_nonneg ε)).trans (hle_int.trans_eq hval)
  rcases le_or_gt 0 ε with hε0 | hε0
  · rwa [abs_of_nonneg hε0] at hnorm_h_abs
  · rwa [abs_of_neg hε0, h_even] at hnorm_h_abs

/-! ### Section 3: Reference comb logarithm, edge phase `Φ₀`, and Euler--Maclaurin `Φ₁` -/

/-- Index-$f$ logarithmic comb phase on $\mathcal N$:
$\log B^{(f)}(b) = i\pi + \varphi_{\chi_f}(b) +
  \sum_{k \ge f+1} (\varphi_{\chi_k + i\varepsilon_k}(b) + \varphi_{\chi_k - i\varepsilon_k}(b))$. -/
noncomputable def logRefComb (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) : ℂ :=
  (π : ℂ) * Complex.I + phiZeta (chiQuantile c' f : ℂ) b +
    ∑' m : ℕ, (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
      phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b)

/-- Asymptotic edge phase potential $\Phi_0(b) = \int_{\xi_*}^\infty \rho_U(y) \varphi_y(b)\,dy$. -/
noncomputable def phi0 (b : ℂ) : ℂ :=
  ∫ y in Ioi xiStar, (rhoU y : ℂ) * phiZeta (y : ℂ) b

/-- $n_1 = f - 1/4$. -/
noncomputable def n1Comb (f : ℕ) : ℝ := (f : ℝ) - 1 / 4

/-- Normalized tip average $\bar\varphi^{(f)}(b) = \frac{c'}{2 n_1} \int_{\xi_*}^{\chi_f} \rho_U(y)\varphi_y(b)\,dy$. -/
noncomputable def barPhi (c' : ℝ) (f : ℕ) (b : ℂ) : ℂ :=
  ((1 / (2 * n1Comb f) : ℝ) : ℂ) * (c' : ℂ) *
    ∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * phiZeta (y : ℂ) b

/-- Detuning shift $\Delta_{\mathrm{det}}^{(f)}(b) =
\sum_{k \ge f+1} (\varphi_{\chi_k + i\varepsilon_k}(b) + \varphi_{\chi_k - i\varepsilon_k}(b) - 2\varphi_{\chi_k}(b))$. -/
noncomputable def deltaDetComb (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) : ℂ :=
  ∑' m : ℕ,
    (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
      phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b -
      2 * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b)

/-- Periodic second Bernoulli polynomial on $[0, 1]$: $P_2(t) = \frac{1}{2}(t^2 - t + \frac{1}{6})$. -/
noncomputable def bernoulliP2 (t : ℝ) : ℝ := (t ^ 2 - t + 1 / 6) / 2

lemma abs_bernoulliP2_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |bernoulliP2 t| ≤ 1 / 12 := by
  unfold bernoulliP2
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t - 1 / 2)]

/-- First $a$-derivative of $2\,\partial_b^i \varphi_{\chi_a}(b)$. -/
noncomputable def emKernFDeriv (i : ℕ) (c' : ℝ) (b : ℂ) (a : ℝ) : ℂ :=
  2 * combPhiDeriv i 1 (chiQuantile c' a : ℂ) b * (chiDeriv c' a : ℂ)

/-- Second $a$-derivative of $2\,\partial_b^i \varphi_{\chi_a}(b)$. -/
noncomputable def emKernFSecond (i : ℕ) (c' : ℝ) (b : ℂ) (a : ℝ) : ℂ :=
  2 * (combPhiDeriv i 2 (chiQuantile c' a : ℂ) b * ((chiDeriv c' a ^ 2 : ℝ) : ℂ) +
    combPhiDeriv i 1 (chiQuantile c' a : ℂ) b * ((chiSecond c' a : ℝ) : ℂ))

/-- Second-order Euler--Maclaurin remainder integral $R_2^{(f)}$ (and its $i$-th $b$-derivative). -/
noncomputable def emRem2Deriv (i : ℕ) (c' : ℝ) (f : ℕ) (b : ℂ) : ℂ :=
  -∑' m : ℕ, ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond i c' b ((f + m : ℕ) + t)

/-- Total Euler--Maclaurin remainder $R_{\mathrm{EM}}^{(f)}(b) = -\frac{1}{12} F'(f) + R_2^{(f)}(b)$. -/
noncomputable def emRem (c' : ℝ) (f : ℕ) (b : ℂ) : ℂ :=
  -(1 / 12 : ℂ) * emKernFDeriv 0 c' b f + emRem2Deriv 0 c' f b

/-- Subleading phase remainder $\Phi_1^{(f)} = i\pi - 2 n_1 \bar\varphi^{(f)} + \Delta_{\mathrm{det}}^{(f)} + R_{\mathrm{EM}}^{(f)}$. -/
noncomputable def phi1Comb (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) : ℂ :=
  (π : ℂ) * Complex.I - ((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b +
    deltaDetComb c' f η₀ b + emRem c' f b

lemma cexp_logRefComb (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ {b : ℂ}, b ∈ combN →
      Complex.exp (logRefComb c' f η₀ b) = refComb c' f η₀ b := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [eventually_gt_atTop 0, h_ev] with c' hc' ⟨hgap_k, _, _, hgap_1⟩ b hb
  have hb_strip : |b.im| ≤ 7 / 8 := by
    have := abs_le.mp (show |b.im - 1 / 2| ≤ 1 / 4 from hb)
    rw [abs_le]; constructor <;> linarith
  have hχ_nn : ∀ a : ℝ, 1 / 4 ≤ a → 0 ≤ chiQuantile c' a := fun a ha =>
    xiStar_pos.le.trans (chiQuantile_spec hc' ha).1
  have ha_f : (1 / 4 : ℝ) ≤ (f : ℕ) := by
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  have ha_m : ∀ m : ℕ, (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := fun m => by
    have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    linarith
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (f + 1 + m)| ≤ 1 / 8 := fun m => by
    have hgap_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn (ha_m m)
        ((ha_m m).trans (by linarith)) (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgap_nn)]
    have hgk := (hgap_k (f + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (f + 1 + m) ≤ (1 / 4) * (1 / 2) := mul_le_mul hη₀1 hgk hgap_nn (by norm_num)
      _ = 1 / 8 := by norm_num
  have hsum_term : Summable fun m : ℕ =>
      phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
      phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b := by
    obtain ⟨C, hC, hbd⟩ := norm_phiZeta_le
    refine Summable.of_norm_bounded (g := fun m : ℕ => 2 * C * Real.exp (π * |b.re|) *
        Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ))) ?_ fun m => ?_
    · exact (summable_exp_neg_pi_chiQuantile hc' f).mul_left (2 * C * Real.exp (π * |b.re|))
    · have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
        ofReal_add_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
      have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
        ofReal_sub_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
      have hn1 := (hbd hb hζ1).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      have hn2 := (hbd hb hζ2).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      have hexp_eq : C * Real.exp (-π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) =
          C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by
        rw [show -π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) =
          π * |b.re| + -π * chiQuantile c' (f + 1 + m : ℕ) by ring, Real.exp_add]; ring
      have hre1 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
          chiQuantile c' (f + 1 + m : ℕ) := by simp
      have hre2 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
          chiQuantile c' (f + 1 + m : ℕ) := by simp
      rw [hre1] at hn1; rw [hre2] at hn2
      rw [hexp_eq] at hn1 hn2
      exact (norm_add_le _ _).trans (by linarith)
  have hexp_tsum : Complex.exp (∑' m : ℕ, (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
      phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b)) =
      ∏' m : ℕ, (blaschkeT ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b *
        blaschkeT ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b) := by
    rw [← hsum_term.hasSum.cexp.tprod_eq]
    refine tprod_congr fun m => ?_
    dsimp only [Function.comp_apply]
    have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_add_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
    have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_sub_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
    rw [Complex.exp_add, cexp_phiZeta hb hζ1, cexp_phiZeta hb hζ2, neg_mul_neg]
  unfold logRefComb refComb
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I,
    cexp_phiZeta hb ⟨by simp [hχ_nn _ ha_f], by simp⟩, hexp_tsum]
  ring

/-! ### Section 4: Integrability, change of variables `y = χ_a`, and Euler--Maclaurin identity -/

private lemma chiQuantile_cov_complex {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) (hab : a ≤ b)
    (g : ℝ → ℂ) :
    ∫ t in a..b, (chiDeriv c' t : ℂ) * g (chiQuantile c' t) =
      ∫ y in (chiQuantile c' a)..(chiQuantile c' b), g y := by
  have hc_on : ContinuousOn (chiQuantile c') (Set.uIcc a b) :=
    (continuousOn_chiQuantile hc').mono fun t ht =>
      ha.trans (Set.uIcc_of_le hab ▸ ht).1
  have hd_on : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt (chiQuantile c') (chiDeriv c' t) t := by
    intro t ht; rw [min_eq_left hab, max_eq_right hab] at ht
    exact (hasDerivAt_chiQuantile hc' (lt_of_le_of_lt ha ht.1)).1
  have hpos : ∀ t ∈ Ioo (min a b) (max a b), 0 ≤ chiDeriv c' t := by
    intro t ht; rw [min_eq_left hab, max_eq_right hab] at ht
    unfold chiDeriv
    exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
  have hid := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := g) hc_on hd_on hpos
  simpa only [Function.comp_def, Complex.real_smul] using hid

private lemma rhoU_le_lin_bound {y : ℝ} (hy : xiStar ≤ y) :
    rhoU y ≤ (4 / 3 : ℝ) * y + 4 / (3 * π) := by
  have hpi := Real.pi_pos
  have harccosh_le : ∀ x : ℝ, 1 ≤ x → arccoshR x ≤ Real.log (2 * x) := by
    intro x hx
    unfold arccoshR
    apply Real.log_le_log (by have := Real.sqrt_nonneg (x ^ 2 - 1); linarith)
    have hsqrt : √(x ^ 2 - 1) ≤ x := by rw [Real.sqrt_le_left (by positivity)]; linarith
    linarith
  rw [rhoU_eq_of_ge hy]
  have hy_nn : 0 ≤ y := xiStar_pos.le.trans hy
  have hs1 : 1 ≤ Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith)
  have hsh_le : 2 * Real.sinh (π * y) ≤ Real.exp (π * y) := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-(π * y))]
  have hlog_le : arccoshR (Real.sinh (π * y)) ≤ π * y := by
    refine (harccosh_le _ hs1).trans ?_
    calc Real.log (2 * Real.sinh (π * y)) ≤ Real.log (Real.exp (π * y)) :=
          Real.log_le_log (by positivity) hsh_le
      _ = π * y := Real.log_exp _
  calc (4 / (3 * π)) * arccoshR (Real.sinh (π * y))
      ≤ (4 / (3 * π)) * (π * y) := by gcongr
    _ = (4 / 3) * y := by field_simp [hpi.ne']
    _ ≤ (4 / 3) * y + 4 / (3 * π) := le_add_of_nonneg_right (by positivity)

private lemma integrable_mul_exp_neg_pi_Ioi {M : ℝ} (hM : xiStar ≤ M) :
    IntegrableOn (fun y : ℝ => rhoU y * Real.exp (-π * y)) (Ioi M) volume := by
  have hpi := Real.pi_pos
  have hcont : ContinuousOn (fun y : ℝ => rhoU y * Real.exp (-π * y)) (Ioi M) :=
    (continuousOn_rhoU.mono (Ioi_subset_Ici_self.trans (Ici_subset_Ici.mpr hM))).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hdom : IntegrableOn (fun y : ℝ => ((4 / 3 : ℝ) * y + 4 / (3 * π)) * Real.exp (-π * y))
      (Ioi (0 : ℝ)) volume := by
    have h1 : IntegrableOn (fun y : ℝ => y * Real.exp (-π * y)) (Ioi (0 : ℝ)) volume := by
      have hle : ∀ y ∈ Ioi (0 : ℝ), ‖y * Real.exp (-π * y)‖ ≤ (2 / π) * Real.exp (-(π / 2) * y) := by
        intro y hy
        have hy0 : 0 < y := hy
        rw [Real.norm_of_nonneg (mul_nonneg hy0.le (Real.exp_pos _).le)]
        have hexp : (π / 2) * y ≤ Real.exp ((π / 2) * y) := by
          linarith [Real.add_one_lt_exp (show (π / 2) * y ≠ 0 by positivity)]
        calc y * Real.exp (-π * y) = (2 / π) * ((π / 2) * y) * Real.exp (-π * y) := by
              field_simp [hpi.ne']
          _ ≤ (2 / π) * Real.exp ((π / 2) * y) * Real.exp (-π * y) := by
              gcongr
          _ = (2 / π) * Real.exp (-(π / 2) * y) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      exact ((integrableOn_exp_mul_Ioi (by linarith : -(π / 2) < 0) 0).const_mul (2 / π)).mono'
        (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioi hle)
    have h2 : IntegrableOn (fun y : ℝ => Real.exp (-π * y)) (Ioi (0 : ℝ)) volume :=
      integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0
    have heq : (fun y : ℝ => ((4 / 3 : ℝ) * y + 4 / (3 * π)) * Real.exp (-π * y)) =
        fun y => (4 / 3 : ℝ) * (y * Real.exp (-π * y)) + (4 / (3 * π)) * Real.exp (-π * y) := by
      ext y; ring
    rw [heq]
    exact (h1.const_mul _).add (h2.const_mul _)
  refine (hdom.mono_set (Ioi_subset_Ioi (xiStar_pos.le.trans hM))).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
  have hy_xi : xiStar ≤ y := hM.trans hy.le
  rw [Real.norm_of_nonneg (mul_nonneg (rhoU_nonneg y) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (rhoU_le_lin_bound hy_xi) (Real.exp_pos _).le

private lemma integrable_rhoU_combPhiDeriv {i j : ℕ} (hij : i + j ≤ 4) {b : ℂ} (hb : b ∈ combNMid) :
    IntegrableOn (fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i j (y : ℂ) b) (Ioi xiStar) volume := by
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i j (y : ℂ) b) (volume.restrict (Ioi xiStar)) := by
    have hcont : ContinuousOn (fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i j (y : ℂ) b) (Ioi xiStar) := by
      intro y hy
      have hρ := (continuousOn_rhoU.mono Ioi_subset_Ici_self) y hy
      have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith [xiStar_pos, hy.out])
      have hφ := (hasDerivAt_combPhiDeriv_zeta (i := i) (j := j)
        (combNMid_subset_combNOpen hb) hζ).continuousAt.comp Complex.continuous_ofReal.continuousAt
      exact (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hρ).mul
        hφ.continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  refine ((integrable_mul_exp_neg_pi_Ioi le_rfl).const_mul (C * Real.exp (π * |b.re|))).mono' hmeas
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
  have hζ : (y : ℂ) ∈ combZ := ofReal_mem_combZ (xiStar_pos.le.trans hy.le)
  have h1 := (hbd i j hij hb hζ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
  have hexp : C * Real.exp (-π * (y - |b.re|)) = C * Real.exp (π * |b.re|) * Real.exp (-π * y) := by
    rw [show -π * (y - |b.re|) = π * |b.re| + -π * y by ring, Real.exp_add]; ring
  simp only [Complex.ofReal_re] at h1
  rw [hexp] at h1
  calc ‖(rhoU y : ℂ) * combPhiDeriv i j (y : ℂ) b‖
      = rhoU y * ‖combPhiDeriv i j (y : ℂ) b‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoU_nonneg y)]
    _ ≤ rhoU y * (C * Real.exp (π * |b.re|) * Real.exp (-π * y)) := by
        gcongr; exact rhoU_nonneg y
    _ = C * Real.exp (π * |b.re|) * (rhoU y * Real.exp (-π * y)) := by ring

private lemma rhoU_mul_chiDeriv_eq_two_div {c' t : ℝ} (hc' : 0 < c') (ht : 1 / 4 < t) :
    (c' : ℂ) * ((chiDeriv c' t : ℂ) * ((rhoU (chiQuantile c' t) : ℂ) * g)) = (2 : ℂ) * g := by
  have hρ_ne : rhoU (chiQuantile c' t) ≠ 0 := (rhoU_pos (xiStar_lt_chiQuantile hc' ht)).ne'
  unfold chiDeriv
  have hreal : c' * ((2 / (c' * rhoU (chiQuantile c' t))) * rhoU (chiQuantile c' t)) = 2 := by
    field_simp [hc'.ne', hρ_ne]
  calc (c' : ℂ) * ((chiDeriv c' t : ℂ) * ((rhoU (chiQuantile c' t) : ℂ) * g))
      = (((c' * ((2 / (c' * rhoU (chiQuantile c' t))) * rhoU (chiQuantile c' t)) : ℝ)) : ℂ) * g := by
        unfold chiDeriv; push_cast; ring
    _ = (2 : ℂ) * g := by rw [hreal]; norm_cast

private lemma chiQuantile_cov_integrand {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) (hab : a ≤ b)
    (h : ℝ → ℂ) :
    (c' : ℂ) * ∫ y in (chiQuantile c' a)..(chiQuantile c' b), (rhoU y : ℂ) * h y =
      ∫ t in a..b, (2 : ℂ) * h (chiQuantile c' t) := by
  rw [← chiQuantile_cov_complex hc' ha hab (fun y => (rhoU y : ℂ) * h y),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
  rw [Set.uIoc_of_le hab] at ht
  exact rhoU_mul_chiDeriv_eq_two_div hc' (lt_of_le_of_lt ha ht.1)

private lemma continuousOn_bernoulli_mul_emKernFSecond {k : ℕ} (_hk : k ≤ 2) {c' : ℝ} (hc' : 0 < c')
    {f : ℕ} (hf : 1 ≤ f) (m : ℕ) {w : ℂ} (hw : w ∈ combNMid) :
    ContinuousOn (fun t : ℝ => (bernoulliP2 t : ℂ) * emKernFSecond k c' w ((f + m : ℕ) + t))
      (Icc 0 1) := by
  intro t ht
  have hm1 : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
  have ht14 : 1 / 4 < ((f + m : ℕ) : ℝ) + t := by linarith [ht.1]
  have hρ_gt : xiStar < chiQuantile c' (((f + m : ℕ) : ℝ) + t) := xiStar_lt_chiQuantile hc' ht14
  have hχ_c : ContinuousAt (fun s : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + s)) t :=
    ContinuousAt.comp (f := fun s : ℝ => ((f + m : ℕ) : ℝ) + s)
      (hasDerivAt_chiQuantile hc' ht14).1.continuousAt (continuousAt_const.add continuousAt_id)
  have hcd_c : ContinuousAt (fun s : ℝ => chiDeriv c' (((f + m : ℕ) : ℝ) + s)) t :=
    ContinuousAt.comp (f := fun s : ℝ => ((f + m : ℕ) : ℝ) + s)
      (hasDerivAt_chiQuantile hc' ht14).2.continuousAt (continuousAt_const.add continuousAt_id)
  have hρ_c : ContinuousAt (fun s : ℝ => rhoU (chiQuantile c' (((f + m : ℕ) : ℝ) + s))) t :=
    ContinuousAt.comp (f := fun s : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + s))
      (hasDerivAt_rhoU hρ_gt).continuousAt hχ_c
  have hρ'_c : ContinuousAt (fun s : ℝ => rhoUDeriv (chiQuantile c' (((f + m : ℕ) : ℝ) + s))) t :=
    ContinuousAt.comp (f := fun s : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + s))
      (continuousAt_rhoUDeriv hρ_gt) hχ_c
  have hsec_c : ContinuousAt (fun s : ℝ => chiSecond c' (((f + m : ℕ) : ℝ) + s)) t :=
    ((hcd_c.pow 2).neg).mul (hρ'_c.div hρ_c (rhoU_pos hρ_gt).ne')
  have hζ : (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) ∈ combZOpen :=
    ofReal_mem_combZOpen (by linarith [xiStar_pos, hρ_gt])
  have hχ_cc : ContinuousAt (fun s : ℝ => (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ)) t :=
    ContinuousAt.comp (f := fun s : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + s))
      Complex.continuous_ofReal.continuousAt hχ_c
  have hd2_c : ContinuousAt (fun s : ℝ =>
      combPhiDeriv k 1 (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ) w) t :=
    ContinuousAt.comp (f := fun s : ℝ => (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ))
      (hasDerivAt_combPhiDeriv_zeta (i := k) (j := 1)
        (combNMid_subset_combNOpen hw) hζ).continuousAt hχ_cc
  have hd1_c : ContinuousAt (fun s : ℝ =>
      combPhiDeriv k 0 (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ) w) t :=
    ContinuousAt.comp (f := fun s : ℝ => (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ))
      (hasDerivAt_combPhiDeriv_zeta (i := k) (j := 0)
        (combNMid_subset_combNOpen hw) hζ).continuousAt hχ_cc
  have hP2_c : ContinuousAt (fun s : ℝ => (bernoulliP2 s : ℂ)) t :=
    (Complex.continuous_ofReal.comp
      ((continuous_id.pow 2 |>.sub continuous_id |>.add continuous_const).div_const 2)).continuousAt
  have hcd2_c : ContinuousAt (fun s : ℝ => ((chiDeriv c' (((f + m : ℕ) : ℝ) + s) ^ 2 : ℝ) : ℂ)) t :=
    ContinuousAt.comp (f := fun s : ℝ => chiDeriv c' (((f + m : ℕ) : ℝ) + s) ^ 2)
      Complex.continuous_ofReal.continuousAt (hcd_c.pow 2)
  have hsec_cc : ContinuousAt (fun s : ℝ => (chiSecond c' (((f + m : ℕ) : ℝ) + s) : ℂ)) t :=
    ContinuousAt.comp (f := fun s : ℝ => chiSecond c' (((f + m : ℕ) : ℝ) + s))
      Complex.continuous_ofReal.continuousAt hsec_c
  have hkern_c : ContinuousAt (fun s : ℝ =>
      (bernoulliP2 s : ℂ) * (2 * (combPhiDeriv k 2 (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ) w *
        ((chiDeriv c' (((f + m : ℕ) : ℝ) + s) ^ 2 : ℝ) : ℂ) +
        combPhiDeriv k 1 (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ) w *
          (chiSecond c' (((f + m : ℕ) : ℝ) + s) : ℂ)))) t := by
    have hd2'_c : ContinuousAt (fun s : ℝ =>
        combPhiDeriv k 2 (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ) w) t :=
      ContinuousAt.comp (f := fun s : ℝ => (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ))
        (hasDerivAt_combPhiDeriv_zeta (i := k) (j := 2)
          (combNMid_subset_combNOpen hw) hζ).continuousAt hχ_cc
    exact hP2_c.mul (continuousAt_const.mul ((hd2'_c.mul hcd2_c).add (hd2_c.mul hsec_cc)))
  exact hkern_c.continuousWithinAt

private lemma eulerMaclaurin_unit_cell {c' : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f)
    {b : ℂ} (hb : b ∈ combNMid) (m : ℕ) :
    ∫ t in (0 : ℝ)..1, (2 : ℂ) * phiZeta (chiQuantile c' ((f + m : ℕ) + t : ℝ) : ℂ) b =
      (phiZeta (chiQuantile c' (f + m : ℕ) : ℂ) b +
        phiZeta (chiQuantile c' (f + m + 1 : ℕ) : ℂ) b) -
      (1 / 12 : ℂ) * (emKernFDeriv 0 c' b (f + m + 1 : ℕ) - emKernFDeriv 0 c' b (f + m : ℕ)) +
      ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b ((f + m : ℕ) + t) := by
  have hm14 : ∀ t ∈ Icc (0 : ℝ) 1, 1 / 4 < ((f + m : ℕ) : ℝ) + t := fun t ht => by
    have : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
    linarith [ht.1]
  have hF_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ) b)
        (emKernFDeriv 0 c' b (((f + m : ℕ) : ℝ) + t)) t := by
    intro t ht
    have ht14 := hm14 t ht
    have hχ : HasDerivAt (fun s : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + s))
        (chiDeriv c' (((f + m : ℕ) : ℝ) + t)) t :=
      ((hasDerivAt_chiQuantile hc' ht14).1.comp t ((hasDerivAt_id t).const_add _)).congr_deriv (by ring)
    have hχ' : HasDerivAt (fun s : ℝ => (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ))
        (chiDeriv c' (((f + m : ℕ) : ℝ) + t) : ℂ) t :=
      (Complex.ofRealCLM.hasDerivAt.scomp t hχ).congr_deriv (by simp)
    have hζ : (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) ∈ combZOpen :=
      ofReal_mem_combZOpen (by linarith [xiStar_pos, xiStar_lt_chiQuantile hc' ht14])
    have hφ := (hasDerivAt_combPhiDeriv_zeta (i := 0) (j := 0)
      (combNMid_subset_combNOpen hb) hζ).scomp t hχ'
    have htot := hφ.const_mul (2 : ℂ)
    exact htot.congr_deriv (by simp [emKernFDeriv, combPhiDeriv, smul_eq_mul]; ring)
  have hF'_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => emKernFDeriv 0 c' b (((f + m : ℕ) : ℝ) + s))
        (emKernFSecond 0 c' b (((f + m : ℕ) : ℝ) + t)) t := by
    intro t ht
    have ht14 := hm14 t ht
    have hχ1 : HasDerivAt (fun s : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + s))
        (chiDeriv c' (((f + m : ℕ) : ℝ) + t)) t :=
      ((hasDerivAt_chiQuantile hc' ht14).1.comp t ((hasDerivAt_id t).const_add _)).congr_deriv (by ring)
    have hχ1c : HasDerivAt (fun s : ℝ => (chiQuantile c' (((f + m : ℕ) : ℝ) + s) : ℂ))
        (chiDeriv c' (((f + m : ℕ) : ℝ) + t) : ℂ) t :=
      (Complex.ofRealCLM.hasDerivAt.scomp t hχ1).congr_deriv (by simp)
    have hχ2 : HasDerivAt (fun s : ℝ => chiDeriv c' (((f + m : ℕ) : ℝ) + s))
        (chiSecond c' (((f + m : ℕ) : ℝ) + t)) t :=
      ((hasDerivAt_chiQuantile hc' ht14).2.comp t ((hasDerivAt_id t).const_add _)).congr_deriv (by ring)
    have hχ2c : HasDerivAt (fun s : ℝ => (chiDeriv c' (((f + m : ℕ) : ℝ) + s) : ℂ))
        (chiSecond c' (((f + m : ℕ) : ℝ) + t) : ℂ) t :=
      (Complex.ofRealCLM.hasDerivAt.scomp t hχ2).congr_deriv (by simp)
    have hζ : (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) ∈ combZOpen :=
      ofReal_mem_combZOpen (by linarith [xiStar_pos, xiStar_lt_chiQuantile hc' ht14])
    have hd1 := (hasDerivAt_combPhiDeriv_zeta (i := 0) (j := 1)
      (combNMid_subset_combNOpen hb) hζ).scomp t hχ1c
    have hprod := (hd1.const_mul (2 : ℂ)).mul hχ2c
    refine hprod.congr_deriv ?_
    dsimp only [Function.comp_apply]
    simp only [smul_eq_mul]
    unfold emKernFSecond; push_cast; ring
  have hP2_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (bernoulliP2 s : ℂ)) ((t - 1 / 2 : ℝ) : ℂ) t := by
    intro t
    have hr : HasDerivAt bernoulliP2 (t - 1 / 2) t := by
      unfold bernoulliP2
      have := (((hasDerivAt_pow 2 t).sub (hasDerivAt_id t)).add_const (1 / 6 : ℝ)).div_const 2
      refine this.congr_deriv ?_; simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
    exact (Complex.ofRealCLM.hasDerivAt.scomp t hr).congr_deriv (by simp)
  have hlin_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((s - 1 / 2 : ℝ) : ℂ)) (1 : ℂ) t := by
    intro t
    have hs := (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
    exact (Complex.ofRealCLM.hasDerivAt.scomp t hs).congr_deriv (by simp)
  let H : ℝ → ℂ := fun t =>
    (bernoulliP2 t : ℂ) * emKernFDeriv 0 c' b (((f + m : ℕ) : ℝ) + t) -
      ((t - 1 / 2 : ℝ) : ℂ) * ((2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b)
  have hH_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt H ((bernoulliP2 t : ℂ) * emKernFSecond 0 c' b (((f + m : ℕ) : ℝ) + t) -
        (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b) t := by
    intro t ht
    have hterm1 := (hP2_deriv t).mul (hF'_deriv t ht)
    have hterm2 := (hlin_deriv t).mul (hF_deriv t ht)
    exact (hterm1.sub hterm2).congr_deriv (by ring)
  have hcont_F : ContinuousOn
      (fun t : ℝ => (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b) (Icc 0 1) :=
    fun t ht => (hF_deriv t ht).continuousAt.continuousWithinAt
  have hcont_int2 : ContinuousOn
      (fun t : ℝ => (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b (((f + m : ℕ) : ℝ) + t)) (Icc 0 1) :=
    continuousOn_bernoulli_mul_emKernFSecond (k := 0) (by omega) hc' hf m hb
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t ht => hH_deriv t (by simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht))
    (hcont_int2.sub hcont_F |>.intervalIntegrable_of_Icc zero_le_one)
  rw [intervalIntegral.integral_sub (hcont_int2.intervalIntegrable_of_Icc zero_le_one)
    (hcont_F.intervalIntegrable_of_Icc zero_le_one)] at hftc
  have hH1 : H 1 = (1 / 12 : ℂ) * emKernFDeriv 0 c' b (f + m + 1 : ℕ) -
      phiZeta (chiQuantile c' (f + m + 1 : ℕ) : ℂ) b := by
    dsimp [H, bernoulliP2]
    have hcast : (((f + m : ℕ) : ℝ) + 1) = ((f + m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    norm_num; ring
  have hH0 : H 0 = (1 / 12 : ℂ) * emKernFDeriv 0 c' b (f + m : ℕ) +
      phiZeta (chiQuantile c' (f + m : ℕ) : ℂ) b := by
    dsimp [H, bernoulliP2]
    rw [add_zero]
    norm_num; ring
  have h_rearrange :
      ∫ t in (0 : ℝ)..1, (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b =
      (∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b ((f + m : ℕ) + t)) -
        (H 1 - H 0) := by
    calc ∫ t in (0 : ℝ)..1, (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b
        = (∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b (((f + m : ℕ) : ℝ) + t)) -
            ((∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b (((f + m : ℕ) : ℝ) + t)) -
              ∫ t in (0 : ℝ)..1, (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b) := by
            ring
      _ = (∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b ((f + m : ℕ) + t)) -
            (H 1 - H 0) := by rw [hftc]
  rw [h_rearrange, hH1, hH0]
  ring

private lemma tendsto_chiQuantile_nat_atTop {c' : ℝ} (hc' : 0 < c') (f : ℕ) :
    Tendsto (fun M : ℕ => chiQuantile c' (f + M : ℕ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt (c' * ((max y xiStar) ^ 2 + (max y xiStar)) + 1)
  refine ⟨N, fun M hM => ?_⟩
  by_contra hlt
  push Not at hlt
  have ha : (1 / 4 : ℝ) ≤ (f + M : ℕ) := by
    have hN_lt : c' * ((max y xiStar) ^ 2 + max y xiStar) + 1 < N := hN
    have hNM : (N : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : N ≤ f + M)
    have hY0 : 0 ≤ max y xiStar := xiStar_pos.le.trans (le_max_right y xiStar)
    have h1 : (1 : ℝ) ≤ c' * ((max y xiStar) ^ 2 + max y xiStar) + 1 := by
      linarith [mul_nonneg hc'.le (add_nonneg (sq_nonneg (max y xiStar)) hY0)]
    linarith
  have hspec := chiQuantile_spec hc' ha
  have hcum_le : cumulN (chiQuantile c' (f + M : ℕ)) ≤ (max y xiStar) ^ 2 + max y xiStar := by
    have hm := cumulN_strictMonoOn.monotoneOn hspec.1 (le_max_right y xiStar) (hlt.le.trans (le_max_left y xiStar))
    refine hm.trans ?_
    unfold cumulN
    set Y := max y xiStar
    have hY : xiStar ≤ Y := le_max_right y xiStar
    have hY0 : 0 ≤ Y := xiStar_pos.le.trans hY
    have h1 := intervalIntegrable_rhoU le_rfl hY
    have h2 : IntervalIntegrable (fun t => (4 / 3 : ℝ) * t + 4 / (3 * π)) volume xiStar Y :=
      ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on hY h1 h2 fun t ht => rhoU_le_lin_bound ht.1
    have hval : ∫ t in xiStar..Y, ((4 / 3 : ℝ) * t + 4 / (3 * π)) ≤
        (2 / 3 : ℝ) * Y ^ 2 + (4 / (3 * π)) * Y := by
      have hi1 : IntervalIntegrable (fun t : ℝ => (4 / 3 : ℝ) * t) volume xiStar Y :=
        (continuous_const.mul continuous_id).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun _ : ℝ => (4 / (3 * π))) volume xiStar Y :=
        intervalIntegrable_const
      rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      have hsub1 : (4 / 3 : ℝ) * ((Y ^ 2 - xiStar ^ 2) / 2) ≤ (2 / 3 : ℝ) * Y ^ 2 := by
        nlinarith [sq_nonneg xiStar]
      have h43pi_nn : 0 ≤ 4 / (3 * π) := by positivity
      have hsub2 : (Y - xiStar) * (4 / (3 * π)) ≤ (4 / (3 * π)) * Y := by
        calc (Y - xiStar) * (4 / (3 * π)) = (4 / (3 * π)) * Y - (4 / (3 * π)) * xiStar := by ring
          _ ≤ (4 / (3 * π)) * Y := sub_le_self _ (mul_nonneg h43pi_nn xiStar_pos.le)
      linarith
    have hpi3 : 4 / (3 * π) ≤ 2 := by
      calc 4 / (3 * π) ≤ 4 / (3 * 3) := by gcongr; exact Real.pi_gt_three.le
        _ ≤ 2 := by norm_num
    have hmul : (4 / (3 * π)) * Y ≤ 2 * Y := mul_le_mul_of_nonneg_right hpi3 hY0
    nlinarith [sq_nonneg Y]
  have h1 : ((f + M : ℕ) : ℝ) - 1 / 4 ≤ c' * ((max y xiStar) ^ 2 + max y xiStar) := by
    rw [← hspec.2]; exact mul_le_mul_of_nonneg_left hcum_le hc'.le
  have h2 : (N : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : N ≤ f + M)
  linarith

private lemma summable_exp_neg_pi_chiQuantile_gen {c' : ℝ} (hc' : 0 < c') (f : ℕ) :
    Summable fun m : ℕ => Real.exp (-π * chiQuantile c' (f + m : ℕ)) := by
  have heq : (fun m : ℕ => Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ))) =
      fun m : ℕ => Real.exp (-π * chiQuantile c' (f + (m + 1) : ℕ)) := by
    ext m; ring_nf
  have hsum := summable_exp_neg_pi_chiQuantile hc' f
  rw [heq] at hsum
  exact (summable_nat_add_iff 1).mp hsum

/-- Exact decomposition `log B^(f) = c' Φ_0 + Φ_1^(f)` on `combNMid` (hence `combN`) for large `c'`. -/
theorem logRefComb_eq_comb_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ {b : ℂ}, b ∈ combNMid →
      logRefComb c' f η₀ b = (c' : ℂ) * phi0 b + phi1Comb c' f η₀ b := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [eventually_gt_atTop 0, h_ev] with c' hc' ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_1⟩ b hb
  have ha_f : (1 / 4 : ℝ) ≤ (f : ℕ) := by
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  have ha_m : ∀ m : ℕ, (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := fun m => by
    have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    linarith
  have hχ_nn : ∀ a : ℝ, 1 / 4 ≤ a → 0 ≤ chiQuantile c' a := fun a ha =>
    xiStar_pos.le.trans (chiQuantile_spec hc' ha).1
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (f + 1 + m)| ≤ 1 / 8 := fun m => by
    have hgap_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn (ha_m m)
        ((ha_m m).trans (by linarith)) (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgap_nn)]
    have hgk := (hgap_k (f + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (f + 1 + m) ≤ (1 / 4) * (1 / 2) := mul_le_mul hη₀1 hgk hgap_nn (by norm_num)
      _ = 1 / 8 := by norm_num
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  have hsum_det : Summable fun m : ℕ =>
      (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b -
        2 * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => 4 * C * Real.exp (π * |b.re|) *
        Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ))) ?_ fun m => ?_
    · exact (summable_exp_neg_pi_chiQuantile hc' f).mul_left _
    · have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
        ofReal_add_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
      have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
        ofReal_sub_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
      have hζ0 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) ∈ combZ :=
        ofReal_mem_combZ (hχ_nn _ (ha_m m))
      have b1 := (hbd 0 0 (by norm_num) hb hζ1).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      have b2 := (hbd 0 0 (by norm_num) hb hζ2).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      have b0 := (hbd 0 0 (by norm_num) hb hζ0).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      simp only [combPhiDeriv_zero] at b1 b2 b0
      have hexp : C * Real.exp (-π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) =
          C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by
        rw [show -π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) =
          π * |b.re| + -π * chiQuantile c' (f + 1 + m : ℕ) by ring, Real.exp_add]; ring
      have hre1 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
          chiQuantile c' (f + 1 + m : ℕ) := by simp
      have hre2 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
          chiQuantile c' (f + 1 + m : ℕ) := by simp
      have hre0 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ)).re =
          chiQuantile c' (f + 1 + m : ℕ) := by simp
      rw [hre1] at b1; rw [hre2] at b2; rw [hre0] at b0
      rw [hexp] at b1 b2 b0
      calc ‖_‖ ≤ ‖phiZeta _ b‖ + ‖phiZeta _ b‖ + ‖2 * phiZeta _ b‖ := by
            refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_add_le _ _
        _ ≤ C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) +
            C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) +
            2 * (C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ))) := by
            rw [norm_mul, Complex.norm_ofNat]; gcongr
        _ = 4 * C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by ring
  have hsum_phi : Summable fun m : ℕ => (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => 2 * C * Real.exp (π * |b.re|) *
        Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ))) ?_ fun m => ?_
    · exact (summable_exp_neg_pi_chiQuantile hc' f).mul_left (2 * C * Real.exp (π * |b.re|))
    · have hζ0 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) ∈ combZ :=
        ofReal_mem_combZ (hχ_nn _ (ha_m m))
      have b0 := (hbd 0 0 (by norm_num) hb hζ0).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      simp only [combPhiDeriv_zero, Complex.ofReal_re] at b0
      have hexp : C * Real.exp (-π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) =
          C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by
        rw [show -π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) =
          π * |b.re| + -π * chiQuantile c' (f + 1 + m : ℕ) by ring, Real.exp_add]; ring
      rw [hexp] at b0
      rw [norm_mul, Complex.norm_ofNat]
      linarith
  have hsum_rem : Summable fun m : ℕ =>
      ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b ((f + m : ℕ) + t) := by
    have hcd1 : ∀ a : ℝ, 1 ≤ a → chiDeriv c' a ≤ chiDeriv c' 1 := fun a ha => by
      rcases eq_or_lt_of_le ha with rfl | hlt
      · exact le_rfl
      · exact (chiDeriv_strictAntiOn hc' (show (1 / 4 : ℝ) < 1 by norm_num)
          (show (1 / 4 : ℝ) < a by linarith) hlt).le
    have hsec1 : ∀ a : ℝ, 1 ≤ a → |chiSecond c' a| ≤ (4 / 3) * chiDeriv c' 1 := fun a ha => by
      have ha14 : 1 / 4 < a := by linarith
      have hcd_pos : 0 < chiDeriv c' a := by
        unfold chiDeriv; exact div_pos two_pos (mul_pos hc' (rhoU_pos (xiStar_lt_chiQuantile hc' ha14)))
      have hcd1_nn : 0 ≤ chiDeriv c' 1 := by
        unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
      have h1 := abs_logDeriv_chiDeriv_le hc' ha14
      rw [abs_div, abs_of_pos hcd_pos, div_le_iff₀ hcd_pos] at h1
      calc |chiSecond c' a| ≤ 1 / (a - 1 / 4) * chiDeriv c' a := h1
        _ ≤ 1 / (1 - 1 / 4) * chiDeriv c' 1 :=
            mul_le_mul (one_div_le_one_div_of_le (by norm_num) (by linarith))
              (hcd1 a ha) hcd_pos.le (by norm_num)
        _ = (4 / 3) * chiDeriv c' 1 := by norm_num
    set K := (1 / 6 : ℝ) * C * Real.exp (π * |b.re|) * (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)
    refine Summable.of_norm_bounded (g := fun m : ℕ => K * Real.exp (-π * chiQuantile c' (f + m : ℕ)))
      ((summable_exp_neg_pi_chiQuantile_gen hc' f).mul_left K) fun m => ?_
    refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
    have hconst : ∫ t in (0 : ℝ)..1, K * Real.exp (-π * chiQuantile c' (f + m : ℕ)) =
        K * Real.exp (-π * chiQuantile c' (f + m : ℕ)) := by simp
    rw [← hconst]
    refine intervalIntegral.integral_mono_on zero_le_one
      ((continuousOn_bernoulli_mul_emKernFSecond (k := 0) (by omega) hc' hf m hb).norm.intervalIntegrable_of_Icc
        zero_le_one)
      intervalIntegrable_const fun t ht => ?_
    have hm_ge : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
    have ht1 : (1 : ℝ) ≤ ((f + m : ℕ) : ℝ) + t := by linarith [ht.1]
    have hχ_ge : chiQuantile c' (f + m : ℕ) ≤ chiQuantile c' (((f + m : ℕ) : ℝ) + t) :=
      (chiQuantile_strictMonoOn hc').monotoneOn
        (show (1 / 4 : ℝ) ≤ (f + m : ℕ) by linarith)
        (show (1 / 4 : ℝ) ≤ ((f + m : ℕ) : ℝ) + t by linarith)
        (by linarith [ht.1])
    have hζ : (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) ∈ combZ :=
      ofReal_mem_combZ (xiStar_pos.le.trans ((chiQuantile_spec hc' (by linarith)).1))
    have hb2 := (hbd 0 2 (by omega) hb hζ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have hb1 := (hbd 0 1 (by omega) hb hζ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have hexp_le : Real.exp (-π * (chiQuantile c' (((f + m : ℕ) : ℝ) + t) - |b.re|)) ≤
        Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    simp only [Complex.ofReal_re] at hb2 hb1
    have hP2 := abs_bernoulliP2_le ht.1 ht.2
    have hsec_bd : ‖emKernFSecond 0 c' b ((f + m : ℕ) + t)‖ ≤
        2 * (C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) *
          (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)) := by
      unfold emKernFSecond
      have hc1 : 0 ≤ chiDeriv c' 1 := by
        unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
      have hcd_le := hcd1 _ ht1
      have hcd_nn : 0 ≤ chiDeriv c' ((f + m : ℕ) + t) := by
        unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
      have hsec_le := hsec1 _ ht1
      calc ‖2 * (combPhiDeriv 0 2 _ b * ((chiDeriv c' _ ^ 2 : ℝ) : ℂ) +
              combPhiDeriv 0 1 _ b * ((chiSecond c' _ : ℝ) : ℂ))‖
          ≤ 2 * (‖combPhiDeriv 0 2 _ b‖ * ‖((chiDeriv c' _ ^ 2 : ℝ) : ℂ)‖ +
              ‖combPhiDeriv 0 1 _ b‖ * ‖((chiSecond c' _ : ℝ) : ℂ)‖) := by
              rw [norm_mul, Complex.norm_ofNat]
              gcongr
              exact (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)
        _ ≤ 2 * ((C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + m : ℕ))) *
              (chiDeriv c' 1 ^ 2) +
              (C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + m : ℕ))) *
              ((4 / 3) * chiDeriv c' 1)) := by
              gcongr
              · exact (hb2.trans (mul_le_mul_of_nonneg_left hexp_le hC.le)).trans_eq (by ring)
              · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
                exact pow_le_pow_left₀ hcd_nn hcd_le 2
              · exact (hb1.trans (mul_le_mul_of_nonneg_left hexp_le hC.le)).trans_eq (by ring)
              · rwa [Complex.norm_real, Real.norm_eq_abs]
        _ = 2 * (C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) *
              (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)) := by ring
    rw [norm_mul, Complex.norm_real]
    calc |bernoulliP2 t| * ‖emKernFSecond 0 c' b ((f + m : ℕ) + t)‖
        ≤ (1 / 12) * (2 * (C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) *
            (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1))) := by gcongr
      _ = K * Real.exp (-π * chiQuantile c' (f + m : ℕ)) := by dsimp [K]; ring
  -- Split `logRefComb` into `iπ + Δ_det + (φ_{χ_f} + ∑' m, 2 φ_{χ_{f+1+m}})`:
  have hlog_split : logRefComb c' f η₀ b =
      (π : ℂ) * Complex.I + deltaDetComb c' f η₀ b + phiZeta (chiQuantile c' f : ℂ) b +
        ∑' m : ℕ, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b := by
    have hsum1 : Summable fun m : ℕ =>
        (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
            ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
          phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
            ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b) := by
      have heq := hsum_det.add hsum_phi
      refine heq.congr fun m => ?_
      ring
    unfold logRefComb deltaDetComb
    have hadd := hsum_det.tsum_add hsum_phi
    have heq : (∑' m : ℕ, (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b)) =
        (∑' m : ℕ, (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
            ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
          phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
            ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b -
          2 * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b)) +
        ∑' m : ℕ, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b := by
      rw [← hadd]
      refine tsum_congr fun m => by ring
    rw [heq]; ring
  -- Now prove Euler--Maclaurin identity:
  -- `phiZeta (χ_f) b + ∑' m, 2 phiZeta (χ_{f+1+m}) b = c' * phi0 b - 2 * n1Comb f * barPhi c' f b + emRem c' f b`
  have ha_f1 : (1 : ℝ) ≤ (f : ℕ) := by exact_mod_cast hf
  have hEM_tail : phiZeta (chiQuantile c' f : ℂ) b +
        ∑' m : ℕ, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b =
      (c' : ℂ) * phi0 b - ((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b + emRem c' f b := by
    let F : ℝ → ℂ := fun a => 2 * phiZeta (chiQuantile c' a : ℂ) b
    have h_cell_sum : ∀ M : ℕ,
        phiZeta (chiQuantile c' f : ℂ) b +
          (∑ m ∈ Finset.range M, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b) =
        (∫ a in (f : ℝ)..((f + M : ℕ) : ℝ), (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b) +
          phiZeta (chiQuantile c' (f + M : ℕ) : ℂ) b +
          (1 / 12 : ℂ) * (emKernFDeriv 0 c' b (f + M : ℕ) - emKernFDeriv 0 c' b f) -
          ∑ m ∈ Finset.range M, ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) *
            emKernFSecond 0 c' b ((f + m : ℕ) + t) := by
      intro M
      have h_int_split : ∫ a in (f : ℝ)..((f + M : ℕ) : ℝ),
            (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b =
          ∑ m ∈ Finset.range M,
            ∫ t in (0 : ℝ)..1, (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b := by
        induction M with
        | zero => simp
        | succ M ih =>
          have h1 : IntervalIntegrable (fun a => (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b)
              volume (f : ℝ) ((f + M : ℕ) : ℝ) := by
            rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by exact_mod_cast (by omega : f ≤ f + M))]
            refine ContinuousOn.integrableOn_Icc ?_
            intro a ha
            have hf1 : (1 : ℝ) ≤ (f : ℕ) := ha_f1
            have ha14 : 1 / 4 < a := by linarith [ha.1]
            have hχ_d : HasDerivAt (fun t : ℝ => (chiQuantile c' t : ℂ)) (chiDeriv c' a : ℂ) a :=
              (Complex.ofRealCLM.hasDerivAt.scomp a (hasDerivAt_chiQuantile hc' ha14).1).congr_deriv (by simp)
            have hζ : (chiQuantile c' a : ℂ) ∈ combZOpen :=
              ofReal_mem_combZOpen (by linarith [xiStar_pos, xiStar_lt_chiQuantile hc' ha14])
            have hφ : ContinuousAt (fun t : ℝ => phiZeta (chiQuantile c' t : ℂ) b) a :=
              ContinuousAt.comp (f := fun t : ℝ => (chiQuantile c' t : ℂ))
                (hasDerivAt_combPhiDeriv_zeta (i := 0) (j := 0)
                  (combNMid_subset_combNOpen hb) hζ).continuousAt hχ_d.continuousAt
            exact (continuousAt_const.mul hφ).continuousWithinAt
          have h2 : IntervalIntegrable (fun a => (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b)
              volume ((f + M : ℕ) : ℝ) ((f + (M + 1) : ℕ) : ℝ) := by
            rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by exact_mod_cast (by omega : f + M ≤ f + (M + 1)))]
            refine ContinuousOn.integrableOn_Icc ?_
            intro a ha
            have hm1 : (1 : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + M)
            have ha14 : 1 / 4 < a := by linarith [ha.1]
            have hχ_d : HasDerivAt (fun t : ℝ => (chiQuantile c' t : ℂ)) (chiDeriv c' a : ℂ) a :=
              (Complex.ofRealCLM.hasDerivAt.scomp a (hasDerivAt_chiQuantile hc' ha14).1).congr_deriv (by simp)
            have hζ : (chiQuantile c' a : ℂ) ∈ combZOpen :=
              ofReal_mem_combZOpen (by linarith [xiStar_pos, xiStar_lt_chiQuantile hc' ha14])
            have hφ : ContinuousAt (fun t : ℝ => phiZeta (chiQuantile c' t : ℂ) b) a :=
              ContinuousAt.comp (f := fun t : ℝ => (chiQuantile c' t : ℂ))
                (hasDerivAt_combPhiDeriv_zeta (i := 0) (j := 0)
                  (combNMid_subset_combNOpen hb) hζ).continuousAt hχ_d.continuousAt
            exact (continuousAt_const.mul hφ).continuousWithinAt
          rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, ih, Finset.sum_range_succ]
          congr 1
          have hshift := intervalIntegral.integral_comp_add_left
            (fun a => (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b) ((f + M : ℕ) : ℝ) (a := 0) (b := 1)
          have h0 : ((f + M : ℕ) : ℝ) + 0 = ((f + M : ℕ) : ℝ) := add_zero _
          have h1' : ((f + M : ℕ) : ℝ) + 1 = ((f + (M + 1) : ℕ) : ℝ) := by push_cast; ring
          rw [h0, h1'] at hshift
          exact hshift.symm
      rw [h_int_split]
      clear h_int_split
      have h_cell : ∀ m : ℕ,
          ∫ t in (0 : ℝ)..1, (2 : ℂ) * phiZeta (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) b =
            (phiZeta (chiQuantile c' (f + m : ℕ) : ℂ) b +
              phiZeta (chiQuantile c' (f + m + 1 : ℕ) : ℂ) b) -
            (1 / 12 : ℂ) * (emKernFDeriv 0 c' b (f + m + 1 : ℕ) - emKernFDeriv 0 c' b (f + m : ℕ)) +
            ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b ((f + m : ℕ) + t) :=
        fun m => eulerMaclaurin_unit_cell hc' hf hb m
      simp_rw [h_cell, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h_tel1 : ∀ K : ℕ, (∑ m ∈ Finset.range K, (phiZeta (chiQuantile c' (f + m : ℕ) : ℂ) b +
            phiZeta (chiQuantile c' (f + m + 1 : ℕ) : ℂ) b)) =
          phiZeta (chiQuantile c' f : ℂ) b +
          (∑ m ∈ Finset.range K, 2 * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b) -
          phiZeta (chiQuantile c' (f + K : ℕ) : ℂ) b := by
        intro K
        induction K with
        | zero => simp
        | succ K ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
          have h1 : f + K + 1 = f + (K + 1) := by omega
          have h2 : f + 1 + K = f + (K + 1) := by omega
          rw [h1, h2]; ring
      have h_tel2 : ∀ K : ℕ, (∑ m ∈ Finset.range K,
            ((1 / 12 : ℂ) * (emKernFDeriv 0 c' b (f + m + 1 : ℕ) - emKernFDeriv 0 c' b (f + m : ℕ)))) =
          (1 / 12 : ℂ) * (emKernFDeriv 0 c' b (f + K : ℕ) - emKernFDeriv 0 c' b f) := by
        intro K
        rw [← Finset.mul_sum]
        congr 1
        induction K with
        | zero => simp
        | succ K ih =>
          rw [Finset.sum_range_succ, ih]
          have h1 : f + K + 1 = f + (K + 1) := by omega
          rw [h1]; ring
      rw [h_tel1 M, h_tel2 M]
      ring
    have h_lhs_tend : Tendsto (fun M : ℕ =>
        phiZeta (chiQuantile c' f : ℂ) b +
          ∑ m ∈ Finset.range M, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b)
        atTop (𝓝 (phiZeta (chiQuantile c' f : ℂ) b +
          ∑' m : ℕ, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b)) :=
      tendsto_const_nhds.add hsum_phi.hasSum.tendsto_sum_nat
    have h_int_tend : Tendsto (fun M : ℕ =>
        ∫ a in (f : ℝ)..((f + M : ℕ) : ℝ), (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b)
        atTop (𝓝 ((c' : ℂ) * phi0 b - ((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b)) := by
      have h_cov : ∀ M : ℕ,
          ∫ a in (f : ℝ)..((f + M : ℕ) : ℝ), (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b =
            ((c' : ℂ) * ∫ y in xiStar..(chiQuantile c' (f + M : ℕ)),
              (rhoU y : ℂ) * phiZeta (y : ℂ) b) -
              ((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b := by
        intro M
        have h1 : IntervalIntegrable (fun y : ℝ => (rhoU y : ℂ) * phiZeta (y : ℂ) b)
            volume xiStar (chiQuantile c' f) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (chiQuantile_spec hc' ha_f).1).mpr
            ((integrable_rhoU_combPhiDeriv (i := 0) (j := 0) (by norm_num) hb).mono_set Ioc_subset_Ioi_self)
        have h2 : IntervalIntegrable (fun y : ℝ => (rhoU y : ℂ) * phiZeta (y : ℂ) b)
            volume (chiQuantile c' f) (chiQuantile c' (f + M : ℕ)) := by
          have hm14 : (1 / 4 : ℝ) ≤ (f + M : ℕ) := by
            have : (1 : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + M)
            linarith
          have h_le := (chiQuantile_strictMonoOn hc').monotoneOn ha_f hm14
            (by exact_mod_cast (by omega : f ≤ f + M))
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h_le).mpr
            ((integrable_rhoU_combPhiDeriv (i := 0) (j := 0) (by norm_num) hb).mono_set
              (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (chiQuantile_spec hc' ha_f).1)))
        have hcov := chiQuantile_cov_integrand (a := (f : ℝ)) (b := ((f + M : ℕ) : ℝ)) hc' ha_f
          (by exact_mod_cast (by omega : f ≤ f + M)) (fun y => phiZeta (y : ℂ) b)
        have h_adj_f : ∫ y in xiStar..(chiQuantile c' (f + M : ℕ)), (rhoU y : ℂ) * phiZeta (y : ℂ) b =
            (∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * phiZeta (y : ℂ) b) +
              ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)), (rhoU y : ℂ) * phiZeta (y : ℂ) b :=
          (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
        rw [← hcov, h_adj_f]
        unfold barPhi n1Comb
        set I_f := ∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * phiZeta (y : ℂ) b
        set I_tail := ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
          (rhoU y : ℂ) * phiZeta (y : ℂ) b
        have hn1 : 2 * ((f : ℝ) - 1 / 4) ≠ 0 := by
          have : (1 : ℝ) ≤ f := by exact_mod_cast hf
          linarith
        have hc2 : ((2 * ((f : ℝ) - 1 / 4) : ℝ) : ℂ) * ((1 / (2 * ((f : ℝ) - 1 / 4)) : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, mul_one_div_cancel hn1, Complex.ofReal_one]
        calc (c' : ℂ) * I_tail
            = (c' : ℂ) * (I_f + I_tail) - (((2 * ((f : ℝ) - 1 / 4) : ℝ) : ℂ) *
                ((1 / (2 * ((f : ℝ) - 1 / 4)) : ℝ) : ℂ)) * ((c' : ℂ) * I_f) := by
                rw [hc2, one_mul]; ring
          _ = (c' : ℂ) * (I_f + I_tail) - ((2 * ((f : ℝ) - 1 / 4) : ℝ) : ℂ) *
                (((1 / (2 * ((f : ℝ) - 1 / 4)) : ℝ) : ℂ) * (c' : ℂ) * I_f) := by ring
      have h_ioi : Tendsto (fun M : ℕ => ∫ x in xiStar..(chiQuantile c' (f + M : ℕ)),
          (rhoU x : ℂ) * phiZeta (x : ℂ) b) atTop (𝓝 (phi0 b)) :=
        intervalIntegral_tendsto_integral_Ioi xiStar
          (integrable_rhoU_combPhiDeriv (i := 0) (j := 0) (by norm_num) hb)
          (tendsto_chiQuantile_nat_atTop hc' f)
      have h_tot := (h_ioi.const_mul (c' : ℂ)).sub_const (((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b)
      exact h_tot.congr (fun M => (h_cov M).symm)
    have h_phi_tail_tend : Tendsto (fun M : ℕ => phiZeta (chiQuantile c' (f + M : ℕ) : ℂ) b)
        atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      have hexp0 : Tendsto (fun M : ℕ => C * Real.exp (π * |b.re|) *
          Real.exp (-π * chiQuantile c' (f + M : ℕ))) atTop (𝓝 0) := by
        have ht1 : Tendsto (fun M : ℕ => -π * chiQuantile c' (f + M : ℕ)) atTop atBot :=
          Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
            (tendsto_chiQuantile_nat_atTop hc' f)
        simpa using (Real.tendsto_exp_atBot.comp ht1).const_mul (C * Real.exp (π * |b.re|))
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hexp0
      filter_upwards with M
      have haM : (1 / 4 : ℝ) ≤ (f + M : ℕ) := by
        have : (1 : ℝ) ≤ f := by exact_mod_cast hf
        have : (1 : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + M)
        linarith
      have hζ : (chiQuantile c' (f + M : ℕ) : ℂ) ∈ combZ := ofReal_mem_combZ (hχ_nn _ haM)
      have b0 := (hbd 0 0 (by norm_num) hb hζ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      simp only [combPhiDeriv_zero, Complex.ofReal_re] at b0
      rwa [show C * Real.exp (-π * (chiQuantile c' (f + M : ℕ) - |b.re|)) =
        C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + M : ℕ)) by
          rw [show -π * (chiQuantile c' (f + M : ℕ) - |b.re|) =
            π * |b.re| + -π * chiQuantile c' (f + M : ℕ) by ring, Real.exp_add]; ring] at b0
    have h_fderiv_tail_tend : Tendsto (fun M : ℕ => emKernFDeriv 0 c' b (f + M : ℕ)) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      have hexp0 : Tendsto (fun M : ℕ => 2 * C * chiDeriv c' 1 * Real.exp (π * |b.re|) *
          Real.exp (-π * chiQuantile c' (f + M : ℕ))) atTop (𝓝 0) := by
        have ht1 : Tendsto (fun M : ℕ => -π * chiQuantile c' (f + M : ℕ)) atTop atBot :=
          Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
            (tendsto_chiQuantile_nat_atTop hc' f)
        simpa using (Real.tendsto_exp_atBot.comp ht1).const_mul _
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hexp0
      filter_upwards with M
      have haM1 : (1 : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + M)
      have haM : (1 / 4 : ℝ) ≤ (f + M : ℕ) := by linarith
      have hcd_le : chiDeriv c' (f + M : ℕ) ≤ chiDeriv c' 1 := by
        rcases eq_or_lt_of_le haM1 with h1 | hgt
        · rw [← h1]
        · exact (chiDeriv_strictAntiOn hc' (show (1 / 4 : ℝ) < 1 by norm_num)
            (show (1 / 4 : ℝ) < (f + M : ℕ) by linarith) hgt).le
      have hcd_nn : 0 ≤ chiDeriv c' (f + M : ℕ) := by
        unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
      have hζ : (chiQuantile c' (f + M : ℕ) : ℂ) ∈ combZ := ofReal_mem_combZ (hχ_nn _ haM)
      have b1 := (hbd 0 1 (by omega) hb hζ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      simp only [Complex.ofReal_re] at b1
      unfold emKernFDeriv
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hcd_nn]
      calc 2 * ‖combPhiDeriv 0 1 (chiQuantile c' (f + M : ℕ) : ℂ) b‖ * chiDeriv c' (f + M : ℕ)
          ≤ 2 * (C * Real.exp (-π * (chiQuantile c' (f + M : ℕ) - |b.re|))) * chiDeriv c' 1 := by
            gcongr
        _ = 2 * C * chiDeriv c' 1 * Real.exp (π * |b.re|) *
              Real.exp (-π * chiQuantile c' (f + M : ℕ)) := by
            rw [show -π * (chiQuantile c' (f + M : ℕ) - |b.re|) =
              π * |b.re| + -π * chiQuantile c' (f + M : ℕ) by ring, Real.exp_add]; ring
    have h_rhs_tend : Tendsto (fun M : ℕ =>
        (∫ a in (f : ℝ)..((f + M : ℕ) : ℝ), (2 : ℂ) * phiZeta (chiQuantile c' a : ℂ) b) +
          phiZeta (chiQuantile c' (f + M : ℕ) : ℂ) b +
          (1 / 12 : ℂ) * (emKernFDeriv 0 c' b (f + M : ℕ) - emKernFDeriv 0 c' b f) -
          ∑ m ∈ Finset.range M, ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) *
            emKernFSecond 0 c' b ((f + m : ℕ) + t))
        atTop (𝓝 ((c' : ℂ) * phi0 b - ((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b + emRem c' f b)) := by
      have h1 := ((h_int_tend.add h_phi_tail_tend).add
        (((h_fderiv_tail_tend.sub_const (emKernFDeriv 0 c' b f)).const_mul (1 / 12 : ℂ)))).sub
        hsum_rem.hasSum.tendsto_sum_nat
      have h_eq_lim : ((c' : ℂ) * phi0 b - ((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b + 0 +
          (1 / 12 : ℂ) * (0 - emKernFDeriv 0 c' b f) -
          ∑' m : ℕ, ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond 0 c' b ((f + m : ℕ) + t)) =
          (c' : ℂ) * phi0 b - ((2 * n1Comb f : ℝ) : ℂ) * barPhi c' f b + emRem c' f b := by
        unfold emRem emRem2Deriv; ring
      rwa [h_eq_lim] at h1
    exact tendsto_nhds_unique (h_lhs_tend.congr h_cell_sum) h_rhs_tend
  rw [hlog_split]
  unfold phi1Comb
  rw [show (π : ℂ) * Complex.I + deltaDetComb c' f η₀ b + phiZeta (chiQuantile c' f : ℂ) b +
      ∑' m : ℕ, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b =
    (π : ℂ) * Complex.I + deltaDetComb c' f η₀ b +
      (phiZeta (chiQuantile c' f : ℂ) b +
        ∑' m : ℕ, (2 : ℂ) * phiZeta (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b) by ring, hEM_tail]
  ring

/-! ### Section 5: Boundary reality on `E_+` (`Im b = 1/2`) and `i ≤ 2` termwise derivatives -/

lemma phiZeta_re_eq_zero_of_im_half {y : ℝ} (hy : 0 ≤ y) {b : ℂ} (hb_im : b.im = 1 / 2) :
    (phiZeta (y : ℂ) b).re = 0 := by
  have hb : b ∈ combN := by change |b.im - 1 / 2| ≤ 1 / 4; rw [hb_im]; norm_num
  have hζ : (y : ℂ) ∈ combZ := ofReal_mem_combZ hy
  have hexp : Real.exp (phiZeta (y : ℂ) b).re = 1 := by
    rw [← Complex.norm_exp, cexp_phiZeta hb hζ, norm_neg]
    exact norm_blaschkeT_real_eq_one y (by rw [hb_im, abs_of_pos (by norm_num)])
  rwa [Real.exp_eq_one_iff] at hexp

/-- On $E_+ = \{b \in \mathbb{C} : \operatorname{Im} b = 1/2\}$, $\operatorname{Re} \Phi_1^{(f)}(b) = 0$. -/
theorem re_phi1Comb_eq_zero_of_im_half (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ {b : ℂ}, b.im = 1 / 2 → (phi1Comb c' f η₀ b).re = 0 := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [eventually_gt_atTop 0, h_ev, logRefComb_eq_comb_decomp f hf hη₀0 hη₀1] with
      c' hc' ⟨hgap_k, _, _, hgap_1⟩ h_decomp b hb_im
  have hb : b ∈ combN := by change |b.im - 1 / 2| ≤ 1 / 4; rw [hb_im]; norm_num
  have hb_mid : b ∈ combNMid := combN_subset_combNMid hb
  have hdec := h_decomp hb_mid
  have hre_phi0 : (phi0 b).re = 0 := by
    unfold phi0
    have hint := integrable_rhoU_combPhiDeriv (i := 0) (j := 0) (by norm_num) hb_mid
    have hre_int := Complex.reCLM.integral_comp_comm hint
    simp only [combPhiDeriv_zero] at hre_int
    rw [← Complex.reCLM_apply, ← hre_int]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [phiZeta_re_eq_zero_of_im_half (xiStar_pos.le.trans hy.out.le) hb_im, mul_zero]
  have ha_f : (1 / 4 : ℝ) ≤ (f : ℕ) := by
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  have ha_m : ∀ m : ℕ, (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := fun m => by
    have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    linarith
  have hχ_nn : ∀ a : ℝ, 1 / 4 ≤ a → 0 ≤ chiQuantile c' a := fun a ha =>
    xiStar_pos.le.trans (chiQuantile_spec hc' ha).1
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (f + 1 + m)| ≤ 1 / 8 := fun m => by
    have hgap_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn (ha_m m)
        ((ha_m m).trans (by linarith)) (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgap_nn)]
    have hgk := (hgap_k (f + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (f + 1 + m) ≤ (1 / 4) * (1 / 2) := mul_le_mul hη₀1 hgk hgap_nn (by norm_num)
      _ = 1 / 8 := by norm_num
  have hsum_term : Summable fun m : ℕ =>
      phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
      phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b := by
    obtain ⟨C, hC, hbd⟩ := norm_phiZeta_le
    refine Summable.of_norm_bounded (g := fun m : ℕ => 2 * C * Real.exp (π * |b.re|) *
        Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)))
      ((summable_exp_neg_pi_chiQuantile hc' f).mul_left (2 * C * Real.exp (π * |b.re|))) fun m => ?_
    have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_add_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
    have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_sub_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
    have hn1 := (hbd hb hζ1).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have hn2 := (hbd hb hζ2).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have hexp_eq : C * Real.exp (-π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) =
        C * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by
      rw [show -π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) =
        π * |b.re| + -π * chiQuantile c' (f + 1 + m : ℕ) by ring, Real.exp_add]; ring
    have hre1 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    have hre2 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    rw [hre1] at hn1; rw [hre2] at hn2
    rw [hexp_eq] at hn1 hn2
    exact (norm_add_le _ _).trans (by linarith)
  have hre_pair : ∀ m : ℕ,
      (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b).re = 0 := by
    intro m
    have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_add_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
    have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_sub_I_mul_mem_combZ (hχ_nn _ (ha_m m)) (hε_bd m)
    have hexp : Real.exp (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b).re = 1 := by
      rw [← Complex.norm_exp, Complex.exp_add, cexp_phiZeta hb hζ1, cexp_phiZeta hb hζ2, neg_mul_neg]
      exact norm_pair_blaschkeT_eq_one (chiQuantile c' (f + 1 + m : ℕ)) (η₀ * siteGap c' (f + 1 + m))
        ((hε_bd m).trans (by norm_num)) (by rw [hb_im, abs_of_pos (by norm_num)])
    rwa [Real.exp_eq_one_iff] at hexp
  have hre_log : (logRefComb c' f η₀ b).re = 0 := by
    unfold logRefComb
    rw [Complex.add_re, Complex.add_re]
    have h1 : ((π : ℂ) * Complex.I).re = 0 := by simp
    have h2 : (phiZeta (chiQuantile c' f : ℂ) b).re = 0 :=
      phiZeta_re_eq_zero_of_im_half (hχ_nn _ ha_f) hb_im
    have h3 : (∑' m : ℕ, (phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        phiZeta ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b)).re = 0 := by
      rw [← Complex.reCLM_apply, ContinuousLinearMap.map_tsum Complex.reCLM hsum_term]
      simp only [Complex.reCLM_apply, hre_pair, tsum_zero]
    rw [h1, h2, h3, add_zero, add_zero]
  have hre_dec : (phi1Comb c' f η₀ b).re =
      (logRefComb c' f η₀ b).re - ((c' : ℂ) * phi0 b).re := by
    have : phi1Comb c' f η₀ b = logRefComb c' f η₀ b - (c' : ℂ) * phi0 b := by
      rw [hdec]; ring
    rw [this, Complex.sub_re]
  rw [hre_dec, hre_log, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hre_phi0, mul_zero, sub_zero]

/-- $i$-th $b$-derivative of `barPhi`: $\frac{c'}{2 n_1} \int_{\xi_*}^{\chi_f} \rho_U(y)\,\partial_b^i \varphi_y(b)\,dy$. -/
noncomputable def barPhiDeriv (i : ℕ) (c' : ℝ) (f : ℕ) (b : ℂ) : ℂ :=
  ((1 / (2 * n1Comb f) : ℝ) : ℂ) * (c' : ℂ) *
    ∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b

/-- $i$-th $b$-derivative of `deltaDetComb`. -/
noncomputable def deltaDetCombDeriv (i : ℕ) (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) : ℂ :=
  ∑' m : ℕ,
    (combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
      combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b -
      2 * combPhiDeriv i 0 (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b)

/-- $i$-th $b$-derivative of `emRem`. -/
noncomputable def emRemDeriv (i : ℕ) (c' : ℝ) (f : ℕ) (b : ℂ) : ℂ :=
  -(1 / 12 : ℂ) * emKernFDeriv i c' b f + emRem2Deriv i c' f b

/-- $i$-th $b$-derivative of `phi1Comb`. -/
noncomputable def phi1CombDeriv (i : ℕ) (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) : ℂ :=
  (if i = 0 then (π : ℂ) * Complex.I else 0) - ((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b +
    deltaDetCombDeriv i c' f η₀ b + emRemDeriv i c' f b

lemma hasDerivAt_barPhiDeriv {i : ℕ} (hi : i ≤ 1) {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f)
    {b : ℂ} (hb : b ∈ combNMid) :
    HasDerivAt (barPhiDeriv i c' f) (barPhiDeriv (i + 1) c' f b) b := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have ha_f : (1 / 4 : ℝ) ≤ (f : ℕ) := by linarith
  have hχ_f := (chiQuantile_spec hc' ha_f).1
  set r₀ := (17 / 64 - |b.im - 1 / 2|) / 2
  have hr₀ : 0 < r₀ := by
    have : |b.im - 1 / 2| < 17 / 64 := hb
    dsimp [r₀]; linarith
  have hball_sub : ∀ z ∈ Metric.ball b r₀, z ∈ combNMid := by
    intro z hz
    have him : |z.im - b.im| < r₀ := (Complex.abs_im_le_norm (z - b)).trans_lt (mem_ball_iff_norm.mp hz)
    change |z.im - 1 / 2| < 17 / 64
    have h1 := (abs_lt.mp him).1; have h2 := (abs_lt.mp him).2
    have hb1 := abs_lt.mp (show |b.im - 1 / 2| < 17 / 64 from hb)
    dsimp [r₀] at h1 h2
    rcases abs_cases (b.im - 1 / 2) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  let F : ℂ → ℝ → ℂ := fun w y => (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) w
  let F' : ℂ → ℝ → ℂ := fun w y => (rhoU y : ℂ) * combPhiDeriv (i + 1) 0 (y : ℂ) w
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  have h_meas : ∀ᶠ w in 𝓝 b, AEStronglyMeasurable (F w) (volume.restrict (Set.uIoc xiStar (chiQuantile c' f))) := by
    filter_upwards [Metric.ball_mem_nhds b hr₀] with w hw
    have hw_mid := hball_sub w hw
    have hcont : ContinuousOn (F w) (Icc xiStar (chiQuantile c' f)) := by
      intro y hy
      have hρ : ContinuousWithinAt (fun z : ℝ => (rhoU z : ℂ)) (Icc xiStar (chiQuantile c' f)) y :=
        Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
          ((continuousOn_rhoU.mono Icc_subset_Ici_self) y hy)
      have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith [xiStar_pos, hy.1])
      have hφ : ContinuousAt (fun t : ℝ => combPhiDeriv i 0 (t : ℂ) w) y :=
        (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0)
          (combNMid_subset_combNOpen hw_mid) hζ).continuousAt.comp Complex.continuous_ofReal.continuousAt
      exact hρ.mul hφ.continuousWithinAt
    rw [Set.uIoc_of_le hχ_f]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_int : IntervalIntegrable (F b) volume xiStar (chiQuantile c' f) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hχ_f).mpr
      ((integrable_rhoU_combPhiDeriv (i := i) (j := 0) (by omega) hb).mono_set Ioc_subset_Ioi_self)
  have h_meas' : AEStronglyMeasurable (F' b) (volume.restrict (Set.uIoc xiStar (chiQuantile c' f))) := by
    have hcont : ContinuousOn (F' b) (Icc xiStar (chiQuantile c' f)) := by
      intro y hy
      have hρ : ContinuousWithinAt (fun z : ℝ => (rhoU z : ℂ)) (Icc xiStar (chiQuantile c' f)) y :=
        Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
          ((continuousOn_rhoU.mono Icc_subset_Ici_self) y hy)
      have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith [xiStar_pos, hy.1])
      have hφ : ContinuousAt (fun t : ℝ => combPhiDeriv (i + 1) 0 (t : ℂ) b) y :=
        (hasDerivAt_combPhiDeriv_zeta (i := i + 1) (j := 0)
          (combNMid_subset_combNOpen hb) hζ).continuousAt.comp Complex.continuous_ofReal.continuousAt
      exact hρ.mul hφ.continuousWithinAt
    rw [Set.uIoc_of_le hχ_f]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ᵐ y ∂volume, y ∈ Set.uIoc xiStar (chiQuantile c' f) →
      ∀ w ∈ Metric.ball b r₀, ‖F' w y‖ ≤ C * rhoU y := by
    refine ae_of_all _ fun y hy w hw => ?_
    rw [Set.uIoc_of_le hχ_f] at hy
    have hζ : (y : ℂ) ∈ combZ := ofReal_mem_combZ (xiStar_pos.le.trans hy.1.le)
    have h1 := (hbd (i + 1) 0 (by omega) (hball_sub w hw) hζ).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le)
    rw [mul_one] at h1
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoU_nonneg y)]
    calc rhoU y * ‖combPhiDeriv (i + 1) 0 (y : ℂ) w‖ ≤ rhoU y * C :=
          mul_le_mul_of_nonneg_left h1 (rhoU_nonneg y)
      _ = C * rhoU y := mul_comm _ _
  have h_diff : ∀ᵐ y ∂volume, y ∈ Set.uIoc xiStar (chiQuantile c' f) →
      ∀ w ∈ Metric.ball b r₀, HasDerivAt (fun z => F z y) (F' w y) w := by
    refine ae_of_all _ fun y hy w hw => ?_
    rw [Set.uIoc_of_le hχ_f] at hy
    have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith [xiStar_pos, hy.1])
    exact (hasDerivAt_combPhiDeriv_b (combNMid_subset_combNOpen (hball_sub w hw)) hζ).const_mul _
  have hint_bnd : IntervalIntegrable (fun y : ℝ => C * rhoU y) volume xiStar (chiQuantile c' f) :=
    (intervalIntegrable_rhoU le_rfl hχ_f).const_mul C
  have hd_int := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds b hr₀) h_meas h_int h_meas' h_bound hint_bnd h_diff).2
  unfold barPhiDeriv
  exact hd_int.const_mul _

lemma hasDerivAt_deltaDetCombDeriv {i : ℕ} (hi : i ≤ 1) {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f)
    {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) (hgap_half : siteGap c' 1 ≤ 1 / 2)
    (hgap_k : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ siteGap c' 1)
    {b : ℂ} (hb : b ∈ combNMid) :
    HasDerivAt (deltaDetCombDeriv i c' f η₀) (deltaDetCombDeriv (i + 1) c' f η₀ b) b := by
  set r₀ := (17 / 64 - |b.im - 1 / 2|) / 2
  have hr₀ : 0 < r₀ := by
    have : |b.im - 1 / 2| < 17 / 64 := hb
    dsimp [r₀]; linarith
  have hball_sub : ∀ z ∈ Metric.ball b r₀, z ∈ combNMid := by
    intro z hz
    have him : |z.im - b.im| < r₀ := (Complex.abs_im_le_norm (z - b)).trans_lt (mem_ball_iff_norm.mp hz)
    change |z.im - 1 / 2| < 17 / 64
    have h1 := (abs_lt.mp him).1; have h2 := (abs_lt.mp him).2
    have hb1 := abs_lt.mp (show |b.im - 1 / 2| < 17 / 64 from hb)
    dsimp [r₀] at h1 h2
    rcases abs_cases (b.im - 1 / 2) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have ha_m : ∀ m : ℕ, (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := fun m => by
    have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    linarith
  have hχ_nn : ∀ m : ℕ, 0 ≤ chiQuantile c' (f + 1 + m : ℕ) := fun m =>
    xiStar_pos.le.trans (chiQuantile_spec hc' (ha_m m)).1
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (f + 1 + m)| ≤ 1 / 8 := fun m => by
    have hgap_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn (ha_m m)
        ((ha_m m).trans (by linarith)) (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgap_nn)]
    have hgk := (hgap_k (f + 1 + m) (by omega)).trans hgap_half
    calc η₀ * siteGap c' (f + 1 + m) ≤ (1 / 4) * (1 / 2) := mul_le_mul hη₀1 hgk hgap_nn (by norm_num)
      _ = 1 / 8 := by norm_num
  let G : ℕ → ℂ → ℂ := fun m w =>
    combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) w +
      combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) w -
      2 * combPhiDeriv i 0 (chiQuantile c' (f + 1 + m : ℕ) : ℂ) w
  let G' : ℕ → ℂ → ℂ := fun m w =>
    combPhiDeriv (i + 1) 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) w +
      combPhiDeriv (i + 1) 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) w -
      2 * combPhiDeriv (i + 1) 0 (chiQuantile c' (f + 1 + m : ℕ) : ℂ) w
  have hG_deriv : ∀ m : ℕ, ∀ w ∈ Metric.ball b r₀, HasDerivAt (G m) (G' m w) w := by
    intro m w hw
    have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZOpen :=
      combZ_subset_combZOpen (ofReal_add_I_mul_mem_combZ (hχ_nn m) (hε_bd m))
    have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZOpen :=
      combZ_subset_combZOpen (ofReal_sub_I_mul_mem_combZ (hχ_nn m) (hε_bd m))
    have hζ0 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) ∈ combZOpen :=
      combZ_subset_combZOpen (ofReal_mem_combZ (hχ_nn m))
    have hw_open := combNMid_subset_combNOpen (hball_sub w hw)
    exact ((hasDerivAt_combPhiDeriv_b hw_open hζ1).add
      (hasDerivAt_combPhiDeriv_b hw_open hζ2)).sub
      ((hasDerivAt_combPhiDeriv_b hw_open hζ0).const_mul 2)
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  have hre_ball : ∀ w ∈ Metric.ball b r₀, |w.re| ≤ |b.re| + r₀ := fun w hw => by
    have hr := (Complex.abs_re_le_norm (w - b)).trans_lt (mem_ball_iff_norm.mp hw)
    have h1 := (abs_lt.mp hr).1; have h2 := (abs_lt.mp hr).2
    have hre1 : (w - b).re = w.re - b.re := Complex.sub_re w b
    rw [hre1] at h1 h2
    rcases abs_cases w.re with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases b.re with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  let u : ℕ → ℝ := fun m => 4 * C * Real.exp (π * (|b.re| + r₀)) *
      Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ))
  have hu_sum : Summable u := (summable_exp_neg_pi_chiQuantile hc' f).mul_left _
  have h_le : ∀ (m : ℕ) (w : ℂ), w ∈ Metric.ball b r₀ → ‖G m w‖ ≤ u m := by
    intro m w hw
    have hw_mid := hball_sub w hw
    have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_add_I_mul_mem_combZ (hχ_nn m) (hε_bd m)
    have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_sub_I_mul_mem_combZ (hχ_nn m) (hε_bd m)
    have hζ0 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) ∈ combZ := ofReal_mem_combZ (hχ_nn m)
    have b1 := (hbd i 0 (by omega) hw_mid hζ1).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have b2 := (hbd i 0 (by omega) hw_mid hζ2).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have b0 := (hbd i 0 (by omega) hw_mid hζ0).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have hre_w := hre_ball w hw
    have hexp_w : Real.exp (-π * (chiQuantile c' (f + 1 + m : ℕ) - |w.re|)) ≤
        Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hre1 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    have hre2 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    have hre0 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ)).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    rw [hre1] at b1; rw [hre2] at b2; rw [hre0] at b0
    calc ‖G m w‖
        ≤ ‖combPhiDeriv i 0 _ w‖ + ‖combPhiDeriv i 0 _ w‖ + 2 * ‖combPhiDeriv i 0 _ w‖ := by
            dsimp [G]; refine (norm_sub_le _ _).trans ?_; gcongr
            · exact norm_add_le _ _
            · rw [norm_mul, Complex.norm_ofNat]
      _ ≤ 4 * (C * Real.exp (-π * (chiQuantile c' (f + 1 + m : ℕ) - |w.re|))) := by linarith
      _ ≤ 4 * (C * (Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_w hC.le) (by norm_num)
      _ = u m := by dsimp [u]; ring
  have hs := Complex.hasSum_deriv_of_summable_norm hu_sum
    (fun m w hw => (hG_deriv m w hw).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball h_le (Metric.mem_ball_self hr₀)
  have htsum_eq : (∑' m : ℕ, deriv (G m) b) = deltaDetCombDeriv (i + 1) c' f η₀ b := by
    unfold deltaDetCombDeriv
    refine tsum_congr fun m => (hG_deriv m b (Metric.mem_ball_self hr₀)).deriv
  have hdiff_tsum : DifferentiableAt ℂ (fun w => ∑' m : ℕ, G m w) b :=
    (Complex.differentiableOn_tsum_of_summable_norm hu_sum
      (fun m w hw => (hG_deriv m w hw).differentiableAt.differentiableWithinAt)
      Metric.isOpen_ball h_le).differentiableAt (Metric.ball_mem_nhds b hr₀)
  rw [← htsum_eq, hs.tsum_eq]
  exact hdiff_tsum.hasDerivAt

lemma hasDerivAt_emRem2Deriv {i : ℕ} (hi : i ≤ 1) {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f)
    {b : ℂ} (hb : b ∈ combNMid) :
    HasDerivAt (emRem2Deriv i c' f) (emRem2Deriv (i + 1) c' f b) b := by
  set r₀ := (17 / 64 - |b.im - 1 / 2|) / 2
  have hr₀ : 0 < r₀ := by
    have : |b.im - 1 / 2| < 17 / 64 := hb
    dsimp [r₀]; linarith
  have hball_sub : ∀ z ∈ Metric.ball b r₀, z ∈ combNMid := by
    intro z hz
    have him : |z.im - b.im| < r₀ := (Complex.abs_im_le_norm (z - b)).trans_lt (mem_ball_iff_norm.mp hz)
    change |z.im - 1 / 2| < 17 / 64
    have h1 := (abs_lt.mp him).1; have h2 := (abs_lt.mp him).2
    have hb1 := abs_lt.mp (show |b.im - 1 / 2| < 17 / 64 from hb)
    dsimp [r₀] at h1 h2
    rcases abs_cases (b.im - 1 / 2) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hre_ball : ∀ w ∈ Metric.ball b r₀, |w.re| ≤ |b.re| + r₀ := fun w hw => by
    have hr := (Complex.abs_re_le_norm (w - b)).trans_lt (mem_ball_iff_norm.mp hw)
    have h1 := (abs_lt.mp hr).1; have h2 := (abs_lt.mp hr).2
    have hre1 : (w - b).re = w.re - b.re := Complex.sub_re w b
    rw [hre1] at h1 h2
    rcases abs_cases w.re with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases b.re with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  have hcd1 : ∀ a : ℝ, 1 ≤ a → chiDeriv c' a ≤ chiDeriv c' 1 := fun a ha => by
    rcases eq_or_lt_of_le ha with rfl | hlt
    · exact le_rfl
    · exact (chiDeriv_strictAntiOn hc' (show (1 / 4 : ℝ) < 1 by norm_num)
        (show (1 / 4 : ℝ) < a by linarith) hlt).le
  have hsec1 : ∀ a : ℝ, 1 ≤ a → |chiSecond c' a| ≤ (4 / 3) * chiDeriv c' 1 := fun a ha => by
    have ha14 : 1 / 4 < a := by linarith
    have hcd_pos : 0 < chiDeriv c' a := by
      unfold chiDeriv; exact div_pos two_pos (mul_pos hc' (rhoU_pos (xiStar_lt_chiQuantile hc' ha14)))
    have h1 := abs_logDeriv_chiDeriv_le hc' ha14
    rw [abs_div, abs_of_pos hcd_pos, div_le_iff₀ hcd_pos] at h1
    calc |chiSecond c' a| ≤ 1 / (a - 1 / 4) * chiDeriv c' a := h1
      _ ≤ 1 / (1 - 1 / 4) * chiDeriv c' 1 :=
          mul_le_mul (one_div_le_one_div_of_le (by norm_num) (by linarith))
            (hcd1 a ha) hcd_pos.le (by norm_num)
      _ = (4 / 3) * chiDeriv c' 1 := by norm_num
  have hcd1_nn : 0 ≤ chiDeriv c' 1 := by
    unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
  set K := (1 / 6 : ℝ) * C * Real.exp (π * (|b.re| + r₀)) * (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)
  let G : ℕ → ℂ → ℂ := fun m w =>
    ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond i c' w ((f + m : ℕ) + t)
  let G' : ℕ → ℂ → ℂ := fun m w =>
    ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond (i + 1) c' w ((f + m : ℕ) + t)
  have h_cont_kern : ∀ (k : ℕ) (hk : k ≤ 2) (m : ℕ) {w : ℂ} (hw : w ∈ combNMid),
      ContinuousOn (fun t : ℝ => (bernoulliP2 t : ℂ) * emKernFSecond k c' w ((f + m : ℕ) + t))
        (Icc 0 1) :=
    fun k hk m w hw => continuousOn_bernoulli_mul_emKernFSecond hk hc' hf m hw
  have hG_deriv : ∀ m : ℕ, ∀ w ∈ Metric.ball b r₀, HasDerivAt (G m) (G' m w) w := by
    intro m w hw
    have hw_mid := hball_sub w hw
    set r₁ := min r₀ ((17 / 64 - |w.im - 1 / 2|) / 2)
    have hr₁ : 0 < r₁ := lt_min hr₀ (by have : |w.im - 1 / 2| < 17 / 64 := hw_mid; linarith)
    have hball1_sub : ∀ z ∈ Metric.ball w r₁, z ∈ combNMid := by
      intro z hz
      have him : |z.im - w.im| < (17 / 64 - |w.im - 1 / 2|) / 2 :=
        (Complex.abs_im_le_norm (z - w)).trans_lt ((mem_ball_iff_norm.mp hz).trans_le (min_le_right _ _))
      change |z.im - 1 / 2| < 17 / 64
      have h1 := (abs_lt.mp him).1; have h2 := (abs_lt.mp him).2
      rcases abs_cases (w.im - 1 / 2) with ⟨_, _⟩ | ⟨_, _⟩ <;> exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have h_meas : ∀ᶠ z in 𝓝 w, AEStronglyMeasurable
        (fun t : ℝ => (bernoulliP2 t : ℂ) * emKernFSecond i c' z ((f + m : ℕ) + t))
        (volume.restrict (Set.uIoc 0 1)) := by
      filter_upwards [Metric.ball_mem_nhds w hr₁] with z hz
      rw [Set.uIoc_of_le zero_le_one]
      exact ((h_cont_kern i (by omega) m (hball1_sub z hz)).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc
    have h_int : IntervalIntegrable
        (fun t : ℝ => (bernoulliP2 t : ℂ) * emKernFSecond i c' w ((f + m : ℕ) + t)) volume 0 1 :=
      (h_cont_kern i (by omega) m hw_mid).intervalIntegrable_of_Icc zero_le_one
    have h_meas' : AEStronglyMeasurable
        (fun t : ℝ => (bernoulliP2 t : ℂ) * emKernFSecond (i + 1) c' w ((f + m : ℕ) + t))
        (volume.restrict (Set.uIoc 0 1)) := by
      rw [Set.uIoc_of_le zero_le_one]
      exact ((h_cont_kern (i + 1) (by omega) m hw_mid).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc
    set M_bd := (1 / 6 : ℝ) * C * (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)
    have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ z ∈ Metric.ball w r₁,
        ‖(bernoulliP2 t : ℂ) * emKernFSecond (i + 1) c' z ((f + m : ℕ) + t)‖ ≤ M_bd := by
      refine ae_of_all _ fun t ht z hz => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht1 : (1 : ℝ) ≤ (f + m : ℕ) + t := by
        have : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
        linarith [ht.1]
      have hζ : (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) ∈ combZ :=
        ofReal_mem_combZ (xiStar_pos.le.trans ((chiQuantile_spec hc' (by linarith)).1))
      have hb2 := (hbd (i + 1) 2 (by omega) (hball1_sub z hz) hζ).trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le)
      have hb1 := (hbd (i + 1) 1 (by omega) (hball1_sub z hz) hζ).trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le)
      rw [mul_one] at hb2 hb1
      have hcd_le := hcd1 _ ht1
      have hcd_nn : 0 ≤ chiDeriv c' ((f + m : ℕ) + t) := by
        unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
      have hsec_le := hsec1 _ ht1
      have hP2 := abs_bernoulliP2_le ht.1.le ht.2
      rw [norm_mul, Complex.norm_real]
      have hsec_bd : ‖emKernFSecond (i + 1) c' z ((f + m : ℕ) + t)‖ ≤
          2 * C * (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1) := by
        unfold emKernFSecond
        calc ‖2 * (combPhiDeriv (i + 1) 2 _ z * ((chiDeriv c' _ ^ 2 : ℝ) : ℂ) +
                combPhiDeriv (i + 1) 1 _ z * ((chiSecond c' _ : ℝ) : ℂ))‖
            ≤ 2 * (‖combPhiDeriv (i + 1) 2 _ z‖ * ‖((chiDeriv c' _ ^ 2 : ℝ) : ℂ)‖ +
                ‖combPhiDeriv (i + 1) 1 _ z‖ * ‖((chiSecond c' _ : ℝ) : ℂ)‖) := by
                rw [norm_mul, Complex.norm_ofNat]; gcongr
                exact (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)
          _ ≤ 2 * (C * (chiDeriv c' 1 ^ 2) + C * ((4 / 3) * chiDeriv c' 1)) := by
                gcongr
                · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
                  exact pow_le_pow_left₀ hcd_nn hcd_le 2
                · rwa [Complex.norm_real, Real.norm_eq_abs]
          _ = 2 * C * (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1) := by ring
      calc |bernoulliP2 t| * ‖emKernFSecond (i + 1) c' z ((f + m : ℕ) + t)‖
          ≤ (1 / 12) * (2 * C * (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)) := by gcongr
        _ = M_bd := by dsimp [M_bd]; ring
    have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ z ∈ Metric.ball w r₁,
        HasDerivAt (fun s => (bernoulliP2 t : ℂ) * emKernFSecond i c' s ((f + m : ℕ) + t))
          ((bernoulliP2 t : ℂ) * emKernFSecond (i + 1) c' z ((f + m : ℕ) + t)) z := by
      refine ae_of_all _ fun t ht z hz => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hm1 : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
      have ht14 : 1 / 4 < ((f + m : ℕ) : ℝ) + t := by linarith [ht.1]
      have hζ : (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) ∈ combZOpen :=
        ofReal_mem_combZOpen (by linarith [xiStar_pos, xiStar_lt_chiQuantile hc' ht14])
      have hz_open := combNMid_subset_combNOpen (hball1_sub z hz)
      unfold emKernFSecond
      have hd2 := (hasDerivAt_combPhiDeriv_b hz_open hζ (i := i) (j := 2)).mul_const
        ((chiDeriv c' (((f + m : ℕ) : ℝ) + t) ^ 2 : ℝ) : ℂ)
      have hd1 := (hasDerivAt_combPhiDeriv_b hz_open hζ (i := i) (j := 1)).mul_const
        ((chiSecond c' (((f + m : ℕ) : ℝ) + t) : ℝ) : ℂ)
      exact ((hd2.add hd1).const_mul (2 : ℂ)).const_mul (bernoulliP2 t : ℂ)
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds w hr₁) h_meas h_int h_meas' h_bound intervalIntegrable_const h_diff).2
  let u : ℕ → ℝ := fun m => K * Real.exp (-π * chiQuantile c' (f + m : ℕ))
  have hu_sum : Summable u := (summable_exp_neg_pi_chiQuantile_gen hc' f).mul_left K
  have h_le : ∀ (m : ℕ) (w : ℂ), w ∈ Metric.ball b r₀ → ‖G m w‖ ≤ u m := by
    intro m w hw
    have hw_mid := hball_sub w hw
    refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
    have hconst : ∫ t in (0 : ℝ)..1, u m = u m := by simp
    rw [← hconst]
    refine intervalIntegral.integral_mono_on zero_le_one
      (h_cont_kern i (by omega) m hw_mid |>.norm.intervalIntegrable_of_Icc zero_le_one)
      intervalIntegrable_const fun t ht => ?_
    have hm1 : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
    have ht1 : (1 : ℝ) ≤ ((f + m : ℕ) : ℝ) + t := by linarith [ht.1]
    have hχ_ge : chiQuantile c' (f + m : ℕ) ≤ chiQuantile c' (((f + m : ℕ) : ℝ) + t) :=
      (chiQuantile_strictMonoOn hc').monotoneOn
        (show (1 / 4 : ℝ) ≤ (f + m : ℕ) by linarith)
        (show (1 / 4 : ℝ) ≤ ((f + m : ℕ) : ℝ) + t by linarith)
        (by linarith [ht.1])
    have hζ : (chiQuantile c' (((f + m : ℕ) : ℝ) + t) : ℂ) ∈ combZ :=
      ofReal_mem_combZ (xiStar_pos.le.trans ((chiQuantile_spec hc' (by linarith)).1))
    have hb2 := (hbd i 2 (by omega) hw_mid hζ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have hb1 := (hbd i 1 (by omega) hw_mid hζ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    have hre_w := hre_ball w hw
    have hexp_le : Real.exp (-π * (chiQuantile c' (((f + m : ℕ) : ℝ) + t) - |w.re|)) ≤
        Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    simp only [Complex.ofReal_re] at hb2 hb1
    have hP2 := abs_bernoulliP2_le ht.1 ht.2
    have hcd_le := hcd1 _ ht1
    have hcd_nn : 0 ≤ chiDeriv c' ((f + m : ℕ) + t) := by
      unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
    have hsec_le := hsec1 _ ht1
    have hsec_bd : ‖emKernFSecond i c' w ((f + m : ℕ) + t)‖ ≤
        2 * (C * Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) *
          (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)) := by
      unfold emKernFSecond
      calc ‖2 * (combPhiDeriv i 2 _ w * ((chiDeriv c' _ ^ 2 : ℝ) : ℂ) +
              combPhiDeriv i 1 _ w * ((chiSecond c' _ : ℝ) : ℂ))‖
          ≤ 2 * (‖combPhiDeriv i 2 _ w‖ * ‖((chiDeriv c' _ ^ 2 : ℝ) : ℂ)‖ +
              ‖combPhiDeriv i 1 _ w‖ * ‖((chiSecond c' _ : ℝ) : ℂ)‖) := by
              rw [norm_mul, Complex.norm_ofNat]; gcongr
              exact (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)
        _ ≤ 2 * ((C * Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + m : ℕ))) *
              (chiDeriv c' 1 ^ 2) +
              (C * Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + m : ℕ))) *
              ((4 / 3) * chiDeriv c' 1)) := by
              gcongr
              · exact (hb2.trans (mul_le_mul_of_nonneg_left hexp_le hC.le)).trans_eq (by ring)
              · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
                exact pow_le_pow_left₀ hcd_nn hcd_le 2
              · exact (hb1.trans (mul_le_mul_of_nonneg_left hexp_le hC.le)).trans_eq (by ring)
              · rwa [Complex.norm_real, Real.norm_eq_abs]
        _ = 2 * (C * Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) *
              (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1)) := by ring
    rw [norm_mul, Complex.norm_real]
    calc |bernoulliP2 t| * ‖emKernFSecond i c' w ((f + m : ℕ) + t)‖
        ≤ (1 / 12) * (2 * (C * Real.exp (π * (|b.re| + r₀)) * Real.exp (-π * chiQuantile c' (f + m : ℕ)) *
            (chiDeriv c' 1 ^ 2 + (4 / 3) * chiDeriv c' 1))) := by gcongr
      _ = u m := by dsimp [u, K]; ring
  have hs := Complex.hasSum_deriv_of_summable_norm hu_sum
    (fun m w hw => (hG_deriv m w hw).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball h_le (Metric.mem_ball_self hr₀)
  have htsum_eq : (∑' m : ℕ, deriv (G m) b) = -emRem2Deriv (i + 1) c' f b := by
    unfold emRem2Deriv
    rw [neg_neg]
    exact tsum_congr fun m => (hG_deriv m b (Metric.mem_ball_self hr₀)).deriv
  have hdiff_tsum : DifferentiableAt ℂ (fun w => ∑' m : ℕ, G m w) b :=
    (Complex.differentiableOn_tsum_of_summable_norm hu_sum
      (fun m w hw => (hG_deriv m w hw).differentiableAt.differentiableWithinAt)
      Metric.isOpen_ball h_le).differentiableAt (Metric.ball_mem_nhds b hr₀)
  have hd_neg := hdiff_tsum.hasDerivAt.neg
  have heq_neg : -(fun w => ∑' m : ℕ, G m w) = emRem2Deriv i c' f := by
    ext w; rfl
  rw [heq_neg, ← hs.tsum_eq, htsum_eq, neg_neg] at hd_neg
  exact hd_neg

lemma hasDerivAt_emRemDeriv {i : ℕ} (hi : i ≤ 1) {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f)
    {b : ℂ} (hb : b ∈ combNMid) :
    HasDerivAt (emRemDeriv i c' f) (emRemDeriv (i + 1) c' f b) b := by
  have ha_f : (1 / 4 : ℝ) ≤ (f : ℕ) := by
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  have hζ : (chiQuantile c' f : ℂ) ∈ combZOpen :=
    combZ_subset_combZOpen (ofReal_mem_combZ (xiStar_pos.le.trans (chiQuantile_spec hc' ha_f).1))
  have h1 : HasDerivAt (fun w => -(1 / 12 : ℂ) * emKernFDeriv i c' w f)
      (-(1 / 12 : ℂ) * emKernFDeriv (i + 1) c' b f) b := by
    unfold emKernFDeriv
    have hb_open := combNMid_subset_combNOpen hb
    exact (((hasDerivAt_combPhiDeriv_b hb_open hζ).const_mul (2 : ℂ)).mul_const
      (chiDeriv c' f : ℂ)).const_mul (-(1 / 12 : ℂ))
  exact h1.add (hasDerivAt_emRem2Deriv hi hc' f hf hb)

lemma iteratedDeriv_comb_eq {i : ℕ} (hi : i ≤ 2) {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f)
    {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) (hgap_half : siteGap c' 1 ≤ 1 / 2)
    (hgap_k : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ siteGap c' 1)
    {b : ℂ} (hb : b ∈ combNMid) :
    iteratedDeriv i (barPhi c' f) b = barPhiDeriv i c' f b ∧
      iteratedDeriv i (deltaDetComb c' f η₀) b = deltaDetCombDeriv i c' f η₀ b ∧
      iteratedDeriv i (emRem c' f) b = emRemDeriv i c' f b ∧
      iteratedDeriv i (phi1Comb c' f η₀) b = phi1CombDeriv i c' f η₀ b := by
  have hbar : ∀ j ≤ 2, ∀ {w : ℂ}, w ∈ combNMid → iteratedDeriv j (barPhi c' f) w = barPhiDeriv j c' f w := by
    intro j hj w hw
    induction j generalizing w with
    | zero => simp [barPhi, barPhiDeriv, combPhiDeriv_zero]
    | succ j ih =>
      have hev : (fun z => iteratedDeriv j (barPhi c' f) z) =ᶠ[𝓝 w] fun z => barPhiDeriv j c' f z := by
        filter_upwards [isOpen_combNMid.mem_nhds hw] with z hz; exact ih (by omega) hz
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hasDerivAt_barPhiDeriv (i := j) (by omega) hc' f hf hw).deriv
  have hdet : ∀ j ≤ 2, ∀ {w : ℂ}, w ∈ combNMid →
      iteratedDeriv j (deltaDetComb c' f η₀) w = deltaDetCombDeriv j c' f η₀ w := by
    intro j hj w hw
    induction j generalizing w with
    | zero => simp [deltaDetComb, deltaDetCombDeriv, combPhiDeriv_zero]
    | succ j ih =>
      have hev : (fun z => iteratedDeriv j (deltaDetComb c' f η₀) z) =ᶠ[𝓝 w]
          fun z => deltaDetCombDeriv j c' f η₀ z := by
        filter_upwards [isOpen_combNMid.mem_nhds hw] with z hz; exact ih (by omega) hz
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hasDerivAt_deltaDetCombDeriv (i := j) (by omega) hc' f hf hη₀0 hη₀1 hgap_half hgap_k hw).deriv
  have hem : ∀ j ≤ 2, ∀ {w : ℂ}, w ∈ combNMid →
      iteratedDeriv j (emRem c' f) w = emRemDeriv j c' f w := by
    intro j hj w hw
    induction j generalizing w with
    | zero => simp [emRem, emRemDeriv]
    | succ j ih =>
      have hev : (fun z => iteratedDeriv j (emRem c' f) z) =ᶠ[𝓝 w] fun z => emRemDeriv j c' f z := by
        filter_upwards [isOpen_combNMid.mem_nhds hw] with z hz; exact ih (by omega) hz
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hasDerivAt_emRemDeriv (i := j) (by omega) hc' f hf hw).deriv
  have hphi1 : ∀ j ≤ 2, ∀ {w : ℂ}, w ∈ combNMid →
      iteratedDeriv j (phi1Comb c' f η₀) w = phi1CombDeriv j c' f η₀ w := by
    intro j hj w hw
    induction j generalizing w with
    | zero =>
      simp [phi1Comb, phi1CombDeriv, barPhi, barPhiDeriv, deltaDetComb, deltaDetCombDeriv,
        emRem, emRemDeriv, combPhiDeriv_zero]
    | succ j ih =>
      have hev : (fun z => iteratedDeriv j (phi1Comb c' f η₀) z) =ᶠ[𝓝 w]
          fun z => phi1CombDeriv j c' f η₀ z := by
        filter_upwards [isOpen_combNMid.mem_nhds hw] with z hz; exact ih (by omega) hz
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have hd1 : HasDerivAt (fun _ : ℂ => (if j = 0 then (π : ℂ) * Complex.I else 0)) 0 w :=
        hasDerivAt_const _ _
      have hj1 : j ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj)
      have hd2 := (hasDerivAt_barPhiDeriv hj1 hc' f hf hw).const_mul ((2 * n1Comb f : ℝ) : ℂ)
      have hd3 := hasDerivAt_deltaDetCombDeriv hj1 hc' f hf hη₀0 hη₀1 hgap_half hgap_k hw
      have hd4 := hasDerivAt_emRemDeriv hj1 hc' f hf hw
      have htot := ((hd1.sub hd2).add hd3).add hd4
      exact htot.congr_deriv (by unfold phi1CombDeriv; simp) |>.deriv
  exact ⟨hbar i hi hb, hdet i hi hb, hem i hi hb, hphi1 i hi hb⟩

/-! ### Section 6: Uniform K3 bounds for `i = 0, 1, 2` on `combN` -/

private lemma deltaDetCombDeriv_bound :
    ∃ K_det > 0, ∀ {c' Cgap : ℝ}, 0 < c' → 0 < Cgap →
      (∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ siteGap c' 1) →
      siteGap c' 1 ≤ chiDeriv c' 1 →
      chiDeriv c' 1 ≤ Cgap * lambdaComb c' →
      siteGap c' 1 ≤ 1 / 2 →
      ∀ (f : ℕ), 1 ≤ f → ∀ {η₀ : ℝ}, 0 ≤ η₀ → η₀ ≤ 1 / 4 →
      ∀ (i : ℕ), i ≤ 2 → ∀ {b : ℂ}, b ∈ combNMid →
        ‖deltaDetCombDeriv i c' f η₀ b‖ ≤ K_det * Cgap * lambdaComb c' := by
  obtain ⟨Cφ, hCφ, _, hφ_min⟩ := combPhiDeriv_bound
  obtain ⟨Cdet, hCdet, h_detune⟩ := combPhiDeriv_detune_bound
  have hpi := Real.pi_pos
  set K_det := Cdet * (1 / 16 : ℝ) * Real.exp (π / 2) * (2 / π)
  refine ⟨K_det, by positivity, fun {c' Cgap} hc' hCgap hgap_k hgap_1_bd hcd1_bd hgap_1
    f hf {η₀} hη₀0 hη₀1 i hi {b} hb_mid => ?_⟩
  have ha_m : ∀ m : ℕ, (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := fun m => by
    have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    linarith
  have hχ_nn : ∀ m : ℕ, 0 ≤ chiQuantile c' (f + 1 + m : ℕ) := fun m =>
    xiStar_pos.le.trans (chiQuantile_spec hc' (ha_m m)).1
  have hgap_nn : ∀ m : ℕ, 0 ≤ siteGap c' (f + 1 + m) := fun m => by
    unfold siteGap
    exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn (ha_m m)
      ((ha_m m).trans (by linarith)) (by linarith))
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (f + 1 + m)| ≤ 1 / 8 := fun m => by
    rw [abs_of_nonneg (mul_nonneg hη₀0 (hgap_nn m))]
    have hgk := (hgap_k (f + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (f + 1 + m) ≤ (1 / 4) * (1 / 2) := mul_le_mul hη₀1 hgk (hgap_nn m) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hterm_bd : ∀ m : ℕ,
      ‖combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b -
        2 * combPhiDeriv i 0 (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b‖ ≤
      Cdet * (1 / 16 : ℝ) * (Cgap * lambdaComb c') *
        (siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|))) := by
    intro m
    have hdt := h_detune i hi (hχ_nn m) (hε_bd m) hb_mid
    have hgk1 : siteGap c' (f + 1 + m) ≤ Cgap * lambdaComb c' :=
      (hgap_k (f + 1 + m) (by omega)).trans (hgap_1_bd.trans hcd1_bd)
    have hsq : (η₀ * siteGap c' (f + 1 + m)) ^ 2 ≤
        (1 / 16 : ℝ) * (Cgap * lambdaComb c') * siteGap c' (f + 1 + m) := by
      have hgnn := hgap_nn m
      calc (η₀ * siteGap c' (f + 1 + m)) ^ 2
          = η₀ ^ 2 * siteGap c' (f + 1 + m) * siteGap c' (f + 1 + m) := by ring
        _ ≤ (1 / 4) ^ 2 * (Cgap * lambdaComb c') * siteGap c' (f + 1 + m) := by gcongr
        _ = (1 / 16 : ℝ) * (Cgap * lambdaComb c') * siteGap c' (f + 1 + m) := by norm_num
    calc ‖_‖ ≤ Cdet * (η₀ * siteGap c' (f + 1 + m)) ^ 2 *
          Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) := hdt
      _ ≤ Cdet * ((1 / 16 : ℝ) * (Cgap * lambdaComb c') * siteGap c' (f + 1 + m)) *
          Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) := by gcongr
      _ = Cdet * (1 / 16 : ℝ) * (Cgap * lambdaComb c') *
          (siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|))) := by
          ring
  have h_sg_eq : ∀ k : ℕ, siteGap c' k = chiQuantile c' (k + 1 : ℕ) - chiQuantile c' k := fun k => by
    unfold siteGap; push_cast; rfl
  have hcell_int : ∀ m : ℕ,
      siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) ≤
        Real.exp (π / 2) * ∫ y in (chiQuantile c' (f + 1 + m : ℕ))..(chiQuantile c' (f + 1 + m + 1 : ℕ)),
          Real.exp (-π * abs (y - |b.re|)) := by
    intro m
    have h_le_χ : chiQuantile c' (f + 1 + m : ℕ) ≤ chiQuantile c' (f + 1 + m + 1 : ℕ) := by
      have := hgap_nn m; rw [h_sg_eq] at this; linarith
    have hpt_y : ∀ y ∈ Icc (chiQuantile c' (f + 1 + m : ℕ)) (chiQuantile c' (f + 1 + m + 1 : ℕ)),
        Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) ≤
          Real.exp (π / 2) * Real.exp (-π * abs (y - |b.re|)) := by
      intro y hy
      have hgap_le : y - chiQuantile c' (f + 1 + m : ℕ) ≤ 1 / 2 := by
        have : y - chiQuantile c' (f + 1 + m : ℕ) ≤ siteGap c' (f + 1 + m) := by
          rw [h_sg_eq]; linarith [hy.2]
        exact this.trans ((hgap_k (f + 1 + m) (by omega)).trans hgap_1)
      have hdiff_abs : abs (y - |b.re|) ≤ abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) + 1 / 2 := by
        have : abs (y - |b.re|) - abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) ≤
            |(y - |b.re|) - (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)| := abs_sub_abs_le_abs_sub _ _
        have heq : (y - |b.re|) - (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) =
            y - chiQuantile c' (f + 1 + m : ℕ) := by ring
        rw [heq, abs_of_nonneg (sub_nonneg.mpr hy.1)] at this
        linarith
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hint1 : IntervalIntegrable (fun _ : ℝ =>
        Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)))
        volume (chiQuantile c' (f + 1 + m : ℕ)) (chiQuantile c' (f + 1 + m + 1 : ℕ)) :=
      intervalIntegrable_const
    have hint2 : IntervalIntegrable (fun y : ℝ => Real.exp (π / 2) * Real.exp (-π * abs (y - |b.re|)))
        volume (chiQuantile c' (f + 1 + m : ℕ)) (chiQuantile c' (f + 1 + m + 1 : ℕ)) :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        (continuous_abs.comp (continuous_id.sub continuous_const))))).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on h_le_χ hint1 hint2 hpt_y
    rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at hmono
    calc siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|))
        = (chiQuantile c' (f + 1 + m + 1 : ℕ) - chiQuantile c' (f + 1 + m : ℕ)) *
            Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) := by rw [h_sg_eq]
      _ ≤ Real.exp (π / 2) * ∫ y in (chiQuantile c' (f + 1 + m : ℕ))..(chiQuantile c' (f + 1 + m + 1 : ℕ)),
            Real.exp (-π * abs (y - |b.re|)) := hmono
  have h_sum_int : ∀ M : ℕ,
      ∑ m ∈ Finset.range M,
        siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) ≤
      Real.exp (π / 2) * (2 / π) := by
    intro M
    have hcont_exp : Continuous fun y : ℝ => Real.exp (-π * abs (y - |b.re|)) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const)))
    have h_adj : ∑ m ∈ Finset.range M,
          ∫ y in (chiQuantile c' (f + 1 + m : ℕ))..(chiQuantile c' (f + 1 + m + 1 : ℕ)),
            Real.exp (-π * abs (y - |b.re|)) =
        ∫ y in (chiQuantile c' (f + 1 : ℕ))..(chiQuantile c' (f + 1 + M : ℕ)),
          Real.exp (-π * abs (y - |b.re|)) := by
      induction M with
      | zero => simp
      | succ M ih =>
        rw [Finset.sum_range_succ, ih, intervalIntegral.integral_add_adjacent_intervals
          (hcont_exp.intervalIntegrable _ _) (hcont_exp.intervalIntegrable _ _)]
        have h1 : f + 1 + M + 1 = f + 1 + (M + 1) := by omega
        rw [h1]
    have hint_exp : Integrable (fun y : ℝ => Real.exp (-π * abs (y - |b.re|))) volume :=
      integrable_exp_neg_pi_abs.comp_sub_right |b.re|
    have h_le_tot : ∫ y in (chiQuantile c' (f + 1 : ℕ))..(chiQuantile c' (f + 1 + M : ℕ)),
          Real.exp (-π * abs (y - |b.re|)) ≤ 2 / π := by
      have h1M : (1 : ℝ) ≤ (f + 1 + M : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + M)
      have h_le_χ : chiQuantile c' (f + 1 : ℕ) ≤ chiQuantile c' (f + 1 + M : ℕ) :=
        (chiQuantile_strictMonoOn hc').monotoneOn (ha_m 0)
          (show (1 / 4 : ℝ) ≤ (f + 1 + M : ℕ) by linarith)
          (by exact_mod_cast (by omega : f + 1 ≤ f + 1 + M))
      rw [intervalIntegral.integral_of_le h_le_χ]
      calc ∫ y in Ioc (chiQuantile c' (f + 1 : ℕ)) (chiQuantile c' (f + 1 + M : ℕ)),
            Real.exp (-π * abs (y - |b.re|))
          ≤ ∫ y : ℝ, Real.exp (-π * abs (y - |b.re|)) :=
            setIntegral_le_integral hint_exp (Eventually.of_forall fun _ => (Real.exp_pos _).le)
        _ = 2 / π := by
            rw [integral_sub_right_eq_self (fun u : ℝ => Real.exp (-π * |u|)) |b.re|,
              integral_exp_neg_pi_abs]
    calc ∑ m ∈ Finset.range M,
          siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|))
        ≤ ∑ m ∈ Finset.range M, (Real.exp (π / 2) *
            ∫ y in (chiQuantile c' (f + 1 + m : ℕ))..(chiQuantile c' (f + 1 + m + 1 : ℕ)),
              Real.exp (-π * abs (y - |b.re|))) := Finset.sum_le_sum fun m _ => hcell_int m
      _ = Real.exp (π / 2) * ∑ m ∈ Finset.range M,
            ∫ y in (chiQuantile c' (f + 1 + m : ℕ))..(chiQuantile c' (f + 1 + m + 1 : ℕ)),
              Real.exp (-π * abs (y - |b.re|)) := (Finset.mul_sum _ _ _).symm
      _ = Real.exp (π / 2) * ∫ y in (chiQuantile c' (f + 1 : ℕ))..(chiQuantile c' (f + 1 + M : ℕ)),
            Real.exp (-π * abs (y - |b.re|)) := by rw [h_adj]
      _ ≤ Real.exp (π / 2) * (2 / π) := by gcongr
  have hlam_pos : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  have hsum_det_norm : Summable fun m : ℕ =>
      ‖combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b -
        2 * combPhiDeriv i 0 (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_exp_neg_pi_chiQuantile hc' f).mul_left (4 * Cφ * Real.exp (π * |b.re|)))
    have hζ1 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_add_I_mul_mem_combZ (hχ_nn m) (hε_bd m)
    have hζ2 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I ∈ combZ :=
      ofReal_sub_I_mul_mem_combZ (hχ_nn m) (hε_bd m)
    have hζ0 : (chiQuantile c' (f + 1 + m : ℕ) : ℂ) ∈ combZ := ofReal_mem_combZ (hχ_nn m)
    have b1 := (hφ_min i 0 (by omega) hb_mid hζ1).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCφ.le)
    have b2 := (hφ_min i 0 (by omega) hb_mid hζ2).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCφ.le)
    have b0 := (hφ_min i 0 (by omega) hb_mid hζ0).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCφ.le)
    have hre1 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    have hre2 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    have hre0 : ((chiQuantile c' (f + 1 + m : ℕ) : ℂ)).re =
        chiQuantile c' (f + 1 + m : ℕ) := by simp
    rw [hre1] at b1; rw [hre2] at b2; rw [hre0] at b0
    have hexp : Cφ * Real.exp (-π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)) =
        Cφ * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by
      rw [show -π * (chiQuantile c' (f + 1 + m : ℕ) - |b.re|) =
        π * |b.re| + -π * chiQuantile c' (f + 1 + m : ℕ) by ring, Real.exp_add]; ring
    rw [hexp] at b1 b2 b0
    calc ‖_‖ ≤ ‖combPhiDeriv i 0 _ b‖ + ‖combPhiDeriv i 0 _ b‖ + ‖2 * combPhiDeriv i 0 _ b‖ := by
          refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_add_le _ _
      _ ≤ Cφ * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) +
          Cφ * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) +
          2 * (Cφ * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ))) := by
          rw [norm_mul, Complex.norm_ofNat]; gcongr
      _ = 4 * Cφ * Real.exp (π * |b.re|) * Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by ring
  have htsum_det_le : ∑' m : ℕ, ‖combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b +
        combPhiDeriv i 0 ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b -
        2 * combPhiDeriv i 0 (chiQuantile c' (f + 1 + m : ℕ) : ℂ) b‖ ≤
      K_det * Cgap * lambdaComb c' := by
    refine hsum_det_norm.tsum_le_of_sum_le fun s => ?_
    obtain ⟨M, hMs⟩ := Finset.exists_nat_subset_range s
    calc ∑ m ∈ s, ‖_‖ ≤ ∑ m ∈ Finset.range M, ‖_‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hMs (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ m ∈ Finset.range M, (Cdet * (1 / 16 : ℝ) * (Cgap * lambdaComb c') *
            (siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|)))) :=
          Finset.sum_le_sum fun m _ => hterm_bd m
      _ = Cdet * (1 / 16 : ℝ) * (Cgap * lambdaComb c') * ∑ m ∈ Finset.range M,
            (siteGap c' (f + 1 + m) * Real.exp (-π * abs (chiQuantile c' (f + 1 + m : ℕ) - |b.re|))) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Cdet * (1 / 16 : ℝ) * (Cgap * lambdaComb c') * (Real.exp (π / 2) * (2 / π)) := by gcongr; exact h_sum_int M
      _ = K_det * Cgap * lambdaComb c' := by dsimp [K_det]; ring
  exact (norm_tsum_le_tsum_norm hsum_det_norm).trans htsum_det_le

private lemma emRemDeriv_bound :
    ∃ K_em > 0, ∀ {c' Cgap : ℝ}, 0 < c' → 0 < Cgap →
      chiDeriv c' 1 ≤ Cgap * lambdaComb c' →
      lambdaComb c' * phiQuantile 1 ≤ 1 →
      lambdaComb c' ≤ 1 →
      ∀ (f : ℕ), 1 ≤ f → ∀ (i : ℕ), i ≤ 2 → ∀ {b : ℂ}, b ∈ combNMid →
        ‖emRemDeriv i c' f b‖ ≤ K_em * (Cgap + 1) * lambdaComb c' := by
  obtain ⟨Cφ, hCφ, hφ_exp, hφ_min⟩ := combPhiDeriv_bound
  have hpi := Real.pi_pos
  have hk_pos : 0 < kTip := kTip_pos
  set c₀ := (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile 1
  have hc₀ : 0 < c₀ := by have := c1K0_pos; dsimp [c₀]; unfold phiQuantile; positivity
  set K_int := (1 / 6 : ℝ) * Cφ * ((8 / 3 : ℝ) * c₀ ^ (-(1 / 2 : ℝ)) + (6 / π) * kTip)
  set K_em := max ((1 / 6 : ℝ) * Cφ) K_int
  refine ⟨K_em, by positivity, fun {c' Cgap} hc' hCgap hcd1_bd hr1_bd hlam1 f hf i hi {b} hb_mid => ?_⟩
  have ha_f1 : (1 : ℝ) ≤ (f : ℕ) := by exact_mod_cast hf
  have ha_f : (1 / 4 : ℝ) ≤ (f : ℕ) := by linarith
  have hlam_pos : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  have h_em_bd : ‖emRemDeriv i c' f b‖ ≤ ((1 / 6 : ℝ) * Cφ * Cgap + K_int) * lambdaComb c' := by
    have hcd_f : chiDeriv c' f ≤ chiDeriv c' 1 := by
      rcases eq_or_lt_of_le ha_f1 with h1 | hlt
      · rw [← h1]
      · exact (chiDeriv_strictAntiOn hc' (show (1 / 4 : ℝ) < 1 by norm_num)
          (show (1 / 4 : ℝ) < f by linarith) hlt).le
    have hcd_f_nn : 0 ≤ chiDeriv c' f := by
      unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
    have h_fderiv_bd : ‖-(1 / 12 : ℂ) * emKernFDeriv i c' b f‖ ≤ (1 / 6) * Cφ * Cgap * lambdaComb c' := by
      have hζ : (chiQuantile c' f : ℂ) ∈ combZ :=
        ofReal_mem_combZ (xiStar_pos.le.trans (chiQuantile_spec hc' ha_f).1)
      have b1 := (hφ_min i 1 (by omega) hb_mid hζ).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hCφ.le)
      rw [mul_one] at b1
      unfold emKernFDeriv
      rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hcd_f_nn]
      calc (1 / 12 : ℝ) * (2 * ‖combPhiDeriv i 1 (chiQuantile c' f : ℂ) b‖ * chiDeriv c' f)
          ≤ (1 / 12 : ℝ) * (2 * Cφ * (Cgap * lambdaComb c')) := by
            gcongr; exact hcd_f.trans hcd1_bd
        _ = (1 / 6) * Cφ * Cgap * lambdaComb c' := by ring
    have h_inv_c'_lam : (c' : ℝ)⁻¹ * lambdaComb c' ^ (-(1 / 2 : ℝ)) = kTip * lambdaComb c' := by
      have hl32 : lambdaComb c' ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
        unfold lambdaComb
        rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
          Real.rpow_neg_one]
      have hmul : lambdaComb c' ^ (3 / 2 : ℝ) * lambdaComb c' ^ (-(1 / 2 : ℝ)) = lambdaComb c' := by
        rw [← Real.rpow_add hlam_pos, show (3 / 2 : ℝ) + -(1 / 2) = 1 by norm_num, Real.rpow_one]
      calc (c' : ℝ)⁻¹ * lambdaComb c' ^ (-(1 / 2 : ℝ))
          = kTip * (lambdaComb c' ^ (3 / 2 : ℝ) * lambdaComb c' ^ (-(1 / 2 : ℝ))) := by
            rw [hl32]; field_simp [hc'.ne', hk_pos.ne']
        _ = kTip * lambdaComb c' := by rw [hmul]
    have h_inv_c'_le : (c' : ℝ)⁻¹ ≤ kTip * lambdaComb c' := by
      have hl32 : (c' : ℝ)⁻¹ = kTip * lambdaComb c' ^ (3 / 2 : ℝ) := by
        unfold lambdaComb
        rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
          Real.rpow_neg_one]
        field_simp [hc'.ne', hk_pos.ne']
      rw [hl32]
      have hp : lambdaComb c' ^ (3 / 2 : ℝ) ≤ lambdaComb c' ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hlam_pos hlam1 (by norm_num)
      rw [Real.rpow_one] at hp
      exact mul_le_mul_of_nonneg_left hp hk_pos.le
    have hr1_ge : c₀ * lambdaComb c' ≤ siteRadius c' 1 := by
      have hr1 : siteRadius c' 1 ≤ 1 := (siteRadius_bounds hc' (by norm_num)).2.trans hr1_bd
      exact (siteRadius_le_one_bounds hc' (by norm_num) hr1).1.trans_eq' (by dsimp [c₀]; ring)
    have h_em2_norm : ∀ a : ℝ, 1 ≤ a →
        ‖emKernFSecond i c' b a‖ ≤
          2 * Cφ * chiDeriv c' a * (2 / (c' * rhoU (chiQuantile c' a))) *
            (Real.exp (-π * abs (chiQuantile c' a - |b.re|)) * (1 + (siteRadius c' a)⁻¹)) := by
      intro a ha1
      have ha14 : 1 / 4 < a := by linarith
      have hχ_gt : xiStar < chiQuantile c' a := xiStar_lt_chiQuantile hc' ha14
      have hr_pos : 0 < siteRadius c' a := sub_pos.mpr hχ_gt
      have hρ_pos : 0 < rhoU (chiQuantile c' a) := rhoU_pos hχ_gt
      have hcd_pos : 0 < chiDeriv c' a := by unfold chiDeriv; exact div_pos two_pos (mul_pos hc' hρ_pos)
      have hζ : (chiQuantile c' a : ℂ) ∈ combZ := ⟨by simp [xiStar_pos.le.trans hχ_gt.le], by simp⟩
      have hb2 := hφ_exp i 2 (by omega) (by omega) hb_mid hζ
      have hb1 := hφ_exp i 1 (by omega) (by omega) hb_mid hζ
      simp only [Complex.ofReal_re] at hb2 hb1
      have hld := (logDeriv_rhoU_bounds hr_pos).2
      have hld_pos := (logDeriv_rhoU_bounds hr_pos).1
      rw [show xiStar + siteRadius c' a = chiQuantile c' a by unfold siteRadius; ring] at hld hld_pos
      have hsec_eq : |chiSecond c' a| =
          chiDeriv c' a ^ 2 * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) := by
        unfold chiSecond
        rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) hld_pos.le)]
      have hsec_le : |chiSecond c' a| ≤ chiDeriv c' a * (2 / (c' * rhoU (chiQuantile c' a))) * (siteRadius c' a)⁻¹ := by
        rw [hsec_eq]
        calc chiDeriv c' a ^ 2 * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a))
            ≤ chiDeriv c' a ^ 2 * (1 / siteRadius c' a) := by gcongr
          _ = chiDeriv c' a * (2 / (c' * rhoU (chiQuantile c' a))) * (siteRadius c' a)⁻¹ := by
              unfold chiDeriv; ring
      have hcd_sq : chiDeriv c' a ^ 2 = chiDeriv c' a * (2 / (c' * rhoU (chiQuantile c' a))) := by
        unfold chiDeriv; ring
      unfold emKernFSecond
      calc ‖2 * (combPhiDeriv i 2 (chiQuantile c' a : ℂ) b * ((chiDeriv c' a ^ 2 : ℝ) : ℂ) +
              combPhiDeriv i 1 (chiQuantile c' a : ℂ) b * ((chiSecond c' a : ℝ) : ℂ))‖
          ≤ 2 * (‖combPhiDeriv i 2 (chiQuantile c' a : ℂ) b‖ * ‖((chiDeriv c' a ^ 2 : ℝ) : ℂ)‖ +
              ‖combPhiDeriv i 1 (chiQuantile c' a : ℂ) b‖ * ‖((chiSecond c' a : ℝ) : ℂ)‖) := by
              rw [norm_mul, Complex.norm_ofNat]; gcongr
              exact (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)
        _ ≤ 2 * (Cφ * Real.exp (-π * abs (chiQuantile c' a - |b.re|)) * (chiDeriv c' a ^ 2) +
              Cφ * Real.exp (-π * abs (chiQuantile c' a - |b.re|)) * |chiSecond c' a|) := by
              gcongr
              · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
              · rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 * (Cφ * Real.exp (-π * abs (chiQuantile c' a - |b.re|)) *
              (chiDeriv c' a * (2 / (c' * rhoU (chiQuantile c' a)))) +
              Cφ * Real.exp (-π * abs (chiQuantile c' a - |b.re|)) *
              (chiDeriv c' a * (2 / (c' * rhoU (chiQuantile c' a))) * (siteRadius c' a)⁻¹)) := by
              rw [hcd_sq]; gcongr
        _ = 2 * Cφ * chiDeriv c' a * (2 / (c' * rhoU (chiQuantile c' a))) *
              (Real.exp (-π * abs (chiQuantile c' a - |b.re|)) * (1 + (siteRadius c' a)⁻¹)) := by ring
    -- Continuous majorant on `(0, ∞)`
    let majorantR : ℝ → ℝ := fun r =>
      (2 / (3 * kTip)) * r ^ (-(3 / 2 : ℝ)) + (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + r - |b.re|))
    have h_majorant : ∀ r : ℝ, 0 < r →
        Real.exp (-π * abs (xiStar + r - |b.re|)) * (1 + r⁻¹) / rhoU (xiStar + r) ≤ majorantR r := by
      intro r hr
      dsimp [majorantR]
      rcases le_or_gt r 1 with hr1 | hr1
      · have hexp1 : Real.exp (-π * abs (xiStar + r - |b.re|)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (xiStar + r - |b.re|)])
        have h1r : 1 + r⁻¹ ≤ 2 * r⁻¹ := by
          have : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
          linarith
        have hρ := (le_max_left _ _).trans (rhoU_ge_max hr.le)
        have hρ_pos : 0 < 3 * kTip * √r := by positivity
        have hr_pow : r⁻¹ / √r = r ^ (-(3 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_sub hr]; norm_num
        have h1 : Real.exp (-π * abs (xiStar + r - |b.re|)) * (1 + r⁻¹) / rhoU (xiStar + r) ≤
            (2 / (3 * kTip)) * r ^ (-(3 / 2 : ℝ)) := by
          calc Real.exp (-π * abs (xiStar + r - |b.re|)) * (1 + r⁻¹) / rhoU (xiStar + r)
              ≤ 1 * (2 * r⁻¹) / (3 * kTip * √r) := by gcongr
            _ = (2 / (3 * kTip)) * (r⁻¹ / √r) := by ring
            _ = (2 / (3 * kTip)) * r ^ (-(3 / 2 : ℝ)) := by rw [hr_pow]
        linarith [show 0 ≤ (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + r - |b.re|)) by positivity]
      · have h1r : 1 + r⁻¹ ≤ 2 := by
          have : r⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hr1.le
          linarith
        have hρ := (le_max_right _ _).trans (rhoU_ge_max hr.le)
        have hρ' : (4 / 3 : ℝ) ≤ rhoU (xiStar + r) := by linarith
        have h2 : Real.exp (-π * abs (xiStar + r - |b.re|)) * (1 + r⁻¹) / rhoU (xiStar + r) ≤
            (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + r - |b.re|)) := by
          calc Real.exp (-π * abs (xiStar + r - |b.re|)) * (1 + r⁻¹) / rhoU (xiStar + r)
              ≤ Real.exp (-π * abs (xiStar + r - |b.re|)) * 2 / (4 / 3) := by gcongr
            _ = (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + r - |b.re|)) := by ring
        have hpos_r : 0 ≤ (2 / (3 * kTip)) * r ^ (-(3 / 2 : ℝ)) := by positivity
        linarith
    have h_cell_em : ∀ m : ℕ,
        ∫ t in (0 : ℝ)..1, ‖(bernoulliP2 t : ℂ) * emKernFSecond i c' b ((f + m : ℕ) + t)‖ ≤
          (1 / 6 : ℝ) * Cφ * (2 / c') *
            ∫ y in (chiQuantile c' (f + m : ℕ))..(chiQuantile c' (f + m + 1 : ℕ)),
              majorantR (y - xiStar) := by
      intro m
      have hm1 : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
      have hm14 : 1 / 4 ≤ ((f + m : ℕ) : ℝ) := by linarith
      have hm1_succ : (1 : ℝ) ≤ (f + m + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m + 1)
      have h_le_χ : chiQuantile c' (f + m : ℕ) ≤ chiQuantile c' (f + m + 1 : ℕ) :=
        (chiQuantile_strictMonoOn hc').monotoneOn hm14
          (show (1 / 4 : ℝ) ≤ (f + m + 1 : ℕ) by linarith)
          (by exact_mod_cast (by omega : f + m ≤ f + m + 1))
      have h_pt_t : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖(bernoulliP2 t : ℂ) * emKernFSecond i c' b ((f + m : ℕ) + t)‖ ≤
            ((1 / 6 : ℝ) * Cφ * (2 / c')) *
              (chiDeriv c' ((f + m : ℕ) + t) * majorantR (siteRadius c' ((f + m : ℕ) + t))) := by
        intro t ht
        have ha1 : (1 : ℝ) ≤ (f + m : ℕ) + t := by linarith [ht.1]
        have hr_pos : 0 < siteRadius c' ((f + m : ℕ) + t) :=
          sub_pos.mpr (xiStar_lt_chiQuantile hc' (by linarith))
        have hP2 := abs_bernoulliP2_le ht.1 ht.2
        have h2 := h_em2_norm _ ha1
        have hmaj := h_majorant (siteRadius c' ((f + m : ℕ) + t)) hr_pos
        rw [show xiStar + siteRadius c' ((f + m : ℕ) + t) = chiQuantile c' ((f + m : ℕ) + t) by
          unfold siteRadius; ring] at hmaj
        have hcd_nn : 0 ≤ chiDeriv c' ((f + m : ℕ) + t) := by
          unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
        rw [norm_mul, Complex.norm_real]
        calc |bernoulliP2 t| * ‖emKernFSecond i c' b ((f + m : ℕ) + t)‖
            ≤ (1 / 12) * (2 * Cφ * chiDeriv c' ((f + m : ℕ) + t) *
                (2 / (c' * rhoU (chiQuantile c' ((f + m : ℕ) + t)))) *
                (Real.exp (-π * abs (chiQuantile c' ((f + m : ℕ) + t) - |b.re|)) *
                  (1 + (siteRadius c' ((f + m : ℕ) + t))⁻¹))) := by gcongr
          _ = ((1 / 6 : ℝ) * Cφ * (2 / c')) * (chiDeriv c' ((f + m : ℕ) + t) *
                (Real.exp (-π * abs (chiQuantile c' ((f + m : ℕ) + t) - |b.re|)) *
                  (1 + (siteRadius c' ((f + m : ℕ) + t))⁻¹) /
                  rhoU (chiQuantile c' ((f + m : ℕ) + t)))) := by ring
          _ ≤ ((1 / 6 : ℝ) * Cφ * (2 / c')) * (chiDeriv c' ((f + m : ℕ) + t) *
                majorantR (siteRadius c' ((f + m : ℕ) + t))) := by gcongr
      have h_int_left : IntervalIntegrable (fun t : ℝ =>
          ‖(bernoulliP2 t : ℂ) * emKernFSecond i c' b ((f + m : ℕ) + t)‖) volume 0 1 :=
        (continuousOn_bernoulli_mul_emKernFSecond hi hc' hf m hb_mid).norm.intervalIntegrable_of_Icc
          zero_le_one
      have h_int_right : IntervalIntegrable (fun t : ℝ =>
          ((1 / 6 : ℝ) * Cφ * (2 / c')) *
            (chiDeriv c' ((f + m : ℕ) + t) * majorantR (siteRadius c' ((f + m : ℕ) + t))))
          volume 0 1 := by
        have h_cont_maj : ContinuousOn (fun t : ℝ => chiDeriv c' ((f + m : ℕ) + t) *
            majorantR (siteRadius c' ((f + m : ℕ) + t))) (Icc 0 1) := by
          intro t ht
          have hm1 : (1 : ℝ) ≤ (f + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + m)
          have ht14 : 1 / 4 < ((f + m : ℕ) : ℝ) + t := by linarith [ht.1]
          have hr_pos : 0 < siteRadius c' (((f + m : ℕ) : ℝ) + t) :=
            sub_pos.mpr (xiStar_lt_chiQuantile hc' ht14)
          have hχ_c := (((hasDerivAt_chiQuantile hc' ht14).1.comp t
            ((hasDerivAt_id t).const_add _)).congr_deriv (by ring)).continuousAt
          have hcd_c := (((hasDerivAt_chiQuantile hc' ht14).2.comp t
            ((hasDerivAt_id t).const_add _)).congr_deriv (by ring)).continuousAt
          have hr_c : ContinuousAt (fun s : ℝ => siteRadius c' (((f + m : ℕ) : ℝ) + s)) t :=
            hχ_c.sub continuousAt_const
          have hrpow_c := hr_c.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hr_pos.ne')
          have hexp_c : ContinuousAt (fun s : ℝ =>
              Real.exp (-π * abs (xiStar + siteRadius c' (((f + m : ℕ) : ℝ) + s) - |b.re|))) t :=
            ContinuousAt.comp
              (f := fun s : ℝ => -π * abs (xiStar + siteRadius c' (((f + m : ℕ) : ℝ) + s) - |b.re|))
              Real.continuous_exp.continuousAt
              (continuousAt_const.mul ((continuousAt_const.add hr_c |>.sub continuousAt_const).abs))
          exact (hcd_c.mul ((continuousAt_const.mul hrpow_c).add (continuousAt_const.mul hexp_c))).continuousWithinAt
        exact (h_cont_maj.intervalIntegrable_of_Icc zero_le_one).const_mul _
      have h_mono := intervalIntegral.integral_mono_on zero_le_one h_int_left h_int_right h_pt_t
      rw [intervalIntegral.integral_const_mul] at h_mono
      have hf_cont : ContinuousOn (fun t : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + t)) [[(0 : ℝ), 1]] := by
        rw [uIcc_of_le zero_le_one]
        intro t ht
        have ht14 : 1 / 4 < ((f + m : ℕ) : ℝ) + t := by linarith [ht.1, hm1]
        exact (ContinuousAt.comp (f := fun s : ℝ => ((f + m : ℕ) : ℝ) + s)
          (hasDerivAt_chiQuantile hc' ht14).1.continuousAt
          (continuousAt_const.add continuousAt_id)).continuousWithinAt
      have hf_deriv : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
          HasDerivAt (fun s : ℝ => chiQuantile c' (((f + m : ℕ) : ℝ) + s))
            (chiDeriv c' (((f + m : ℕ) : ℝ) + t)) t := by
        rw [min_eq_left zero_le_one, max_eq_right zero_le_one]
        intro t ht
        have ht14 : 1 / 4 < ((f + m : ℕ) : ℝ) + t := by linarith [ht.1, hm1]
        have hdc := (hasDerivAt_chiQuantile hc' ht14).1.comp t ((hasDerivAt_id t).const_add _)
        exact hdc.congr_deriv (by ring)
      have hf_nn : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
          0 ≤ chiDeriv c' (((f + m : ℕ) : ℝ) + t) := fun t _ => by
        unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
      have h_cov := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg hf_cont hf_deriv hf_nn
        (g := fun y => majorantR (y - xiStar))
      have hf0 : chiQuantile c' (((f + m : ℕ) : ℝ) + 0) = chiQuantile c' (f + m : ℕ) := by simp
      have hf1 : chiQuantile c' (((f + m : ℕ) : ℝ) + 1) = chiQuantile c' (f + m + 1 : ℕ) := by
        congr 1; push_cast; ring
      rw [hf0, hf1] at h_cov
      dsimp only [Function.comp_apply, smul_eq_mul] at h_cov
      unfold siteRadius at h_mono
      rw [h_cov] at h_mono
      exact h_mono
    have h_sum_majorant : ∀ M : ℕ,
        ((1 / 6 : ℝ) * Cφ * (2 / c')) * ∑ m ∈ Finset.range M,
          ∫ y in (chiQuantile c' (f + m : ℕ))..(chiQuantile c' (f + m + 1 : ℕ)),
            majorantR (y - xiStar) ≤ K_int * lambdaComb c' := by
      intro M
      have hfM1 : (1 : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + M)
      have h_le_χM : chiQuantile c' f ≤ chiQuantile c' (f + M : ℕ) :=
        (chiQuantile_strictMonoOn hc').monotoneOn ha_f
          (show (1 / 4 : ℝ) ≤ (f + M : ℕ) by linarith)
          (by exact_mod_cast (by omega : f ≤ f + M))
      have hr_f_pos : 0 < siteRadius c' f := sub_pos.mpr (xiStar_lt_chiQuantile hc' (by linarith))
      have hr_fM_pos : 0 < siteRadius c' (f + M : ℕ) :=
        sub_pos.mpr (xiStar_lt_chiQuantile hc' (by linarith))
      have hcont_maj_y : ∀ a b_y : ℝ, xiStar < a → a ≤ b_y →
          ContinuousOn (fun y : ℝ => majorantR (y - xiStar)) (Icc a b_y) := by
        intro a b_y ha_lt _ y hy
        have hy_gt : 0 < y - xiStar := by linarith [hy.1]
        have hr_c : ContinuousAt (fun z : ℝ => (z - xiStar) ^ (-(3 / 2 : ℝ))) y :=
          (continuousAt_id.sub continuousAt_const).rpow_const (Or.inl hy_gt.ne')
        have he_c : ContinuousAt (fun z : ℝ => Real.exp (-π * abs (xiStar + (z - xiStar) - |b.re|))) y :=
          ContinuousAt.comp
            (f := fun z : ℝ => -π * abs (xiStar + (z - xiStar) - |b.re|))
            Real.continuous_exp.continuousAt
            (continuousAt_const.mul ((continuousAt_const.add (continuousAt_id.sub continuousAt_const) |>.sub continuousAt_const).abs))
        exact ((continuousAt_const.mul hr_c).add (continuousAt_const.mul he_c)).continuousWithinAt
      have h_adj : ∑ m ∈ Finset.range M,
            ∫ y in (chiQuantile c' (f + m : ℕ))..(chiQuantile c' (f + m + 1 : ℕ)),
              majorantR (y - xiStar) =
          ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)), majorantR (y - xiStar) := by
        clear hfM1 h_le_χM hr_fM_pos
        induction M with
        | zero => simp
        | succ M ih =>
          rw [Finset.sum_range_succ, ih]
          have hm1_a : (1 : ℝ) ≤ (f + M : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + M)
          have hm1_b : (1 : ℝ) ≤ (f + M + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + M + 1)
          have h12 : chiQuantile c' f ≤ chiQuantile c' (f + M : ℕ) :=
            (chiQuantile_strictMonoOn hc').monotoneOn ha_f
              (show (1 / 4 : ℝ) ≤ (f + M : ℕ) by linarith)
              (by exact_mod_cast (by omega : f ≤ f + M))
          have h23 : chiQuantile c' (f + M : ℕ) ≤ chiQuantile c' (f + M + 1 : ℕ) :=
            (chiQuantile_strictMonoOn hc').monotoneOn
              (show (1 / 4 : ℝ) ≤ (f + M : ℕ) by linarith)
              (show (1 / 4 : ℝ) ≤ (f + M + 1 : ℕ) by linarith)
              (by exact_mod_cast (by omega : f + M ≤ f + M + 1))
          have hgt1 : xiStar < chiQuantile c' f := xiStar_lt_chiQuantile hc' (by linarith)
          have hgt2 : xiStar < chiQuantile c' (f + M : ℕ) := xiStar_lt_chiQuantile hc' (by linarith)
          have h_add := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
            ((hcont_maj_y _ _ hgt1 h12).intervalIntegrable_of_Icc h12)
            ((hcont_maj_y _ _ hgt2 h23).intervalIntegrable_of_Icc h23)
          have heq : f + M + 1 = f + (M + 1) := by omega
          rw [h_add, heq]
      have hχf_gt : xiStar < chiQuantile c' f := xiStar_lt_chiQuantile hc' (by linarith)
      have hint_pow : IntervalIntegrable (fun y : ℝ =>
          (2 / (3 * kTip)) * (y - xiStar) ^ (-(3 / 2 : ℝ))) volume
          (chiQuantile c' f) (chiQuantile c' (f + M : ℕ)) := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le h_le_χM]
        refine ContinuousOn.integrableOn_Icc ?_
        intro y hy
        have hy_gt : 0 < y - xiStar := by linarith [hy.1, hχf_gt]
        exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).rpow_const
          (Or.inl hy_gt.ne'))).continuousWithinAt
      have hint_exp_y : IntervalIntegrable (fun y : ℝ =>
          (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + (y - xiStar) - |b.re|))) volume
          (chiQuantile c' f) (chiQuantile c' (f + M : ℕ)) :=
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.add
          (continuous_id.sub continuous_const) |>.sub continuous_const).abs)))).intervalIntegrable _ _
      have h_pow_ftc : ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
            (2 / (3 * kTip)) * (y - xiStar) ^ (-(3 / 2 : ℝ)) ≤
          (4 / (3 * kTip)) * (c₀ * lambdaComb c') ^ (-(1 / 2 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
        have h_ftc : ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
              (y - xiStar) ^ (-(3 / 2 : ℝ)) =
            (-2 * (chiQuantile c' (f + M : ℕ) - xiStar) ^ (-(1 / 2 : ℝ))) -
              (-2 * (chiQuantile c' f - xiStar) ^ (-(1 / 2 : ℝ))) := by
          refine intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun y : ℝ => -2 * (y - xiStar) ^ (-(1 / 2 : ℝ))) ?_ ?_
          · intro y hy
            rw [uIcc_of_le h_le_χM] at hy
            have hy_gt : 0 < y - xiStar := by linarith [hy.1, hχf_gt]
            have hd := ((hasDerivAt_id y).sub_const xiStar).rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hy_gt.ne')
            have hd2 := hd.const_mul (-2 : ℝ)
            exact hd2.congr_deriv (by
              dsimp only [id_eq]
              rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]
              ring)
          · rw [intervalIntegrable_iff_integrableOn_Icc_of_le h_le_χM]
            refine ContinuousOn.integrableOn_Icc ?_
            intro y hy
            have hy_gt : 0 < y - xiStar := by linarith [hy.1, hχf_gt]
            exact ((continuousAt_id.sub continuousAt_const).rpow_const
              (Or.inl hy_gt.ne')).continuousWithinAt
        change (2 / (3 * kTip)) * ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
            (y - xiStar) ^ (-(3 / 2 : ℝ)) ≤ _
        rw [h_ftc]
        change (2 / (3 * kTip)) * ((-2 * (siteRadius c' (f + M : ℕ)) ^ (-(1 / 2 : ℝ))) -
            (-2 * (siteRadius c' f) ^ (-(1 / 2 : ℝ)))) ≤ _
        have hr_f_ge : c₀ * lambdaComb c' ≤ siteRadius c' f := by
          refine hr1_ge.trans ?_
          unfold siteRadius
          have h1_le := (chiQuantile_strictMonoOn hc').monotoneOn (by norm_num) ha_f ha_f1
          linarith
        have hc0lam_pos : 0 < c₀ * lambdaComb c' := mul_pos hc₀ hlam_pos
        have hr_pow_le : siteRadius c' f ^ (-(1 / 2 : ℝ)) ≤ (c₀ * lambdaComb c') ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hc0lam_pos hr_f_ge (by norm_num)
        have hpos_fM : 0 ≤ (siteRadius c' (f + M : ℕ)) ^ (-(1 / 2 : ℝ)) := by positivity
        calc (2 / (3 * kTip)) * ((-2 * (siteRadius c' (f + M : ℕ)) ^ (-(1 / 2 : ℝ))) -
              (-2 * (siteRadius c' f) ^ (-(1 / 2 : ℝ))))
            ≤ (2 / (3 * kTip)) * (2 * (siteRadius c' f) ^ (-(1 / 2 : ℝ))) := by gcongr; linarith
          _ ≤ (2 / (3 * kTip)) * (2 * (c₀ * lambdaComb c') ^ (-(1 / 2 : ℝ))) := by gcongr
          _ = (4 / (3 * kTip)) * (c₀ * lambdaComb c') ^ (-(1 / 2 : ℝ)) := by ring
      have h_exp_tot : ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
            (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + (y - xiStar) - |b.re|)) ≤ 3 / π := by
        have heq_e : (fun y : ℝ => (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + (y - xiStar) - |b.re|))) =
            fun y : ℝ => (3 / 2 : ℝ) * Real.exp (-π * abs (y - |b.re|)) := by
          ext y; ring_nf
        rw [heq_e, intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le h_le_χM]
        have hint_exp : Integrable (fun y : ℝ => Real.exp (-π * abs (y - |b.re|))) volume :=
          integrable_exp_neg_pi_abs.comp_sub_right |b.re|
        have hset : ∫ y in Ioc (chiQuantile c' f) (chiQuantile c' (f + M : ℕ)),
              Real.exp (-π * abs (y - |b.re|)) ≤ 2 / π := by
          calc ∫ y in Ioc (chiQuantile c' f) (chiQuantile c' (f + M : ℕ)),
                Real.exp (-π * abs (y - |b.re|))
              ≤ ∫ y : ℝ, Real.exp (-π * abs (y - |b.re|)) :=
                setIntegral_le_integral hint_exp (Eventually.of_forall fun _ => (Real.exp_pos _).le)
            _ = 2 / π := by
                rw [integral_sub_right_eq_self (fun u : ℝ => Real.exp (-π * |u|)) |b.re|,
                  integral_exp_neg_pi_abs]
        calc (3 / 2 : ℝ) * ∫ y in Ioc (chiQuantile c' f) (chiQuantile c' (f + M : ℕ)),
              Real.exp (-π * abs (y - |b.re|))
            ≤ (3 / 2 : ℝ) * (2 / π) := by gcongr
          _ = 3 / π := by ring
      have h_maj_split : ∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)), majorantR (y - xiStar) =
          (∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
              (2 / (3 * kTip)) * (y - xiStar) ^ (-(3 / 2 : ℝ))) +
            (∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
              (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + (y - xiStar) - |b.re|))) :=
        intervalIntegral.integral_add hint_pow hint_exp_y
      have hc₀lam_split : (c₀ * lambdaComb c') ^ (-(1 / 2 : ℝ)) =
          c₀ ^ (-(1 / 2 : ℝ)) * lambdaComb c' ^ (-(1 / 2 : ℝ)) :=
        Real.mul_rpow hc₀.le hlam_pos.le
      rw [h_adj, h_maj_split]
      calc ((1 / 6 : ℝ) * Cφ * (2 / c')) *
            ((∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
                (2 / (3 * kTip)) * (y - xiStar) ^ (-(3 / 2 : ℝ))) +
              (∫ y in (chiQuantile c' f)..(chiQuantile c' (f + M : ℕ)),
                (3 / 2 : ℝ) * Real.exp (-π * abs (xiStar + (y - xiStar) - |b.re|))))
          ≤ ((1 / 6 : ℝ) * Cφ * (2 / c')) *
              ((4 / (3 * kTip)) * (c₀ * lambdaComb c') ^ (-(1 / 2 : ℝ)) + 3 / π) := by
            gcongr
        _ = (1 / 6 : ℝ) * Cφ * ((8 / (3 * kTip)) * c₀ ^ (-(1 / 2 : ℝ)) *
              ((c' : ℝ)⁻¹ * lambdaComb c' ^ (-(1 / 2 : ℝ))) + (6 / π) * (c' : ℝ)⁻¹) := by
            rw [hc₀lam_split]; ring
        _ ≤ (1 / 6 : ℝ) * Cφ * ((8 / (3 * kTip)) * c₀ ^ (-(1 / 2 : ℝ)) * (kTip * lambdaComb c') +
              (6 / π) * (kTip * lambdaComb c')) := by
            rw [h_inv_c'_lam]; gcongr
        _ = K_int * lambdaComb c' := by
            dsimp [K_int]; field_simp [hk_pos.ne']
    let I_cell : ℕ → ℂ := fun m =>
      ∫ t in (0 : ℝ)..1, (bernoulliP2 t : ℂ) * emKernFSecond i c' b ((f + m : ℕ) + t)
    have h_cell_bd : ∀ m : ℕ, ‖I_cell m‖ ≤ ((1 / 6 : ℝ) * Cφ * (2 / c')) *
        ∫ y in (chiQuantile c' (f + m : ℕ))..(chiQuantile c' (f + m + 1 : ℕ)),
          majorantR (y - xiStar) := fun m =>
      (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans (h_cell_em m)
    have h_partial_em : ∀ M : ℕ, ∑ m ∈ Finset.range M, ‖I_cell m‖ ≤ K_int * lambdaComb c' := by
      intro M
      calc ∑ m ∈ Finset.range M, ‖I_cell m‖
          ≤ ∑ m ∈ Finset.range M, ((1 / 6 : ℝ) * Cφ * (2 / c')) *
              ∫ y in (chiQuantile c' (f + m : ℕ))..(chiQuantile c' (f + m + 1 : ℕ)),
                majorantR (y - xiStar) := Finset.sum_le_sum fun m _ => h_cell_bd m
        _ = ((1 / 6 : ℝ) * Cφ * (2 / c')) * ∑ m ∈ Finset.range M,
              ∫ y in (chiQuantile c' (f + m : ℕ))..(chiQuantile c' (f + m + 1 : ℕ)),
                majorantR (y - xiStar) := (Finset.mul_sum _ _ _).symm
        _ ≤ K_int * lambdaComb c' := h_sum_majorant M
    have h_sum_norm : Summable (fun m : ℕ => ‖I_cell m‖) :=
      summable_of_sum_range_le (fun _ => norm_nonneg _) h_partial_em
    have h_rem2_bd : ‖emRem2Deriv i c' f b‖ ≤ K_int * lambdaComb c' := by
      have hem2_eq : emRem2Deriv i c' f b = -∑' m : ℕ, I_cell m := rfl
      rw [hem2_eq, norm_neg]
      exact (norm_tsum_le_tsum_norm h_sum_norm).trans
        (h_sum_norm.tsum_le_of_sum_le fun s => by
          obtain ⟨M, hMs⟩ := Finset.exists_nat_subset_range s
          exact (Finset.sum_le_sum_of_subset_of_nonneg hMs fun _ _ _ => norm_nonneg _).trans
            (h_partial_em M))
    have hem_def : emRemDeriv i c' f b = -(1 / 12 : ℂ) * emKernFDeriv i c' b f + emRem2Deriv i c' f b := rfl
    rw [hem_def]
    calc ‖-(1 / 12 : ℂ) * emKernFDeriv i c' b f + emRem2Deriv i c' f b‖
        ≤ ‖-(1 / 12 : ℂ) * emKernFDeriv i c' b f‖ + ‖emRem2Deriv i c' f b‖ := norm_add_le _ _
      _ ≤ (1 / 6) * Cφ * Cgap * lambdaComb c' + K_int * lambdaComb c' := add_le_add h_fderiv_bd h_rem2_bd
      _ = ((1 / 6 : ℝ) * Cφ * Cgap + K_int) * lambdaComb c' := by ring
  refine h_em_bd.trans ?_
  have h1 : (1 / 6 : ℝ) * Cφ ≤ K_em := le_max_left _ _
  have h2 : K_int ≤ K_em := le_max_right _ _
  have hsum : (1 / 6 : ℝ) * Cφ * Cgap + K_int ≤ K_em * (Cgap + 1) := by
    nlinarith
  exact mul_le_mul_of_nonneg_right hsum hlam_pos.le

/-- **K3 derivative and remainder bounds** (`cmb:K3`):
There exists an absolute constant $C > 0$ such that for all sufficiently large $c'$, every integer $f \ge 1$,
every $\eta_0 \in [0, 1/4]$, every $i \in \{0, 1, 2\}$, and every $b \in \mathcal N$:
1. $\|\partial_b^i \Delta_{\mathrm{det}}^{(f)}(b)\| + \|\partial_b^i R_{\mathrm{EM}}^{(f)}(b)\| \le C\lambda$,
2. $\|\partial_b^i \Phi_1^{(f)}(b)\| \le C n_1$,
3. $\|\partial_b^i (\bar\varphi^{(f)}(b) - \varphi_{\xi_*}(b))\| \le C n_1^{2/3} \lambda$. -/
theorem edgePhase_bounds :
    ∃ C > 0, ∀ᶠ c' in atTop, ∀ (f : ℕ) (_hf : 1 ≤ f) {η₀ : ℝ}, 0 ≤ η₀ → η₀ ≤ 1 / 4 →
      ∀ (i : ℕ), i ≤ 2 → ∀ {b : ℂ}, b ∈ combN →
        (‖iteratedDeriv i (deltaDetComb c' f η₀) b‖ + ‖iteratedDeriv i (emRem c' f) b‖ ≤
            C * lambdaComb c') ∧
        ‖iteratedDeriv i (phi1Comb c' f η₀) b‖ ≤ C * n1Comb f ∧
        ‖iteratedDeriv i (fun w => barPhi c' f w - phiZeta (xiStar : ℂ) w) b‖ ≤
            C * n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c' := by
  obtain ⟨Cφ, hCφ, _, hφ_min⟩ := combPhiDeriv_bound
  obtain ⟨Cdiff, hCdiff, hφ_sub⟩ := combPhiDeriv_sub_xiStar_le
  obtain ⟨K_det0, hK_det0, h_det_lem⟩ := deltaDetCombDeriv_bound
  obtain ⟨K_em0, hK_em0, h_em_lem⟩ := emRemDeriv_bound
  obtain ⟨Cgap, hCgap, hgap_ev⟩ := siteGap_eventually_le
  have hpi := Real.pi_pos
  have h_r1_ev : ∀ᶠ c' in atTop, lambdaComb c' * phiQuantile 1 ≤ 1 := by
    have ht := tendsto_lambdaComb_atTop.mul_const (phiQuantile 1)
    simp only [zero_mul] at ht
    exact ht.eventually_le_const zero_lt_one
  have h_lam1_ev : ∀ᶠ c' in atTop, lambdaComb c' ≤ 1 :=
    tendsto_lambdaComb_atTop.eventually_le_const zero_lt_one
  set K_det := K_det0 * Cgap
  set K_em := K_em0 * (Cgap + 1)
  set K₁ := K_det + K_em
  set K_bar := Cdiff
  set K_tot := max K₁ (max K_bar ((4 / 3 : ℝ) * (π + K₁) + 2 * Cφ))
  refine ⟨K_tot, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 0, hgap_ev, h_r1_ev, h_lam1_ev] with
      c' hc' ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_1⟩ hr1_bd hlam1
      f hf η₀ hη₀0 hη₀1 i hi b hb
  have hb_mid : b ∈ combNMid := combN_subset_combNMid hb
  have ha_f1 : (1 : ℝ) ≤ (f : ℕ) := by exact_mod_cast hf
  have ha_f : (1 / 4 : ℝ) ≤ (f : ℕ) := by linarith
  have hn1_pos : 0 < n1Comb f := by unfold n1Comb; linarith
  have hlam_pos : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  obtain ⟨hi_bar, hi_det, hi_em, hi_phi1⟩ :=
    iteratedDeriv_comb_eq hi hc' f hf hη₀0 hη₀1 hgap_1 hgap_k hb_mid
  have h_det_bd : ‖deltaDetCombDeriv i c' f η₀ b‖ ≤ K_det * lambdaComb c' :=
    h_det_lem hc' hCgap hgap_k hgap_1_bd hcd1_bd hgap_1 f hf hη₀0 hη₀1 i hi hb_mid
  have h_em_bd : ‖emRemDeriv i c' f b‖ ≤ K_em * lambdaComb c' :=
    h_em_lem hc' hCgap hcd1_bd hr1_bd hlam1 f hf i hi hb_mid
  have hspec_f := chiQuantile_spec hc' ha_f
  have h_le_f : xiStar ≤ chiQuantile c' f := hspec_f.1
  have h_cum_f : c' * ∫ y in xiStar..(chiQuantile c' f), rhoU y = 2 * n1Comb f := by
    have hs := hspec_f.2
    unfold cumulN at hs
    unfold n1Comb
    linarith
  have h2 : ‖iteratedDeriv i (phi1Comb c' f η₀) b‖ ≤ K_tot * n1Comb f := by
    rw [hi_phi1]
    have hbar_bd : ‖barPhiDeriv i c' f b‖ ≤ Cφ := by
      have h_le1 := intervalIntegral.norm_integral_le_integral_norm
        (f := fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b) (μ := volume) h_le_f
      have h_pt : ∀ y ∈ Icc xiStar (chiQuantile c' f),
          ‖(rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b‖ ≤ Cφ * rhoU y := fun y hy => by
        have hζ : (y : ℂ) ∈ combZ := ofReal_mem_combZ (xiStar_pos.le.trans hy.1)
        have hb0 := (hφ_min i 0 (by omega) hb_mid hζ).trans
          (mul_le_mul_of_nonneg_left (min_le_left _ _) hCφ.le)
        rw [mul_one] at hb0
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoU_nonneg y)]
        calc rhoU y * ‖combPhiDeriv i 0 (y : ℂ) b‖
            ≤ rhoU y * Cφ := mul_le_mul_of_nonneg_left hb0 (rhoU_nonneg y)
          _ = Cφ * rhoU y := mul_comm _ _
      have h_intL : IntervalIntegrable (fun y : ℝ =>
          ‖(rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b‖) volume xiStar (chiQuantile c' f) := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le h_le_f]
        refine ContinuousOn.integrableOn_Icc (ContinuousOn.norm ?_)
        intro y hy
        have hρ : ContinuousWithinAt (fun z : ℝ => (rhoU z : ℂ)) (Icc xiStar (chiQuantile c' f)) y :=
          Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
            ((continuousOn_rhoU.mono Icc_subset_Ici_self) y hy)
        have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith [xiStar_pos, hy.1])
        have hφ : ContinuousAt (fun t : ℝ => combPhiDeriv i 0 (t : ℂ) b) y :=
          ((hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0)
            (combNMid_subset_combNOpen hb_mid) hζ).comp_ofReal).continuousAt
        exact hρ.mul hφ.continuousWithinAt
      have h_intR : IntervalIntegrable (fun y : ℝ => Cφ * rhoU y) volume xiStar (chiQuantile c' f) :=
        (intervalIntegrable_rhoU le_rfl h_le_f).const_mul Cφ
      have hm := intervalIntegral.integral_mono_on h_le_f h_intL h_intR h_pt
      rw [intervalIntegral.integral_const_mul] at hm
      have h_norm_int := h_le1.trans hm
      have h_eq : barPhiDeriv i c' f b = ((1 / (2 * n1Comb f) : ℝ) : ℂ) * (c' : ℂ) *
          ∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b := rfl
      rw [h_eq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hc'.le]
      calc (1 / (2 * n1Comb f)) * c' *
            ‖∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b‖
          ≤ (1 / (2 * n1Comb f)) * c' * (Cφ * ∫ y in xiStar..(chiQuantile c' f), rhoU y) := by gcongr
        _ = (1 / (2 * n1Comb f)) * Cφ * (c' * ∫ y in xiStar..(chiQuantile c' f), rhoU y) := by ring
        _ = (1 / (2 * n1Comb f)) * Cφ * (2 * n1Comb f) := by rw [h_cum_f]
        _ = Cφ := by field_simp [hn1_pos.ne']
    have hphi_eq : phi1CombDeriv i c' f η₀ b =
        (if i = 0 then (π : ℂ) * Complex.I else 0) - ((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b +
          deltaDetCombDeriv i c' f η₀ b + emRemDeriv i c' f b := rfl
    rw [hphi_eq]
    have h_if_bd : ‖if i = 0 then (π : ℂ) * Complex.I else 0‖ ≤ π := by
      split_ifs <;> simp [Real.pi_pos.le]
    have hn1_34 : (3 / 4 : ℝ) ≤ n1Comb f := by unfold n1Comb; linarith
    have h1_le_n1 : (1 : ℝ) ≤ (4 / 3 : ℝ) * n1Comb f := by linarith
    have hlam_le_n1 : lambdaComb c' ≤ (4 / 3 : ℝ) * n1Comb f := hlam1.trans h1_le_n1
    have hle_tot : (4 / 3 : ℝ) * (π + K₁) + 2 * Cφ ≤ K_tot :=
      (le_max_right K_bar _).trans (le_max_right K₁ _)
    calc ‖(if i = 0 then (π : ℂ) * Complex.I else 0) -
            ((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b +
            deltaDetCombDeriv i c' f η₀ b + emRemDeriv i c' f b‖
        ≤ ‖(if i = 0 then (π : ℂ) * Complex.I else 0) -
              ((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b‖ +
            ‖deltaDetCombDeriv i c' f η₀ b‖ + ‖emRemDeriv i c' f b‖ := by
          have t1 := norm_add_le ((if i = 0 then (π : ℂ) * Complex.I else 0) -
            ((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b + deltaDetCombDeriv i c' f η₀ b)
            (emRemDeriv i c' f b)
          have t2 := norm_add_le ((if i = 0 then (π : ℂ) * Complex.I else 0) -
            ((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b) (deltaDetCombDeriv i c' f η₀ b)
          linarith
      _ ≤ (‖if i = 0 then (π : ℂ) * Complex.I else 0‖ +
              ‖((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b‖) +
            (‖deltaDetCombDeriv i c' f η₀ b‖ + ‖emRemDeriv i c' f b‖) := by
          have t3 := norm_sub_le (if i = 0 then (π : ℂ) * Complex.I else 0)
            (((2 * n1Comb f : ℝ) : ℂ) * barPhiDeriv i c' f b)
          linarith
      _ ≤ (π + 2 * n1Comb f * Cφ) + K₁ * lambdaComb c' := by
          gcongr
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left hbar_bd (by positivity)
          · calc ‖deltaDetCombDeriv i c' f η₀ b‖ + ‖emRemDeriv i c' f b‖
                ≤ K_det * lambdaComb c' + K_em * lambdaComb c' := add_le_add h_det_bd h_em_bd
              _ = K₁ * lambdaComb c' := by dsimp [K₁]; ring
      _ ≤ (π * ((4 / 3 : ℝ) * n1Comb f) + 2 * n1Comb f * Cφ) + K₁ * ((4 / 3 : ℝ) * n1Comb f) :=
          add_le_add (add_le_add (le_mul_of_one_le_right hpi.le h1_le_n1) le_rfl)
            (mul_le_mul_of_nonneg_left hlam_le_n1 (by positivity))
      _ = ((4 / 3 : ℝ) * (π + K₁) + 2 * Cφ) * n1Comb f := by ring
      _ ≤ K_tot * n1Comb f := mul_le_mul_of_nonneg_right hle_tot hn1_pos.le
  have h3 : ‖iteratedDeriv i (fun w => barPhi c' f w - phiZeta (xiStar : ℂ) w) b‖ ≤
      K_tot * n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c' := by
    have hdiff_bar : ContDiffAt ℂ i (barPhi c' f) b := by
      have h_on : DifferentiableOn ℂ (barPhi c' f) combNMid := fun w hw =>
        (hasDerivAt_barPhiDeriv (i := 0) (by omega) hc' f hf hw).differentiableAt.differentiableWithinAt
      exact (h_on.analyticAt (isOpen_combNMid.mem_nhds hb_mid)).contDiffAt.of_le le_top
    have hζ_xi : (xiStar : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith [xiStar_pos])
    have hdiff_xi : ContDiffAt ℂ i (fun w => phiZeta (xiStar : ℂ) w) b := by
      have h_on : DifferentiableOn ℂ (fun w => phiZeta (xiStar : ℂ) w) combNOpen := fun w hw =>
        (hasDerivAt_phiZeta_b hw hζ_xi).differentiableAt.differentiableWithinAt
      exact (h_on.analyticAt (isOpen_combNOpen.mem_nhds (combNMid_subset_combNOpen hb_mid))).contDiffAt.of_le le_top
    have h_it_xi : iteratedDeriv i (fun w => phiZeta (xiStar : ℂ) w) b =
        combPhiDeriv i 0 (xiStar : ℂ) b := by
      have heq : (fun w => phiZeta (xiStar : ℂ) w) = fun w => combPhiDeriv 0 0 (xiStar : ℂ) w := by
        ext w; exact (combPhiDeriv_zero _ _).symm
      rw [heq]
      exact iteratedDeriv_combPhiDeriv_b i 0 (combNMid_subset_combNOpen hb_mid) hζ_xi
    have hsub_eq : iteratedDeriv i (fun w => barPhi c' f w - phiZeta (xiStar : ℂ) w) b =
        barPhiDeriv i c' f b - combPhiDeriv i 0 (xiStar : ℂ) b := by
      change iteratedDeriv i (barPhi c' f - fun w => phiZeta (xiStar : ℂ) w) b = _
      rw [iteratedDeriv_sub hdiff_bar hdiff_xi, hi_bar, h_it_xi]
    rw [hsub_eq]
    have h_int_rho : IntervalIntegrable (fun y : ℝ => (rhoU y : ℂ)) volume xiStar (chiQuantile c' f) :=
      ContinuousOn.intervalIntegrable_of_Icc h_le_f
        (Complex.continuous_ofReal.comp_continuousOn (continuousOn_rhoU.mono Icc_subset_Ici_self))
    have h_int_phi : IntervalIntegrable (fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b)
        volume xiStar (chiQuantile c' f) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le h_le_f]
      refine ContinuousOn.integrableOn_Icc ?_
      intro y hy
      have hρ : ContinuousWithinAt (fun z : ℝ => (rhoU z : ℂ)) (Icc xiStar (chiQuantile c' f)) y :=
        Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
          ((continuousOn_rhoU.mono Icc_subset_Ici_self) y hy)
      have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen (by linarith [xiStar_pos, hy.1])
      have hφ : ContinuousAt (fun t : ℝ => combPhiDeriv i 0 (t : ℂ) b) y :=
        ((hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0)
          (combNMid_subset_combNOpen hb_mid) hζ).comp_ofReal).continuousAt
      exact hρ.mul hφ.continuousWithinAt
    have h_norm_int_rho : ∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) =
        ((∫ y in xiStar..(chiQuantile c' f), rhoU y : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    have h_xi_term : combPhiDeriv i 0 (xiStar : ℂ) b =
        ((1 / (2 * n1Comb f) : ℝ) : ℂ) * (c' : ℂ) *
          ∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * combPhiDeriv i 0 (xiStar : ℂ) b := by
      rw [intervalIntegral.integral_mul_const, h_norm_int_rho]
      have hc1 : (((1 / (2 * n1Comb f) : ℝ) : ℂ) * (c' : ℂ) *
          ((∫ y in xiStar..(chiQuantile c' f), rhoU y : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
          show (1 / (2 * n1Comb f)) * c' * ∫ y in xiStar..(chiQuantile c' f), rhoU y =
            (1 / (2 * n1Comb f)) * (c' * ∫ y in xiStar..(chiQuantile c' f), rhoU y) by ring,
          h_cum_f]
        norm_cast; field_simp [hn1_pos.ne']
      rw [← mul_assoc, hc1, one_mul]
    have h_diff_int : barPhiDeriv i c' f b - combPhiDeriv i 0 (xiStar : ℂ) b =
        ((1 / (2 * n1Comb f) : ℝ) : ℂ) * (c' : ℂ) *
          ∫ y in xiStar..(chiQuantile c' f),
            (rhoU y : ℂ) * (combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (xiStar : ℂ) b) := by
      have hbar_def : barPhiDeriv i c' f b = (((1 / (2 * n1Comb f) : ℝ) : ℂ) * (c' : ℂ)) *
          ∫ y in xiStar..(chiQuantile c' f), (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b := rfl
      conv_lhs => rw [hbar_def, h_xi_term]
      rw [← mul_sub,
        ← intervalIntegral.integral_sub h_int_phi (h_int_rho.mul_const (combPhiDeriv i 0 (xiStar : ℂ) b))]
      congr 1; apply intervalIntegral.integral_congr; intro y _; exact (mul_sub _ _ _).symm
    have h_rad : siteRadius c' f ≤ lambdaComb c' * n1Comb f ^ (2 / 3 : ℝ) := by
      simpa [phiQuantile, n1Comb] using (siteRadius_bounds hc' ha_f).2
    have h_pt_diff : ∀ y ∈ Icc xiStar (chiQuantile c' f),
        ‖(rhoU y : ℂ) * (combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (xiStar : ℂ) b)‖ ≤
          Cdiff * (n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c') * rhoU y := fun y hy => by
      have hsub := hφ_sub i hi hy.1 hb_mid
      have hy_rad : y - xiStar ≤ siteRadius c' f := by unfold siteRadius; linarith [hy.2]
      have hy_le : y - xiStar ≤ n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c' :=
        hy_rad.trans (h_rad.trans_eq (mul_comm _ _))
      have hρ_nn : 0 ≤ rhoU y := rhoU_nonneg y
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn]
      calc rhoU y * ‖combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (xiStar : ℂ) b‖
          ≤ rhoU y * (Cdiff * (y - xiStar)) := by gcongr
        _ ≤ rhoU y * (Cdiff * (n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c')) := by gcongr
        _ = Cdiff * (n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c') * rhoU y := by ring
    have h_intL_d : IntervalIntegrable (fun y : ℝ =>
        ‖(rhoU y : ℂ) * (combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (xiStar : ℂ) b)‖)
        volume xiStar (chiQuantile c' f) :=
      (h_int_phi.sub (h_int_rho.mul_const (combPhiDeriv i 0 (xiStar : ℂ) b))).norm.congr
        fun y _ => by simp [mul_sub]
    have h_intR_d : IntervalIntegrable (fun y : ℝ =>
        Cdiff * (n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c') * rhoU y) volume xiStar (chiQuantile c' f) :=
      (intervalIntegrable_rhoU le_rfl h_le_f).const_mul _
    have hm_d := intervalIntegral.integral_mono_on h_le_f h_intL_d h_intR_d h_pt_diff
    rw [intervalIntegral.integral_const_mul] at hm_d
    have h_norm_d := (intervalIntegral.norm_integral_le_integral_norm h_le_f).trans hm_d
    have hKbar_le : Cdiff ≤ K_tot := (le_max_left _ _).trans (le_max_right _ _)
    rw [h_diff_int, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hc'.le]
    calc (1 / (2 * n1Comb f)) * c' *
          ‖∫ y in xiStar..(chiQuantile c' f),
              (rhoU y : ℂ) * (combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (xiStar : ℂ) b)‖
        ≤ (1 / (2 * n1Comb f)) * c' *
            (Cdiff * (n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c') *
              ∫ y in xiStar..(chiQuantile c' f), rhoU y) := by gcongr
      _ = (1 / (2 * n1Comb f)) * (Cdiff * (n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c')) *
            (c' * ∫ y in xiStar..(chiQuantile c' f), rhoU y) := by ring
      _ = (1 / (2 * n1Comb f)) * (Cdiff * (n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c')) * (2 * n1Comb f) := by
          rw [h_cum_f]
      _ = Cdiff * n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c' := by field_simp [hn1_pos.ne']
      _ ≤ K_tot * n1Comb f ^ (2 / 3 : ℝ) * lambdaComb c' := by gcongr
  have h1 : ‖iteratedDeriv i (deltaDetComb c' f η₀) b‖ + ‖iteratedDeriv i (emRem c' f) b‖ ≤
      K_tot * lambdaComb c' := by
    rw [hi_det, hi_em]
    calc ‖deltaDetCombDeriv i c' f η₀ b‖ + ‖emRemDeriv i c' f b‖
        ≤ K_det * lambdaComb c' + K_em * lambdaComb c' := add_le_add h_det_bd h_em_bd
      _ = K₁ * lambdaComb c' := by dsimp [K₁]; ring
      _ ≤ K_tot * lambdaComb c' := mul_le_mul_of_nonneg_right (le_max_left _ _) hlam_pos.le
  exact ⟨h1, h2, h3⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.cexp_logRefComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.cexp_logRefComb

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.logRefComb_eq_comb_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.logRefComb_eq_comb_decomp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.re_phi1Comb_eq_zero_of_im_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.re_phi1Comb_eq_zero_of_im_half

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.edgePhase_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.edgePhase_bounds

end FormalResearch.ModularBootstrap.Upper.Comb
