module

public import FormalResearch.CohnElkies.MellinMainKernel
public import FormalResearch.CohnElkies.AirySeedFloors
public import FormalResearch.Analysis.VanDerCorput

/-!
# Reflected-Line Symbol Bounds (`O.2`), Dual-Phase Estimate (`O.3(1)`), and `GT.2b(3)` / `GT.3a`

Formalization of `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, `u1c_estimate_proofs.tex`, and
`ce_o1_global_transfer.tex` (`origin/main`):

* **Section 1 — Lemma `O.2` (`u1co:O2`, `(e29)`):**
  `o2_reflected_line_contDiff`, `o2_reflected_line_deriv_bound`, `o2_imag_weighted_deriv_bound`.
* **Section 2 — Binomial expansion of `bsplineMult`:**
  `bsplineMult_binomial_eq`.
* **Section 3 — Lemma `O.3(1)` core phase bound (`(u1co:dual-phase)`):**
  `dual_phase_oscillatory_bound` (`|∫ a(τ) e^{i c Φ(τ; L)} dτ| ≤ C A c^{-1/2} min(L^{-1/4}, L^{-3/2})`
  for `c ≥ 2`, `L > 0`, `c L^{3/2} ≥ 1`), proved unconditionally by interval splitting at
  `±τ₀/2, ±2τ₀` (and `±exp(L/2)` for `L > 8`), twice integration by parts on `[-exp(L/2), exp(L/2)]`,
  and `van_der_corput_first` / `van_der_corput_second`.
* **Section 4 — Lemma `O.3(1)` `(e3)`, Lemma `GT.2b(3)`, and `(cegt:GT3a)`:**
  `dualEdgeIntegral`, `gt2b_dual_integral_general`, `gt2b_dual_integral_fixed`,
  `gt2b_dual_integral_reflected`, and `o3_dual_bound`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators Interval

namespace FormalResearch.CohnElkies

open FormalResearch.Analysis
open FormalResearch.Asymptotics
open FormalResearch.Special

/-! ## Section 0: Shared holomorphic Cauchy and Leibniz helpers -/

private lemma holomorphic_real_contDiff_and_cauchy {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hR : ∀ t : ℝ, (t : ℂ) ∈ U) {r : ℝ} (hr : 0 < r)
    (hball : ∀ τ : ℝ, Metric.closedBall (τ : ℂ) r ⊆ U)
    {B : ℝ → ℝ} (hB : ∀ τ : ℝ, ∀ ω ∈ Metric.sphere (τ : ℂ) r, ‖F ω‖ ≤ B τ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) ∧
      ∀ (j : ℕ) (τ : ℝ), ‖iteratedDeriv j (fun t : ℝ => F (t : ℂ)) τ‖ ≤ j.factorial * B τ / r ^ j := by
  have hC_on : ContDiffOn ℂ (⊤ : ℕ∞) F U := (hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) := contDiff_iff_contDiffAt.mpr fun t =>
    ((hC_on.contDiffAt (hU.mem_nhds (hR t))).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  have hiter : ∀ (j : ℕ) (t : ℝ), iteratedDeriv j (fun s : ℝ => F (s : ℂ)) t = iteratedDeriv j F (t : ℂ) := by
    intro j; induction j with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun s : ℝ => F (s : ℂ)) = fun s : ℝ => iteratedDeriv k F (s : ℂ) from funext ih,
        iteratedDeriv_succ]
      have hwk := hC_on.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast WithTop.coe_lt_top k) hU.uniqueDiffOn
      exact (((hwk _ (hR t)).differentiableAt (hU.mem_nhds (hR t))).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hU.mem_nhds (hR t)) fun z hz => (iteratedDerivWithin_of_isOpen hU hz).symm) |>.hasDerivAt.comp_ofReal).deriv
  refine ⟨hC, fun j τ => ?_⟩; rw [hiter j τ]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    ⟨hF.mono (Metric.ball_subset_closedBall.trans (hball τ)),
      (hF.continuousOn.mono (hball τ)).mono Metric.closure_ball_subset_closedBall⟩ (hB τ)

private lemma reflected_line_diffOn {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re}) {α : ℝ} (hα : 0 < α) :
    IsOpen {ω : ℂ | -1 < ω.im} ∧ DifferentiableOn ℂ (fun ω => F ((α : ℂ) * (1 - Complex.I * ω))) {ω : ℂ | -1 < ω.im} ∧
      (∀ ω ∈ {ω : ℂ | -1 < ω.im}, 0 < ((α : ℂ) * (1 - Complex.I * ω)).re) ∧
      (∀ t : ℝ, Metric.closedBall (t : ℂ) (1 / 2) ⊆ {ω : ℂ | -1 < ω.im}) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F ((α : ℂ) * (1 - Complex.I * (t : ℂ)))) := by
  let U : Set ℂ := {ω : ℂ | -1 < ω.im}; have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hre : ∀ ω ∈ U, 0 < ((α : ℂ) * (1 - Complex.I * ω)).re := fun ω hω => by
    change -1 < ω.im at hω; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_re, Complex.one_re, Complex.I_re, Complex.I_im, one_mul]; exact mul_pos hα (by linarith)
  have hG : DifferentiableOn ℂ (fun ω => F ((α : ℂ) * (1 - Complex.I * ω))) U := fun ω hω =>
    (hF _ (hre ω hω)).comp ω (((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.const_mul Complex.I)).const_mul _ |>.differentiableWithinAt) (fun _ hz => hre _ hz)
  have hball : ∀ t : ℝ, Metric.closedBall (t : ℂ) (1 / 2) ⊆ U := fun t ω hω => by
    have him : |ω.im| ≤ 1 / 2 := by simpa [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (ω - (t : ℂ))).trans (by simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hω)
    change -1 < ω.im; linarith [(abs_le.mp him).1]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F ((α : ℂ) * (1 - Complex.I * (t : ℂ)))) := contDiff_iff_contDiffAt.mpr fun t =>
    (((hG.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn).contDiffAt (hU.mem_nhds (by change -1 < ((t : ℂ)).im; simp)) |>.restrict_scalars ℝ).comp t
      Complex.ofRealCLM.contDiff.contDiffAt
  exact ⟨hU, hG, hre, hball, hcd⟩

private lemma norm_one_sub_I_mul_half_ge {τ : ℝ} {ω : ℂ} (hdist : ‖ω - (τ : ℂ)‖ ≤ 1 / 2) :
    Real.sqrt (1 + τ ^ 2) / 2 ≤ ‖1 - Complex.I * ω‖ := by
  have hτ_norm : ‖1 - Complex.I * (τ : ℂ)‖ = Real.sqrt (1 + τ ^ 2) := by rw [Complex.norm_def, Complex.normSq_apply]; simp [sq]
  have htri : ‖1 - Complex.I * (τ : ℂ)‖ ≤ ‖1 - Complex.I * ω‖ + 1 / 2 :=
    calc ‖1 - Complex.I * (τ : ℂ)‖ = ‖(1 - Complex.I * ω) + Complex.I * (ω - (τ : ℂ))‖ := by congr 1; ring
      _ ≤ ‖1 - Complex.I * ω‖ + ‖Complex.I * (ω - (τ : ℂ))‖ := norm_add_le _ _
      _ ≤ ‖1 - Complex.I * ω‖ + 1 / 2 := by rw [norm_mul, Complex.norm_I, one_mul]; linarith
  have h1_ge : 1 ≤ ‖1 - Complex.I * (τ : ℂ)‖ := hτ_norm ▸ Real.one_le_sqrt.mpr (by linarith [sq_nonneg τ])
  linarith

private lemma norm_iteratedDeriv_mul_le {f g : ℝ → ℂ} {N j : ℕ} {τ A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hj : j ≤ N)
    (hf_cd : ContDiff ℝ N f) (hg_cd : ContDiff ℝ N g) (hf : ∀ i ≤ j, ‖iteratedDeriv i f τ‖ ≤ A) (hg : ∀ i ≤ j, ‖iteratedDeriv i g τ‖ ≤ B) :
    ‖iteratedDeriv j (fun t => f t * g t) τ‖ ≤ (2 : ℝ) ^ N * A * B := by
  rw [iteratedDeriv_fun_mul (hf_cd.contDiffAt.of_le (by exact_mod_cast hj)) (hg_cd.contDiffAt.of_le (by exact_mod_cast hj))]
  have hsum : ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i f τ * iteratedDeriv (j - i) g τ‖ ≤ (2 : ℝ) ^ j * (A * B) := by
    rw [show (2 : ℝ) ^ j = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) from by exact_mod_cast (Nat.sum_range_choose j).symm, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi); rw [norm_mul, norm_mul, Complex.norm_natCast]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hf i hij) (Nat.cast_nonneg _)) (hg (j - i) (Nat.sub_le j i))
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)).trans_eq (by ring)
  have hp : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
  calc _ ≤ (2 : ℝ) ^ j * (A * B) := hsum
    _ ≤ (2 : ℝ) ^ N * (A * B) := by gcongr
    _ = _ := by ring

/-! ## Section 1: Lemma `O.2` (`(u1co:O2)` and `(e29)`) -/

/-- Smoothness along the reflected line `τ ↦ F(c^{1/3}(1 - i τ))` for `F` holomorphic on `Re w > 0`. -/
lemma o2_reflected_line_contDiff {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re}) {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) :=
  (reflected_line_diffOn hF (Real.rpow_pos_of_pos hc _)).2.2.2.2

/-- **Lemma `O.2` (`u1c_o1_upper.tex`, `(u1co:O2)`):** Cauchy derivative bound along the reflected line
`τ ↦ F(c^{1/3}(1 - i τ))` for `F` holomorphic on `Re w > 0` with `‖F w‖ ≤ C_star ‖1 + w‖^{-5/2}`. -/
theorem o2_reflected_line_deriv_bound {F : ℂ → ℂ} {C_star : ℝ} (hC : 0 ≤ C_star)
    (hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re}) (hbd : ∀ w : ℂ, 0 < w.re → ‖F w‖ ≤ C_star * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    {c : ℝ} (hc : 2 ≤ c) (τ : ℝ) (r : ℕ) :
    ‖iteratedDeriv r (fun t : ℝ => F ((c ^ (1 / 3 : ℝ) : ℝ) * (1 - Complex.I * t))) τ‖ ≤
      (2 : ℝ) ^ ((r : ℝ) + 5 / 2) * (r.factorial : ℝ) * C_star * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by
  have hc_pos : 0 < c := by linarith
  let α : ℝ := c ^ (1 / 3 : ℝ); have hα : 0 < α := Real.rpow_pos_of_pos hc_pos _
  obtain ⟨hU, hG, hre, hball, _⟩ := reflected_line_diffOn hF hα
  let B : ℝ → ℝ := fun t => (2 : ℝ) ^ (5 / 2 : ℝ) * C_star * c ^ (-(5 / 6 : ℝ)) * (1 + t ^ 2) ^ (-(5 / 4 : ℝ))
  have hsphere : ∀ t : ℝ, ∀ ω ∈ Metric.sphere (t : ℂ) (1 / 2), ‖F ((α : ℂ) * (1 - Complex.I * ω))‖ ≤ B t := fun t ω hω => by
    have hw_re : 0 < ((α : ℂ) * (1 - Complex.I * ω)).re := hre ω (hball t (Metric.sphere_subset_closedBall hω))
    have hdist : ‖ω - (t : ℂ)‖ ≤ 1 / 2 := by simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hω).le
    set w : ℂ := (α : ℂ) * (1 - Complex.I * ω)
    have hnorm_ge_w : ‖w‖ ≤ ‖1 + w‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]; nlinarith [hw_re]
    have hnorm_w_ge : α * Real.sqrt (1 + t ^ 2) / 2 ≤ ‖w‖ := by
      dsimp [w]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
      calc α * Real.sqrt (1 + t ^ 2) / 2 = α * (Real.sqrt (1 + t ^ 2) / 2) := by ring
        _ ≤ α * ‖1 - Complex.I * ω‖ := mul_le_mul_of_nonneg_left (norm_one_sub_I_mul_half_ge hdist) hα.le
    have hrpow_le := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < α * Real.sqrt (1 + t ^ 2) / 2)
      (hnorm_w_ge.trans hnorm_ge_w) (by norm_num : -(5 / 2 : ℝ) ≤ 0)
    have hpow_eq : (α * Real.sqrt (1 + t ^ 2) / 2) ^ (-(5 / 2 : ℝ)) = (2 : ℝ) ^ (5 / 2 : ℝ) * c ^ (-(5 / 6 : ℝ)) * (1 + t ^ 2) ^ (-(5 / 4 : ℝ)) := by
      rw [show α * Real.sqrt (1 + t ^ 2) / 2 = (2 : ℝ)⁻¹ * (α * Real.sqrt (1 + t ^ 2)) by ring,
        Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hα.le (Real.sqrt_nonneg _),
        Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv,
        show α ^ (-(5 / 2 : ℝ)) = c ^ (-(5 / 6 : ℝ)) by dsimp [α]; rw [← Real.rpow_mul hc_pos.le]; norm_num,
        show Real.sqrt (1 + t ^ 2) ^ (-(5 / 2 : ℝ)) = (1 + t ^ 2) ^ (-(5 / 4 : ℝ)) by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; norm_num]
      ring
    exact (hbd w hw_re).trans ((mul_le_mul_of_nonneg_left (hrpow_le.trans_eq hpow_eq) hC).trans_eq (by dsimp [B]; ring))
  have hbd_cauchy := (holomorphic_real_contDiff_and_cauchy hU hG (fun t => by change -1 < ((t : ℂ)).im; simp)
    (by norm_num : (0 : ℝ) < 1 / 2) hball hsphere).2 r τ
  have h2pow : (2 : ℝ) ^ (r : ℝ) * (2 : ℝ) ^ (5 / 2 : ℝ) = (2 : ℝ) ^ ((r : ℝ) + 5 / 2) := by rw [← Real.rpow_add zero_lt_two]
  calc ‖iteratedDeriv r (fun t : ℝ => F ((c ^ (1 / 3 : ℝ) : ℝ) * (1 - Complex.I * t))) τ‖ ≤ (r.factorial : ℝ) * B τ / (1 / 2 : ℝ) ^ r := hbd_cauchy
    _ = (r.factorial : ℝ) * ((2 : ℝ) ^ r * (2 : ℝ) ^ (5 / 2 : ℝ)) * C_star * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by
        dsimp [B]; rw [div_eq_mul_inv, ← inv_pow, show ((1 / 2 : ℝ)⁻¹) = 2 by norm_num]; ring
    _ = _ := by rw [← Real.rpow_natCast (2 : ℝ) r, h2pow]; ring

private lemma iteratedDeriv_bsplineE1_imag {β : ℝ} (l : ℕ) (v : ℝ) :
    iteratedDeriv l (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ))) v =
      (Complex.I * (β : ℂ)) ^ l * iteratedDeriv l bsplineE1 (Complex.I * (β : ℂ) * (v : ℂ)) := by
  rw [show (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ))) =
    fun u : ℝ => bsplineE1 ((Complex.I * (β : ℂ)) * (u : ℂ)) from funext fun u => by ring_nf]
  induction l generalizing v with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih, iteratedDeriv_succ]
    have hdiff : DifferentiableAt ℂ (iteratedDeriv k bsplineE1) ((Complex.I * (β : ℂ)) * (v : ℂ)) :=
      contDiff_bsplineE1.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top k) _
    have haff : HasDerivAt (fun u : ℝ => (Complex.I * (β : ℂ)) * (u : ℂ)) (Complex.I * (β : ℂ)) v := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (Complex.I * (β : ℂ))
    have hd := (hdiff.hasDerivAt.comp v haff).const_mul ((Complex.I * (β : ℂ)) ^ k)
    dsimp only [Function.comp_def] at hd; rw [hd.deriv, pow_succ]; ring

lemma bsplineE1_imag_pow_deriv_bound :
    ∀ (m k : ℕ), ∃ C > 0, ∀ {β : ℝ}, 0 < β → ∀ v : ℝ,
      ‖iteratedDeriv k (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ m) v‖ ≤ C * β ^ k * (1 + β * |v|) ^ (-(m : ℝ)) := by
  intro m; induction m with
  | zero =>
    intro k; refine ⟨1, one_pos, fun {β} hβ v => ?_⟩
    rw [show (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ 0) = fun _ => (1 : ℂ) from funext fun _ => pow_zero _]
    have hne0 : ∀ l (x : ℝ), iteratedDeriv (l + 1) (fun _ : ℝ => (1 : ℂ)) x = 0 := fun l => by
      induction l with | zero => intro x; simp | succ n ih => intro x; rw [iteratedDeriv_succ, funext ih]; simp
    cases k with | zero => simp | succ k => rw [hne0 k v, norm_zero]; positivity
  | succ m ih =>
    intro k; let Cj : ℕ → ℝ := fun j => Classical.choose (ih j)
    have hCj_pos : ∀ j, 0 < Cj j := fun j => (Classical.choose_spec (ih j)).1
    have hCj_bd : ∀ j {β : ℝ}, 0 < β → ∀ v : ℝ, ‖iteratedDeriv j (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ m) v‖ ≤
        Cj j * β ^ j * (1 + β * |v|) ^ (-(m : ℝ)) := fun j {_} hβ v => (Classical.choose_spec (ih j)).2 hβ v
    let S : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Cj j * ((k - j : ℕ) + 3 : ℝ)
    have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCj_pos j).le) (by positivity)
    refine ⟨S + 1, by linarith, fun {β} hβ v => ?_⟩
    have h_cd1_k : ContDiff ℝ k (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ))) :=
      ((contDiff_bsplineE1.restrict_scalars ℝ).comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    rw [show (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ (m + 1)) =
        fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ m * bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) from funext fun u => by ring,
      iteratedDeriv_fun_mul (h_cd1_k.pow m).contDiffAt h_cd1_k.contDiffAt]
    have hsingle : ∀ l : ℕ, ‖iteratedDeriv l (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ))) v‖ ≤ (l + 3 : ℝ) * β ^ l * (1 + β * |v|) ^ (-1 : ℝ) := fun l => by
      rw [iteratedDeriv_bsplineE1_imag l v, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
      have hE := (norm_iteratedDeriv_bsplineE1_le l (by simp : 0 ≤ (Complex.I * (β : ℂ) * (v : ℂ)).re)).2.2
      have hnorm : ‖Complex.I * (β : ℂ) * (v : ℂ)‖ = β * |v| := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hβ]
      rw [hnorm, div_eq_mul_inv, ← Real.rpow_neg_one] at hE; exact (mul_le_mul_of_nonneg_left hE (pow_nonneg hβ.le l)).trans_eq (by ring)
    have hsum : ‖∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * iteratedDeriv j (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ m) v *
          iteratedDeriv (k - j) (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ))) v‖ ≤ S * β ^ k * (1 + β * |v|) ^ (-((m + 1 : ℕ) : ℝ)) := by
      rw [Finset.sum_mul, Finset.sum_mul]; refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj); rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hβp : β ^ j * β ^ (k - j) = β ^ k := by rw [← pow_add, Nat.add_sub_of_le hjk]
      have hvp : (1 + β * |v|) ^ (-(m : ℝ)) * (1 + β * |v|) ^ (-1 : ℝ) = (1 + β * |v|) ^ (-((m + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add (by positivity)]; push_cast; congr 2; ring
      have h1 := hCj_bd j hβ v; have h2 := hsingle (k - j)
      exact (mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (hCj_pos j).le (pow_nonneg hβ.le j)) (by positivity)))).trans_eq
        (by rw [show (k.choose j : ℝ) * (Cj j * β ^ j * (1 + β * |v|) ^ (-(m : ℝ))) * (((k - j : ℕ) + 3 : ℝ) * β ^ (k - j) * (1 + β * |v|) ^ (-1 : ℝ)) =
            (k.choose j : ℝ) * Cj j * ((k - j : ℕ) + 3 : ℝ) * (β ^ j * β ^ (k - j)) * ((1 + β * |v|) ^ (-(m : ℝ)) * (1 + β * |v|) ^ (-1 : ℝ)) by ring, hβp, hvp])
    exact hsum.trans (by nlinarith [show 0 ≤ β ^ k * (1 + β * |v|) ^ (-((m + 1 : ℕ) : ℝ)) by positivity])

/-- **Lemma `O.2` (`u1c_o1_upper.tex`, `(e29)`):** uniform-in-`δ₀` imaginary-axis weighted derivative
bounds at every order `r ≤ m` for `bsplineE1(i c_s δ₀ u / m)^m * g(u)`. -/
theorem o2_imag_weighted_deriv_bound {m : ℕ} (hm : 1 ≤ m) :
    ∃ C > 0, ∀ {C_g : ℝ}, 0 ≤ C_g → ∀ {g : ℝ → ℂ}, ContDiff ℝ m g →
      (∀ j ≤ m, ∀ v : ℝ, 1 ≤ |v| → ‖iteratedDeriv j g v‖ ≤ C_g * |v| ^ (-(5 / 2 : ℝ) - (j : ℝ))) →
      ∀ {r : ℕ}, r ≤ m → ∀ {δ₀ : ℝ}, δ₀ ∈ Ioc 0 2 → ∀ {v : ℝ}, 1 ≤ |v| →
        ‖iteratedDeriv r (fun u : ℝ => bsplineE1 (Complex.I * (ceCs * δ₀ / m : ℝ) * (u : ℂ)) ^ m * g u) v‖ ≤
          C * C_g * |v| ^ (-(5 / 2 : ℝ) - (r : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ)) := by
  let Ck : ℕ → ℝ := fun k => Classical.choose (bsplineE1_imag_pow_deriv_bound m k)
  have hCk_pos : ∀ k, 0 < Ck k := fun k => (Classical.choose_spec (bsplineE1_imag_pow_deriv_bound m k)).1
  have hCk_bd : ∀ k {β : ℝ}, 0 < β → ∀ v : ℝ, ‖iteratedDeriv k (fun u : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ m) v‖ ≤
      Ck k * β ^ k * (1 + β * |v|) ^ (-(m : ℝ)) := fun k {_} hβ v => (Classical.choose_spec (bsplineE1_imag_pow_deriv_bound m k)).2 hβ v
  let c₀ : ℝ := min 1 (ceCs / m); have hc₀ : 0 < c₀ := lt_min one_pos (div_pos ceCs_pos (Nat.cast_pos.mpr hm))
  let C_pre : ℕ → ℝ := fun k => Ck k * (ceCs / m) ^ k * c₀ ^ (-(m : ℝ))
  let C_sup : ℝ := ∑ k ∈ Finset.range (m + 1), C_pre k
  have hCsup_pos : 0 < C_sup := Finset.sum_pos (fun k _ => mul_pos (mul_pos (hCk_pos k)
    (pow_pos (div_pos ceCs_pos (by positivity)) k)) (Real.rpow_pos_of_pos hc₀ _)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩
  refine ⟨(2 : ℝ) ^ m * C_sup, by positivity, fun {C_g} hCg {g} hg_cd hg_bd {r} hr {δ₀} hδ {v} hv => ?_⟩
  have hδ_pos : 0 < δ₀ := hδ.1; let β : ℝ := ceCs * δ₀ / m; have hβ : 0 < β := div_pos (mul_pos ceCs_pos hδ_pos) (Nat.cast_pos.mpr hm)
  let μ : ℝ → ℂ := fun u => bsplineE1 (Complex.I * (β : ℂ) * (u : ℂ)) ^ m
  have hμ_cd : ContDiff ℝ m μ := (((contDiff_bsplineE1.restrict_scalars ℝ).comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).pow m).of_le (by simp)
  have hv_pos : 0 < |v| := by linarith
  have h1δv : 1 ≤ 1 + δ₀ * |v| := by linarith [mul_nonneg hδ_pos.le (abs_nonneg v)]
  have h1β_lb : c₀ * (1 + δ₀ * |v|) ≤ 1 + β * |v| := by
    have h1 : c₀ ≤ 1 := min_le_left _ _; have h2 : c₀ ≤ ceCs / m := min_le_right _ _
    calc c₀ * (1 + δ₀ * |v|) = c₀ + c₀ * δ₀ * |v| := by ring
      _ ≤ 1 + (ceCs / m) * δ₀ * |v| := by gcongr
      _ = 1 + β * |v| := by dsimp [β]; ring
  have hμ_k : ∀ k ≤ r, ‖iteratedDeriv k μ v‖ ≤ C_sup * |v| ^ (-(k : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ)) := fun k hk => by
    have hkm : k ≤ m := hk.trans hr
    have hrpow_β : (1 + β * |v|) ^ (-(m : ℝ)) ≤ c₀ ^ (-(m : ℝ)) * (1 + δ₀ * |v|) ^ (-(m : ℝ)) :=
      (Real.rpow_le_rpow_of_nonpos (by positivity) h1β_lb (by simp)).trans_eq (Real.mul_rpow hc₀.le (by positivity))
    have hδk : δ₀ ^ k ≤ (1 + δ₀ * |v|) ^ k * (|v|⁻¹) ^ k :=
      (pow_le_pow_left₀ hδ_pos.le ((le_mul_inv_iff₀ hv_pos).mpr (by linarith)) k).trans_eq (mul_pow _ _ _)
    have hδ_comb : δ₀ ^ k * (1 + δ₀ * |v|) ^ (-(m : ℝ)) ≤ |v| ^ (-(k : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ)) := by
      have h1 : (1 + δ₀ * |v|) ^ k * (1 + δ₀ * |v|) ^ (-(m : ℝ)) = (1 + δ₀ * |v|) ^ ((k : ℝ) - (m : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]; ring_nf
      have h2 : (1 + δ₀ * |v|) ^ ((k : ℝ) - (m : ℝ)) ≤ (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le h1δv (by rw [Nat.cast_sub hr]; linarith [show (k : ℝ) ≤ (r : ℝ) from Nat.cast_le.mpr hk])
      have hvk : (|v|⁻¹) ^ k = |v| ^ (-(k : ℝ)) := by rw [Real.rpow_neg hv_pos.le, Real.rpow_natCast, inv_pow]
      calc δ₀ ^ k * (1 + δ₀ * |v|) ^ (-(m : ℝ)) ≤ ((1 + δ₀ * |v|) ^ k * (|v|⁻¹) ^ k) * (1 + δ₀ * |v|) ^ (-(m : ℝ)) := by gcongr
        _ = (|v|⁻¹) ^ k * ((1 + δ₀ * |v|) ^ k * (1 + δ₀ * |v|) ^ (-(m : ℝ))) := by ring
        _ ≤ |v| ^ (-(k : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ)) := by rw [h1, hvk]; gcongr
    have hC_le : C_pre k ≤ C_sup := Finset.single_le_sum (f := C_pre)
      (fun i _ => mul_nonneg (mul_nonneg (hCk_pos i).le (pow_nonneg (div_nonneg ceCs_pos.le (by positivity)) i)) (Real.rpow_nonneg hc₀.le _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkm))
    have hstep_c0 : Ck k * (ceCs / m) ^ k * (δ₀ ^ k * (1 + β * |v|) ^ (-(m : ℝ))) ≤ C_pre k * (δ₀ ^ k * (1 + δ₀ * |v|) ^ (-(m : ℝ))) := by
      have hck_nn : 0 ≤ Ck k * (ceCs / m) ^ k := mul_nonneg (hCk_pos k).le (pow_nonneg (div_nonneg ceCs_pos.le (Nat.cast_nonneg m)) k)
      dsimp [C_pre]
      calc Ck k * (ceCs / m) ^ k * (δ₀ ^ k * (1 + β * |v|) ^ (-(m : ℝ)))
          ≤ Ck k * (ceCs / m) ^ k * (δ₀ ^ k * (c₀ ^ (-(m : ℝ)) * (1 + δ₀ * |v|) ^ (-(m : ℝ)))) := by gcongr
        _ = _ := by ring
    calc ‖iteratedDeriv k μ v‖ ≤ Ck k * β ^ k * (1 + β * |v|) ^ (-(m : ℝ)) := hCk_bd k hβ v
      _ = Ck k * (ceCs / m) ^ k * (δ₀ ^ k * (1 + β * |v|) ^ (-(m : ℝ))) := by dsimp [β]; rw [div_eq_mul_inv, mul_assoc ceCs δ₀, mul_pow, mul_pow]; ring
      _ ≤ C_pre k * (δ₀ ^ k * (1 + δ₀ * |v|) ^ (-(m : ℝ))) := hstep_c0
      _ ≤ C_sup * (|v| ^ (-(k : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ))) := mul_le_mul hC_le hδ_comb (by positivity) hCsup_pos.le
      _ = _ := by ring
  rw [show (fun u : ℝ => bsplineE1 (Complex.I * (ceCs * δ₀ / m : ℝ) * (u : ℂ)) ^ m * g u) =
      fun u : ℝ => μ u * g u from by funext u; simp [μ, β],
    iteratedDeriv_fun_mul (hμ_cd.contDiffAt.of_le (by exact_mod_cast hr)) (hg_cd.contDiffAt.of_le (by exact_mod_cast hr))]
  have hsum : ‖∑ k ∈ Finset.range (r + 1), (r.choose k : ℂ) * iteratedDeriv k μ v * iteratedDeriv (r - k) g v‖ ≤
      (2 : ℝ) ^ r * (C_sup * C_g * |v| ^ (-(5 / 2 : ℝ) - (r : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ))) := by
    rw [show (2 : ℝ) ^ r = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) from by exact_mod_cast (Nat.sum_range_choose r).symm, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk); rw [norm_mul, norm_mul, Complex.norm_natCast]
    have hvp : |v| ^ (-(k : ℝ)) * |v| ^ (-(5 / 2 : ℝ) - ((r - k : ℕ) : ℝ)) = |v| ^ (-(5 / 2 : ℝ) - (r : ℝ)) := by
      rw [← Real.rpow_add hv_pos, Nat.cast_sub hkr]; ring_nf
    calc (r.choose k : ℝ) * ‖iteratedDeriv k μ v‖ * ‖iteratedDeriv (r - k) g v‖
        ≤ (r.choose k : ℝ) * (C_sup * |v| ^ (-(k : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ))) *
            (C_g * |v| ^ (-(5 / 2 : ℝ) - ((r - k : ℕ) : ℝ))) := by gcongr; exact hμ_k k hkr; exact hg_bd (r - k) ((Nat.sub_le r k).trans hr) v hv
      _ = (r.choose k : ℝ) * (C_sup * C_g * (|v| ^ (-(k : ℝ)) * |v| ^ (-(5 / 2 : ℝ) - ((r - k : ℕ) : ℝ))) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ))) := by ring
      _ = _ := by rw [hvp]
  have hr2m : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  calc _ ≤ (2 : ℝ) ^ r * (C_sup * C_g * |v| ^ (-(5 / 2 : ℝ) - (r : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ))) := hsum
    _ ≤ (2 : ℝ) ^ m * (C_sup * C_g * |v| ^ (-(5 / 2 : ℝ) - (r : ℝ)) * (1 + δ₀ * |v|) ^ (-((m - r : ℕ) : ℝ))) := by gcongr
    _ = _ := by ring

/-! ## Section 2: Exact binomial expansion of `bsplineMult` -/

/-- Exact binomial expansion of the reflected `m`-fold B-spline multiplier `bsplineMult b m τ` (`b > 0`). -/
theorem bsplineMult_binomial_eq {b : ℝ} (hb : 0 < b) (m : ℕ) (τ : ℝ) :
    bsplineMult b m τ =
      ((b : ℂ) * (1 - Complex.I * (τ : ℂ))) ^ (-(m : ℤ)) *
        ∑ j ∈ Finset.range (m + 1),
          (-1 : ℂ) ^ j * (m.choose j : ℂ) * Complex.exp (-((j : ℝ) * b : ℂ)) * Complex.exp (Complex.I * ((j : ℝ) * b : ℂ) * (τ : ℂ)) := by
  let ζ : ℂ := (b : ℂ) * (1 - Complex.I * (τ : ℂ))
  have hζ : ζ ≠ 0 := fun h => by
    have hz : ζ.re = 0 := by rw [h]; simp
    simp [ζ] at hz; linarith
  have h1 : bsplineE1 ζ = ζ⁻¹ * (1 + (-Complex.exp (-ζ))) := by simp only [bsplineE1, hζ, ↓reduceIte]; ring
  rw [bsplineMult, show ((b : ℂ) * (1 - Complex.I * (τ : ℂ))) = ζ from rfl, h1, mul_pow, inv_pow, ← zpow_natCast ζ m, ← zpow_neg]
  congr 1; rw [add_comm (1 : ℂ), add_pow]; refine Finset.sum_congr rfl fun j _ => ?_
  have hexp : (-Complex.exp (-ζ)) ^ j = (-1 : ℂ) ^ j * Complex.exp (-((j : ℝ) * b : ℂ)) * Complex.exp (Complex.I * ((j : ℝ) * b : ℂ) * (τ : ℂ)) := by
    rw [show (-Complex.exp (-ζ)) = (-1 : ℂ) * Complex.exp (-ζ) by ring, mul_pow, ← Complex.exp_nat_mul,
      mul_assoc ((-1 : ℂ) ^ j), ← Complex.exp_add]; congr 2; push_cast [ζ]; ring
  rw [one_pow, mul_one, hexp]; ring

/-! ## Section 3: Lemma `O.3(1)` core phase bound `(u1co:dual-phase)` -/

private lemma edgePhi_contDiff (L : ℝ) : ContDiff ℝ 3 (edgePhi L) := by
  rw [show edgePhi L = fun τ => L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ from funext (edgePhi_eq_cubic_add_ceHth L)]
  exact (((contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 3))).add edgeR_contDiff)

lemma hasDerivAt_edgePhiDeriv (L τ : ℝ) : HasDerivAt (edgePhiDeriv L) (edgePhiDeriv2 τ) τ := by
  have hcd : ContDiff ℝ 2 (edgePhiDeriv L) := by
    rw [show edgePhiDeriv L = deriv (edgePhi L) from funext fun t => (hasDerivAt_edgePhi L t).deriv.symm]; exact (edgePhi_contDiff L).deriv'
  have hdiff : DifferentiableAt ℝ (edgePhiDeriv L) τ := (hcd.differentiable (by decide)).differentiableAt
  suffices deriv (edgePhiDeriv L) τ = edgePhiDeriv2 τ from this ▸ hdiff.hasDerivAt
  have hne : ∀ t ≠ 0, deriv (edgePhiDeriv L) t = edgePhiDeriv2 t := fun t ht => by
    rcases lt_or_gt_of_ne ht with htn | htp
    · have htp' : 0 < -t := neg_pos.mpr htn
      have hev : edgePhiDeriv L =ᶠ[𝓝 t] fun s => L - ceEll (Real.pi * (-s) / 2) := by
        filter_upwards [IsOpen.mem_nhds isOpen_Iio htn] with s hs
        rw [edgePhiDeriv, ite_eq_right_iff.mpr (fun h => absurd h (ne_of_lt hs)), abs_of_neg hs, ← sub_neg_eq_add, ← Real.log_inv, inv_div, ceEll]
      have hd := ((m2_bounds htp').1.comp t (hasDerivAt_neg t)).const_sub L
      have hodd : edgePhiDeriv2 (-t) = -edgePhiDeriv2 t := by unfold edgePhiDeriv2; simp only [mul_neg, Real.sinh_neg]; ring
      exact (hev.deriv_eq.trans hd.deriv).trans (by rw [hodd]; ring)
    · have hev : edgePhiDeriv L =ᶠ[𝓝 t] fun s => L - ceEll (Real.pi * s / 2) := by
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi htp] with s hs
        rw [edgePhiDeriv, ite_eq_right_iff.mpr (fun h => absurd h (ne_of_gt hs)), abs_of_pos hs, ← sub_neg_eq_add, ← Real.log_inv, inv_div, ceEll]
      exact (hev.deriv_eq.trans ((m2_bounds htp).1.const_sub L).deriv).trans (by ring)
  by_cases hτ : τ = 0
  · subst hτ
    have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht1 : Tendsto (fun n : ℕ => ‖deriv (edgePhiDeriv L) (1 / ((n : ℝ) + 1))‖) atTop (𝓝 ‖deriv (edgePhiDeriv L) 0‖) :=
      ((hcd.continuous_deriv (by decide)).continuousAt.tendsto.comp hseq).norm
    have ht2 : Tendsto (fun n : ℕ => Real.pi ^ 2 / 6 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := Real.pi ^ 2 / 6)).mul hseq
    have hle : ∀ n : ℕ, ‖deriv (edgePhiDeriv L) (1 / ((n : ℝ) + 1))‖ ≤ Real.pi ^ 2 / 6 * (1 / ((n : ℝ) + 1)) := fun n => by
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      conv_lhs => rw [hne _ hn.ne', Real.norm_eq_abs]
      conv_rhs => rw [← abs_of_pos hn]
      exact (edgePhiDeriv2_abs_le hn.ne').trans (min_le_left _ _)
    simp [edgePhiDeriv2, norm_le_zero_iff.mp (le_of_tendsto_of_tendsto' ht1 ht2 hle)]
  · exact hne τ hτ

private lemma edgePhiDeriv2_neg (τ : ℝ) : edgePhiDeriv2 (-τ) = -edgePhiDeriv2 τ := by
  unfold edgePhiDeriv2; simp only [mul_neg, Real.sinh_neg]; ring

private lemma edgePhiDeriv2_nonpos_of_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : edgePhiDeriv2 τ ≤ 0 := by
  rcases eq_or_lt_of_le hτ with rfl | hpos
  · simp [edgePhiDeriv2]
  · linarith [(m2_bounds hpos).2.1, div_nonneg hpos.le (by positivity : 0 ≤ 1 + τ ^ 2)]

private lemma edgePhiDeriv_antitoneOn_nonneg {L a b : ℝ} (ha : 0 ≤ a) : AntitoneOn (edgePhiDeriv L) (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (fun t _ => (hasDerivAt_edgePhiDeriv L t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_edgePhiDeriv L t).hasDerivWithinAt) (fun _ ht => edgePhiDeriv2_nonpos_of_nonneg (ha.trans (interior_subset ht).1))

private lemma edgePhiDeriv_monotoneOn_nonpos {L a b : ℝ} (hb : b ≤ 0) : MonotoneOn (edgePhiDeriv L) (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (fun t _ => (hasDerivAt_edgePhiDeriv L t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_edgePhiDeriv L t).hasDerivWithinAt) (fun _ ht => by
      have h := edgePhiDeriv2_nonpos_of_nonneg (neg_nonneg.mpr ((interior_subset ht).2.trans hb)); rw [edgePhiDeriv2_neg] at h; linarith)

private lemma edgePhiDeriv2_abs_le_two (τ : ℝ) : |edgePhiDeriv2 τ| ≤ 2 := by
  by_cases hτ : τ = 0; · subst hτ; simp [edgePhiDeriv2]
  · rcases le_or_gt |τ| 1 with h1 | h1
    · have hpi2 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
      exact (edgePhiDeriv2_abs_le hτ).trans ((min_le_left _ _).trans (by nlinarith [abs_nonneg τ]))
    · exact (edgePhiDeriv2_abs_le hτ).trans ((min_le_right _ _).trans ((inv_le_one_iff₀.mpr (Or.inr h1.le)).trans (by norm_num)))

private lemma hasDerivAt_edgePhiDeriv2 (τ : ℝ) :
    HasDerivAt edgePhiDeriv2 (iteratedDeriv 3 (edgePhi 0) τ) τ ∧ Continuous (iteratedDeriv 3 (edgePhi 0)) ∧ |iteratedDeriv 3 (edgePhi 0) τ| ≤ 7 := by
  have hcd3 : ContDiff ℝ 3 (edgePhi 0) := edgePhi_contDiff 0
  have heq : edgePhiDeriv2 = iteratedDeriv 2 (edgePhi 0) := funext fun t => by
    rw [iteratedDeriv_succ, iteratedDeriv_one, show deriv (edgePhi 0) = edgePhiDeriv 0 from funext fun s => (hasDerivAt_edgePhi 0 s).deriv]
    exact (hasDerivAt_edgePhiDeriv 0 t).deriv.symm
  have hhd : HasDerivAt edgePhiDeriv2 (iteratedDeriv 3 (edgePhi 0) τ) τ := by
    rw [heq]; simpa only [iteratedDeriv_succ] using (hcd3.differentiable_iteratedDeriv 2 (by decide) τ).hasDerivAt
  let p : ℝ → ℝ := fun s => -(Real.pi ^ 2 / 36) * s ^ 3; have hp_cd : ContDiff ℝ 3 p := contDiff_const.mul (contDiff_id.pow 3)
  have hdecomp : edgePhi 0 = fun s => p s + edgeR s := funext fun s => by rw [edgePhi_eq_cubic_add_ceHth]; unfold edgeR; dsimp [p]; ring
  have hd2 : deriv (deriv p) = fun s => -(Real.pi ^ 2 / 6) * s := by
    have hd1 : deriv p = fun s => -(Real.pi ^ 2 / 12) * s ^ 2 := funext fun s => (((hasDerivAt_pow 3 s).const_mul (-(Real.pi ^ 2 / 36))).congr_deriv (by ring)).deriv
    rw [hd1]; exact funext fun s => (((hasDerivAt_pow 2 s).const_mul (-(Real.pi ^ 2 / 12))).congr_deriv (by ring)).deriv
  have hp3 : iteratedDeriv 3 p τ = -(Real.pi ^ 2 / 6) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hd2]
    exact (((hasDerivAt_id τ).const_mul (-(Real.pi ^ 2 / 6))).congr_deriv (by ring)).deriv
  have hadd3 : iteratedDeriv 3 (edgePhi 0) τ = -(Real.pi ^ 2 / 6) + iteratedDeriv 3 edgeR τ := by
    rw [hdecomp, iteratedDeriv_fun_add hp_cd.contDiffAt edgeR_contDiff.contDiffAt, hp3]
  have hbd3 : |iteratedDeriv 3 (edgePhi 0) τ| ≤ 7 := by
    rw [hadd3]; have htri : |-(Real.pi ^ 2 / 6) + iteratedDeriv 3 edgeR τ| ≤ Real.pi ^ 2 / 6 + Real.pi ^ 2 / 2 :=
      (abs_add_le _ _).trans (by rw [abs_neg, abs_of_pos (by positivity)]; gcongr; exact (edgeR_deriv_bounds τ).2.2.2)
    exact htri.trans (by nlinarith [Real.pi_pos, Real.pi_lt_d2])
  exact ⟨hhd, hcd3.continuous_iteratedDeriv 3 le_rfl, hbd3⟩

private lemma eVariationOn_le_integral_norm_deriv {h h' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x) (hh' : IntervalIntegrable h' volume a b) :
    eVariationOn h (Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, ‖h' t‖) := by
  have hh'_n : IntervalIntegrable (fun t => ‖h' t‖) volume a b := hh'.norm
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  have hstep : ∀ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i)) ≤ ENNReal.ofReal (∫ t in u i..u (i + 1), ‖h' t‖) := fun i _ => by
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i); have h_sub : Icc (u i) (u (i + 1)) ⊆ Icc a b := Icc_subset_Icc (hus i).1 (hus (i + 1)).2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by rw [uIcc_of_le hui] at hx; exact hh x (h_sub hx))
      (hh'.mono_set (by rw [uIcc_of_le hui, uIcc_of_le hab]; exact h_sub))
    rw [edist_dist, dist_eq_norm, ← hftc]; exact ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hui)
  have htele : ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), ‖h' t‖) = ENNReal.ofReal (∫ t in u 0..u n, ‖h' t‖) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) fun _ _ => norm_nonneg _)]
    congr 1; exact intervalIntegral.sum_integral_adjacent_intervals fun i _ =>
      hh'_n.mono_set (by rw [uIcc_of_le (hu (Nat.le_succ i)), uIcc_of_le hab]; exact Icc_subset_Icc (hus i).1 (hus (i + 1)).2)
  exact (Finset.sum_le_sum hstep).trans (htele.symm ▸ ENNReal.ofReal_le_ofReal
    (intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2 (Eventually.of_forall fun _ => norm_nonneg _) hh'_n))

private lemma integral_one_add_sq_neg_three_halves_le_pi {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) ≤ Real.pi := by
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 + t ^ 2) ^ (-(3 / 2 : ℝ))) volume a b :=
    (Continuous.rpow (by fun_prop) continuous_const (fun _ => Or.inl (by positivity))).intervalIntegrable a b
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 + t ^ 2)⁻¹) volume a b :=
    (Continuous.inv₀ (by fun_prop) (fun _ => by positivity)).intervalIntegrable a b
  refine (intervalIntegral.integral_mono_on hab hint1 hint2 fun t _ =>
    (Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg t]) (by norm_num : -(3 / 2 : ℝ) ≤ -1)).trans_eq (Real.rpow_neg_one _)).trans ?_
  rw [intervalIntegral.integral_of_le hab, ← integral_univ_inv_one_add_sq]
  exact setIntegral_le_integral integrable_inv_one_add_sq (Eventually.of_forall fun _ => by positivity)

private lemma integral_one_add_sq_neg_three_halves_tail_pos {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫ t in u..v, (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) ≤ (2 * u ^ 2)⁻¹ := by
  let F : ℝ → ℝ := fun t => -(2 : ℝ)⁻¹ * (t ^ 2)⁻¹
  have hderiv : ∀ t ∈ uIcc u v, HasDerivAt F (t ^ (-3 : ℝ)) t := fun t ht => by
    rw [uIcc_of_le huv] at ht; have ht0 : 0 < t := hu.trans_le ht.1
    exact (((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht0.ne')).const_mul (-(2 : ℝ)⁻¹)).congr_deriv (by
      rw [Real.rpow_neg ht0.le, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; field_simp [ht0.ne']; ring)
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 + t ^ 2) ^ (-(3 / 2 : ℝ))) volume u v :=
    (Continuous.rpow (by fun_prop) continuous_const (fun _ => Or.inl (by positivity))).intervalIntegrable u v
  have hint2 : IntervalIntegrable (fun t : ℝ => t ^ (-3 : ℝ)) volume u v :=
    ContinuousOn.intervalIntegrable (by rw [uIcc_of_le huv]; exact continuousOn_id.rpow_const fun t ht => Or.inl (hu.trans_le ht.1).ne')
  have hmono : ∫ t in u..v, (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) ≤ ∫ t in u..v, t ^ (-3 : ℝ) :=
    intervalIntegral.integral_mono_on huv hint1 hint2 fun t ht =>
      (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (hu.trans_le ht.1)) (by linarith : t ^ 2 ≤ 1 + t ^ 2) (by norm_num : -(3 / 2 : ℝ) ≤ 0)).trans_eq
        (by rw [← Real.rpow_natCast, ← Real.rpow_mul (hu.trans_le ht.1).le]; norm_num)
  refine hmono.trans ?_; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
  have hv0 : 0 < v := hu.trans_le huv; rw [show F v - F u = (2 * u ^ 2)⁻¹ - (2 * v ^ 2)⁻¹ by dsimp [F]; field_simp; ring]
  linarith [inv_nonneg.mpr (by positivity : 0 ≤ 2 * v ^ 2)]

private lemma eVariationOn_decay_le {a : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A) (ha_cd : ContDiff ℝ 2 a)
    (ha_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ))) {u v : ℝ} (huv : u ≤ v) :
    (eVariationOn a (Icc u v)).toReal ≤ A * Real.pi ∧ (0 < u → (eVariationOn a (Icc u v)).toReal ≤ A * (2 * u ^ 2)⁻¹) ∧
      (v < 0 → (eVariationOn a (Icc u v)).toReal ≤ A * (2 * v ^ 2)⁻¹) := by
  have hint : IntervalIntegrable (deriv a) volume u v := (ha_cd.continuous_deriv (by decide)).intervalIntegrable u v
  have hev := eVariationOn_le_integral_norm_deriv huv (fun x _ => ((ha_cd.differentiable (by decide)) x).hasDerivAt) hint
  have hmono : ∫ t in u..v, ‖deriv a t‖ ≤ A * ∫ t in u..v, (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on huv hint.norm
      (((Continuous.rpow (by fun_prop) continuous_const (fun _ => Or.inl (by positivity))).const_mul A).intervalIntegrable u v)
      fun t _ => by rw [← iteratedDeriv_one]; exact ha_bd 1 (by decide) t
  have hev' : (eVariationOn a (Icc u v)).toReal ≤ A * ∫ t in u..v, (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA (intervalIntegral.integral_nonneg huv fun _ _ => by positivity)) (hev.trans (ENNReal.ofReal_le_ofReal hmono))
  refine ⟨hev'.trans (mul_le_mul_of_nonneg_left (integral_one_add_sq_neg_three_halves_le_pi huv) hA),
    fun hu => hev'.trans (mul_le_mul_of_nonneg_left (integral_one_add_sq_neg_three_halves_tail_pos hu huv) hA),
    fun hv => hev'.trans (mul_le_mul_of_nonneg_left ?_ hA)⟩
  have hneg := integral_one_add_sq_neg_three_halves_tail_pos (neg_pos.mpr hv) (neg_le_neg huv)
  rw [← intervalIntegral.integral_comp_neg (fun t => (1 + t ^ 2) ^ (-(3 / 2 : ℝ)))] at hneg; simpa [neg_sq] using hneg

private lemma eVariationOn_tail_abs_le {a : ℝ → ℂ} {A u v c₀ : ℝ} (hA : 0 ≤ A) (hc₀ : 0 < c₀)
    (ha_cd : ContDiff ℝ 2 a) (ha_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)))
    (huv : u ≤ v) (habs : ∀ x ∈ Icc u v, c₀ ≤ |x|) : (eVariationOn a (Icc u v)).toReal ≤ A * (2 * c₀ ^ 2)⁻¹ := by
  have hV_all := eVariationOn_decay_le hA ha_cd ha_bd huv
  rcases lt_or_ge 0 u with hu_pos | hu_nonpos
  · have : c₀ ≤ u := by simpa [abs_of_pos hu_pos] using habs u (left_mem_Icc.mpr huv)
    exact (hV_all.2.1 hu_pos).trans (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by gcongr)) hA)
  · have hv_neg : v < 0 := by
      by_contra hv_nn; push Not at hv_nn
      have h0 := habs 0 ⟨hu_nonpos, hv_nn⟩; simp only [abs_zero] at h0; linarith
    have : c₀ ≤ -v := by simpa [abs_of_neg hv_neg] using habs v (right_mem_Icc.mpr huv)
    exact (hV_all.2.2 hv_neg).trans (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by nlinarith)) hA)

private lemma osc_vdc1_bound {u v c L lam M V : ℝ} (huv : u ≤ v) (hc : 0 < c) (hlam : 0 < lam)
    (hmono : MonotoneOn (edgePhiDeriv L) (Icc u v) ∨ AntitoneOn (edgePhiDeriv L) (Icc u v)) (hlb : ∀ x ∈ Icc u v, lam ≤ |edgePhiDeriv L x|)
    {a : ℝ → ℂ} (ha_cd : ContDiff ℝ 2 a) (hM : ∀ x ∈ Icc u v, ‖a x‖ ≤ M) (hV : (eVariationOn a (Icc u v)).toReal ≤ V) (hV_fin : eVariationOn a (Icc u v) ≠ ⊤) :
    ‖∫ x in u..v, a x * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L x : ℂ))‖ ≤ 3 * (M + V) / (c * lam) := by
  have h1 := van_der_corput_first huv hc hlam (fun y _ => hasDerivAt_edgePhi L y) (fun y _ => (hasDerivAt_edgePhiDeriv L y).continuousAt.continuousWithinAt)
    hmono hlb ha_cd.continuous.continuousOn hV_fin hM
  simpa only [mul_assoc] using h1.trans (by gcongr)

private lemma osc_vdc2_bound {u v c L lam M V : ℝ} (huv : u ≤ v) (hc : 0 < c) (hlam : 0 < lam)
    (hmono : MonotoneOn (edgePhiDeriv L) (Icc u v) ∨ AntitoneOn (edgePhiDeriv L) (Icc u v)) (hlb : ∀ x ∈ Icc u v, lam ≤ |edgePhiDeriv2 x|)
    {a : ℝ → ℂ} (ha_cd : ContDiff ℝ 2 a) (hM : ∀ x ∈ Icc u v, ‖a x‖ ≤ M) (hV : (eVariationOn a (Icc u v)).toReal ≤ V) (hV_fin : eVariationOn a (Icc u v) ≠ ⊤) :
    ‖∫ x in u..v, a x * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L x : ℂ))‖ ≤ 8 * (M + V) / Real.sqrt (c * lam) := by
  have h2 := van_der_corput_second huv hc hlam (fun y _ => hasDerivAt_edgePhi L y) (fun y _ => hasDerivAt_edgePhiDeriv L y)
    hmono hlb ha_cd.continuous.continuousOn hV_fin hM
  simpa only [mul_assoc] using h2.trans (by gcongr)

private lemma eVariationOn_decay_ne_top {a : ℝ → ℂ} {A : ℝ} (_hA : 0 ≤ A) (ha_cd : ContDiff ℝ 2 a) {u v : ℝ} (huv : u ≤ v) : eVariationOn a (Icc u v) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_le_integral_norm_deriv huv (fun x _ => ((ha_cd.differentiable (by decide)) x).hasDerivAt)
    ((ha_cd.continuous_deriv (by decide)).intervalIntegrable u v))

private lemma ibp_edgePhi_step {u u' : ℝ → ℂ} {α β c L : ℝ}
    (hu : ∀ t ∈ Icc α β, HasDerivAt u (u' t) t) (hu'_cont : ContinuousOn u' (Icc α β)) (hc : 0 < c) (hαβ : α ≤ β) :
    ∫ t in α..β, (u t * (edgePhiDeriv L t : ℂ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) =
      (-Complex.I / (c : ℂ)) * (u β * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L β : ℂ)) -
        u α * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L α : ℂ)) - ∫ t in α..β, u' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))) := by
  let E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))
  let E' : ℝ → ℂ := fun t => Complex.I * (c : ℂ) * (edgePhiDeriv L t : ℂ) * E t
  have hE : ∀ t ∈ [[α, β]], HasDerivAt E (E' t) t := fun t _ => by
    simpa [E, E', mul_comm (E t)] using ((hasDerivAt_edgePhi L t).ofReal_comp.const_mul (Complex.I * (c : ℂ))).cexp
  have hE'_cont : Continuous E' :=
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgePhiDeriv L t).continuousAt))).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgePhi L t).continuousAt))))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t ht => hu t (by rwa [uIcc_of_le hαβ] at ht)) hE
    ((uIcc_of_le hαβ ▸ hu'_cont).intervalIntegrable) (hE'_cont.intervalIntegrable α β)
  have hconst : (-Complex.I / (c : ℂ)) * (Complex.I * (c : ℂ)) = 1 := by
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    calc (-Complex.I / (c : ℂ)) * (Complex.I * (c : ℂ)) = -(Complex.I * Complex.I) * ((c : ℂ) / (c : ℂ)) := by ring
      _ = 1 := by rw [Complex.I_mul_I, neg_neg, div_self hc0, mul_one]
  calc ∫ t in α..β, (u t * (edgePhiDeriv L t : ℂ)) * E t
      = ∫ t in α..β, (-Complex.I / (c : ℂ)) * (u t * E' t) := intervalIntegral.integral_congr fun t _ => by
          dsimp [E']; rw [← one_mul ((u t * (edgePhiDeriv L t : ℂ)) * E t), ← hconst]; ring
    _ = (-Complex.I / (c : ℂ)) * ∫ t in α..β, u t * E' t := intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [hibp]

private lemma edgePhiDeriv_ge_quarter_on_exp_half {L τ : ℝ} (hL : 8 < L) (hτ : |τ| ≤ Real.exp (L / 2)) : L / 4 ≤ edgePhiDeriv L τ := by
  have hT1 : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by linarith); have hpi2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_d2]
  have harg : 1 + Real.pi * |τ| / 2 ≤ 3 * Real.exp (L / 2) := by
    calc 1 + Real.pi * |τ| / 2 = 1 + (Real.pi / 2) * |τ| := by ring
      _ ≤ Real.exp (L / 2) + 2 * Real.exp (L / 2) := by gcongr
      _ = 3 * Real.exp (L / 2) := by ring
  have hlog_ub : Real.log (1 + Real.pi * |τ| / 2) ≤ Real.log 3 + L / 2 :=
    (Real.log_le_log (by positivity) harg).trans_eq (by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp])
  have hlog3 : Real.log 3 ≤ 2 := (Real.log_le_iff_le_exp (by norm_num)).mpr (by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have he2 : (4 : ℝ) ≤ Real.exp 2 := by rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
    linarith)
  linarith [edgePhiDeriv_ge_log_bound L τ]

private lemma osc_twice_ibp_center {c L A : ℝ} (hc : 2 ≤ c) (hL : 8 < L) (hA : 0 ≤ A) {a : ℝ → ℂ} (ha_cd : ContDiff ℝ 2 a)
    (ha_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ))) :
    let T := Real.exp (L / 2)
    ‖∫ τ in -T..T, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤ 900 * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
  intro T; have hc_pos : 0 < c := by linarith
  have hT_pos : 0 < T := Real.exp_pos _; have hTT : -T ≤ T := by linarith
  have hΦ'_lb : ∀ t ∈ Icc (-T) T, L / 4 ≤ edgePhiDeriv L t := fun t ht => edgePhiDeriv_ge_quarter_on_exp_half hL (abs_le.mpr ht)
  have hΦ'_ne : ∀ t ∈ Icc (-T) T, (edgePhiDeriv L t : ℂ) ≠ 0 := fun t ht => Complex.ofReal_ne_zero.mpr (by linarith [hΦ'_lb t ht])
  have ha0_diff : Differentiable ℝ a := ha_cd.differentiable (by decide); have ha1_cd : ContDiff ℝ 1 (deriv a) := ha_cd.deriv'
  have ha1_diff : Differentiable ℝ (deriv a) := ha1_cd.differentiable (by decide)
  let Φ' : ℝ → ℂ := fun t => (edgePhiDeriv L t : ℂ); let Φ'' : ℝ → ℂ := fun t => (edgePhiDeriv2 t : ℂ)
  let Φ''' : ℝ → ℂ := fun t => ((iteratedDeriv 3 (edgePhi 0) t : ℝ) : ℂ)
  let u₁ : ℝ → ℂ := fun t => a t / Φ' t; let u₁' : ℝ → ℂ := fun t => (deriv a t * Φ' t - a t * Φ'' t) / Φ' t ^ 2
  let u₂ : ℝ → ℂ := fun t => deriv a t / Φ' t ^ 2 - a t * Φ'' t / Φ' t ^ 3
  let u₂' : ℝ → ℂ := fun t => (iteratedDeriv 2 a t * Φ' t ^ 2 - deriv a t * (2 * Φ' t * Φ'' t)) / (Φ' t ^ 2) ^ 2 -
      ((deriv a t * Φ'' t + a t * Φ''' t) * Φ' t ^ 3 - a t * Φ'' t * (3 * Φ' t ^ 2 * Φ'' t)) / (Φ' t ^ 3) ^ 2
  have hu₁ : ∀ t ∈ Icc (-T) T, HasDerivAt u₁ (u₁' t) t := fun t ht => ((ha0_diff t).hasDerivAt).div (hasDerivAt_edgePhiDeriv L t).ofReal_comp (hΦ'_ne t ht)
  have hu₂ : ∀ t ∈ Icc (-T) T, HasDerivAt u₂ (u₂' t) t := fun t ht => by
    have hne := hΦ'_ne t ht; have h1 : HasDerivAt (deriv a) (iteratedDeriv 2 a t) t := by rw [iteratedDeriv_succ, iteratedDeriv_one]; exact (ha1_diff t).hasDerivAt
    have hΦ := (hasDerivAt_edgePhiDeriv L t).ofReal_comp; have hΦ2 := (hasDerivAt_edgePhiDeriv2 t).1.ofReal_comp
    have hnum : HasDerivAt (fun s => a s * Φ'' s) (deriv a t * Φ'' t + a t * Φ''' t) t := ((ha0_diff t).hasDerivAt.mul hΦ2).congr_deriv (by dsimp [Φ'', Φ'''])
    have hden : HasDerivAt (fun s => Φ' s ^ 3) (3 * Φ' t ^ 2 * Φ'' t) t := (hΦ.pow 3).congr_deriv (by dsimp [Φ', Φ''])
    exact (h1.div ((hΦ.pow 2).congr_deriv (by dsimp [Φ', Φ'']; ring)) (pow_ne_zero 2 hne)).sub (hnum.div hden (pow_ne_zero 3 hne))
  have hc_p1 : Continuous Φ' := Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgePhiDeriv L t).continuousAt)
  have hc_p2 : Continuous Φ'' := Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgePhiDeriv2 t).1.continuousAt)
  have hc_p3 : Continuous Φ''' := Complex.continuous_ofReal.comp (hasDerivAt_edgePhiDeriv2 0).2.1
  have hu₁'_cont : ContinuousOn u₁' (Icc (-T) T) := ((ha1_cd.continuous.continuousOn.mul hc_p1.continuousOn).sub (ha_cd.continuous.continuousOn.mul hc_p2.continuousOn)).div
    (hc_p1.continuousOn.pow 2) (fun t ht => pow_ne_zero 2 (hΦ'_ne t ht))
  have hu₂'_cont : ContinuousOn u₂' (Icc (-T) T) := ContinuousOn.sub
    (ContinuousOn.div ((ha_cd.continuous_iteratedDeriv 2 le_rfl |>.continuousOn.mul (hc_p1.continuousOn.pow 2)).sub
      (ha1_cd.continuous.continuousOn.mul ((continuousOn_const.mul hc_p1.continuousOn).mul hc_p2.continuousOn)))
      ((hc_p1.continuousOn.pow 2).pow 2) (fun t ht => pow_ne_zero _ (pow_ne_zero _ (hΦ'_ne t ht))))
    (ContinuousOn.div (((ha1_cd.continuous.continuousOn.mul hc_p2.continuousOn).add (ha_cd.continuous.continuousOn.mul hc_p3.continuousOn)).mul (hc_p1.continuousOn.pow 3) |>.sub
      ((ha_cd.continuous.continuousOn.mul hc_p2.continuousOn).mul ((continuousOn_const.mul (hc_p1.continuousOn.pow 2)).mul hc_p2.continuousOn)))
      ((hc_p1.continuousOn.pow 3).pow 2) (fun t ht => pow_ne_zero _ (pow_ne_zero _ (hΦ'_ne t ht))))
  have hstep1 : ∫ t in -T..T, a t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) =
      (-Complex.I / (c : ℂ)) * (u₁ T * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L T : ℂ)) -
        u₁ (-T) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-T) : ℂ)) - ∫ t in -T..T, u₁' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))) := by
    have hrew : ∀ t ∈ uIcc (-T) T, a t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) =
        (u₁ t * (edgePhiDeriv L t : ℂ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) := fun t ht => by
      rw [uIcc_of_le hTT] at ht; dsimp [u₁]; rw [div_mul_cancel₀ _ (hΦ'_ne t ht)]
    rw [intervalIntegral.integral_congr hrew]; exact ibp_edgePhi_step hu₁ hu₁'_cont hc_pos hTT
  have hstep2 : ∫ t in -T..T, u₁' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) =
      (-Complex.I / (c : ℂ)) * (u₂ T * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L T : ℂ)) -
        u₂ (-T) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-T) : ℂ)) - ∫ t in -T..T, u₂' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))) := by
    have hrew : ∀ t ∈ uIcc (-T) T, u₁' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) =
        (u₂ t * (edgePhiDeriv L t : ℂ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) := fun t ht => by
      rw [uIcc_of_le hTT] at ht; have hne'' : (edgePhiDeriv L t : ℂ) ≠ 0 := hΦ'_ne t ht; dsimp [u₁', u₂, Φ']; field_simp [hne'']
    rw [intervalIntegral.integral_congr hrew]; exact ibp_edgePhi_step hu₂ hu₂'_cont hc_pos hTT
  have hΦ'n : ∀ t ∈ Icc (-T) T, L / 4 ≤ ‖Φ' t‖ := fun t ht => by rw [Complex.norm_real, Real.norm_eq_abs]; exact (hΦ'_lb t ht).trans (le_abs_self _)
  have hΦ''n : ∀ t : ℝ, ‖Φ'' t‖ ≤ 2 := fun t => by rw [Complex.norm_real, Real.norm_eq_abs]; exact edgePhiDeriv2_abs_le_two t
  have hΦ'''n : ∀ t : ℝ, ‖Φ''' t‖ ≤ 7 := fun t => by rw [Complex.norm_real, Real.norm_eq_abs]; exact (hasDerivAt_edgePhiDeriv2 t).2.2
  have hLm2 : (L ^ (2 : ℕ))⁻¹ = L ^ (-2 : ℝ) := by rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpowk : ∀ t ∈ Icc (-T) T, ∀ (x : ℂ) {k : ℕ} {B : ℝ}, 2 ≤ k → ‖x‖ ≤ B * (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) →
      ‖x / Φ' t ^ k‖ ≤ 16 * B * L ^ (-2 : ℝ) * (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) := fun t ht x {k B} hk hx => by
    have hpk : (L / 4) ^ 2 ≤ ‖Φ' t‖ ^ k := (pow_le_pow_right₀ (by linarith) hk).trans (pow_le_pow_left₀ (by linarith) (hΦ'n t ht) k)
    rw [norm_div, norm_pow]; exact (div_le_div₀ ((norm_nonneg x).trans hx) hx (by positivity) hpk).trans_eq (by rw [← hLm2]; ring)
  have hb_u1 : ∀ t ∈ Icc (-T) T, ‖u₁ t‖ ≤ 4 * A * L⁻¹ * (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) := fun t ht => by
    have ha0 := ha_bd 0 (by decide) t; rw [iteratedDeriv_zero] at ha0; rw [show u₁ t = a t / Φ' t from rfl, norm_div]
    exact (div_le_div₀ (mul_nonneg hA (by positivity)) ha0 (by linarith) (hΦ'n t ht)).trans_eq (by ring)
  have hb_u2 : ∀ t ∈ Icc (-T) T, ‖u₂ t‖ ≤ 48 * A * L ^ (-2 : ℝ) * (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) := fun t ht => by
    have ha0 := ha_bd 0 (by decide) t; rw [iteratedDeriv_zero] at ha0; have ha1 := ha_bd 1 (by decide) t; rw [iteratedDeriv_one] at ha1
    have h1 := hpowk t ht (deriv a t) (B := A) (by decide : 2 ≤ 2) ha1
    have h2 := hpowk t ht (a t * Φ'' t) (B := 2 * A) (by decide : 2 ≤ 3) (by rw [norm_mul]; exact (mul_le_mul ha0 (hΦ''n t) (norm_nonneg _) (mul_nonneg hA (by positivity))).trans_eq (by ring))
    dsimp [u₂]; exact (norm_sub_le _ _).trans (by linarith)
  have hb_u2' : ∀ t ∈ Icc (-T) T, ‖u₂' t‖ ≤ 416 * A * L ^ (-2 : ℝ) * (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) := fun t ht => by
    have hne' : Φ' t ≠ 0 := hΦ'_ne t ht
    have hrew : u₂' t = (iteratedDeriv 2 a t / Φ' t ^ 2 - 2 * (deriv a t * Φ'' t) / Φ' t ^ 3) -
        (deriv a t * Φ'' t / Φ' t ^ 3 + a t * Φ''' t / Φ' t ^ 3 - 3 * (a t * Φ'' t ^ 2) / Φ' t ^ 4) := by dsimp [u₂']; field_simp [hne']
    have ha0 := ha_bd 0 (by decide) t; rw [iteratedDeriv_zero] at ha0; have ha1 := ha_bd 1 (by decide) t; rw [iteratedDeriv_one] at ha1
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h3n : ‖(3 : ℂ)‖ = 3 := by norm_num
    have hnnA : 0 ≤ A * (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) := mul_nonneg hA (by positivity)
    have h1 := hpowk t ht (iteratedDeriv 2 a t) (B := A) (by decide : 2 ≤ 2) (ha_bd 2 (by decide) t)
    have h2 := hpowk t ht (2 * (deriv a t * Φ'' t)) (B := 4 * A) (by decide : 2 ≤ 3) (by rw [norm_mul, norm_mul, h2n]; exact (mul_le_mul_of_nonneg_left (mul_le_mul ha1 (hΦ''n t) (norm_nonneg _) hnnA) (by norm_num)).trans_eq (by ring))
    have h3 := hpowk t ht (deriv a t * Φ'' t) (B := 2 * A) (by decide : 2 ≤ 3) (by rw [norm_mul]; exact (mul_le_mul ha1 (hΦ''n t) (norm_nonneg _) hnnA).trans_eq (by ring))
    have h4 := hpowk t ht (a t * Φ''' t) (B := 7 * A) (by decide : 2 ≤ 3) (by rw [norm_mul]; exact (mul_le_mul ha0 (hΦ'''n t) (norm_nonneg _) hnnA).trans_eq (by ring))
    have h5 := hpowk t ht (3 * (a t * Φ'' t ^ 2)) (B := 12 * A) (by decide : 2 ≤ 4) (by rw [norm_mul, norm_mul, norm_pow, h3n]; exact (mul_le_mul_of_nonneg_left (mul_le_mul ha0 (pow_le_pow_left₀ (norm_nonneg (Φ'' t)) (hΦ''n t) 2) (by positivity) hnnA) (by norm_num)).trans_eq (by ring))
    rw [hrew]; refine ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)))).trans ?_; linarith
  have hc_E : Continuous fun t : ℝ => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgePhi L t).continuousAt)))
  have hnorm_E : ∀ t : ℝ, ‖Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))‖ = 1 := fun t => by
    rw [show Complex.I * (c : ℂ) * (edgePhi L t : ℂ) = ((c * edgePhi L t : ℝ) : ℂ) * Complex.I by push_cast; ring]; exact Complex.norm_exp_ofReal_mul_I _
  have hc_bd : ‖-Complex.I / (c : ℂ)‖ = c⁻¹ := by rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_pos, one_div]
  have hc_cmp : c⁻¹ ≤ c ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_neg_one c]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hL_mul : L⁻¹ * L⁻¹ = L ^ (-2 : ℝ) := by rw [← Real.rpow_neg_one L, ← Real.rpow_add (by linarith)]; norm_num
  have hL_cmp2 : L ^ (-2 : ℝ) ≤ L ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hb_int2 : ‖∫ t in -T..T, u₂' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))‖ ≤ 416 * Real.pi * A * L ^ (-2 : ℝ) := by
    have hdec : IntervalIntegrable (fun t : ℝ => (416 * A * L ^ (-2 : ℝ)) * (1 + t ^ 2) ^ (-(3 / 2 : ℝ))) volume (-T) T :=
      ((Continuous.rpow (by fun_prop) continuous_const (fun _ => Or.inl (by positivity))).const_mul _).intervalIntegrable (-T) T
    have hm : ∫ t in -T..T, ‖u₂' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))‖ ≤ (416 * A * L ^ (-2 : ℝ)) * ∫ t in -T..T, (1 + t ^ 2) ^ (-(3 / 2 : ℝ)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hTT ((hu₂'_cont.mul hc_E.continuousOn).norm.intervalIntegrable_of_Icc hTT)
        hdec fun t ht => by rw [norm_mul, hnorm_E t, mul_one]; exact hb_u2' t ht
    exact (intervalIntegral.norm_integral_le_integral_norm hTT).trans (hm.trans ((mul_le_mul_of_nonneg_left (integral_one_add_sq_neg_three_halves_le_pi hTT) (mul_nonneg (mul_nonneg (by norm_num) hA) (by positivity))).trans_eq (by ring)))
  have hnorm_s2 : ‖∫ t in -T..T, u₁' t * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))‖ ≤ (96 + 416 * Real.pi) * A * c⁻¹ * L ^ (-2 : ℝ) := by
    rw [hstep2, norm_mul, hc_bd]
    have hT_le1 : (1 + T ^ 2) ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg T]) (by norm_num)
    have h48_nn : 0 ≤ 48 * A * L ^ (-2 : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hA) (by positivity)
    have hbT : ‖u₂ T‖ ≤ 48 * A * L ^ (-2 : ℝ) := (hb_u2 T (right_mem_Icc.mpr hTT)).trans (mul_le_of_le_one_right h48_nn hT_le1)
    have hbmT : ‖u₂ (-T)‖ ≤ 48 * A * L ^ (-2 : ℝ) := (hb_u2 (-T) (left_mem_Icc.mpr hTT)).trans (mul_le_of_le_one_right h48_nn (by simpa only [neg_sq] using hT_le1))
    let E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L t : ℂ))
    have hbT' : ‖u₂ T * E T‖ ≤ 48 * A * L ^ (-2 : ℝ) := by rw [norm_mul, hnorm_E T, mul_one]; exact hbT
    have hbmT' : ‖u₂ (-T) * E (-T)‖ ≤ 48 * A * L ^ (-2 : ℝ) := by rw [norm_mul, hnorm_E (-T), mul_one]; exact hbmT
    have htri : ‖u₂ T * E T - u₂ (-T) * E (-T) - ∫ t in -T..T, u₂' t * E t‖ ≤ (96 + 416 * Real.pi) * A * L ^ (-2 : ℝ) :=
      ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) hb_int2)).trans (by linarith)
    exact (mul_le_mul_of_nonneg_left htri (by positivity)).trans_eq (by ring)
  have hT_dec : (1 + T ^ 2) ^ (-(3 / 2 : ℝ)) ≤ 2 * L⁻¹ :=
    ((Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hT_pos) (by linarith) (by norm_num)).trans_eq (by rw [← Real.rpow_natCast, ← Real.rpow_mul hT_pos.le]; norm_num)).trans
      ((by rw [← Real.rpow_neg_one T]; exact Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (by linarith)) (by norm_num) : T ^ (-3 : ℝ) ≤ T⁻¹).trans
        ((inv_anti₀ (by linarith : 0 < L / 2) (by linarith [Real.add_one_le_exp (L / 2)] : L / 2 ≤ T)).trans_eq (by ring)))
  have hb1 : ∀ t ∈ Icc (-T) T, |t| = T → ‖u₁ t‖ ≤ 8 * A * L ^ (-2 : ℝ) := fun t ht habs =>
    ((hb_u1 t ht).trans_eq (by rw [← sq_abs t, habs])).trans ((mul_le_mul_of_nonneg_left hT_dec (by positivity)).trans_eq (by rw [← hL_mul]; ring))
  rw [hstep1, norm_mul, hc_bd]
  let E : ℝ → ℂ := fun s => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L s : ℂ))
  have hbT1 : ‖u₁ T * E T‖ ≤ 8 * A * L ^ (-2 : ℝ) := by rw [norm_mul, hnorm_E T, mul_one]; exact hb1 T (right_mem_Icc.mpr hTT) (abs_of_pos hT_pos)
  have hbmT1 : ‖u₁ (-T) * E (-T)‖ ≤ 8 * A * L ^ (-2 : ℝ) := by rw [norm_mul, hnorm_E (-T), mul_one]; exact hb1 (-T) (left_mem_Icc.mpr hTT) ((abs_neg T).trans (abs_of_pos hT_pos))
  have hinner : ‖u₁ T * E T - u₁ (-T) * E (-T) - ∫ t in -T..T, u₁' t * E t‖ ≤ 16 * A * L ^ (-2 : ℝ) + (96 + 416 * Real.pi) * A * c⁻¹ * L ^ (-2 : ℝ) :=
    ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) hnorm_s2)).trans (by linarith)
  have hpi4 : Real.pi ≤ 4 := by linarith [Real.pi_lt_d2]
  have hcc : c⁻¹ * c⁻¹ ≤ (2 : ℝ)⁻¹ * c ^ (-(1 / 2 : ℝ)) := mul_le_mul (inv_anti₀ (by norm_num) hc) hc_cmp (by positivity) (by norm_num)
  have hterm1 : 16 * A * c⁻¹ * L ^ (-2 : ℝ) ≤ 16 * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by gcongr
  have hterm2 : (96 + 416 * Real.pi) * A * (c⁻¹ * c⁻¹) * L ^ (-2 : ℝ) ≤ 880 * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) :=
    (show (96 + 416 * Real.pi) * A * (c⁻¹ * c⁻¹) * L ^ (-2 : ℝ) ≤ (96 + 416 * 4) * A * ((2 : ℝ)⁻¹ * c ^ (-(1 / 2 : ℝ))) * L ^ (-(3 / 2 : ℝ)) by gcongr).trans_eq (by ring)
  have htot := (mul_le_mul_of_nonneg_left hinner (by positivity)).trans
    ((by ring : c⁻¹ * (16 * A * L ^ (-2 : ℝ) + (96 + 416 * Real.pi) * A * c⁻¹ * L ^ (-2 : ℝ)) =
      16 * A * c⁻¹ * L ^ (-2 : ℝ) + (96 + 416 * Real.pi) * A * (c⁻¹ * c⁻¹) * L ^ (-2 : ℝ)) ▸ add_le_add hterm1 hterm2)
  have hX_nn : 0 ≤ A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by positivity
  exact htot.trans (by linarith)

private lemma tau0_lt_bound {L : ℝ} (hL : 0 < L) (hL8 : L ≤ 8) : tau0 L < 5000 := by
  have h7000 : 8 < ceEll 7000 := by
    have hth_pos : 0 < Real.tanh 7000 := by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos 7000)
    have hth_lt1 : Real.tanh 7000 < 1 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos 7000), Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-7000 : ℝ)]
    have hdiv : (7000 : ℝ) < 7000 / Real.tanh 7000 := (lt_div_iff₀ hth_pos).mpr (by nlinarith)
    have h8u : Real.exp 8 ≤ (3 : ℝ) ^ 8 := (by rw [← Real.exp_nat_mul]; norm_num : Real.exp 8 = (Real.exp 1) ^ 8) ▸
      pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) 8
    rw [ceEll]; exact (Real.lt_log_iff_exp_lt (div_pos (by norm_num) hth_pos)).mpr (by linarith)
  have hlt : ceEll (Real.pi * tau0 L / 2) < ceEll 7000 := (ceEll_tau0 hL).symm ▸ (hL8.trans_lt h7000)
  have hpi_lt : Real.pi * tau0 L / 2 < 7000 := by
    by_contra hge; push Not at hge
    exact hlt.not_ge (ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr (by norm_num : (0 : ℝ) < 7000))
      (mem_Ioi.mpr (div_pos (mul_pos Real.pi_pos (tau0_pos hL)) two_pos)) hge)
  nlinarith [Real.pi_gt_three]

private lemma dual_phase_integrable {a : ℝ → ℂ} {A c L : ℝ} (ha_cd : ContDiff ℝ 2 a) (hA : 0 ≤ A)
    (ha_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ))) :
    Continuous (fun τ : ℝ => a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) ∧
      Integrable (fun τ : ℝ => a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) := by
  have hc : Continuous fun τ : ℝ => a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) :=
    ha_cd.continuous.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgePhi L t).continuousAt))))
  refine ⟨hc, (integrable_inv_one_add_sq.const_mul A).mono' hc.aestronglyMeasurable (ae_of_all _ fun τ => ?_)⟩
  rw [norm_mul, show Complex.I * (c : ℂ) * (edgePhi L τ : ℂ) = ((c * edgePhi L τ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h0 := ha_bd 0 (by decide) τ; rw [iteratedDeriv_zero] at h0
  exact h0.trans (mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg τ]) (by norm_num : -(3 / 2 : ℝ) ≤ -1)).trans_eq (Real.rpow_neg_one _)) hA)

private lemma dual_phase_regime_small :
    ∃ C > 0, ∀ {a : ℝ → ℂ} {A c L R : ℝ}, ContDiff ℝ 2 a → 0 ≤ A → (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ))) →
      2 ≤ c → 0 < L → L ≤ 8 → 1 ≤ c * L ^ (3 / 2 : ℝ) → 2 * tau0 L ≤ R →
      ‖∫ τ in -R..R, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤ C * A * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  let ν₁ : ℝ := Real.log (3 / 2) * (149 / 8000); have hν₁ : 0 < ν₁ := mul_pos (Real.log_pos (by norm_num)) (by norm_num)
  let C₁ : ℝ := 3 * (1 + Real.pi) / ν₁; let c₂ : ℝ := 9 / 1280000000; let C₂ : ℝ := 8 * (1 + Real.pi) / Real.sqrt c₂
  refine ⟨8 ^ (5 / 4 : ℝ) * (4 * C₁ + 2 * C₂), by positivity, fun {a} {A c L R} ha_cd hA ha_bd hc hL hL8 hcL hR => ?_⟩
  let τ₀ := tau0 L; have hτ₀ := tau0_pos hL; have hτ₀_eq := ceEll_tau0 hL
  have hτ₀_lt := tau0_lt_bound hL hL8; have hτ₀_lb := tau0_gt_sqrt hL hτ₀ hτ₀_eq; have hc_pos : 0 < c := by linarith
  have hP2 := edgePhiDeriv_phase_floor_P2 hL hτ₀ hτ₀_eq
  have hmin_ge : ν₁ * L ≤ Real.log (3 / 2) * min (L / 4) (149 / 1000) := by
    dsimp [ν₁]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_min (by linarith) (by linarith)) (Real.log_pos (by norm_num)).le
  have hinv_cL : (c * L)⁻¹ ≤ c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := by
    have hcr : c⁻¹ = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := (Real.rpow_neg_one c).symm.trans (by rw [← Real.rpow_add hc_pos]; norm_num)
    have hLr : L⁻¹ = L ^ (-(1 / 4 : ℝ)) * L ^ (-(3 / 4 : ℝ)) := (Real.rpow_neg_one L).symm.trans (by rw [← Real.rpow_add hL]; norm_num)
    have h1 : (c * L)⁻¹ = c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) * (c * L ^ (3 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow hc_pos.le (Real.rpow_nonneg hL.le _), ← Real.rpow_mul hL.le, mul_inv, hcr, hLr]; norm_num; ring
    rw [h1]; exact mul_le_of_le_one_right (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos hcL (by norm_num))
  have hM_all : ∀ x : ℝ, ‖a x‖ ≤ A := fun x => by
    have h0 := ha_bd 0 (by decide) x; rw [iteratedDeriv_zero] at h0
    exact h0.trans (mul_le_of_le_one_right hA (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg x]) (by norm_num)))
  let I : ℝ → ℝ → ℂ := fun u v => ∫ τ in u..v, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
  have hvdc1 : ∀ u v : ℝ, u ≤ v → (MonotoneOn (edgePhiDeriv L) (Icc u v) ∨ AntitoneOn (edgePhiDeriv L) (Icc u v)) →
      (∀ x ∈ Icc u v, ν₁ * L ≤ |edgePhiDeriv L x|) → ‖I u v‖ ≤ C₁ * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := fun u v huv hmono hlb =>
    (osc_vdc1_bound huv hc_pos (mul_pos hν₁ hL) hmono hlb ha_cd (fun x _ => hM_all x)
      (eVariationOn_decay_le hA ha_cd ha_bd huv).1 (eVariationOn_decay_ne_top hA ha_cd huv)).trans
      (by calc 3 * (A + A * Real.pi) / (c * (ν₁ * L)) = C₁ * A * (c * L)⁻¹ := by dsimp [C₁]; ring
        _ ≤ C₁ * A * (c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ))) := by gcongr
        _ = _ := by ring)
  have hband_lb : ∀ x : ℝ, 3 * τ₀ / 8 ≤ |x| → |x| ≤ 2 * τ₀ → c₂ * Real.sqrt L ≤ |edgePhiDeriv2 x| := fun x hlo hhi => by
    have hu_lb : Real.sqrt L / 4 ≤ 3 * τ₀ / 8 := by
      have hr : 2 * 1.7 / 3.15 ≤ 2 * Real.sqrt 3 / Real.pi := by gcongr; exact Real.le_sqrt_of_sq_le (by norm_num); exact Real.pi_lt_d2.le
      nlinarith [(mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _)).trans hτ₀_lb.le]
    have hpi6 : (6 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hden : 6 + Real.pi ^ 2 * (3 * τ₀ / 8) ^ 2 ≤ 40000000 := by
      have h10 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
      have h36 : (3 * τ₀ / 8) ^ 2 ≤ 3600000 := by nlinarith
      nlinarith
    calc c₂ * Real.sqrt L = (3 / 16 : ℝ) * (6 * (Real.sqrt L / 4) / 40000000) := by dsimp [c₂]; ring
      _ ≤ (3 / 16 : ℝ) * (Real.pi ^ 2 * (3 * τ₀ / 8) / (6 + Real.pi ^ 2 * (3 * τ₀ / 8) ^ 2)) := by gcongr
      _ ≤ |edgePhiDeriv2 x| := abs_edgePhiDeriv2_band_ge hτ₀ hlo hhi
  have hvdc2 : ∀ u v : ℝ, u ≤ v → (MonotoneOn (edgePhiDeriv L) (Icc u v) ∨ AntitoneOn (edgePhiDeriv L) (Icc u v)) →
      (∀ x ∈ Icc u v, 3 * τ₀ / 8 ≤ |x| ∧ |x| ≤ 2 * τ₀) → ‖I u v‖ ≤ C₂ * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := fun u v huv hmono hxy => by
    have hb := osc_vdc2_bound huv hc_pos (mul_pos (by dsimp [c₂]; positivity) (Real.sqrt_pos.mpr hL)) hmono (fun x hx => hband_lb x (hxy x hx).1 (hxy x hx).2)
      ha_cd (fun x _ => hM_all x) (eVariationOn_decay_le hA ha_cd ha_bd huv).1 (eVariationOn_decay_ne_top hA ha_cd huv)
    have hsq : Real.sqrt (c * (c₂ * Real.sqrt L)) = Real.sqrt c₂ * c ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
      rw [show c * (c₂ * Real.sqrt L) = c₂ * (c * Real.sqrt L) by ring, Real.sqrt_mul (by dsimp [c₂]; positivity),
        Real.sqrt_mul hc_pos.le, Real.sqrt_eq_rpow c, Real.sqrt_eq_rpow L, Real.sqrt_eq_rpow (L ^ (1 / 2 : ℝ)), ← Real.rpow_mul hL.le]; norm_num; ring
    refine hb.trans_eq ?_; rw [hsq, show 8 * (A + A * Real.pi) / (Real.sqrt c₂ * c ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ)) =
      C₂ * A * (c ^ (1 / 2 : ℝ))⁻¹ * (L ^ (1 / 4 : ℝ))⁻¹ by dsimp [C₂]; ring, ← Real.rpow_neg hc_pos.le, ← Real.rpow_neg hL.le]
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun τ => a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) volume u v :=
    fun u v => (dual_phase_integrable ha_cd hA ha_bd).1.intervalIntegrable u v
  have hsplit : I (-R) R = I (-R) (-(2 * τ₀)) + I (-(2 * τ₀)) (-(τ₀ / 2)) + I (-(τ₀ / 2)) 0 + I 0 (τ₀ / 2) + I (τ₀ / 2) (2 * τ₀) + I (2 * τ₀) R := by
    dsimp [I]; rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _), intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _), intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hb1 := hvdc1 (-R) (-(2 * τ₀)) (by linarith) (Or.inl (edgePhiDeriv_monotoneOn_nonpos (by linarith)))
    fun x hx => hmin_ge.trans ((hP2.2 x (by dsimp [τ₀] at *; rw [abs_of_nonpos (hx.2.trans (by linarith))]; linarith [hx.2])).trans (neg_le_abs _))
  have hb2 := hvdc2 (-(2 * τ₀)) (-(τ₀ / 2)) (by linarith) (Or.inl (edgePhiDeriv_monotoneOn_nonpos (by linarith)))
    fun x hx => by dsimp [τ₀] at *; rw [abs_of_nonpos (hx.2.trans (by linarith))]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hb3 := hvdc1 (-(τ₀ / 2)) 0 (by linarith) (Or.inl (edgePhiDeriv_monotoneOn_nonpos le_rfl))
    fun x hx => hmin_ge.trans ((hP2.1 x (by dsimp [τ₀] at *; exact abs_le.mpr ⟨hx.1, hx.2.trans (by linarith)⟩)).trans (le_abs_self _))
  have hb4 := hvdc1 0 (τ₀ / 2) (by linarith) (Or.inr (edgePhiDeriv_antitoneOn_nonneg le_rfl))
    fun x hx => hmin_ge.trans ((hP2.1 x (by dsimp [τ₀] at *; exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)).trans (le_abs_self _))
  have hb5 := hvdc2 (τ₀ / 2) (2 * τ₀) (by linarith) (Or.inr (edgePhiDeriv_antitoneOn_nonneg (by linarith)))
    fun x hx => by dsimp [τ₀] at *; rw [abs_of_nonneg (by linarith [hx.1])]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hb6 := hvdc1 (2 * τ₀) R hR (Or.inr (edgePhiDeriv_antitoneOn_nonneg (by linarith)))
    fun x hx => hmin_ge.trans ((hP2.2 x (by dsimp [τ₀] at *; rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1])).trans (neg_le_abs _))
  have hsum_bd : ‖I (-R) R‖ ≤ (4 * C₁ + 2 * C₂) * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := by
    rw [hsplit]; have := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hb3)) hb4)) hb5)) hb6); linarith
  have hmin_L : L ^ (-(1 / 4 : ℝ)) ≤ 8 ^ (5 / 4 : ℝ) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
    rcases le_or_gt L 1 with hL1 | hL1
    · rw [min_eq_left (Real.rpow_le_rpow_of_exponent_ge hL hL1 (by norm_num))]; exact le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (by norm_num) (by norm_num))
    · rw [min_eq_right (Real.rpow_le_rpow_of_exponent_le hL1.le (by norm_num)),
        show L ^ (-(1 / 4 : ℝ)) = L ^ (5 / 4 : ℝ) * L ^ (-(3 / 2 : ℝ)) from by rw [← Real.rpow_add hL]; norm_num]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hL.le hL8 (by norm_num)) (by positivity)
  exact hsum_bd.trans ((mul_le_mul_of_nonneg_left hmin_L (by positivity)).trans_eq (by ring))

private lemma dual_phase_regime_large :
    ∃ C > 0, ∀ {a : ℝ → ℂ} {A c L R : ℝ}, ContDiff ℝ 2 a → 0 ≤ A → (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ))) →
      2 ≤ c → 8 < L → 2 * tau0 L ≤ R →
      ‖∫ τ in -R..R, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤ C * A * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  let ν₀ : ℝ := Real.log (3 / 2) * (149 / 1000); have hν₀ : 0 < ν₀ := mul_pos (Real.log_pos (by norm_num)) (by norm_num)
  let C₁ : ℝ := 18 / ν₀; let C₂ : ℝ := 160 * (100 / 59 : ℝ) ^ (3 / 2 : ℝ)
  refine ⟨900 + 4 * C₁ + 2 * C₂, by positivity, fun {a} {A c L R} ha_cd hA ha_bd hc hL hR => ?_⟩
  let τ₀ := tau0 L; let T := Real.exp (L / 2); have hL_pos : 0 < L := by linarith
  have hc_pos : 0 < c := by linarith
  have hτ₀ := tau0_pos hL_pos; have hτ₀_eq := ceEll_tau0 hL_pos; have hτ₀_exp := (tau0_gt_exp (by linarith) hτ₀ hτ₀_eq).2; have hT_pos : 0 < T := Real.exp_pos _
  have hT_gt : 16 < T := by
    have h2e : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h16 : (16 : ℝ) < Real.exp (4 : ℝ) := by
      calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
        _ < (Real.exp 1) ^ (4 : ℕ) := pow_lt_pow_left₀ h2e (by norm_num) (by norm_num)
        _ = Real.exp (4 : ℝ) := by rw [← Real.exp_nat_mul]; norm_num
    exact h16.trans (Real.exp_lt_exp.mpr (by linarith))
  have hTT : T * T = Real.exp L := by rw [← Real.exp_add]; congr 1; ring
  have hT_half : 2 * T ≤ τ₀ := by nlinarith [hTT]
  have hτ₀_L : (59 / 100 : ℝ) * L ≤ τ₀ := by linarith [Real.add_one_le_exp L]
  have hτ₀_gt1 : 1 < τ₀ := by linarith
  have hmin_eq : min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) = L ^ (-(3 / 2 : ℝ)) := min_eq_right (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have hc_cmp : c⁻¹ ≤ c ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_neg_one c]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hT_sq : T ^ (-2 : ℝ) ≤ 4 * L ^ (-(3 / 2 : ℝ)) := by
    have hT2 : (L / 2) ^ 2 ≤ T ^ 2 := by gcongr; linarith [Real.add_one_le_exp (L / 2)]
    have hTm : T ^ (-2 : ℝ) = (T ^ 2)⁻¹ := by rw [Real.rpow_neg hT_pos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hLm : L ^ (-2 : ℝ) = (L ^ 2)⁻¹ := by rw [Real.rpow_neg hL_pos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hinv : (T ^ 2)⁻¹ ≤ 4 * (L ^ 2)⁻¹ := by rw [← show ((L / 2) ^ 2)⁻¹ = 4 * (L ^ 2)⁻¹ by ring]; exact inv_anti₀ (by positivity) hT2
    have hL23 := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ L) (by norm_num : (-2 : ℝ) ≤ -(3 / 2 : ℝ))
    linarith
  have hP2 := edgePhiDeriv_phase_floor_P2 hL_pos hτ₀ hτ₀_eq
  have hν₀_min : ν₀ ≤ Real.log (3 / 2) * min (L / 4) (149 / 1000) := by dsimp [ν₀]; rw [min_eq_right (by linarith)]
  let I : ℝ → ℝ → ℂ := fun u v => ∫ τ in u..v, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
  have hvdc1_T : ∀ u v : ℝ, u ≤ v → (MonotoneOn (edgePhiDeriv L) (Icc u v) ∨ AntitoneOn (edgePhiDeriv L) (Icc u v)) →
      (∀ x ∈ Icc u v, T ≤ |x|) → (∀ x ∈ Icc u v, ν₀ ≤ |edgePhiDeriv L x|) → ‖I u v‖ ≤ C₁ * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) :=
    fun u v huv hmono hT_abs hlb => by
      have hM : ∀ x ∈ Icc u v, ‖a x‖ ≤ A * T ^ (-2 : ℝ) := fun x hx => by
        have h0 := ha_bd 0 (by decide) x; rw [iteratedDeriv_zero] at h0
        have h1x : T ^ 2 ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, hT_abs x hx]
        have hd : (1 + x ^ 2) ^ (-(3 / 2 : ℝ)) ≤ T ^ (-3 : ℝ) :=
          (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hT_pos) h1x (by norm_num)).trans_eq (by rw [← Real.rpow_natCast, ← Real.rpow_mul hT_pos.le]; norm_num)
        exact h0.trans (mul_le_mul_of_nonneg_left (hd.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))) hA)
      have hV : (eVariationOn a (Icc u v)).toReal ≤ (1 / 2) * A * T ^ (-2 : ℝ) :=
        (eVariationOn_tail_abs_le hA hT_pos ha_cd ha_bd huv hT_abs).trans_eq (by rw [Real.rpow_neg hT_pos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring)
      exact (osc_vdc1_bound huv hc_pos hν₀ hmono hlb ha_cd hM hV (eVariationOn_decay_ne_top hA ha_cd huv)).trans
        (by calc 3 * (A * T ^ (-2 : ℝ) + 1 / 2 * A * T ^ (-2 : ℝ)) / (c * ν₀) = (9 / (2 * ν₀)) * A * c⁻¹ * T ^ (-2 : ℝ) := by ring
          _ ≤ (9 / (2 * ν₀)) * A * c ^ (-(1 / 2 : ℝ)) * (4 * L ^ (-(3 / 2 : ℝ))) := by gcongr
          _ = C₁ * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by dsimp [C₁]; ring)
  have hvdc2_band : ∀ u v : ℝ, u ≤ v → (MonotoneOn (edgePhiDeriv L) (Icc u v) ∨ AntitoneOn (edgePhiDeriv L) (Icc u v)) →
      (∀ x ∈ Icc u v, τ₀ / 2 ≤ |x| ∧ |x| ≤ 2 * τ₀) → ‖I u v‖ ≤ C₂ * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) :=
    fun u v huv hmono hxy => by
      have hM : ∀ x ∈ Icc u v, ‖a x‖ ≤ 8 * A * τ₀ ^ (-2 : ℝ) := fun x hx => by
        have h0 := ha_bd 0 (by decide) x; rw [iteratedDeriv_zero] at h0
        have h1x : (τ₀ / 2) ^ 2 ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, (hxy x hx).1]
        have hsq3 : ((τ₀ / 2) ^ (2 : ℕ)) ^ (-(3 / 2 : ℝ)) = (τ₀ / 2) ^ (-3 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        have hd : (1 + x ^ 2) ^ (-(3 / 2 : ℝ)) ≤ (τ₀ / 2) ^ (-3 : ℝ) := (Real.rpow_le_rpow_of_nonpos (by positivity) h1x (by norm_num)).trans_eq hsq3
        have h3e : (τ₀ / 2) ^ (-3 : ℝ) = 8 * τ₀ ^ (-3 : ℝ) := by
          rw [Real.rpow_neg (by positivity), Real.rpow_neg hτ₀.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast, Real.rpow_natCast, div_pow, inv_div, div_eq_mul_inv]; norm_num; ring
        have h32 := Real.rpow_le_rpow_of_exponent_le hτ₀_gt1.le (by norm_num : (-3 : ℝ) ≤ -2)
        exact h0.trans (by
          calc A * (1 + x ^ 2) ^ (-(3 / 2 : ℝ)) ≤ A * (8 * τ₀ ^ (-3 : ℝ)) := by gcongr; exact hd.trans_eq h3e
            _ = 8 * A * τ₀ ^ (-3 : ℝ) := by ring
            _ ≤ 8 * A * τ₀ ^ (-2 : ℝ) := by gcongr)
      have hV : (eVariationOn a (Icc u v)).toReal ≤ 2 * A * τ₀ ^ (-2 : ℝ) :=
        (eVariationOn_tail_abs_le hA (half_pos hτ₀) ha_cd ha_bd huv fun x hx => (hxy x hx).1).trans_eq (by rw [Real.rpow_neg hτ₀.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring)
      have hlb : ∀ x ∈ Icc u v, (4 * τ₀)⁻¹ ≤ |edgePhiDeriv2 x| := fun x hx => by
        have hpi9 : (6 : ℝ) ≤ Real.pi ^ 2 * (3 * τ₀ / 8) ^ 2 := by
          have : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
          have : (1 : ℝ) ≤ 3 * τ₀ / 8 := by linarith
          nlinarith
        have h1 : (4 * τ₀)⁻¹ = (3 / 16 : ℝ) * (Real.pi ^ 2 * (3 * τ₀ / 8) / (2 * (Real.pi ^ 2 * (3 * τ₀ / 8) ^ 2))) := by field_simp [hτ₀.ne', Real.pi_ne_zero]; ring
        have h2 : (3 / 16 : ℝ) * (Real.pi ^ 2 * (3 * τ₀ / 8) / (2 * (Real.pi ^ 2 * (3 * τ₀ / 8) ^ 2))) ≤
            (3 / 16 : ℝ) * (Real.pi ^ 2 * (3 * τ₀ / 8) / (6 + Real.pi ^ 2 * (3 * τ₀ / 8) ^ 2)) := by gcongr; linarith
        exact (h1 ▸ h2).trans (abs_edgePhiDeriv2_band_ge hτ₀ (by linarith [(hxy x hx).1]) (hxy x hx).2)
      have hb := osc_vdc2_bound huv hc_pos (by positivity) hmono hlb ha_cd hM hV (eVariationOn_decay_ne_top hA ha_cd huv)
      have hsq : Real.sqrt (c * (4 * τ₀)⁻¹) = (2 : ℝ)⁻¹ * c ^ (1 / 2 : ℝ) * τ₀ ^ (-(1 / 2 : ℝ)) := by
        rw [mul_inv, Real.sqrt_mul hc_pos.le, Real.sqrt_mul (by norm_num), Real.sqrt_inv (4 : ℝ), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num), Real.sqrt_eq_rpow c, Real.sqrt_inv τ₀, Real.sqrt_eq_rpow τ₀, Real.rpow_neg hτ₀.le]; ring
      have hτ32 : τ₀ ^ (-(3 / 2 : ℝ)) ≤ (100 / 59 : ℝ) ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ)) :=
        (Real.rpow_le_rpow_of_nonpos (by positivity) hτ₀_L (by norm_num)).trans_eq (by
          rw [Real.mul_rpow (by norm_num) hL_pos.le, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), inv_div])
      have hτ_inv : (τ₀ ^ (-(1 / 2 : ℝ)))⁻¹ = τ₀ ^ (1 / 2 : ℝ) := by rw [Real.rpow_neg hτ₀.le, inv_inv]
      have hτ_comb : τ₀ ^ (-2 : ℝ) * τ₀ ^ (1 / 2 : ℝ) = τ₀ ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hτ₀]; norm_num; rfl
      calc ‖I u v‖ ≤ 8 * (8 * A * τ₀ ^ (-2 : ℝ) + 2 * A * τ₀ ^ (-2 : ℝ)) / Real.sqrt (c * (4 * τ₀)⁻¹) := hb
        _ = 160 * A * c ^ (-(1 / 2 : ℝ)) * (τ₀ ^ (-2 : ℝ) * τ₀ ^ (1 / 2 : ℝ)) := by
            rw [hsq, div_eq_mul_inv, mul_inv, mul_inv, inv_inv, ← Real.rpow_neg hc_pos.le, hτ_inv]; ring
        _ ≤ 160 * A * c ^ (-(1 / 2 : ℝ)) * ((100 / 59 : ℝ) ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ))) := by rw [hτ_comb]; gcongr
        _ = C₂ * A * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by dsimp [C₂]; ring
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun τ => a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) volume u v :=
    fun u v => (dual_phase_integrable ha_cd hA ha_bd).1.intervalIntegrable u v
  have hsplit : I (-R) R = I (-R) (-(2 * τ₀)) + I (-(2 * τ₀)) (-(τ₀ / 2)) + I (-(τ₀ / 2)) (-T) + I (-T) T + I T (τ₀ / 2) + I (τ₀ / 2) (2 * τ₀) + I (2 * τ₀) R := by
    dsimp [I]; rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _), intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _), intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _), intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hb1 := hvdc1_T (-R) (-(2 * τ₀)) (by linarith) (Or.inl (edgePhiDeriv_monotoneOn_nonpos (by linarith)))
    (fun x hx => by dsimp [τ₀, T] at *; rw [abs_of_nonpos (hx.2.trans (by linarith))]; linarith [hx.2])
    (fun x hx => hν₀_min.trans ((hP2.2 x (by dsimp [τ₀] at *; rw [abs_of_nonpos (hx.2.trans (by linarith))]; linarith [hx.2])).trans (neg_le_abs _)))
  have hb2 := hvdc2_band (-(2 * τ₀)) (-(τ₀ / 2)) (by linarith) (Or.inl (edgePhiDeriv_monotoneOn_nonpos (by linarith)))
    (fun x hx => by dsimp [τ₀] at *; rw [abs_of_nonpos (hx.2.trans (by linarith))]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hb3 := hvdc1_T (-(τ₀ / 2)) (-T) (by linarith) (Or.inl (edgePhiDeriv_monotoneOn_nonpos (by linarith)))
    (fun x hx => by dsimp [T] at *; rw [abs_of_nonpos (hx.2.trans (by linarith))]; linarith [hx.2])
    (fun x hx => hν₀_min.trans ((hP2.1 x (by dsimp [τ₀] at *; exact abs_le.mpr ⟨hx.1, hx.2.trans (by linarith)⟩)).trans (le_abs_self _)))
  have hb4 := osc_twice_ibp_center hc hL hA ha_cd ha_bd
  have hb5 := hvdc1_T T (τ₀ / 2) (by linarith) (Or.inr (edgePhiDeriv_antitoneOn_nonneg hT_pos.le))
    (fun x hx => by dsimp [T] at *; rw [abs_of_nonneg (hT_pos.le.trans hx.1)]; exact hx.1)
    (fun x hx => hν₀_min.trans ((hP2.1 x (by dsimp [τ₀] at *; exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)).trans (le_abs_self _)))
  have hb6 := hvdc2_band (τ₀ / 2) (2 * τ₀) (by linarith) (Or.inr (edgePhiDeriv_antitoneOn_nonneg (by linarith)))
    (fun x hx => by dsimp [τ₀] at *; rw [abs_of_nonneg (by linarith [hx.1])]; exact ⟨hx.1, hx.2⟩)
  have hb7 := hvdc1_T (2 * τ₀) R hR (Or.inr (edgePhiDeriv_antitoneOn_nonneg (by linarith)))
    (fun x hx => by dsimp [τ₀, T] at *; rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1])
    (fun x hx => hν₀_min.trans ((hP2.2 x (by dsimp [τ₀] at *; rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1])).trans (neg_le_abs _)))
  rw [hmin_eq]; change ‖I (-R) R‖ ≤ _; rw [hsplit]
  have := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hb3)) hb4)) hb5)) hb6)) hb7)
  linarith

/-- **Lemma `O.3(1)` core dual-phase bound (`u1c_o1_upper.tex`, `(u1co:dual-phase)`):**
for `c ≥ 2`, `L > 0` with `c L^{3/2} ≥ 1`, and any `C²` amplitude `a` with `‖a^{(r)}(τ)‖ ≤ A (1 + τ²)^{-3/2}`
(`r ≤ 2`), `‖∫ a(τ) e^{i c Φ(τ; L)} dτ‖ ≤ C A c^{-1/2} min(L^{-1/4}, L^{-3/2})`. -/
theorem dual_phase_oscillatory_bound :
    ∃ C > 0, ∀ {a : ℝ → ℂ} {A c L : ℝ},
      ContDiff ℝ 2 a → 0 ≤ A → (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ))) →
      2 ≤ c → 0 < L → 1 ≤ c * L ^ (3 / 2 : ℝ) →
      ‖∫ τ : ℝ, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤ C * A * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨Cs, _, hs⟩ := dual_phase_regime_small; obtain ⟨Cl, hCl, hl⟩ := dual_phase_regime_large
  refine ⟨max Cs Cl, lt_max_of_lt_right hCl, fun {a} {A c L} ha_cd hA ha_bd hc hL hcL => ?_⟩
  have htend : Tendsto (fun R : ℝ => ‖∫ τ in -R..R, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖)
      atTop (𝓝 ‖∫ τ : ℝ, a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖) :=
    (intervalIntegral_tendsto_integral (dual_phase_integrable ha_cd hA ha_bd).2 tendsto_neg_atTop_atBot tendsto_id).norm
  refine le_of_tendsto htend (eventually_atTop.mpr ⟨2 * tau0 L, fun R hR => ?_⟩)
  rcases le_or_gt L 8 with hL8 | hL8
  · exact (hs ha_cd hA ha_bd hc hL hL8 hcL hR).trans (by gcongr; exact le_max_left _ _)
  · exact (hl ha_cd hA ha_bd hc hL8 hR).trans (by gcongr; exact le_max_right _ _)

/-! ## Section 4: `dualEdgeIntegral`, Lemma `GT.2b(3)` / `(cegt:GT3a)`, and Lemma `O.3(1)` `(e3)` -/

/-- Dual edge integral `c^{1/3} / (2 π ξ_L) ∫ e^{i c Φ(τ; L)} (1 - i τ)^{-1/2} e^{B_c(i τ) - B_c(0)} W(τ) dτ`
where `ξ_L = e^L / π²` (`u1c_o1_upper.tex`, `ce_o1_global_transfer.tex`). -/
noncomputable def dualEdgeIntegral (c L : ℝ) (W : ℝ → ℂ) : ℂ :=
  ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * ((Real.exp L / Real.pi ^ 2 : ℝ) : ℂ)) *
    ∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * W τ) *
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))

private lemma cpow_mul_binet_deriv_bound {μ c : ℝ} (hμ : 0 < μ) (hc : 2 ≤ c) :
    ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => (1 - Complex.I * (τ : ℂ)) ^ (-(μ : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ)))) ∧
      ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r (fun t : ℝ => (1 - Complex.I * (t : ℂ)) ^ (-(μ : ℂ)) * Complex.exp (binetDiff c (Complex.I * (t : ℂ)))) τ‖ ≤
        (8 * (2 ^ μ * Real.exp 1)) * (1 + τ ^ 2) ^ (-(μ / 2)) := by
  let U : Set ℂ := {ω : ℂ | -1 < ω.im}; have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  let F : ℂ → ℂ := fun ω => (1 - Complex.I * ω) ^ (-(μ : ℂ)) * Complex.exp (binetDiff c (Complex.I * ω))
  have h1re : ∀ ω : ℂ, (1 - Complex.I * ω).re = 1 + ω.im := fun ω => by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub, sub_neg_eq_add]
  have hIre : ∀ ω : ℂ, (Complex.I * ω).re = -ω.im := fun ω => by simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub]
  have hre : ∀ ω ∈ U, 0 < (1 - Complex.I * ω).re := fun ω hω => by change -1 < ω.im at hω; rw [h1re]; linarith
  have hF_diff : DifferentiableOn ℂ F U := fun ω hω => by
    have h1 := ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.const_mul Complex.I)).cpow (differentiableAt_const (-(μ : ℂ))) (Or.inl (hre ω hω))
    have hw_re : 0 < ((c : ℂ) * (1 - Complex.I * ω)).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; exact mul_pos (by linarith) (hre ω hω)
    have hbin : DifferentiableAt ℂ (fun z => binetDiff c (Complex.I * z)) ω :=
      ((((binetRem_differentiableOn _ hw_re).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw_re)).comp ω
        (((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.const_mul Complex.I)).const_mul (c : ℂ))).sub_const
        (binetRem (c : ℂ))).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    exact (h1.mul hbin.cexp).differentiableWithinAt
  have hball : ∀ t : ℝ, Metric.closedBall (t : ℂ) (1 / 2) ⊆ U := fun t ω hω => by
    have him : |ω.im| ≤ 1 / 2 := by simpa [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (ω - (t : ℂ))).trans (by simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hω)
    change -1 < ω.im; linarith [(abs_le.mp him).1]
  have hsphere : ∀ (t : ℝ) (ω : ℂ), ω ∈ Metric.sphere (t : ℂ) (1 / 2) → ‖F ω‖ ≤ (2 ^ μ * Real.exp 1) * (1 + t ^ 2) ^ (-(μ / 2)) := fun t ω hω => by
    have hdist : ‖ω - (t : ℂ)‖ ≤ 1 / 2 := by simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hω).le
    have him : |ω.im| ≤ 1 / 2 := by simpa [Complex.sub_im, Complex.ofReal_im, sub_zero] using (Complex.abs_im_le_norm (ω - (t : ℂ))).trans hdist
    have hcp : ‖(1 - Complex.I * ω) ^ (-(μ : ℂ))‖ ≤ 2 ^ μ * (1 + t ^ 2) ^ (-(μ / 2)) := by
      rw [show -(μ : ℂ) = ((-μ : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_real]
      refine (Real.rpow_le_rpow_of_nonpos (by positivity) (norm_one_sub_I_mul_half_ge hdist) (by linarith)).trans_eq ?_
      rw [div_eq_mul_inv, Real.mul_rpow (Real.sqrt_nonneg _) (by norm_num), Real.inv_rpow (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; ring_nf
    have hbin_bd : ‖Complex.exp (binetDiff c (Complex.I * ω))‖ ≤ Real.exp 1 := by
      have hre_lt : (Complex.I * ω).re < 1 := by rw [hIre]; linarith [(abs_le.mp him).1]
      have hbd := binetDiff_norm_le (by linarith : 0 < c) hre_lt
      have h1re_lb : 1 / 2 ≤ 1 - (Complex.I * ω).re := by rw [hIre]; linarith [(abs_le.mp him).1]
      have hnorm : ‖binetDiff c (Complex.I * ω)‖ ≤ 1 := hbd.trans (by
        have h1 : 1 / (1 - (Complex.I * ω).re) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        have h2 : 1 / (12 * c) ≤ 1 / 24 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        calc 1 / (12 * c) * (1 / (1 - (Complex.I * ω).re) + 1) ≤ (1 / 24) * (2 + 1) := by gcongr
          _ ≤ 1 := by norm_num)
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hnorm)
    calc ‖F ω‖ = ‖(1 - Complex.I * ω) ^ (-(μ : ℂ))‖ * ‖Complex.exp (binetDiff c (Complex.I * ω))‖ := norm_mul _ _
      _ ≤ (2 ^ μ * (1 + t ^ 2) ^ (-(μ / 2))) * Real.exp 1 := mul_le_mul hcp hbin_bd (norm_nonneg _) (by positivity)
      _ = _ := by ring
  obtain ⟨hcd, hcau⟩ := holomorphic_real_contDiff_and_cauchy hU hF_diff (fun t => by change -1 < ((t : ℂ)).im; simp) (by norm_num : (0 : ℝ) < 1 / 2) hball hsphere
  refine ⟨hcd, fun r hr τ => ?_⟩
  have hrf : (r.factorial : ℝ) ≤ 2 := by exact_mod_cast (by interval_cases r <;> decide : r.factorial ≤ 2)
  have hr2 : (1 / 2 : ℝ)⁻¹ ^ r ≤ 4 := by interval_cases r <;> norm_num
  have hmul : (r.factorial : ℝ) * (1 / 2 : ℝ)⁻¹ ^ r ≤ 8 := by linarith [mul_le_mul hrf hr2 (by positivity) (by positivity)]
  have hcb := hcau r τ; rw [div_eq_mul_inv, ← inv_pow] at hcb
  calc ‖iteratedDeriv r (fun t : ℝ => F (t : ℂ)) τ‖ ≤ (r.factorial : ℝ) * ((2 ^ μ * Real.exp 1) * (1 + τ ^ 2) ^ (-(μ / 2))) * (1 / 2 : ℝ)⁻¹ ^ r := hcb
    _ = ((r.factorial : ℝ) * (1 / 2 : ℝ)⁻¹ ^ r) * ((2 ^ μ * Real.exp 1) * (1 + τ ^ 2) ^ (-(μ / 2))) := by ring
    _ ≤ 8 * ((2 ^ μ * Real.exp 1) * (1 + τ ^ 2) ^ (-(μ / 2))) := by gcongr
    _ = _ := by ring

private lemma bsplineMult_small_deriv_bound {b : ℝ} (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) {j : ℕ} (hj : j ≤ 2) (τ : ℝ) :
    ‖iteratedDeriv j (bsplineMult b m) τ‖ ≤ (max 1 (m * b)) ^ 2 := by
  let h : ℝ → ℂ := fun t => bsplineE1 ((b : ℂ) * (1 - Complex.I * (t : ℂ)))
  have hcd : ContDiff ℝ (⊤ : ℕ∞) h := (contDiff_bsplineE1.restrict_scalars ℝ).comp (contDiff_const.mul ((contDiff_const).sub (contDiff_const.mul Complex.ofRealCLM.contDiff)))
  have hdiff : Differentiable ℝ h := hcd.differentiable (by simp)
  have hiter_h : ∀ (l : ℕ) (t : ℝ), iteratedDeriv l h t = (-Complex.I * (b : ℂ)) ^ l * iteratedDeriv l bsplineE1 ((b : ℂ) * (1 - Complex.I * (t : ℂ))) := by
    intro l; induction l with | zero => intro t; simp [h] | succ k ih =>
      intro t; rw [iteratedDeriv_succ, funext ih, iteratedDeriv_succ]
      have hd_b : DifferentiableAt ℂ (iteratedDeriv k bsplineE1) ((b : ℂ) * (1 - Complex.I * (t : ℂ))) :=
        contDiff_bsplineE1.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top k) _
      have haff : HasDerivAt (fun s : ℝ => (b : ℂ) * (1 - Complex.I * (s : ℂ))) (-Complex.I * (b : ℂ)) t :=
        ((((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I).const_sub (1 : ℂ)).const_mul (b : ℂ)).congr_deriv (by simp; ring)
      have hd := (hd_b.hasDerivAt.comp t haff).const_mul ((-Complex.I * (b : ℂ)) ^ k); dsimp only [Function.comp_def] at hd; rw [hd.deriv, pow_succ]; ring
  have hbd_h : ∀ (l : ℕ) (t : ℝ), ‖iteratedDeriv l h t‖ ≤ b ^ l := fun l t => by
    rw [hiter_h l t, norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_iteratedDeriv_bsplineE1_le l (by simp [hb.le])).1 (pow_nonneg hb.le l)
  have hmax1 : (1 : ℝ) ≤ (max 1 (m * b)) ^ 2 := one_le_pow₀ (le_max_left _ _)
  have hmax_ge : m * b ≤ (max 1 (m * b)) ^ 2 := (le_max_right 1 (m * b)).trans (le_self_pow₀ (le_max_left _ _) (by decide))
  have hmax_sq : (m * b) ^ 2 ≤ (max 1 (m * b)) ^ 2 := pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2
  rw [show bsplineMult b m = fun t => h t ^ m from rfl]; interval_cases j
  · rw [iteratedDeriv_zero, norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) (by simpa using hbd_h 0 τ) m).trans (by simp [hmax1])
  · have hdm := (hdiff τ).hasDerivAt.pow m; change HasDerivAt (fun t => h t ^ m) _ τ at hdm
    rw [iteratedDeriv_one, hdm.deriv, norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    have h1 := hbd_h 1 τ; rw [iteratedDeriv_one, pow_one] at h1; have h0 := hbd_h 0 τ; rw [iteratedDeriv_zero, pow_zero] at h0
    calc (m : ℝ) * ‖h τ‖ ^ (m - 1) * ‖deriv h τ‖ ≤ (m : ℝ) * 1 ^ (m - 1) * b :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h0 _) (Nat.cast_nonneg _)) h1 (norm_nonneg _) (by positivity)
      _ = m * b := by simp
      _ ≤ (max 1 (m * b)) ^ 2 := hmax_ge
  · rcases eq_or_lt_of_le hm with rfl | hm2
    · simpa [pow_one] using (hbd_h 2 τ).trans (by simpa using hmax_sq)
    · have hderiv1 : deriv (fun t => h t ^ m) = fun t => (m : ℂ) * h t ^ (m - 1) * deriv h t := funext fun t => by
        have hdm := (hdiff t).hasDerivAt.pow m; change HasDerivAt (fun s => h s ^ m) _ t at hdm; exact hdm.deriv
      have hcd1 : ContDiff ℝ 1 (deriv h) := (hcd.of_le (by simp) : ContDiff ℝ 2 h).deriv'
      have h2deriv : HasDerivAt (fun t => (m : ℂ) * h t ^ (m - 1) * deriv h t)
          ((m : ℂ) * (((m - 1 : ℕ) : ℂ) * h τ ^ (m - 2) * deriv h τ) * deriv h τ + (m : ℂ) * h τ ^ (m - 1) * deriv (deriv h) τ) τ :=
        (((hdiff τ).hasDerivAt.pow (m - 1)).const_mul (m : ℂ)).mul (hcd1.differentiable (by decide) τ).hasDerivAt
      rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv1, h2deriv.deriv]
      have h0 := hbd_h 0 τ; rw [iteratedDeriv_zero, pow_zero] at h0; have h1 := hbd_h 1 τ; rw [iteratedDeriv_one, pow_one] at h1
      have h2 := hbd_h 2 τ; rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
      have ht1 : ‖(m : ℂ) * (((m - 1 : ℕ) : ℂ) * h τ ^ (m - 2) * deriv h τ) * deriv h τ‖ ≤ (m : ℝ) * ((m - 1 : ℕ) : ℝ) * b ^ 2 := by
        simp only [norm_mul, Complex.norm_natCast, norm_pow]; calc _ ≤ (m : ℝ) * (((m - 1 : ℕ) : ℝ) * 1 ^ (m - 2) * b) * b := by gcongr
          _ = _ := by ring
      have ht2 : ‖(m : ℂ) * h τ ^ (m - 1) * deriv (deriv h) τ‖ ≤ (m : ℝ) * b ^ 2 := by
        simp only [norm_mul, Complex.norm_natCast, norm_pow]; calc _ ≤ (m : ℝ) * 1 ^ (m - 1) * b ^ 2 := by gcongr
          _ = _ := by ring
      have hsum : (m : ℝ) * ((m - 1 : ℕ) : ℝ) * b ^ 2 + (m : ℝ) * b ^ 2 = ((m : ℝ) * b) ^ 2 := by rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
      exact (norm_add_le _ _).trans (by linarith)

private lemma S_ge_one_implies_cL {c L : ℝ} (hc : 0 < c) (_hL : 0 < L) (hS : 1 ≤ L / (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ)))) : 1 ≤ c * L ^ (3 / 2 : ℝ) := by
  have hd : 0 < Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ)) := by positivity
  have hlhs : (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ))) ^ (3 / 2 : ℝ) = Real.pi ^ 3 * c⁻¹ := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast Real.pi 2, ← Real.rpow_mul Real.pi_pos.le,
      ← Real.rpow_mul hc.le, show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show -(2 / 3 : ℝ) * (3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one c]
  have hpow := hlhs ▸ Real.rpow_le_rpow hd.le ((one_le_div hd).mp hS) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  exact (one_le_pow₀ (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)).trans
    ((by field_simp [hc.ne'] : Real.pi ^ 3 = c * (Real.pi ^ 3 * c⁻¹)).trans_le (mul_le_mul_of_nonneg_left hpow hc.le))

private lemma min_rpow_antitone {L L' : ℝ} (hL : 0 < L) (hLL' : L ≤ L') :
    min (L' ^ (-(1 / 4 : ℝ))) (L' ^ (-(3 / 2 : ℝ))) ≤ min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) :=
  le_min ((min_le_left _ _).trans (Real.rpow_le_rpow_of_nonpos hL hLL' (by norm_num))) ((min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hL hLL' (by norm_num)))

/-- **Lemma `GT.2b(3)` / `(cegt:GT3a)` (`ce_o1_global_transfer.tex`):** uniform bound for
`dualEdgeIntegral c L (bsplineMult (ceCs * κ / m) m * f)` for all `κ > 0` (`m ≥ 3`, `c ≥ 2`, `S ≥ 1`),
with explicit `κ^{-m}` decay (and hence independent of `κ ≥ 1`). -/
theorem gt2b_dual_integral_general {m : ℕ} (hm : 3 ≤ m) :
    ∃ C > 0, ∀ {κ : ℝ}, 0 < κ → ∀ {c L A_f : ℝ}, 2 ≤ c → 0 < L → 1 ≤ L / (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ))) → 0 ≤ A_f →
      ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f → (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r f τ‖ ≤ A_f * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) →
        c * (Real.exp L / Real.pi ^ 2) * ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * κ / m) m τ * f τ)‖ ≤
          C * κ ^ (-(m : ℝ)) * c ^ (5 / 6 : ℝ) * A_f * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C_osc, hC_osc, hosc⟩ := dual_phase_oscillatory_bound
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega); let μ : ℝ := (m : ℝ) + 1 / 2; have hμ : 0 < μ := by dsimp [μ]; positivity
  let C_K : ℝ := 8 * (2 ^ μ * Real.exp 1); have hC_K : 0 < C_K := by dsimp [C_K]; positivity
  let C_amp : ℝ := 4 * C_K; have hC_amp : 0 < C_amp := mul_pos (by norm_num) hC_K
  refine ⟨(2 * Real.pi)⁻¹ * C_osc * C_amp * (2 * m / ceCs) ^ m,
    mul_pos (mul_pos (mul_pos (inv_pos.mpr (mul_pos two_pos Real.pi_pos)) hC_osc) hC_amp) (pow_pos (div_pos (mul_pos two_pos hm_pos) ceCs_pos) m),
    fun {κ} hκ {c L A_f} hc hL hS hAf {f} hf_cd hf_bd => ?_⟩
  let b : ℝ := ceCs * κ / m; have hb : 0 < b := div_pos (mul_pos ceCs_pos hκ) hm_pos
  have hc_pos : 0 < c := by linarith
  have hcL := S_ge_one_implies_cL hc_pos hL hS
  obtain ⟨hk_cd, hk_bd⟩ := cpow_mul_binet_deriv_bound hμ hc
  let k_m : ℝ → ℂ := fun τ => (1 - Complex.I * (τ : ℂ)) ^ (-(μ : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ)))
  have hk_54 : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r k_m τ‖ ≤ C_K * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := fun r hr τ => by
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hexp : -(μ / 2) ≤ -(5 / 4 : ℝ) := by dsimp [μ]; linarith
    exact (hk_bd r hr τ).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg τ] : (1 : ℝ) ≤ 1 + τ ^ 2) hexp) hC_K.le)
  let g : ℝ → ℂ := fun τ => k_m τ * f τ; have hg_cd : ContDiff ℝ 2 g := (hk_cd.of_le (by simp)).mul hf_cd
  have hg_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r g τ‖ ≤ C_amp * A_f * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := fun r hr τ =>
    (norm_iteratedDeriv_mul_le (by positivity : 0 ≤ C_K * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) (by positivity : 0 ≤ A_f * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)))
      hr (hk_cd.of_le (by simp)) hf_cd (fun i hi => hk_54 i (hi.trans hr) τ) (fun i hi => hf_bd i (hi.trans hr) τ)).trans_eq
      (by rw [show (2 : ℝ) ^ 2 * (C_K * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) * (A_f * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) =
          C_amp * A_f * ((1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) by dsimp [C_amp]; ring, ← Real.rpow_add (by linarith [sq_nonneg τ])]; norm_num)
  let s_of : ℕ → ℂ := fun j => (-1 : ℂ) ^ j * (m.choose j : ℂ) * Complex.exp (-((j : ℝ) * b : ℂ)) * (b : ℂ) ^ (-(m : ℤ))
  let term : ℕ → ℝ → ℂ := fun j τ => s_of j * g τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (L + (j : ℝ) * b / c) τ : ℂ))
  have hdecomp : ∀ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
      (bsplineMult b m τ * f τ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) = ∑ j ∈ Finset.range (m + 1), term j τ := fun τ => by
    rw [bsplineMult_binomial_eq hb m τ, mul_zpow]
    have hw_ne : (1 - Complex.I * (τ : ℂ)) ≠ 0 := fun h => by
      have hre : (1 - Complex.I * (τ : ℂ)).re = 0 := by rw [h]; simp
      simp at hre
    have hcp : (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * (1 - Complex.I * (τ : ℂ)) ^ (-(m : ℤ)) = (1 - Complex.I * (τ : ℂ)) ^ (-(μ : ℂ)) := by
      rw [← Complex.cpow_intCast _ (-(m : ℤ)), ← Complex.cpow_add _ _ hw_ne]; congr 1; dsimp [μ]; push_cast; ring
    have hphi : ∀ j : ℕ, Complex.exp (Complex.I * ((j : ℝ) * b : ℂ) * (τ : ℂ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) =
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi (L + (j : ℝ) * b / c) τ : ℂ)) := fun j => by
      rw [← Complex.exp_add]; congr 1; rw [edgePhi_eq_cubic_add_ceHth (L + (j : ℝ) * b / c), edgePhi_eq_cubic_add_ceHth L]; push_cast; field_simp [hc_pos.ne']; ring
    simp only [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
    calc (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * ((b : ℂ) ^ (-(m : ℤ)) * (1 - Complex.I * (τ : ℂ)) ^ (-(m : ℤ)) *
          ((-1 : ℂ) ^ j * (m.choose j : ℂ) * Complex.exp (-((j : ℝ) * b : ℂ)) * Complex.exp (Complex.I * ((j : ℝ) * b : ℂ) * (τ : ℂ))) * f τ) *
          Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
        = (-1 : ℂ) ^ j * (m.choose j : ℂ) * Complex.exp (-((j : ℝ) * b : ℂ)) * (b : ℂ) ^ (-(m : ℤ)) *
            (((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * (1 - Complex.I * (τ : ℂ)) ^ (-(m : ℤ))) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * f τ) *
            (Complex.exp (Complex.I * ((j : ℝ) * b : ℂ) * (τ : ℂ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) := by ring
      _ = term j τ := by rw [hcp, hphi j]
  have hterm_bd : ∀ j : ℕ, ‖∫ τ : ℝ, term j τ‖ ≤ (m.choose j : ℝ) * b ^ (-(m : ℝ)) *
      (C_osc * (C_amp * A_f) * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) := fun j => by
    have hsj_norm : ‖s_of j‖ ≤ (m.choose j : ℝ) * b ^ (-(m : ℝ)) := by
      have hexp1 : ‖Complex.exp (-((j : ℝ) * b : ℂ))‖ ≤ 1 := by
        rw [show (-((j : ℝ) * b : ℂ)) = ((-(j : ℝ) * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
        exact Real.exp_le_one_iff.mpr (by nlinarith [hb.le, (Nat.cast_nonneg j : 0 ≤ (j : ℝ))])
      have hbm : ‖(b : ℂ) ^ (-(m : ℤ))‖ = b ^ (-(m : ℝ)) := by
        rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, zpow_neg, zpow_natCast, Real.rpow_neg hb.le, Real.rpow_natCast]
      dsimp [s_of]; rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, hbm]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (Nat.cast_nonneg _) hexp1) (by positivity)
    have hL_le : L ≤ L + (j : ℝ) * b / c := by linarith [show 0 ≤ (j : ℝ) * b / c by positivity]
    have hosc_j := hosc (L := L + (j : ℝ) * b / c) hg_cd (by positivity : 0 ≤ C_amp * A_f) hg_bd hc (by positivity)
      (hcL.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL.le hL_le (by norm_num)) hc_pos.le))
    rw [show ∫ τ : ℝ, term j τ = s_of j * ∫ τ : ℝ, g τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (L + (j : ℝ) * b / c) τ : ℂ)) from by
      simpa [term, mul_assoc] using integral_const_mul (s_of j) _, norm_mul]
    exact (mul_le_mul hsj_norm (hosc_j.trans (mul_le_mul_of_nonneg_left (min_rpow_antitone hL hL_le) (by positivity)))
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hterm_int : ∀ j ∈ Finset.range (m + 1), Integrable (term j) := fun j _ =>
    ((dual_phase_integrable hg_cd (by positivity : 0 ≤ C_amp * A_f) hg_bd).2.const_mul (s_of j)).congr (ae_of_all _ fun τ => by dsimp [term]; ring)
  have hint_norm : ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
      (bsplineMult b m τ * f τ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
      (2 : ℝ) ^ m * b ^ (-(m : ℝ)) * (C_osc * C_amp * A_f * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) := by
    rw [show (fun τ : ℝ => _) = fun τ => ∑ j ∈ Finset.range (m + 1), term j τ from funext hdecomp, integral_finsetSum _ hterm_int]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hterm_bd j).trans_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, show (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m by exact_mod_cast Nat.sum_range_choose m]; ring
  have hbm_κ : (2 : ℝ) ^ m * b ^ (-(m : ℝ)) = (2 * m / ceCs) ^ m * κ ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg hb.le, Real.rpow_neg hκ.le, Real.rpow_natCast, Real.rpow_natCast]; dsimp [b]; rw [div_pow, mul_pow, div_pow]
    field_simp [ceCs_pos.ne', hκ.ne', hm_pos.ne']; rw [mul_pow]
  have hξ_pos : 0 < Real.exp L / Real.pi ^ 2 := div_pos (Real.exp_pos _) (sq_pos_of_pos Real.pi_pos)
  have hpre : c * (Real.exp L / Real.pi ^ 2) *
      ‖((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * ((Real.exp L / Real.pi ^ 2 : ℝ) : ℂ))‖ = (2 * Real.pi)⁻¹ * c ^ (4 / 3 : ℝ) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hc_pos _),
      show (2 * (Real.pi : ℂ) * ((Real.exp L / Real.pi ^ 2 : ℝ) : ℂ)) = ((2 * Real.pi * (Real.exp L / Real.pi ^ 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hc43 : c * c ^ (1 / 3 : ℝ) = c ^ (4 / 3 : ℝ) := by
      calc c * c ^ (1 / 3 : ℝ) = c ^ (1 : ℝ) * c ^ (1 / 3 : ℝ) := by rw [Real.rpow_one]
        _ = c ^ (4 / 3 : ℝ) := by rw [← Real.rpow_add hc_pos]; norm_num
    field_simp [hξ_pos.ne', Real.pi_ne_zero]; rw [hc43]
  have hc56 : c ^ (4 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) = c ^ (5 / 6 : ℝ) := by rw [← Real.rpow_add hc_pos]; norm_num
  unfold dualEdgeIntegral; dsimp only; rw [norm_mul, ← mul_assoc, hpre]
  calc (2 * Real.pi)⁻¹ * c ^ (4 / 3 : ℝ) * ‖∫ τ : ℝ, _‖
      ≤ (2 * Real.pi)⁻¹ * c ^ (4 / 3 : ℝ) * ((2 : ℝ) ^ m * b ^ (-(m : ℝ)) * (C_osc * C_amp * A_f * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))))) := by gcongr
    _ = ((2 * Real.pi)⁻¹ * C_osc * C_amp * (2 * m / ceCs) ^ m) * κ ^ (-(m : ℝ)) * (c ^ (4 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ))) * A_f * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by rw [hbm_κ]; ring
    _ = _ := by rw [hc56]

/-- Fixed-`κ` corollary of `gt2b_dual_integral_general` (`ce_o1_global_transfer.tex`, `Lemma GT.2b(3)`). -/
theorem gt2b_dual_integral_fixed {m : ℕ} (hm : 3 ≤ m) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C > 0, ∀ {c L A_f : ℝ}, 2 ≤ c → 0 < L → 1 ≤ L / (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ))) → 0 ≤ A_f →
      ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f → (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r f τ‖ ≤ A_f * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) →
        c * (Real.exp L / Real.pi ^ 2) * ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * κ / m) m τ * f τ)‖ ≤
          C * c ^ (5 / 6 : ℝ) * A_f * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := gt2b_dual_integral_general hm
  exact ⟨C * κ ^ (-(m : ℝ)), mul_pos hC (Real.rpow_pos_of_pos hκ _), fun {c L A_f} hc hL hS hAf {f} hf_cd hf_bd =>
    (h hκ hc hL hS hAf hf_cd hf_bd).trans_eq (by ring)⟩

private lemma integrable_pow2_mul_airyEnv_mul_exp {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2 * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u))) := by
  have h_neg : IntegrableOn (fun u : ℝ => (1 + |u|) ^ 2 * airyEnv (u : ℂ) * Real.exp (c * u)) (Iio 0) := by
    let M : ℝ := 2 * (1 + (4 / c) ^ 2)
    have hhi : IntegrableOn (fun u : ℝ => M * Real.exp ((c / 2) * u)) (Iio 0) :=
      ((integrableOn_exp_mul_Iic (half_pos hc) 0).mono_set Iio_subset_Iic_self).const_mul M
    refine hhi.mono' (((by fun_prop : Continuous fun u : ℝ => (1 - u) ^ 2 * 1 * Real.exp (c * u)).aestronglyMeasurable.restrict).congr
      (ae_restrict_of_forall_mem measurableSet_Iio fun u hu => by dsimp only; rw [abs_of_neg hu, airyEnv_ofReal_neg hu]; ring))
      (ae_restrict_of_forall_mem measurableSet_Iio fun u hu => ?_)
    have hu0 : u ≤ 0 := le_of_lt hu; rw [abs_of_neg hu, airyEnv_ofReal_neg hu, Real.norm_of_nonneg (by positivity)]
    have hexp_sq : ((c / 4) * (-u)) ^ 2 ≤ Real.exp (-(c / 2) * u) := by
      have h2 := pow_le_pow_left₀ (by nlinarith) (by linarith [Real.add_one_le_exp ((c / 4) * (-u))] : (c / 4) * (-u) ≤ Real.exp ((c / 4) * (-u))) 2
      rwa [← Real.exp_nat_mul, show (2 : ℕ) * ((c / 4) * (-u)) = -(c / 2) * u by ring] at h2
    have hu_sq_eq : u ^ 2 = (4 / c) ^ 2 * ((c / 4) * (-u)) ^ 2 := by field_simp [hc.ne']
    have hu_sq : u ^ 2 ≤ (4 / c) ^ 2 * Real.exp (-(c / 2) * u) := hu_sq_eq ▸ mul_le_mul_of_nonneg_left hexp_sq (by positivity)
    have h1e : (1 : ℝ) ≤ Real.exp (-(c / 2) * u) := Real.one_le_exp (by nlinarith); have hsq : (1 + -u) ^ 2 ≤ 2 * (1 + u ^ 2) := by linarith [sq_nonneg (1 + u)]
    calc (1 + -u) ^ 2 * 1 * Real.exp (c * u) ≤ 2 * (1 + u ^ 2) * Real.exp (c * u) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ 2 * (Real.exp (-(c / 2) * u) + (4 / c) ^ 2 * Real.exp (-(c / 2) * u)) * Real.exp (c * u) := by gcongr
      _ = M * (Real.exp (-(c / 2) * u) * Real.exp (c * u)) := by dsimp [M]; ring
      _ = M * Real.exp ((c / 2) * u) := by rw [← Real.exp_add]; congr 2; ring
  have h_pos : IntegrableOn (fun u : ℝ => (1 + |u|) ^ 2 * airyEnv (u : ℂ) * Real.exp (R * u)) (Ici 0) := by
    let M2 : ℝ := 74 * Real.exp (R ^ 3 / 3 + 2 / 3)
    have hhi : IntegrableOn (fun u : ℝ => M2 * Real.exp (-(1 / 3 : ℝ) * u)) (Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 3 : ℝ) < 0) 0).const_mul M2)
    have hcont : ContinuousOn (fun u : ℝ => (1 + u) ^ 2 * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) * Real.exp (R * u)) (Ici 0) :=
      (((continuous_const.add continuous_id).pow 2).continuousOn.mul (ContinuousOn.rexp (continuousOn_const.mul
        (continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num))))).mul (by fun_prop)
    refine hhi.mono' ((hcont.aestronglyMeasurable measurableSet_Ici).congr (ae_restrict_of_forall_mem measurableSet_Ici fun u hu => by
      dsimp only; rw [abs_of_nonneg hu, airyEnv_ofReal_nonneg hu])) (ae_restrict_of_forall_mem measurableSet_Ici fun u hu => ?_)
    have hu0 : 0 ≤ u := mem_Ici.mp hu; rw [abs_of_nonneg hu0, airyEnv_ofReal_nonneg hu0, Real.norm_of_nonneg (by positivity), ← airyEnv_ofReal_nonneg hu0]
    have hexp_sq : (u / 6) ^ 2 ≤ Real.exp (u / 3) := by
      have h2 := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (u / 6)] : u / 6 ≤ Real.exp (u / 6)) 2
      rwa [← Real.exp_nat_mul, show (2 : ℕ) * (u / 6) = u / 3 by ring] at h2
    have h1u : (1 + u) ^ 2 ≤ 74 * Real.exp (u / 3) := by nlinarith [Real.one_le_exp (by linarith : 0 ≤ u / 3)]
    calc (1 + u) ^ 2 * airyEnv (u : ℂ) * Real.exp (R * u) = (1 + u) ^ 2 * (Real.exp (R * u) * airyEnv (u : ℂ)) := by ring
      _ ≤ (74 * Real.exp (u / 3)) * (Real.exp (R ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) :=
          mul_le_mul h1u (exp_mul_airyEnv_le hR hu0) (mul_nonneg (Real.exp_pos _).le (by rw [airyEnv_ofReal_nonneg hu0]; positivity)) (by positivity)
      _ = M2 * (Real.exp (u / 3) * Real.exp (-(2 / 3) * u)) := by dsimp [M2]; ring
      _ = M2 * Real.exp (-(1 / 3 : ℝ) * u) := by rw [← Real.exp_add]; congr 2; ring
  exact ((integrable_indicator_iff measurableSet_Iio).mpr h_neg |>.add ((integrable_indicator_iff measurableSet_Ici).mpr h_pos)).congr
    (ae_of_all _ fun u => by by_cases hu : u < 0 <;> simp [hu, mem_Iio, mem_Ici, not_le])

private lemma airyTwistedLaplaceC_diffOn_of_le {X : ℝ → ℝ} (hXm : AEStronglyMeasurable (fun u : ℝ => (X u : ℂ)) volume)
    {C_X : ℝ} (hCX : 0 ≤ C_X) (hX_bd : ∀ u : ℝ, |X u| ≤ C_X * (1 + |u|) * airyEnv (u : ℂ)) : DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re} := by
  intro y₀ hy₀; have hy₀_pos : 0 < y₀.re := hy₀; let c₀ : ℝ := y₀.re / 2; let R₀ : ℝ := ‖y₀‖ + c₀
  have hdom : Integrable (fun u : ℝ => C_X * ((1 + |u|) ^ 2 * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u)))) :=
    (integrable_pow2_mul_airyEnv_mul_exp (half_pos hy₀_pos) (by positivity)).const_mul C_X
  have hball : ∀ {y : ℂ}, y ∈ Metric.ball y₀ c₀ → c₀ ≤ y.re ∧ y.re ≤ R₀ := fun {y} hy => by
    rw [Metric.mem_ball, Complex.dist_eq] at hy
    have hd : |y.re - y₀.re| ≤ c₀ := by rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hy.le
    dsimp [c₀, R₀] at *; exact ⟨by linarith [(abs_le.mp hd).1], (Complex.re_le_norm y).trans ((norm_le_insert' y y₀).trans (by linarith))⟩
  have hexp_if : ∀ {y : ℂ}, c₀ ≤ y.re → y.re ≤ R₀ → ∀ u : ℝ, Real.exp (y.re * u) ≤ if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u) :=
    fun hc_le hR_le u => by split_ifs with hu <;> [exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hc_le hu.le); exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hR_le (not_lt.mp hu))]
  have hnn_env : ∀ u : ℝ, 0 ≤ airyEnv (u : ℂ) := fun u => by
    by_cases hu : u < 0
    · rw [airyEnv_ofReal_neg hu]; norm_num
    · rw [airyEnv_ofReal_nonneg (not_lt.mp hu)]; positivity
  have hint_ball : ∀ y ∈ Metric.ball y₀ c₀, Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ))) := fun y hy => by
    obtain ⟨hc_le, hR_le⟩ := hball hy; refine hdom.mono' (hXm.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun u => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hnn_if : 0 ≤ if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u) := by split_ifs <;> positivity
    have h1u : 1 + |u| ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
    calc |X u| * Real.exp (y.re * u) ≤ C_X * (1 + |u|) * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u)) :=
          mul_le_mul (hX_bd u) (hexp_if hc_le hR_le u) (Real.exp_pos _).le (mul_nonneg (mul_nonneg hCX (by linarith [abs_nonneg u])) (hnn_env u))
      _ = C_X * ((1 + |u|) * (airyEnv (u : ℂ) * (if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u)))) := by ring
      _ ≤ C_X * ((1 + |u|) ^ 2 * (airyEnv (u : ℂ) * (if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u)))) := by gcongr; exact mul_nonneg (hnn_env u) hnn_if
      _ = _ := by ring
  let F : ℂ → ℝ → ℂ := fun y u => (X u : ℂ) * Complex.exp (y * (u : ℂ)); let F' : ℂ → ℝ → ℂ := fun y u => (u : ℂ) * (X u : ℂ) * Complex.exp (y * (u : ℂ))
  have hF'_meas : AEStronglyMeasurable (F' y₀) volume :=
    ((Complex.continuous_ofReal.aestronglyMeasurable.mul (hXm.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)).congr (ae_of_all _ fun u => by dsimp [F']; ring))
  have hd_int := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (Metric.ball_mem_nhds y₀ (half_pos hy₀_pos))
    (Eventually.of_forall fun y => hXm.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (hint_ball y₀ (Metric.mem_ball_self (half_pos hy₀_pos))) hF'_meas
    (ae_of_all _ fun u y hy => by
      obtain ⟨hc_le, hR_le⟩ := hball hy; dsimp [F']; rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; have := hnn_env u
      calc |u| * |X u| * Real.exp (y.re * u) ≤ (1 + |u|) * (C_X * (1 + |u|) * airyEnv (u : ℂ)) * (if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u)) :=
            mul_le_mul (mul_le_mul (by linarith [abs_nonneg u]) (hX_bd u) (abs_nonneg _) (by positivity)) (hexp_if hc_le hR_le u) (Real.exp_pos _).le (by positivity)
        _ = C_X * ((1 + |u|) ^ 2 * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c₀ * u) else Real.exp (R₀ * u))) := by ring)
    hdom (ae_of_all _ fun u y _ => (((hasDerivAt_id y).mul_const (u : ℂ)).cexp.const_mul (X u : ℂ)).congr_deriv (by dsimp [F']; ring))
  exact ((((differentiableAt_id.pow 3).neg.div_const 12).cexp.const_mul (ceK : ℂ)).mul hd_int.2.differentiableAt).differentiableWithinAt

private lemma diagAirySource_airyTwisted_contDiff {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n) (hw_sum : Summable w) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => airyTwistedLaplaceC (diagAirySource w) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) := by
  have hXm : AEStronglyMeasurable (fun u : ℝ => (diagAirySource w u : ℂ)) volume := by
    have hcohn : ∀ n : ℕ, AEStronglyMeasurable (fun u : ℝ => ((w n * cohnL n u ^ 2 : ℝ) : ℂ)) volume := fun n =>
      ((aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (w n : ℂ)) volume).mul
        (((Lp.aestronglyMeasurable (cohnLL2 n)).congr (cohnLL2_ae n)).pow 2)).congr (ae_of_all _ fun u => by dsimp only [Pi.mul_apply, Pi.pow_apply]; push_cast; ring)
    exact aestronglyMeasurable_of_tendsto_ae atTop (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n _ => hcohn n)
      (ae_of_all _ fun u => by simpa [diagAirySource, Complex.ofReal_sum] using (Complex.ofRealCLM.hasSum (diagAirySource_summable hw_nn hw_sum u).hasSum).tendsto_sum_nat)
  let C_X : ℝ := (∑' n, w n) * 23; have hCX : 0 ≤ C_X := mul_nonneg (tsum_nonneg hw_nn) (by norm_num)
  have hdiff := airyTwistedLaplaceC_diffOn_of_le hXm hCX fun u => by have h := diagAirySource_le hw_nn hw_sum u; rw [abs_of_nonneg h.1]; exact h.2
  exact (reflected_line_diffOn hdiff (mul_pos ceCs_pos (inv_pos.mpr hε))).2.2.2.2

/-- **Lemma `GT.2b(3)` reflected instantiation (`ce_o1_global_transfer.tex`):** combining `GT2bReflectedData`
with `gt2b_dual_integral_general` yields the `O(κ^{-m} ε min(L^{-1/4}, L^{-3/2}))` estimate at `c = ε^{-3}`. -/
theorem gt2b_dual_integral_reflected {m : ℕ} (hm : 3 ≤ m) :
    ∃ C > 0, ∀ (d : GT2bReflectedData) {κ : ℝ}, 0 < κ → ∀ {ε L : ℝ}, 0 < ε → 2 ≤ ε ^ (-3 : ℝ) → 0 < L → 1 ≤ L / (Real.pi ^ 2 * ε ^ 2) →
      let c : ℝ := ε ^ (-3 : ℝ)
      c * (Real.exp L / Real.pi ^ 2) * ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * κ / m) m τ *
          ((d.θ : ℂ) * airyTwistedLaplaceC (diagAirySource d.w) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ))) + (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε τ))‖ ≤
        C * κ ^ (-(m : ℝ)) * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) * ε * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C₁, _, hdiag_bd⟩ := diagAirySource_dual_deriv_bound; obtain ⟨C₂, hC₂, hgt2b⟩ := gt2b_dual_integral_general hm
  let C_diag : ℝ := max 1 (max (C₁ 0) (max (C₁ 1) (C₁ 2))); have hCd1 : 1 ≤ C_diag := le_max_left _ _
  refine ⟨C₂ * C_diag, mul_pos hC₂ (by linarith), fun d {κ} hκ {ε L} hε hc hL hS => ?_⟩
  have hε1 : ε ≤ 1 := by by_contra h1; push Not at h1; have := Real.rpow_le_rpow_of_nonpos zero_lt_one h1.le (by norm_num : (-3 : ℝ) ≤ 0); rw [Real.one_rpow] at this; linarith
  let c : ℝ := ε ^ (-3 : ℝ)
  have hc23 : c ^ (-(2 / 3 : ℝ)) = ε ^ 2 := by dsimp [c]; rw [← Real.rpow_mul hε.le]; norm_num
  have hc56 : c ^ (5 / 6 : ℝ) * ε ^ (7 / 2 : ℝ) = ε := by dsimp [c]; rw [← Real.rpow_mul hε.le, ← Real.rpow_add hε]; norm_num
  let g₁ : ℝ → ℂ := fun τ => airyTwistedLaplaceC (diagAirySource d.w) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)))
  let f : ℝ → ℂ := fun τ => (d.θ : ℂ) * g₁ τ + (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε τ
  have hg₁_cd := diagAirySource_airyTwisted_contDiff d.hw_nn d.hw_sum hε
  have hf_cd : ContDiff ℝ 2 f := (contDiff_const.mul (hg₁_cd.of_le (by simp))).add (contDiff_const.mul (d.hS₀_cd hε hε1))
  have hdiag1 : ∀ t ≥ 0, ∑' n : ℕ, d.w n * dirichletPhi n t ^ 2 ≤ d.A ^ 2 * (min t 1) ^ (2 * 1) := by simpa using d.hdiag
  let A_f : ℝ := C_diag * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) * ε ^ (7 / 2 : ℝ)
  have hAf : 0 ≤ A_f := mul_nonneg (mul_nonneg (by linarith) (add_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (mul_nonneg (abs_nonneg _) d.hC₀))) (Real.rpow_nonneg hε.le _)
  have hf_bd : ∀ k ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv k f τ‖ ≤ A_f * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := fun k hk τ => by
    have hadd : iteratedDeriv k f τ = (d.θ : ℂ) * iteratedDeriv k g₁ τ + (d.γ : ℂ) * (ε : ℂ) * iteratedDeriv k (d.S₀ ε) τ := by
      dsimp [f]
      rw [iteratedDeriv_fun_add (((contDiff_const.mul hg₁_cd).contDiffAt (x := τ)).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
          ((contDiff_const.mul (d.hS₀_cd hε hε1)).contDiffAt.of_le (by exact_mod_cast hk)),
        iteratedDeriv_const_mul_field (d.θ : ℂ) g₁, show (fun s => (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε s) = fun s => ((d.γ : ℂ) * (ε : ℂ)) * d.S₀ ε s from funext fun s => by ring,
        iteratedDeriv_const_mul_field ((d.γ : ℂ) * (ε : ℂ)) (d.S₀ ε)]
    have hC_le : C₁ k ≤ C_diag := by dsimp [C_diag]; interval_cases k <;> [exact le_trans (le_max_left _ _) (le_max_right _ _); exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _); exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)]
    have hε7 : ε ^ (5 / 2 + 2 * ((1 : ℕ) : ℝ)) ≤ ε ^ (7 / 2 : ℝ) := by rw [Nat.cast_one, show (5 / 2 + 2 * (1 : ℝ)) = 1 + (7 / 2 : ℝ) by norm_num, Real.rpow_add hε, Real.rpow_one]; exact mul_le_of_le_one_left (Real.rpow_nonneg hε.le _) hε1
    have hb1 : ‖iteratedDeriv k g₁ τ‖ ≤ C_diag * d.A ^ 2 * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := (hdiag_bd d.hw_nn d.hw_sum d.hA (Or.inr rfl) hdiag1 k hε τ).trans (by gcongr)
    have hε_mul : ε * ε ^ (5 / 2 : ℝ) = ε ^ (7 / 2 : ℝ) := by calc ε * ε ^ (5 / 2 : ℝ) = ε ^ (1 : ℝ) * ε ^ (5 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = ε ^ (7 / 2 : ℝ) := by rw [← Real.rpow_add hε]; norm_num
    have hb2 : ε * ‖iteratedDeriv k (d.S₀ ε) τ‖ ≤ C_diag * d.C₀ * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
      have hτ := Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg τ] : (1 : ℝ) ≤ 1 + τ ^ 2) (by norm_num : -(5 / 4 : ℝ) ≤ -(1 / 4 : ℝ))
      calc ε * ‖iteratedDeriv k (d.S₀ ε) τ‖ ≤ ε * (d.C₀ * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) := mul_le_mul_of_nonneg_left (d.hS₀_bd hε hε1 k hk τ) hε.le
        _ = 1 * d.C₀ * (ε * ε ^ (5 / 2 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by ring
        _ ≤ C_diag * d.C₀ * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
            rw [hε_mul]; exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCd1 d.hC₀) (Real.rpow_nonneg hε.le _)) hτ (by positivity) (mul_nonneg (mul_nonneg (by linarith) d.hC₀) (Real.rpow_nonneg hε.le _))
    rw [hadd]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε]
    calc |d.θ| * ‖iteratedDeriv k g₁ τ‖ + |d.γ| * ε * ‖iteratedDeriv k (d.S₀ ε) τ‖
        ≤ |d.θ| * (C_diag * d.A ^ 2 * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) + |d.γ| * (C_diag * d.C₀ * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) := by rw [mul_assoc |d.γ| ε]; gcongr
      _ = A_f * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by dsimp [A_f]; ring
  calc c * (Real.exp L / Real.pi ^ 2) * ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * κ / m) m τ * f τ)‖
      ≤ C₂ * κ ^ (-(m : ℝ)) * c ^ (5 / 6 : ℝ) * A_f * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := hgt2b hκ hc hL (by rwa [hc23]) hAf hf_cd hf_bd
    _ = C₂ * C_diag * κ ^ (-(m : ℝ)) * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) * (c ^ (5 / 6 : ℝ) * ε ^ (7 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by dsimp [A_f]; ring
    _ = _ := by rw [hc56]

/-- **Lemma `O.3(1)` (`u1c_o1_upper.tex`, `(e3)`):** reflected dual estimate for `f` obeying the `O.2`
bound `‖f^{(r)}(τ)‖ ≤ C_D c^{-5/6} (1 + τ²)^{-5/4}`, valid uniformly for `δ₀ ∈ (0, 2]`, `c ≥ 2`, `S ≥ 1`. -/
theorem o3_dual_bound {m : ℕ} (hm : 3 ≤ m) :
    ∃ C > 0, ∀ {δ₀ c L C_D : ℝ}, δ₀ ∈ Ioc 0 2 → 2 ≤ c → 0 < L → 1 ≤ L / (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ))) → 0 ≤ C_D →
      ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f → (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r f τ‖ ≤ C_D * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) →
        ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * δ₀ * c ^ (1 / 3 : ℝ) / m) m τ * f τ)‖ ≤
          C * C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C_gt, _, hgt⟩ := gt2b_dual_integral_general hm; obtain ⟨C_osc, _, hosc⟩ := dual_phase_oscillatory_bound
  let C_K1 : ℝ := 8 * (2 ^ (1 / 2 : ℝ) * Real.exp 1); let C_sm : ℝ := (2 * Real.pi)⁻¹ * C_osc * (16 * C_K1 * (max 1 ceCs) ^ 2)
  refine ⟨(2 : ℝ) ^ m * max C_gt C_sm, by positivity, fun {δ₀ c L C_D} hδ hc hL hS hCD {f} hf_cd hf_bd => ?_⟩
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega); have hc_pos : 0 < c := by linarith
  have hξ_pos : 0 < Real.exp L / Real.pi ^ 2 := div_pos (Real.exp_pos _) (sq_pos_of_pos Real.pi_pos)
  let κ : ℝ := δ₀ * c ^ (1 / 3 : ℝ); have hκ : 0 < κ := mul_pos hδ.1 (Real.rpow_pos_of_pos hc_pos _)
  rw [show ceCs * δ₀ * c ^ (1 / 3 : ℝ) / m = ceCs * κ / m by dsimp [κ]; ring]
  rcases lt_or_ge 1 κ with hκ1 | hκ1
  · have hf_14 : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r f τ‖ ≤ (C_D * c ^ (-(5 / 6 : ℝ))) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := fun r hr τ =>
      (hf_bd r hr τ).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg τ]) (by norm_num)) (by positivity))
    have hc_cancel : C_gt * κ ^ (-(m : ℝ)) * c ^ (5 / 6 : ℝ) * (C_D * c ^ (-(5 / 6 : ℝ))) = C_gt * C_D * κ ^ (-(m : ℝ)) := by
      calc _ = C_gt * C_D * κ ^ (-(m : ℝ)) * (c ^ (5 / 6 : ℝ) * c ^ (-(5 / 6 : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hc_pos]; simp
    have hgt_bd := (hgt hκ hc hL hS (by positivity : 0 ≤ C_D * c ^ (-(5 / 6 : ℝ))) hf_cd hf_14).trans_eq (by rw [hc_cancel])
    have hdiv : ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * κ / m) m τ * f τ)‖ ≤
        C_gt * C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * κ ^ (-(m : ℝ)) * c⁻¹ * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
      calc _ = (c * (Real.exp L / Real.pi ^ 2))⁻¹ * (c * (Real.exp L / Real.pi ^ 2) *
            ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * κ / m) m τ * f τ)‖) := by field_simp [hc_pos.ne', hξ_pos.ne']
        _ ≤ (c * (Real.exp L / Real.pi ^ 2))⁻¹ * (C_gt * C_D * κ ^ (-(m : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) := by gcongr
        _ = _ := by rw [mul_inv]; ring
    have hκ_cmp : κ ^ (-(m : ℝ)) ≤ (2 : ℝ) ^ m * (1 + κ) ^ (-(m : ℝ)) := by
      have h2eq : (2 : ℝ) ^ m * (2 : ℝ) ^ (-(m : ℝ)) = 1 := by rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_add zero_lt_two]; simp
      calc κ ^ (-(m : ℝ)) = (2 : ℝ) ^ m * ((2 : ℝ) ^ (-(m : ℝ)) * κ ^ (-(m : ℝ))) := by rw [← mul_assoc, h2eq, one_mul]
        _ ≤ (2 : ℝ) ^ m * (1 + κ) ^ (-(m : ℝ)) := by rw [← Real.mul_rpow (by norm_num) hκ.le]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)) (by positivity)
    exact hdiv.trans ((by ring : C_gt * C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * κ ^ (-(m : ℝ)) * c⁻¹ * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) =
        C_gt * (C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * c⁻¹ * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) * κ ^ (-(m : ℝ))).trans_le
      ((by gcongr; exact le_max_left _ _ : C_gt * (C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * c⁻¹ * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) * κ ^ (-(m : ℝ)) ≤
        max C_gt C_sm * (C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * c⁻¹ * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) * ((2 : ℝ) ^ m * (1 + κ) ^ (-(m : ℝ)))).trans_eq (by ring)))
  · have hcL := S_ge_one_implies_cL hc_pos hL hS
    obtain ⟨hk_cd, hk_bd⟩ := cpow_mul_binet_deriv_bound (by norm_num : (0 : ℝ) < 1 / 2) hc
    let k0 : ℝ → ℂ := fun τ => (1 - Complex.I * (τ : ℂ)) ^ (-((1 / 2 : ℝ) : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ)))
    let b : ℝ := ceCs * κ / m; have hb : 0 < b := div_pos (mul_pos ceCs_pos hκ) hm_pos
    have hmb : (m : ℝ) * b ≤ ceCs := (by dsimp [b]; field_simp [hm_pos.ne'] : (m : ℝ) * b = ceCs * κ) ▸ mul_le_of_le_one_right ceCs_pos.le hκ1
    have hk_bd2 : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r k0 τ‖ ≤ C_K1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := fun r hr τ =>
      (hk_bd r hr τ).trans_eq (by rw [show -((1 / 2 : ℝ) / 2) = -(1 / 4 : ℝ) by norm_num])
    let w_bs : ℝ → ℂ := fun τ => k0 τ * bsplineMult b m τ; have hbs_cd := bsplineMult_contDiff b m
    have hw_cd : ContDiff ℝ 2 w_bs := (hk_cd.of_le (by simp)).mul (hbs_cd.of_le (by simp))
    have hw_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r w_bs τ‖ ≤ (4 * C_K1 * (max 1 ceCs) ^ 2) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := fun r hr τ =>
      (norm_iteratedDeriv_mul_le (by positivity : 0 ≤ C_K1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) (by positivity : 0 ≤ (max 1 ceCs) ^ 2) hr
        (hk_cd.of_le (by simp)) (hbs_cd.of_le (by simp)) (fun i hi => hk_bd2 i (hi.trans hr) τ)
        (fun i hi => (bsplineMult_small_deriv_bound hb (by omega) (hi.trans hr) τ).trans (pow_le_pow_left₀ (by positivity) (max_le_max_left 1 hmb) 2))).trans_eq (by ring)
    let a : ℝ → ℂ := fun τ => w_bs τ * f τ; have ha_cd : ContDiff ℝ 2 a := hw_cd.mul hf_cd
    let A_a : ℝ := (16 * C_K1 * (max 1 ceCs) ^ 2) * C_D * c ^ (-(5 / 6 : ℝ))
    have ha_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r a τ‖ ≤ A_a * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := fun r hr τ =>
      (norm_iteratedDeriv_mul_le (by positivity : 0 ≤ (4 * C_K1 * (max 1 ceCs) ^ 2) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)))
        (by positivity : 0 ≤ C_D * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) hr hw_cd hf_cd
        (fun i hi => hw_bd i (hi.trans hr) τ) (fun i hi => hf_bd i (hi.trans hr) τ)).trans_eq
        (by rw [show (2 : ℝ) ^ 2 * ((4 * C_K1 * (max 1 ceCs) ^ 2) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) *
            (C_D * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) = A_a * ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) by dsimp [A_a]; ring,
          ← Real.rpow_add (by linarith [sq_nonneg τ])]; norm_num)
    have hosc_a := hosc ha_cd (by positivity : 0 ≤ A_a) ha_bd hc hL hcL
    have h1_le : 1 ≤ (2 : ℝ) ^ m * (1 + κ) ^ (-(m : ℝ)) := by
      have h2m : (1 + κ) ^ m ≤ (2 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      rw [Real.rpow_neg (by linarith), Real.rpow_natCast]; exact (mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ m ≠ 0)).symm.trans_le (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2m) (by positivity))
    have hpre : ‖((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * ((Real.exp L / Real.pi ^ 2 : ℝ) : ℂ))‖ = (2 * Real.pi)⁻¹ * (Real.exp L / Real.pi ^ 2)⁻¹ * c ^ (1 / 3 : ℝ) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hc_pos _),
        show 2 * (Real.pi : ℂ) * ((Real.exp L / Real.pi ^ 2 : ℝ) : ℂ) = ((2 * Real.pi * (Real.exp L / Real.pi ^ 2) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp [hξ_pos.ne', Real.pi_ne_zero]
    have hc_pow : c ^ (1 / 3 : ℝ) * c ^ (-(5 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c⁻¹ := by rw [← Real.rpow_add hc_pos, ← Real.rpow_add hc_pos, ← Real.rpow_neg_one c]; norm_num
    unfold dualEdgeIntegral; dsimp only
    rw [show (fun τ : ℝ => ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * (bsplineMult b m τ * f τ)) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) = fun τ : ℝ => a τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) from
        funext fun τ => by dsimp [a, w_bs, k0]; rw [show (-((1 / 2 : ℝ) : ℂ)) = -(1 / 2 : ℂ) by norm_num]; ring, norm_mul, hpre]
    exact ((mul_le_mul_of_nonneg_left hosc_a (by positivity)).trans_eq (by dsimp [C_sm, A_a]; ring)).trans
      (((by rw [hc_pow]; gcongr; exact le_max_right _ _ : C_sm * C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * 1 * (c ^ (1 / 3 : ℝ) * c ^ (-(5 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ))) *
        min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) ≤ max C_gt C_sm * C_D * (Real.exp L / Real.pi ^ 2)⁻¹ * ((2 : ℝ) ^ m * (1 + κ) ^ (-(m : ℝ))) * c⁻¹ *
        min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))))).trans_eq (by ring))

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.o2_reflected_line_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o2_reflected_line_contDiff

/-- info: 'FormalResearch.CohnElkies.o2_reflected_line_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o2_reflected_line_deriv_bound

/-- info: 'FormalResearch.CohnElkies.o2_imag_weighted_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o2_imag_weighted_deriv_bound

/-- info: 'FormalResearch.CohnElkies.bsplineMult_binomial_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.bsplineMult_binomial_eq

/-- info: 'FormalResearch.CohnElkies.dual_phase_oscillatory_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.dual_phase_oscillatory_bound

/-- info: 'FormalResearch.CohnElkies.gt2b_dual_integral_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.gt2b_dual_integral_general

/-- info: 'FormalResearch.CohnElkies.gt2b_dual_integral_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.gt2b_dual_integral_fixed

/-- info: 'FormalResearch.CohnElkies.gt2b_dual_integral_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.gt2b_dual_integral_reflected

/-- info: 'FormalResearch.CohnElkies.o3_dual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o3_dual_bound

end FormalResearch.CohnElkies
