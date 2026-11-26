module

public import FormalResearch.SignUncertainty.UctCeBandFarRef
public import FormalResearch.SignUncertainty.CtOuterPart3
public import FormalResearch.SignUncertainty.CtOuterTheta1
public import FormalResearch.CohnElkies.DualPhaseAndO3

/-!
# Far-band asymptotic for `uct:ce-band` (1)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:ce-band` (1),
far-band conclusion (`L ≥ (1/4) log c`, `c ≥ 60`).

Under the real-axis `C²` exponential-decay bounds `‖A^{(j)}(τ)‖ ≤ C_j e^{-η|τ|}` (`j = 0, 1, 2`),
we prove that for all `c ≥ 60` and `L ≥ (1/4) log c`,
`h_norm^{ĥ}(L) = A(0) c⁻¹ I_fl^{ĥ}(L - θ_1^- / c) + O(c⁻² L⁻²)`,
with implied constant depending only on `η, C₀, C₁, C₂`.
-/

@[expose] public section

noncomputable section

open Complex Real Set Filter MeasureTheory
open scoped Topology Pointwise

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### Small algebraic helpers -/

private lemma rpow_neg_two_eq' (x : ℝ) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp [zpow_neg]

private lemma contDiff_one_deriv_of_two' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ) + 1) f from hf)).2.2

private lemma nonneg_of_zero_of_deriv_nonneg' {g g' : ℝ → ℝ} (h0 : g 0 = 0)
    (hnn : ∀ u ≥ 0, 0 ≤ g' u) (hd : ∀ u : ℝ, HasDerivAt g (g' u) u) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ g y := by
  have hmono : MonotoneOn g (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun u _ => (hd u).continuousAt.continuousWithinAt)
      (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
      (fun u hu => by rw [(hd u).deriv]; exact hnn u (interior_subset hu))
  simpa [h0] using hmono (Set.mem_Ici.mpr le_rfl) hy hy

private lemma norm_exp_ofReal_mul_I_sub_one_le' (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have hftc : Complex.exp ((x : ℂ) * Complex.I) - 1 =
      ∫ t in (0 : ℝ)..x, Complex.I * Complex.exp ((t : ℂ) * Complex.I) := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
          (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) t := fun t _ => by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
      exact ((Complex.hasDerivAt_exp _).comp t h1).congr_deriv (by ring)
    have hcont : Continuous (fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable 0 x)]
    simp
  rw [hftc]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) (a := (0 : ℝ)) (b := x) (C := 1)
    (fun t _ => by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I])
  simpa using hbd

private lemma leibniz_two_norm {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (τ : ℝ) :
    ‖iteratedDeriv 2 (fun t => f t * g t) τ‖ ≤
      ‖iteratedDeriv 2 f τ‖ * ‖g τ‖ + 2 * ‖deriv f τ‖ * ‖deriv g τ‖ + ‖f τ‖ * ‖iteratedDeriv 2 g τ‖ := by
  have h := iteratedDeriv_fun_mul (n := 2) hf.contDiffAt hg.contDiffAt (x := τ)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one,
    Nat.cast_ofNat, one_mul, iteratedDeriv_zero, iteratedDeriv_one, Nat.sub_zero, Nat.sub_self,
    show 2 - 1 = 1 by rfl]
  calc ‖f τ * iteratedDeriv 2 g τ + 2 * deriv f τ * deriv g τ + iteratedDeriv 2 f τ * g τ‖
      ≤ ‖f τ * iteratedDeriv 2 g τ + 2 * deriv f τ * deriv g τ‖ + ‖iteratedDeriv 2 f τ * g τ‖ :=
        norm_add_le _ _
    _ ≤ (‖f τ * iteratedDeriv 2 g τ‖ + ‖2 * deriv f τ * deriv g τ‖) + ‖iteratedDeriv 2 f τ * g τ‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ = ‖iteratedDeriv 2 f τ‖ * ‖g τ‖ + 2 * ‖deriv f τ‖ * ‖deriv g τ‖ + ‖f τ‖ * ‖iteratedDeriv 2 g τ‖ := by
        simp only [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; ring

private lemma deriv_mul_norm {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (τ : ℝ) :
    ‖deriv (fun t => f t * g t) τ‖ ≤ ‖deriv f τ‖ * ‖g τ‖ + ‖f τ‖ * ‖deriv g τ‖ := by
  have hd : HasDerivAt (fun t => f t * g t) (deriv f τ * g τ + f τ * deriv g τ) τ :=
    (hf.differentiable (by decide) τ).hasDerivAt.mul (hg.differentiable (by decide) τ).hasDerivAt
  rw [hd.deriv]
  exact (norm_add_le _ _).trans_eq (by simp only [norm_mul])

private lemma smoothCutoff0_scale_derivs {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    deriv (fun t : ℝ => smoothCutoff0 (t / s)) τ = s⁻¹ * deriv smoothCutoff0 (τ / s) ∧
    iteratedDeriv 2 (fun t : ℝ => smoothCutoff0 (t / s)) τ = s ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / s) := by
  have hd1 : ∀ x : ℝ, deriv (fun t : ℝ => smoothCutoff0 (t / s)) x = s⁻¹ * deriv smoothCutoff0 (x / s) := fun x => by
    have h := ((contDiff_smoothCutoff0.differentiable (by decide)).differentiableAt.hasDerivAt).comp x
      ((hasDerivAt_id x).div_const s)
    rw [show (fun t : ℝ => smoothCutoff0 (t / s)) = smoothCutoff0 ∘ (fun u : ℝ => id u / s) by rfl, h.deriv]
    simp [id_eq]; ring
  refine ⟨hd1 τ, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one, funext hd1]
  have hcd1 : ContDiff ℝ 1 (deriv smoothCutoff0) :=
    contDiff_one_deriv_of_two' (contDiff_smoothCutoff0.of_le (by simp))
  have h := ((hcd1.differentiable (by decide)).differentiableAt.hasDerivAt).comp τ ((hasDerivAt_id τ).div_const s)
  rw [show (fun t : ℝ => s⁻¹ * deriv smoothCutoff0 (t / s)) =
      fun t => s⁻¹ * (deriv smoothCutoff0 ∘ (fun u => id u / s)) t by rfl, (h.const_mul s⁻¹).deriv]
  have hpow : s⁻¹ * (1 / s) = s ^ (-(2 : ℝ)) := by rw [rpow_neg_two_eq', one_div, sq, mul_inv]
  simp only [id_eq]
  calc s⁻¹ * (deriv (deriv smoothCutoff0) (τ / s) * (1 / s))
      = (s⁻¹ * (1 / s)) * deriv (deriv smoothCutoff0) (τ / s) := by ring
    _ = s ^ (-(2 : ℝ)) * deriv (deriv smoothCutoff0) (τ / s) := by rw [hpow]

/-! ### Section 1: Bounds on `θ_1^-` and derivatives of `θ_-` -/

private lemma six_sinh_sub_le_cube_exp {y : ℝ} (hy : 0 ≤ y) :
    6 * (Real.sinh y - y) ≤ y ^ 3 * Real.exp y := by
  let d0 : ℝ → ℝ := fun u => u ^ 3 * Real.exp u - 6 * (Real.sinh u - u)
  let d1 : ℝ → ℝ := fun u => (3 * u ^ 2 + u ^ 3) * Real.exp u - 6 * (Real.cosh u - 1)
  let d2 : ℝ → ℝ := fun u => (6 * u + 6 * u ^ 2 + u ^ 3) * Real.exp u - 6 * Real.sinh u
  let d3 : ℝ → ℝ := fun u => (6 + 18 * u + 9 * u ^ 2 + u ^ 3) * Real.exp u - 6 * Real.cosh u
  have hd3 : ∀ u ≥ 0, 0 ≤ d3 u := fun u hu => by
    dsimp [d3]
    have h1 : Real.cosh u ≤ Real.exp u := by
      rw [Real.cosh_eq]
      have hneg : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
      linarith
    have h2 : 6 ≤ 6 + 18 * u + 9 * u ^ 2 + u ^ 3 := by nlinarith [sq_nonneg u, pow_nonneg hu 3]
    nlinarith [Real.exp_pos u]
  have hd2 : ∀ u ≥ 0, 0 ≤ d2 u := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg' (by simp [d2]) hd3 (fun s => by
      have hA : HasDerivAt (fun t => (6 * t + 6 * t ^ 2 + t ^ 3) * Real.exp t)
          ((6 + 18 * s + 9 * s ^ 2 + s ^ 3) * Real.exp s) s := by
        have hp : HasDerivAt (fun t => 6 * t + 6 * t ^ 2 + t ^ 3) (6 + 12 * s + 3 * s ^ 2) s := by
          have h1 := (hasDerivAt_id s).const_mul 6
          have h2 := (hasDerivAt_pow 2 s).const_mul 6
          have h3 := hasDerivAt_pow 3 s
          exact ((h1.add h2).add h3).congr_deriv (by ring)
        exact (hp.mul (Real.hasDerivAt_exp s)).congr_deriv (by ring)
      exact (hA.sub ((Real.hasDerivAt_sinh s).const_mul 6)).congr_deriv rfl) hu
  have hd1 : ∀ u ≥ 0, 0 ≤ d1 u := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg' (by simp [d1]) hd2 (fun s => by
      have hA : HasDerivAt (fun t => (3 * t ^ 2 + t ^ 3) * Real.exp t)
          ((6 * s + 6 * s ^ 2 + s ^ 3) * Real.exp s) s := by
        have hp : HasDerivAt (fun t => 3 * t ^ 2 + t ^ 3) (6 * s + 3 * s ^ 2) s := by
          have h1 := (hasDerivAt_pow 2 s).const_mul 3
          have h2 := hasDerivAt_pow 3 s
          exact (h1.add h2).congr_deriv (by ring)
        exact (hp.mul (Real.hasDerivAt_exp s)).congr_deriv (by ring)
      have hB : HasDerivAt (fun t => 6 * (Real.cosh t - 1)) (6 * Real.sinh s) s :=
        ((Real.hasDerivAt_cosh s).sub (hasDerivAt_const s 1)).const_mul 6 |>.congr_deriv (by ring)
      exact (hA.sub hB).congr_deriv rfl) hu
  have h0 := nonneg_of_zero_of_deriv_nonneg' (g := d0) (by simp [d0]) hd1 (fun s => by
    have hA : HasDerivAt (fun t => t ^ 3 * Real.exp t) ((3 * s ^ 2 + s ^ 3) * Real.exp s) s :=
      ((hasDerivAt_pow 3 s).mul (Real.hasDerivAt_exp s)).congr_deriv (by ring)
    have hB : HasDerivAt (fun t => 6 * (Real.sinh t - t)) (6 * (Real.cosh s - 1)) s :=
      ((Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)).const_mul 6
    exact (hA.sub hB).congr_deriv rfl) hy
  dsimp [d0] at h0; linarith

private lemma sinh_sub_le_cube_on_unit {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.sinh y - y ≤ y ^ 3 := by
  have h := six_sinh_sub_le_cube_exp hy0
  have he : Real.exp y ≤ 6 := (Real.exp_le_exp.mpr hy1).trans (by linarith [Real.exp_one_lt_d9])
  nlinarith [pow_nonneg hy0 3]

/-- Upper bound `θ_1^- = CtOuter.ctTheta1 (-1) ≤ 12`. -/
lemma ctTheta1_neg_le : CtOuter.ctTheta1 (-1) ≤ 12 := by
  unfold CtOuter.ctTheta1
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  simp only [hne, ↓reduceIte, sub_zero]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  suffices hI0 : CtOuter.ctI0 ≤ 12 by linarith
  unfold CtOuter.ctI0
  let f : ℝ → ℝ := fun y => Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2)
  let g : ℝ → ℝ := fun y => if y ≤ 1 then 2 else 9 * y * Real.exp (-y)
  have hf_le : ∀ y ∈ Ioi (0 : ℝ), f y ≤ g y := fun y hy => by
    have hy0 : 0 < y := hy
    have hsh_gt : y < Real.sinh y := sinh_gt_id hy0
    have hsh_pos : 0 < Real.sinh y := lt_trans hy0 hsh_gt
    have harg_pos : 0 < 6 * (Real.sinh y - y) / y ^ 3 := by
      have : 0 < Real.sinh y - y := by linarith
      positivity
    dsimp only [f, g]
    split_ifs with hy1
    · have hlog_le : Real.log (6 * (Real.sinh y - y) / y ^ 3) ≤ y ^ 2 := by
        have h1 : 6 * (Real.sinh y - y) / y ^ 3 ≤ Real.sinh y / y := by
          rw [div_le_div_iff₀ (pow_pos hy0 3) hy0]
          have h6 := six_sinh_sub_le_sq_sinh hy0.le
          nlinarith [sq_nonneg y]
        have h2 : Real.sinh y / y ≤ 1 + y ^ 2 := by
          rw [div_le_iff₀ hy0]
          have h3 := sinh_sub_le_cube_on_unit hy0.le hy1
          nlinarith
        calc Real.log (6 * (Real.sinh y - y) / y ^ 3)
            ≤ Real.log (Real.sinh y / y) := Real.log_le_log harg_pos h1
          _ ≤ Real.sinh y / y - 1 := Real.log_le_sub_one_of_pos (div_pos hsh_pos hy0)
          _ ≤ y ^ 2 := by linarith
      have hcosh_le : Real.cosh y ≤ 2 := by
        rw [Real.cosh_eq]
        have he1 : Real.exp y ≤ 3 := (Real.exp_le_exp.mpr hy1).trans (by linarith [Real.exp_one_lt_d9])
        have he2 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      have hrat_le : Real.cosh y / Real.sinh y ^ 2 ≤ 2 / y ^ 2 := by
        have hsq : y ^ 2 ≤ Real.sinh y ^ 2 := pow_le_pow_left₀ hy0.le hsh_gt.le 2
        calc Real.cosh y / Real.sinh y ^ 2 ≤ 2 / Real.sinh y ^ 2 :=
              div_le_div_of_nonneg_right hcosh_le (sq_nonneg _)
          _ ≤ 2 / y ^ 2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hy0) hsq
      have hrat_nn : 0 ≤ Real.cosh y / Real.sinh y ^ 2 := div_nonneg (Real.cosh_pos y).le (sq_nonneg _)
      calc Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2)
          ≤ y ^ 2 * (Real.cosh y / Real.sinh y ^ 2) := mul_le_mul_of_nonneg_right hlog_le hrat_nn
        _ ≤ y ^ 2 * (2 / y ^ 2) := mul_le_mul_of_nonneg_left hrat_le (sq_nonneg _)
        _ = 2 := by field_simp [hy0.ne']
    · push Not at hy1
      have hlog_le : Real.log (6 * (Real.sinh y - y) / y ^ 3) ≤ y := by
        have h1 : 6 * (Real.sinh y - y) / y ^ 3 ≤ Real.exp y := by
          rw [div_le_iff₀ (pow_pos hy0 3)]
          exact (six_sinh_sub_le_cube_exp hy0.le).trans_eq (mul_comm _ _)
        calc Real.log (6 * (Real.sinh y - y) / y ^ 3) ≤ Real.log (Real.exp y) := Real.log_le_log harg_pos h1
          _ = y := Real.log_exp y
      have hcosh_le : Real.cosh y ≤ Real.exp y := by
        rw [Real.cosh_eq]
        have : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
        linarith
      have hsinh_ge : Real.exp y / 3 ≤ Real.sinh y := by
        rw [Real.sinh_eq]
        have he2 : Real.exp (-y) ≤ Real.exp y / 3 := by
          have : 3 ≤ Real.exp (2 * y) := by
            calc (3 : ℝ) ≤ (Real.exp 1) ^ 2 := by nlinarith [Real.exp_one_gt_d9]
              _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
              _ ≤ Real.exp (2 * y) := Real.exp_le_exp.mpr (by linarith)
          rw [le_div_iff₀ (by norm_num), Real.exp_neg]
          have hmul : (Real.exp y)⁻¹ * Real.exp y = 1 := inv_mul_cancel₀ (Real.exp_pos y).ne'
          have h2 : Real.exp y * Real.exp y = Real.exp (2 * y) := by rw [← Real.exp_add]; ring_nf
          nlinarith [Real.exp_pos y, inv_pos.mpr (Real.exp_pos y)]
        linarith
      have hrat_le : Real.cosh y / Real.sinh y ^ 2 ≤ 9 * Real.exp (-y) := by
        have hsq : (Real.exp y / 3) ^ 2 ≤ Real.sinh y ^ 2 :=
          pow_le_pow_left₀ (by positivity) hsinh_ge 2
        calc Real.cosh y / Real.sinh y ^ 2 ≤ Real.exp y / Real.sinh y ^ 2 :=
              div_le_div_of_nonneg_right hcosh_le (sq_nonneg _)
          _ ≤ Real.exp y / (Real.exp y / 3) ^ 2 :=
              div_le_div_of_nonneg_left (Real.exp_pos y).le (by positivity) hsq
          _ = 9 * Real.exp (-y) := by rw [Real.exp_neg]; field_simp [(Real.exp_pos y).ne']; ring
      have hrat_nn : 0 ≤ Real.cosh y / Real.sinh y ^ 2 := div_nonneg (Real.cosh_pos y).le (sq_nonneg _)
      calc Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2)
          ≤ y * (Real.cosh y / Real.sinh y ^ 2) := mul_le_mul_of_nonneg_right hlog_le hrat_nn
        _ ≤ y * (9 * Real.exp (-y)) := mul_le_mul_of_nonneg_left hrat_le hy0.le
        _ = 9 * y * Real.exp (-y) := by ring
  have hf_nn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ f y := fun y hy => by
    have hy0 : 0 < y := hy
    have hge1 : 1 ≤ 6 * (Real.sinh y - y) / y ^ 3 := by
      rw [one_le_div (pow_pos hy0 3)]
      let d0 : ℝ → ℝ := fun u => 6 * (Real.sinh u - u) - u ^ 3
      let d1 : ℝ → ℝ := fun u => 6 * (Real.cosh u - 1) - 3 * u ^ 2
      let d2 : ℝ → ℝ := fun u => 6 * Real.sinh u - 6 * u
      have hd2 : ∀ u ≥ 0, 0 ≤ d2 u := fun u hu => by
        dsimp [d2]; rcases eq_or_lt_of_le hu with rfl | hpos; · simp
        linarith [sinh_gt_id hpos]
      have hd1 : ∀ u ≥ 0, 0 ≤ d1 u := fun u hu =>
        nonneg_of_zero_of_deriv_nonneg' (by simp [d1]) hd2 (fun s => by
          have h1 := ((Real.hasDerivAt_cosh s).sub (hasDerivAt_const s 1)).const_mul 6
          have h2 := (hasDerivAt_pow 2 s).const_mul 3
          exact (h1.sub h2).congr_deriv (by dsimp [d2]; ring)) hu
      have h0 := nonneg_of_zero_of_deriv_nonneg' (g := d0) (by simp [d0]) hd1 (fun s => by
        have h1 := ((Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)).const_mul 6
        have h2 := hasDerivAt_pow 3 s
        exact (h1.sub h2).congr_deriv rfl) hy0.le
      dsimp [d0] at h0; linarith
    exact mul_nonneg (Real.log_nonneg hge1) (div_nonneg (Real.cosh_pos y).le (sq_nonneg _))
  have hGamma2 : IntegrableOn (fun y : ℝ => y * Real.exp (-y)) (Ioi (0 : ℝ)) ∧
      ∫ y in Ioi (0 : ℝ), y * Real.exp (-y) = 1 := by
    have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < 2 by norm_num)
    have hEq := Real.Gamma_eq_integral (show (0 : ℝ) < 2 by norm_num)
    rw [Real.Gamma_two] at hEq
    refine ⟨hG.congr_fun (fun y _ => by dsimp only; rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]) measurableSet_Ioi, ?_⟩
    rw [hEq]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => by rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]
  have hg_int_left : IntegrableOn g (Ioc (0 : ℝ) 1) := by
    refine (integrableOn_const (by simp) : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (Ioc 0 1)).congr_fun ?_ measurableSet_Ioc
    intro y hy; simp [g, hy.2]
  have hg_int_right : IntegrableOn g (Ioi (1 : ℝ)) := by
    have h2 : IntegrableOn (fun y : ℝ => 9 * y * Real.exp (-y)) (Ioi (1 : ℝ)) := by
      refine (IntegrableOn.mono_set (hGamma2.1.const_mul 9) (Ioi_subset_Ioi zero_le_one)).congr_fun ?_ measurableSet_Ioi
      intro y _; ring
    exact h2.congr_fun (fun y hy => by dsimp [g]; rw [if_neg (not_le.mpr hy)]) measurableSet_Ioi
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    rw [show Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact hg_int_left.union hg_int_right
  have hf_cont : ContinuousOn f (Ioi (0 : ℝ)) := by
    refine (ContinuousOn.log ?_ ?_).mul ?_
    · exact (continuous_const.mul (Real.continuous_sinh.sub continuous_id)).continuousOn.div
        (continuous_id.pow 3).continuousOn (fun y (hy : 0 < y) => (pow_pos hy 3).ne')
    · intro y (hy : 0 < y)
      exact (div_pos (mul_pos (by norm_num) (by linarith [sinh_gt_id hy])) (pow_pos hy 3)).ne'
    · exact Real.continuous_cosh.continuousOn.div (Real.continuous_sinh.pow 2).continuousOn
        (fun y (hy : 0 < y) => (sq_pos_of_pos (lt_trans hy (sinh_gt_id hy))).ne')
  have hf_int : IntegrableOn f (Ioi (0 : ℝ)) :=
    hg_int.mono' (hf_cont.aestronglyMeasurable measurableSet_Ioi) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Real.norm_of_nonneg (hf_nn y hy)]
      exact hf_le y hy)
  have hle_int : ∫ y in Ioi (0 : ℝ), f y ≤ ∫ y in Ioi (0 : ℝ), g y :=
    setIntegral_mono_on hf_int hg_int measurableSet_Ioi hf_le
  have hval_g : ∫ y in Ioi (0 : ℝ), g y ≤ 12 := by
    have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
      Set.disjoint_left.mpr fun y h1 h2 => by linarith [h1.2, Set.mem_Ioi.mp h2]
    rw [show Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm,
      setIntegral_union hdisj measurableSet_Ioi hg_int_left hg_int_right]
    have hleft : ∫ y in Ioc (0 : ℝ) 1, g y = 2 := by
      have hcongr : ∫ y in Ioc (0 : ℝ) 1, g y = ∫ y in Ioc (0 : ℝ) 1, (2 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioc (fun y hy => by simp [g, hy.2])
      rw [hcongr, setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal zero_le_one, one_mul]
    have hright : ∫ y in Ioi (1 : ℝ), g y ≤ 10 := by
      have heq : ∫ y in Ioi (1 : ℝ), g y = 9 * ∫ y in Ioi (1 : ℝ), y * Real.exp (-y) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        dsimp [g]; rw [if_neg (not_le.mpr hy)]; ring
      rw [heq]
      have hmono : ∫ y in Ioi (1 : ℝ), y * Real.exp (-y) ≤ ∫ y in Ioi (0 : ℝ), y * Real.exp (-y) :=
        setIntegral_mono_set hGamma2.1 (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 0 < y); positivity)
          (Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
      rw [hGamma2.2] at hmono
      linarith
    linarith
  exact hle_int.trans hval_g

/-- Uniform bounds on derivatives of order `1, 2, 3` of `θ_- = CtOuter.outerTheta (-1)` on `ℝ`. -/
lemma outerTheta_neg_deriv_uniform_bounds :
    ∃ M₁ M₂ M₃ : ℝ, 0 < M₁ ∧ 0 < M₂ ∧ 0 < M₃ ∧ ∀ τ : ℝ,
      |deriv (CtOuter.outerTheta (-1)) τ| ≤ M₁ ∧
      |iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ| ≤ M₂ ∧
      |iteratedDeriv 3 (CtOuter.outerTheta (-1)) τ| ≤ M₃ := by
  have hbound_n : ∀ n : ℕ, 0 < n → ∃ M : ℝ, 0 < M ∧ ∀ τ : ℝ, |iteratedDeriv n (CtOuter.outerTheta (-1)) τ| ≤ M := by
    intro n hn
    obtain ⟨C_out, hC_out⟩ := CtOuter.theta_neg_deriv_bound hn
    have hcont : Continuous (iteratedDeriv n (CtOuter.outerTheta (-1))) :=
      (CtOuter.contDiff_outerTheta (-1)).continuous_iteratedDeriv n (by simp)
    obtain ⟨C_in, hC_in⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-1 : ℝ) 1) hcont.continuousOn
    refine ⟨max 1 (max C_in (max 0 C_out)), lt_of_lt_of_le one_pos (le_max_left _ _), fun τ => ?_⟩
    by_cases hτ : |τ| ≤ 1
    · exact (hC_in τ (abs_le.mp hτ)).trans ((le_max_left _ _).trans (le_max_right 1 _))
    · have h1 : 1 ≤ |τ| := (not_le.mp hτ).le
      have hdecay : (1 + |τ|) ^ 2 * Real.exp (-π * |τ|) ≤ 1 := by
        rw [show -π * |τ| = -(π * |τ|) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        have h2 := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ π * |τ|) 3
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
          Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add] at h2
        have hpi : (3 : ℝ) < π := Real.pi_gt_three
        have hpi2 : (9 : ℝ) ≤ π ^ 2 := by nlinarith only [hpi]
        have hsq : 9 * |τ| ^ 2 ≤ (π * |τ|) ^ 2 := by rw [mul_pow]; nlinarith only [hpi2, sq_nonneg |τ|]
        have hlin : 3 * |τ| ≤ π * |τ| := by nlinarith only [hpi, abs_nonneg τ]
        nlinarith only [h2, hsq, hlin, abs_nonneg τ, sq_nonneg |τ|]
      have hbd := hC_out τ h1
      calc |iteratedDeriv n (CtOuter.outerTheta (-1)) τ|
          ≤ C_out * ((1 + |τ|) ^ 2 * Real.exp (-π * |τ|)) := hbd
        _ ≤ max 0 C_out * ((1 + |τ|) ^ 2 * Real.exp (-π * |τ|)) :=
            mul_le_mul_of_nonneg_right (le_max_right 0 C_out) (by positivity)
        _ ≤ max 0 C_out * 1 := mul_le_mul_of_nonneg_left hdecay (le_max_left 0 C_out)
        _ = max 0 C_out := mul_one _
        _ ≤ max 1 (max C_in (max 0 C_out)) := (le_max_right C_in (max 0 C_out)).trans (le_max_right 1 _)
  obtain ⟨M₁, hM₁, h1⟩ := hbound_n 1 one_pos
  obtain ⟨M₂, hM₂, h2⟩ := hbound_n 2 two_pos
  obtain ⟨M₃, hM₃, h3⟩ := hbound_n 3 (by norm_num)
  refine ⟨M₁, M₂, M₃, hM₁, hM₂, hM₃, fun τ => ⟨?_, h2 τ, h3 τ⟩⟩
  simpa [iteratedDeriv_one] using h1 τ

/-! ### Section 2: `edgePhi` smoothness and derivative bounds -/

private lemma edgePhi_contDiff3 (L : ℝ) : ContDiff ℝ 3 (edgePhi L) := by
  rw [show edgePhi L = fun τ => L * τ - π ^ 2 / 36 * τ ^ 3 + edgeR τ from funext (edgePhi_eq_cubic_add_ceHth L)]
  exact (((contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 3))).add edgeR_contDiff)

private lemma edgePhiDeriv2_abs_le_two (τ : ℝ) : |edgePhiDeriv2 τ| ≤ 2 := by
  by_cases hτ : τ = 0
  · subst hτ; simp [edgePhiDeriv2]
  · rcases le_or_gt |τ| 1 with h1 | h1
    · have hpi2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
      exact (edgePhiDeriv2_abs_le hτ).trans ((min_le_left _ _).trans (by nlinarith [abs_nonneg τ]))
    · exact (edgePhiDeriv2_abs_le hτ).trans ((min_le_right _ _).trans
        ((inv_le_one_iff₀.mpr (Or.inr h1.le)).trans (by norm_num)))

private lemma edgePhi_iteratedDeriv_eq (L τ : ℝ) :
    deriv (edgePhi L) τ = edgePhiDeriv L τ ∧
    iteratedDeriv 2 (edgePhi L) τ = edgePhiDeriv2 τ ∧
    |iteratedDeriv 3 (edgePhi L) τ| ≤ 7 := by
  have hd1 : deriv (edgePhi L) = edgePhiDeriv L := funext fun t => (hasDerivAt_edgePhi L t).deriv
  have hd2 : iteratedDeriv 2 (edgePhi L) = edgePhiDeriv2 := funext fun t => by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd1]; exact (hasDerivAt_edgePhiDeriv L t).deriv
  refine ⟨congrFun hd1 τ, congrFun hd2 τ, ?_⟩
  let p : ℝ → ℝ := fun s => L * s - π ^ 2 / 36 * s ^ 3
  have hp_cd : ContDiff ℝ 3 p := (contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 3))
  have hdecomp : edgePhi L = fun s => p s + edgeR s := funext (edgePhi_eq_cubic_add_ceHth L)
  have hp1 : deriv p = fun s => L - π ^ 2 / 12 * s ^ 2 := funext fun s =>
    (((hasDerivAt_id s).const_mul L).sub ((hasDerivAt_pow 3 s).const_mul (π ^ 2 / 36))).congr_deriv (by simp; ring) |>.deriv
  have hp2 : deriv (deriv p) = fun s => -(π ^ 2 / 6) * s := by
    rw [hp1]; exact funext fun s =>
      ((hasDerivAt_const s L).sub ((hasDerivAt_pow 2 s).const_mul (π ^ 2 / 12))).congr_deriv (by simp; ring) |>.deriv
  have hp3 : iteratedDeriv 3 p τ = -(π ^ 2 / 6) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hp2]
    exact ((hasDerivAt_id τ).const_mul (-(π ^ 2 / 6))).congr_deriv (by ring) |>.deriv
  rw [hdecomp, iteratedDeriv_fun_add hp_cd.contDiffAt edgeR_contDiff.contDiffAt, hp3]
  have htri : |-(π ^ 2 / 6) + iteratedDeriv 3 edgeR τ| ≤ π ^ 2 / 6 + π ^ 2 / 2 :=
    (abs_add_le _ _).trans (by
      rw [abs_neg, abs_of_pos (by positivity)]
      exact add_le_add le_rfl (edgeR_deriv_bounds τ).2.2.2)
  have hpi2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  linarith

private lemma edgePhi_sub_linear_bounds (L τ : ℝ) :
    |edgePhi L τ - L * τ| ≤ 2 * |τ| ^ 3 ∧
    |edgePhiDeriv L τ - L| ≤ 2 * τ ^ 2 ∧
    |edgePhiDeriv2 τ| ≤ 2 * |τ| := by
  have hpi2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have h2 : ∀ t : ℝ, |edgePhiDeriv2 t| ≤ 2 * |t| := fun t => by
    by_cases ht : t = 0
    · subst ht; simp [edgePhiDeriv2]
    · exact (edgePhiDeriv2_abs_le ht).trans ((min_le_left _ _).trans (by nlinarith [abs_nonneg t]))
  have h1 : ∀ t : ℝ, |edgePhiDeriv L t - L| ≤ 2 * t ^ 2 := fun t => by
    have h0 : edgePhiDeriv L 0 - L = 0 := by simp [edgePhiDeriv]
    have hdiff : ∀ s : ℝ, HasDerivAt (fun u => edgePhiDeriv L u - L) (edgePhiDeriv2 s) s :=
      fun s => (hasDerivAt_edgePhiDeriv L s).sub_const L
    have hcont : Continuous edgePhiDeriv2 := by
      have : edgePhiDeriv2 = iteratedDeriv 2 (edgePhi L) := funext fun s => (edgePhi_iteratedDeriv_eq L s).2.1.symm
      rw [this]; exact (edgePhi_contDiff3 L).continuous_iteratedDeriv 2 (by decide)
    have hftc : edgePhiDeriv L t - L = ∫ s in (0 : ℝ)..t, edgePhiDeriv2 s := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hdiff s) (hcont.intervalIntegrable 0 t), h0, sub_zero]
    rw [hftc]
    have hbd : ‖∫ s in (0 : ℝ)..t, edgePhiDeriv2 s‖ ≤ (2 * |t|) * |t - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
        rw [Real.norm_eq_abs]
        have hs_le : |s| ≤ |t| := by
          rw [Set.mem_uIoc] at hs
          rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_pos h1, abs_of_pos (lt_of_lt_of_le h1 h2)]; exact h2
          · rw [abs_of_nonpos h2, abs_of_neg (lt_of_lt_of_le h1 h2)]; linarith
        exact (h2 s).trans (by nlinarith)
    rw [Real.norm_eq_abs, sub_zero] at hbd
    exact hbd.trans_eq (by rw [← sq_abs t]; ring)
  have h0_val : edgePhi L 0 - L * 0 = 0 := by
    simp [edgePhi, stripS0Tilde]
  have hdiff0 : ∀ s : ℝ, HasDerivAt (fun u => edgePhi L u - L * u) (edgePhiDeriv L s - L) s := fun s =>
    (hasDerivAt_edgePhi L s).sub (((hasDerivAt_id s).const_mul L).congr_deriv (mul_one L))
  have hcont1 : Continuous (fun s => edgePhiDeriv L s - L) := by
    have : edgePhiDeriv L = deriv (edgePhi L) := funext fun s => (hasDerivAt_edgePhi L s).deriv.symm
    rw [this]; exact ((edgePhi_contDiff3 L).continuous_deriv (by decide)).sub continuous_const
  have hftc0 : edgePhi L τ - L * τ = ∫ s in (0 : ℝ)..τ, (edgePhiDeriv L s - L) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hdiff0 s) (hcont1.intervalIntegrable 0 τ),
      h0_val, sub_zero]
  refine ⟨?_, h1 τ, h2 τ⟩
  rw [hftc0]
  have hbd : ‖∫ s in (0 : ℝ)..τ, (edgePhiDeriv L s - L)‖ ≤ (2 * τ ^ 2) * |τ - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
      rw [Real.norm_eq_abs]
      have hs_le : |s| ≤ |τ| := by
        rw [Set.mem_uIoc] at hs
        rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_pos ha, abs_of_pos (lt_of_lt_of_le ha hb)]; exact hb
        · rw [abs_of_nonpos hb, abs_of_neg (lt_of_lt_of_le ha hb)]; linarith
      have hsq : s ^ 2 ≤ τ ^ 2 := by rw [← sq_abs s, ← sq_abs τ]; exact pow_le_pow_left₀ (abs_nonneg _) hs_le 2
      exact (h1 s).trans (by linarith)
  rw [Real.norm_eq_abs, sub_zero] at hbd
  exact hbd.trans_eq (by rw [← sq_abs τ]; ring)

/-! ### Section 3: Two-fold IBP for a general `C³` phase -/

/-- Two-fold integration by parts for a `C²` amplitude `f` supported in `[-M, M]` against
`e^{i ψ(τ)}` where `ψ ∈ C³` satisfies `|ψ'| ≥ Λ > 0`, `|ψ''| ≤ K₂`, `|ψ'''| ≤ K₃` on `[-M, M]`. -/
lemma ibp_two_phase {M Λ K₂ K₃ : ℝ} (hM : 0 < M) (hΛ : 0 < Λ) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    {f : ℝ → ℂ} {ψ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hψ : ContDiff ℝ 3 ψ)
    (hsupp : ∀ τ : ℝ, M ≤ |τ| → f τ = 0)
    (hψ1 : ∀ τ ∈ Icc (-M) M, Λ ≤ |deriv ψ τ|)
    (hψ2 : ∀ τ ∈ Icc (-M) M, |iteratedDeriv 2 ψ τ| ≤ K₂)
    (hψ3 : ∀ τ ∈ Icc (-M) M, |iteratedDeriv 3 ψ τ| ≤ K₃) :
    ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * (ψ τ : ℂ))‖ ≤
      (Λ ^ (-(2 : ℝ)) + 3 * K₂ * Λ ^ (-(3 : ℝ)) + 3 * K₂ ^ 2 * Λ ^ (-(4 : ℝ)) + K₃ * Λ ^ (-(3 : ℝ))) *
        ∫ τ in Icc (-M) M, (‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖) := by
  have hψ'_ne : ∀ τ ∈ Icc (-M) M, deriv ψ τ ≠ 0 := fun τ hτ h0 => by
    have := hψ1 τ hτ; rw [h0, abs_zero] at this; linarith
  have hstep1 := ibp_one_phase hM (hf.of_le (by decide)) (hψ.of_le (by decide)) hsupp hψ'_ne
  have hsupp_f' : ∀ τ : ℝ, M ≤ |τ| → deriv f τ = 0 := fun τ hτ => by
    rcases lt_or_eq_of_le hτ with hgt | heq
    · have hev : f =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hgt] with s hs
        exact hsupp s hs.le
      rw [hev.deriv_eq, deriv_const]
    · have hcont : Continuous (deriv f) := hf.continuous_deriv (by decide)
      by_cases hpos : 0 ≤ τ
      · have hτM : τ = M := by rw [abs_of_nonneg hpos] at heq; exact heq.symm
        rw [hτM]
        have hseq : Tendsto (fun n : ℕ => M + 1 / ((n : ℝ) + 1)) atTop (𝓝 M) := by
          simpa using (tendsto_const_nhds (x := M)).add tendsto_one_div_add_atTop_nhds_zero_nat
        have hlim := hcont.continuousAt.tendsto.comp hseq
        have hzero : (fun n : ℕ => deriv f (M + 1 / ((n : ℝ) + 1))) = fun _ => 0 := funext fun n => by
          have hgt : M < |M + 1 / ((n : ℝ) + 1)| := by
            rw [abs_of_pos (by positivity)]; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
          have hev : f =ᶠ[𝓝 (M + 1 / ((n : ℝ) + 1))] fun _ => (0 : ℂ) := by
            filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hgt] with s hs
            exact hsupp s hs.le
          rw [hev.deriv_eq, deriv_const]
        have hlim0 : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (deriv f M)) := hlim.congr fun n => congrFun hzero n
        exact tendsto_nhds_unique hlim0 tendsto_const_nhds
      · have hτM : τ = -M := by rw [abs_of_neg (not_le.mp hpos)] at heq; linarith
        rw [hτM]
        have hseq : Tendsto (fun n : ℕ => -M - 1 / ((n : ℝ) + 1)) atTop (𝓝 (-M)) := by
          simpa using (tendsto_const_nhds (x := -M)).sub tendsto_one_div_add_atTop_nhds_zero_nat
        have hlim := hcont.continuousAt.tendsto.comp hseq
        have hzero : (fun n : ℕ => deriv f (-M - 1 / ((n : ℝ) + 1))) = fun _ => 0 := funext fun n => by
          have hgt : M < |-M - 1 / ((n : ℝ) + 1)| := by
            rw [abs_of_neg (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])]
            linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
          have hev : f =ᶠ[𝓝 (-M - 1 / ((n : ℝ) + 1))] fun _ => (0 : ℂ) := by
            filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hgt] with s hs
            exact hsupp s hs.le
          rw [hev.deriv_eq, deriv_const]
        have hlim0 : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (deriv f (-M))) := hlim.congr fun n => congrFun hzero n
        exact tendsto_nhds_unique hlim0 tendsto_const_nhds
  let p1 : ℝ → ℂ := fun t => ((deriv ψ t : ℝ) : ℂ)
  let p2 : ℝ → ℂ := fun t => ((iteratedDeriv 2 ψ t : ℝ) : ℂ)
  let p3 : ℝ → ℂ := fun t => ((iteratedDeriv 3 ψ t : ℝ) : ℂ)
  have hp1_d : ∀ t : ℝ, HasDerivAt p1 (p2 t) t := fun t => by
    have h := (hψ.differentiable_iteratedDeriv 1 (by decide) t).hasDerivAt
    rw [iteratedDeriv_one] at h
    exact h.ofReal_comp.congr_deriv (by dsimp [p2]; rw [iteratedDeriv_succ, iteratedDeriv_one])
  have hp2_d : ∀ t : ℝ, HasDerivAt p2 (p3 t) t := fun t => by
    have h := (hψ.differentiable_iteratedDeriv 2 (by decide) t).hasDerivAt
    exact h.ofReal_comp.congr_deriv (by
      show ((deriv (iteratedDeriv 2 ψ) t : ℝ) : ℂ) = p3 t
      dsimp [p3]; rw [← iteratedDeriv_succ (n := 2)])
  have hf_d : ∀ t : ℝ, HasDerivAt f (deriv f t) t := fun t => (hf.differentiable (by decide) t).hasDerivAt
  have hf'_d : ∀ t : ℝ, HasDerivAt (deriv f) (iteratedDeriv 2 f t) t := fun t => by
    have h := (hf.differentiable_iteratedDeriv 1 (by decide) t).hasDerivAt
    rw [iteratedDeriv_one] at h
    exact h.congr_deriv (by rw [iteratedDeriv_succ, iteratedDeriv_one])
  let q1 : ℝ → ℂ := fun t => (deriv f t * p1 t - f t * p2 t) / p1 t ^ 2
  let q2 : ℝ → ℂ := fun t => q1 t / p1 t
  let q2' : ℝ → ℂ := fun t =>
    iteratedDeriv 2 f t / p1 t ^ 2 - 3 * deriv f t * p2 t / p1 t ^ 3 +
    f t * (3 * p2 t ^ 2 / p1 t ^ 4 - p3 t / p1 t ^ 3)
  have hq1_eq : ∀ t ∈ Icc (-M) M, deriv (fun s : ℝ => f s / p1 s) t = q1 t := fun t ht => by
    have hne : p1 t ≠ 0 := by show ((deriv ψ t : ℝ) : ℂ) ≠ 0; exact_mod_cast hψ'_ne t ht
    exact ((hf_d t).div (hp1_d t) hne).deriv
  have hq2_d : ∀ t ∈ uIcc (-M) M, HasDerivAt q2 (q2' t) t := fun t ht => by
    rw [uIcc_of_le (by linarith)] at ht
    have hne : p1 t ≠ 0 := by show ((deriv ψ t : ℝ) : ℂ) ≠ 0; exact_mod_cast hψ'_ne t ht
    have hnum : HasDerivAt (fun s => deriv f s * p1 s - f s * p2 s)
        (iteratedDeriv 2 f t * p1 t - f t * p3 t) t := by
      have h1 := (hf'_d t).mul (hp1_d t)
      have h2 := (hf_d t).mul (hp2_d t)
      exact (h1.sub h2).congr_deriv (by ring)
    have hden : HasDerivAt (fun s => p1 s ^ 3) (3 * p1 t ^ 2 * p2 t) t :=
      ((hp1_d t).pow 3).congr_deriv (by ring)
    have hq2_eq : q2 = fun s => (deriv f s * p1 s - f s * p2 s) / p1 s ^ 3 := funext fun s => by
      dsimp [q2, q1]; ring
    rw [hq2_eq]
    have hd := hnum.div hden (pow_ne_zero 3 hne)
    refine hd.congr_deriv ?_
    dsimp [q2']
    field_simp [hne]
    ring
  have he_d : ∀ t ∈ uIcc (-M) M,
      HasDerivAt (fun s : ℝ => -Complex.I * Complex.exp (Complex.I * (ψ s : ℂ)))
        (p1 t * Complex.exp (Complex.I * (ψ t : ℂ))) t := fun t _ => by
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * (ψ s : ℂ)) (Complex.I * p1 t) t :=
      ((hψ.differentiable (by decide) t).hasDerivAt.ofReal_comp).const_mul Complex.I
    have h2 := ((Complex.hasDerivAt_exp _).comp t h1).const_mul (-Complex.I)
    refine h2.congr_deriv ?_
    calc -Complex.I * (Complex.exp (Complex.I * (ψ t : ℂ)) * (Complex.I * p1 t))
        = -(Complex.I * Complex.I) * p1 t * Complex.exp (Complex.I * (ψ t : ℂ)) := by ring
      _ = p1 t * Complex.exp (Complex.I * (ψ t : ℂ)) := by rw [Complex.I_mul_I]; ring
  have hcont_q2' : ContinuousOn q2' (Icc (-M) M) := by
    have hc_p1 : Continuous p1 := Complex.continuous_ofReal.comp (hψ.continuous_deriv (by decide))
    have hc_p2 : Continuous p2 := Complex.continuous_ofReal.comp (hψ.continuous_iteratedDeriv 2 (by decide))
    have hc_p3 : Continuous p3 := Complex.continuous_ofReal.comp (hψ.continuous_iteratedDeriv 3 le_rfl)
    have hc_f2 : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
    have hc_f1 : Continuous (deriv f) := hf.continuous_deriv (by decide)
    have hne : ∀ t ∈ Icc (-M) M, p1 t ≠ 0 := fun t ht => by show ((deriv ψ t : ℝ) : ℂ) ≠ 0; exact_mod_cast hψ'_ne t ht
    refine ((hc_f2.continuousOn.div (hc_p1.pow 2).continuousOn (fun t ht => pow_ne_zero 2 (hne t ht))).sub
      (((continuous_const.mul hc_f1).mul hc_p2).continuousOn.div (hc_p1.pow 3).continuousOn
        (fun t ht => pow_ne_zero 3 (hne t ht)))).add
      (hf.continuous.continuousOn.mul
        (((continuous_const.mul (hc_p2.pow 2)).continuousOn.div (hc_p1.pow 4).continuousOn
          (fun t ht => pow_ne_zero 4 (hne t ht))).sub
        (hc_p3.continuousOn.div (hc_p1.pow 3).continuousOn (fun t ht => pow_ne_zero 3 (hne t ht)))))
  have he'_int : IntervalIntegrable (fun t : ℝ => p1 t * Complex.exp (Complex.I * (ψ t : ℂ))) volume (-M) M := by
    have hcont : Continuous fun t : ℝ => p1 t * Complex.exp (Complex.I * (ψ t : ℂ)) :=
      (Complex.continuous_ofReal.comp (hψ.continuous_deriv (by decide))).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hψ.continuous)))
    exact hcont.intervalIntegrable (-M) M
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hq2_d he_d
    (hcont_q2'.intervalIntegrable_of_Icc (by linarith)) he'_int
  have hstep2 : ∫ τ in Icc (-M) M, deriv (fun t : ℝ => f t / p1 t) τ * Complex.exp (Complex.I * (ψ τ : ℂ)) =
      Complex.I * ∫ τ in Icc (-M) M, q2' τ * Complex.exp (Complex.I * (ψ τ : ℂ)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hlhs : ∫ τ in (-M)..M, deriv (fun t : ℝ => f t / p1 t) τ * Complex.exp (Complex.I * (ψ τ : ℂ)) =
        ∫ τ in (-M)..M, q2 τ * (p1 τ * Complex.exp (Complex.I * (ψ τ : ℂ))) := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le (by linarith)] at hτ
      have hne : p1 τ ≠ 0 := by show ((deriv ψ τ : ℝ) : ℂ) ≠ 0; exact_mod_cast hψ'_ne τ hτ
      rw [hq1_eq τ hτ]; dsimp [q2]; field_simp [hne]
    rw [hlhs, hparts]
    have hbdM : q2 M = 0 := by
      simp [q2, q1, hsupp M (by rw [abs_of_pos hM]), hsupp_f' M (by rw [abs_of_pos hM])]
    have hbdnM : q2 (-M) = 0 := by
      simp [q2, q1, hsupp (-M) (by rw [abs_neg, abs_of_pos hM]), hsupp_f' (-M) (by rw [abs_neg, abs_of_pos hM])]
    rw [hbdM, hbdnM, zero_mul, zero_mul, sub_self, zero_sub, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun τ _ => by ring
  rw [hstep1, hstep2, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  have hq2'_bd : ∀ τ ∈ Icc (-M) M,
      ‖q2' τ‖ ≤ (Λ ^ (-(2 : ℝ)) + 3 * K₂ * Λ ^ (-(3 : ℝ)) + 3 * K₂ ^ 2 * Λ ^ (-(4 : ℝ)) + K₃ * Λ ^ (-(3 : ℝ))) *
        (‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖) := fun τ hτ => by
    have hp1_ge : Λ ≤ ‖p1 τ‖ := by simpa [p1, Complex.norm_real, Real.norm_eq_abs] using hψ1 τ hτ
    have hp2_le : ‖p2 τ‖ ≤ K₂ := by simpa [p2, Complex.norm_real, Real.norm_eq_abs] using hψ2 τ hτ
    have hp3_le : ‖p3 τ‖ ≤ K₃ := by simpa [p3, Complex.norm_real, Real.norm_eq_abs] using hψ3 τ hτ
    have hpow_inv : ∀ k : ℕ, Λ ^ k ≤ ‖p1 τ‖ ^ k ∧ (Λ ^ k)⁻¹ = Λ ^ (-(k : ℝ)) := fun k => by
      refine ⟨pow_le_pow_left₀ hΛ.le hp1_ge k, ?_⟩
      rw [show (-(k : ℝ)) = (((-(k : ℤ)) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast, zpow_neg, zpow_natCast]
    have hA : ‖iteratedDeriv 2 f τ / p1 τ ^ 2‖ ≤ Λ ^ (-(2 : ℝ)) * ‖iteratedDeriv 2 f τ‖ := by
      rw [norm_div, norm_pow, div_eq_mul_inv, mul_comm]
      have h2 := hpow_inv 2
      have h2' : (Λ ^ 2)⁻¹ = Λ ^ (-(2 : ℝ)) := by simpa using h2.2
      have : (‖p1 τ‖ ^ 2)⁻¹ ≤ Λ ^ (-(2 : ℝ)) := h2' ▸ inv_anti₀ (pow_pos hΛ 2) h2.1
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hB : ‖3 * deriv f τ * p2 τ / p1 τ ^ 3‖ ≤ (3 * K₂ * Λ ^ (-(3 : ℝ))) * ‖deriv f τ‖ := by
      rw [norm_div, norm_mul, norm_mul, norm_pow, show ‖(3 : ℂ)‖ = 3 by norm_num]
      have h3 := hpow_inv 3
      have h3' : (Λ ^ 3)⁻¹ = Λ ^ (-(3 : ℝ)) := by simpa using h3.2
      have hinv : (‖p1 τ‖ ^ 3)⁻¹ ≤ Λ ^ (-(3 : ℝ)) := h3' ▸ inv_anti₀ (pow_pos hΛ 3) h3.1
      calc 3 * ‖deriv f τ‖ * ‖p2 τ‖ / ‖p1 τ‖ ^ 3
          = (3 * ‖p2 τ‖ * (‖p1 τ‖ ^ 3)⁻¹) * ‖deriv f τ‖ := by ring
        _ ≤ (3 * K₂ * Λ ^ (-(3 : ℝ))) * ‖deriv f τ‖ := by gcongr
    have hC : ‖f τ * (3 * p2 τ ^ 2 / p1 τ ^ 4 - p3 τ / p1 τ ^ 3)‖ ≤
        (3 * K₂ ^ 2 * Λ ^ (-(4 : ℝ)) + K₃ * Λ ^ (-(3 : ℝ))) * ‖f τ‖ := by
      rw [norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h3 := hpow_inv 3
      have h4 := hpow_inv 4
      have h3' : (Λ ^ 3)⁻¹ = Λ ^ (-(3 : ℝ)) := by simpa using h3.2
      have h4' : (Λ ^ 4)⁻¹ = Λ ^ (-(4 : ℝ)) := by simpa using h4.2
      have hinv3 : (‖p1 τ‖ ^ 3)⁻¹ ≤ Λ ^ (-(3 : ℝ)) := h3' ▸ inv_anti₀ (pow_pos hΛ 3) h3.1
      have hinv4 : (‖p1 τ‖ ^ 4)⁻¹ ≤ Λ ^ (-(4 : ℝ)) := h4' ▸ inv_anti₀ (pow_pos hΛ 4) h4.1
      calc ‖3 * p2 τ ^ 2 / p1 τ ^ 4 - p3 τ / p1 τ ^ 3‖
          ≤ ‖3 * p2 τ ^ 2 / p1 τ ^ 4‖ + ‖p3 τ / p1 τ ^ 3‖ := norm_sub_le _ _
        _ = 3 * ‖p2 τ‖ ^ 2 * (‖p1 τ‖ ^ 4)⁻¹ + ‖p3 τ‖ * (‖p1 τ‖ ^ 3)⁻¹ := by
            simp only [div_eq_mul_inv, norm_mul, norm_inv, norm_pow, show ‖(3 : ℂ)‖ = 3 by norm_num]
        _ ≤ 3 * K₂ ^ 2 * Λ ^ (-(4 : ℝ)) + K₃ * Λ ^ (-(3 : ℝ)) := by gcongr
    have htri : ‖q2' τ‖ ≤ ‖iteratedDeriv 2 f τ / p1 τ ^ 2‖ + ‖3 * deriv f τ * p2 τ / p1 τ ^ 3‖ +
        ‖f τ * (3 * p2 τ ^ 2 / p1 τ ^ 4 - p3 τ / p1 τ ^ 3)‖ := by
      dsimp only [q2']
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    have hnn1 : 0 ≤ Λ ^ (-(2 : ℝ)) := Real.rpow_nonneg hΛ.le _
    have hnn2 : 0 ≤ 3 * K₂ * Λ ^ (-(3 : ℝ)) := by positivity
    have hnn3 : 0 ≤ 3 * K₂ ^ 2 * Λ ^ (-(4 : ℝ)) + K₃ * Λ ^ (-(3 : ℝ)) := by positivity
    nlinarith [norm_nonneg (iteratedDeriv 2 f τ), norm_nonneg (deriv f τ), norm_nonneg (f τ)]
  calc ‖∫ τ in Icc (-M) M, q2' τ * Complex.exp (Complex.I * (ψ τ : ℂ))‖
      ≤ ∫ τ in Icc (-M) M, ‖q2' τ * Complex.exp (Complex.I * (ψ τ : ℂ))‖ := norm_integral_le_integral_norm _
    _ = ∫ τ in Icc (-M) M, ‖q2' τ‖ := setIntegral_congr_fun measurableSet_Icc fun τ _ => by
        rw [norm_mul, show Complex.I * (ψ τ : ℂ) = (ψ τ : ℂ) * Complex.I by ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
    _ ≤ ∫ τ in Icc (-M) M, (Λ ^ (-(2 : ℝ)) + 3 * K₂ * Λ ^ (-(3 : ℝ)) +
          3 * K₂ ^ 2 * Λ ^ (-(4 : ℝ)) + K₃ * Λ ^ (-(3 : ℝ))) *
          (‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖) := by
        refine setIntegral_mono_on (hcont_q2'.norm.integrableOn_compact isCompact_Icc)
          ((((hf.continuous_iteratedDeriv 2 le_rfl).norm.add (hf.continuous_deriv (by decide)).norm).add
            hf.continuous.norm).continuousOn.integrableOn_compact isCompact_Icc |>.const_mul _)
          measurableSet_Icc hq2'_bd
    _ = _ := integral_const_mul _ _

/-! ### Section 4: The four far-band pieces -/

/-- Exact identity relating the linear reference value to `c⁻¹ * uctIflHhat L̃`. -/
private lemma linear_ref_eq_uctIflHhat {c Ltilde : ℝ} (hc : 0 < c) (hL : 0 < Ltilde) :
    c ^ (-(1 / 2 : ℝ)) * (π ^ 2 / 4 * |uctCAi|) *
        ((1 / √π) * (c * Ltilde) ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / c) * (c * Ltilde))) =
      c⁻¹ * uctIflHhat Ltilde := by
  unfold uctIflHhat uctAlphaHhat
  rw [Real.mul_rpow hc.le hL.le, show -(1 / c) * (c * Ltilde) = -Ltilde by field_simp [hc.ne']]
  have hpi : π ^ 2 * (1 / √π) = π ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg Real.pi_pos.le, ← Real.rpow_natCast π 2,
      ← Real.rpow_add Real.pi_pos]; norm_num
  have hc_pow : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c⁻¹ := by
    rw [← Real.rpow_add hc, show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  calc c ^ (-(1 / 2 : ℝ)) * (π ^ 2 / 4 * |uctCAi|) *
        ((1 / √π) * (c ^ (-(1 / 2 : ℝ)) * Ltilde ^ (-(1 / 2 : ℝ))) * Real.exp (-Ltilde))
      = (c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ))) *
        ((π ^ 2 * (1 / √π)) * |uctCAi| / 4 * Ltilde ^ (-(1 / 2 : ℝ)) * Real.exp (-Ltilde)) := by ring
    _ = c⁻¹ * (π ^ (3 / 2 : ℝ) / 4 * |uctCAi| * Ltilde ^ (-(1 / 2 : ℝ)) * Real.exp (-Ltilde)) := by
        rw [hc_pow, hpi]; ring

/-- For `L ≥ 6`, `tauStar L / 2 ≥ 1`. -/
private lemma one_le_tauStar_half {L : ℝ} (hL : 6 ≤ L) : 1 ≤ tauStar L / 2 := by
  have hL1 : ¬(L ≤ 1) := by linarith
  rw [tauStar, if_neg hL1, div_div, one_le_div (by positivity)]
  have hexp52 : 2 * π ≤ Real.exp (5 / 2 : ℝ) := by
    have h1 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h52 : Real.exp (5 / 2 : ℝ) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 2 : ℝ) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; norm_num
    rw [h52]
    have hpi : π < 3.15 := Real.pi_lt_d2
    have hprod : (2.7 : ℝ) * 2.7 * (3 / 2) ≤ Real.exp 1 * Real.exp 1 * Real.exp (1 / 2 : ℝ) := by gcongr
    have hnum : (2 : ℝ) * 3.15 ≤ 2.7 * 2.7 * (3 / 2) := by norm_num
    linarith
  have hle := hexp52.trans (Real.exp_le_exp.mpr (by linarith : (5 / 2 : ℝ) ≤ (L - 1) / 2))
  linarith

/-- Piece 1: Far tail `(1 - χ_T) * A * R` is `O(c^{-2} L^{-2})` for `c ≥ 60`, `L ≥ max 6 ((1/4) log c)`. -/
private lemma far_tail_bound {η C₀ : ℝ} (hη : 0 < η) (hC₀ : 0 ≤ C₀) :
    ∃ C_tail : ℝ, 0 < C_tail ∧ ∀ {c L : ℝ} {A : ℝ → ℂ},
      60 ≤ c → (1 / 4 : ℝ) * Real.log c ≤ L → 6 ≤ L →
      Continuous A → (∀ τ : ℝ, ‖A τ‖ ≤ C₀ * Real.exp (-η * |τ|)) →
      ‖((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ) *
        ∫ τ : ℝ, ((1 - smoothCutoff0 (τ / tauStar L) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ‖ ≤
        C_tail * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
  let K : ℝ := (π ^ 2 / 4 * |uctCAi|) * (2 * C₀ / η) *
    ((Nat.factorial 32 : ℝ) * (2 * π / η) ^ 32 * Real.exp 16)
  refine ⟨max 1 K, lt_of_lt_of_le one_pos (le_max_left _ _), fun {c L A} hc hLlog hL6 hA_cont hA_bd => ?_⟩
  have hc0 : 0 < c := by linarith
  have h1c : 0 < 1 / c := by positivity
  have hL1 : ¬(L ≤ 1) := by linarith
  have hT_eq : tauStar L = Real.exp ((L - 1) / 2) / π := by simp [tauStar, hL1]
  have hT_half : 1 ≤ tauStar L / 2 := one_le_tauStar_half hL6
  have hT_pos : 0 < tauStar L := by linarith
  let maj : ℝ → ℝ := fun τ => if tauStar L / 2 ≤ |τ| then C₀ * Real.exp (-η * |τ|) else 0
  have hmaj_int : Integrable maj ∧ ∫ τ : ℝ, maj τ = (2 * C₀ / η) * Real.exp (-η * (tauStar L / 2)) := by
    have hpos_int : IntegrableOn (fun t : ℝ => C₀ * Real.exp (-η * t)) (Ioi (tauStar L / 2)) := by
      have h := integrableOn_exp_mul_Ioi (a := -η) (by linarith) (tauStar L / 2)
      exact h.const_mul C₀
    have hpos_val : ∫ t in Ioi (tauStar L / 2), C₀ * Real.exp (-η * t) = (C₀ / η) * Real.exp (-η * (tauStar L / 2)) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (a := -η) (by linarith) (tauStar L / 2)]
      ring
    have heq : maj = (Iic (-(tauStar L / 2)) ∪ Ici (tauStar L / 2)).indicator (fun τ => C₀ * Real.exp (-η * |τ|)) := by
      ext τ; simp only [maj, Set.indicator, mem_union, mem_Iic, mem_Ici]
      by_cases h : tauStar L / 2 ≤ |τ|
      · have h' : τ ≤ -(tauStar L / 2) ∨ tauStar L / 2 ≤ τ := by
          rcases le_total 0 τ with ht | ht
          · rw [abs_of_nonneg ht] at h; exact Or.inr h
          · rw [abs_of_nonpos ht] at h; exact Or.inl (by linarith)
        simp [h, h']
      · have h' : ¬(τ ≤ -(tauStar L / 2) ∨ tauStar L / 2 ≤ τ) := by
          push Not; constructor <;> [linarith [neg_le_abs τ]; linarith [le_abs_self τ]]
        simp [h, h']
    have hdisj : Disjoint (Iic (-(tauStar L / 2))) (Ici (tauStar L / 2)) :=
      Set.disjoint_left.mpr fun τ h1 h2 => by linarith [mem_Iic.mp h1, mem_Ici.mp h2]
    have hint_R : IntegrableOn (fun τ : ℝ => C₀ * Real.exp (-η * |τ|)) (Ici (tauStar L / 2)) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact hpos_int.congr_fun (fun t (ht : tauStar L / 2 < t) => by rw [abs_of_pos (by linarith)]) measurableSet_Ioi
    have hint_L : IntegrableOn (fun τ : ℝ => C₀ * Real.exp (-η * |τ|)) (Iic (-(tauStar L / 2))) := by
      have hc' := hint_R.comp_neg
      have hset : -Ici (tauStar L / 2) = Iic (-(tauStar L / 2)) := by
        ext x; simp only [Set.mem_neg, mem_Iic, mem_Ici]; constructor <;> intro h <;> linarith
      rw [hset] at hc'
      exact hc'.congr_fun (fun τ _ => by simp [abs_neg]) measurableSet_Iic
    rw [heq]
    refine ⟨(integrable_indicator_iff (measurableSet_Iic.union measurableSet_Ici)).mpr (hint_L.union hint_R), ?_⟩
    rw [integral_indicator (measurableSet_Iic.union measurableSet_Ici),
      setIntegral_union hdisj measurableSet_Ici hint_L hint_R]
    have hR : ∫ τ in Ici (tauStar L / 2), C₀ * Real.exp (-η * |τ|) = (C₀ / η) * Real.exp (-η * (tauStar L / 2)) := by
      rw [integral_Ici_eq_integral_Ioi]
      calc ∫ τ in Ioi (tauStar L / 2), C₀ * Real.exp (-η * |τ|)
          = ∫ τ in Ioi (tauStar L / 2), C₀ * Real.exp (-η * τ) :=
            setIntegral_congr_fun measurableSet_Ioi (fun t (ht : tauStar L / 2 < t) => by rw [abs_of_pos (by linarith)])
        _ = (C₀ / η) * Real.exp (-η * (tauStar L / 2)) := hpos_val
    have hL' : ∫ τ in Iic (-(tauStar L / 2)), C₀ * Real.exp (-η * |τ|) = ∫ τ in Ici (tauStar L / 2), C₀ * Real.exp (-η * |τ|) := by
      have hcomp := Measure.integral_comp_mul_left
        (g := fun τ : ℝ => (Iic (-(tauStar L / 2))).indicator (fun x => C₀ * Real.exp (-η * |x|)) τ) (a := (-1 : ℝ))
      simp only [abs_inv, abs_neg, abs_one, inv_one, one_smul, neg_one_mul] at hcomp
      rw [integral_indicator measurableSet_Iic] at hcomp
      rw [← hcomp]
      have hind : (fun τ : ℝ => (Iic (-(tauStar L / 2))).indicator (fun x => C₀ * Real.exp (-η * |x|)) (-τ)) =
          (Ici (tauStar L / 2)).indicator (fun x => C₀ * Real.exp (-η * |x|)) := by
        ext τ; simp only [Set.indicator, mem_Iic, mem_Ici, abs_neg]
        by_cases h : tauStar L / 2 ≤ τ
        · simp [h, show -τ ≤ -(tauStar L / 2) by linarith]
        · simp [h, show ¬(-τ ≤ -(tauStar L / 2)) by linarith]
      rw [hind, integral_indicator measurableSet_Ici]
    rw [hL', hR]; ring
  have hpt : ∀ τ : ℝ, ‖((1 - smoothCutoff0 (τ / tauStar L) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ‖ ≤ maj τ := fun τ => by
    dsimp only [maj]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ) =
        ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    split_ifs with h
    · have hτ_ne : τ ≠ 0 := fun h0 => by rw [h0, abs_zero] at h; linarith
      have hcut : |1 - smoothCutoff0 (τ / tauStar L)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [smoothCutoff0_nonneg (τ / tauStar L), smoothCutoff0_le_one (τ / tauStar L)]
      have hreg : ‖regSqrt (1 / c) τ‖ ≤ 1 :=
        (norm_regSqrt_le_abs_rpow h1c hτ_ne).trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
      calc |1 - smoothCutoff0 (τ / tauStar L)| * ‖A τ‖ * ‖regSqrt (1 / c) τ‖
          ≤ 1 * (C₀ * Real.exp (-η * |τ|)) * 1 := by gcongr; exact hA_bd τ
        _ = C₀ * Real.exp (-η * |τ|) := by ring
    · push Not at h
      have h1 : |τ / tauStar L| ≤ 1 / 2 := by rw [abs_div, abs_of_pos hT_pos, div_le_iff₀ hT_pos]; linarith
      rw [smoothCutoff0_eq_one h1, sub_self, abs_zero, zero_mul, zero_mul]
  have hcont_int : Continuous (fun τ : ℝ => ((1 - smoothCutoff0 (τ / tauStar L) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ) := by
    have hphi : Continuous (edgePhi L) := (edgePhi_contDiff3 L).continuous
    have hθ : Continuous (CtOuter.outerTheta (-1)) := (CtOuter.contDiff_outerTheta (-1)).continuous
    exact ((((Complex.continuous_ofReal.comp (continuous_const.sub (contDiff_smoothCutoff0.continuous.comp
      (continuous_id.div_const _)))).mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_const.mul hphi).sub hθ))))).mul hA_cont).mul
      (contDiff_regSqrt h1c).continuous)
  have hint_f : Integrable (fun τ : ℝ => ((1 - smoothCutoff0 (τ / tauStar L) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ) :=
    hmaj_int.1.mono' hcont_int.aestronglyMeasurable (Eventually.of_forall hpt)
  have hexp_decay : Real.exp (-η * (tauStar L / 2)) ≤
      (Nat.factorial 32 : ℝ) * (2 * π / η) ^ 32 * Real.exp 16 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
    have hx_pos : 0 < η * (tauStar L / 2) := by positivity
    have hpow := Real.pow_div_factorial_le_exp (η * (tauStar L / 2)) hx_pos.le 32
    have h1 : Real.exp (-η * (tauStar L / 2)) ≤ (Nat.factorial 32 : ℝ) / (η * (tauStar L / 2)) ^ 32 := by
      rw [show -η * (tauStar L / 2) = -(η * (tauStar L / 2)) by ring, Real.exp_neg,
        inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      rw [div_le_iff₀ (by positivity)] at hpow
      rw [div_mul_eq_mul_div, one_le_div (pow_pos hx_pos 32)]
      linarith
    have hT32 : (η * (tauStar L / 2)) ^ 32 = (η / (2 * π)) ^ 32 * Real.exp (16 * L - 16) := by
      rw [hT_eq, show η * (Real.exp ((L - 1) / 2) / π / 2) = (η / (2 * π)) * Real.exp ((L - 1) / 2) by ring,
        mul_pow, ← Real.exp_nat_mul]
      congr 2; ring
    have he16 : c ^ 2 * L ^ 2 ≤ Real.exp (16 * L) := by
      have hc2 : c ^ 2 ≤ Real.exp (8 * L) := by
        calc c ^ 2 = Real.exp (2 * Real.log c) := by
              rw [mul_comm, Real.exp_mul, Real.exp_log hc0, ← Real.rpow_natCast]; norm_num
          _ ≤ Real.exp (8 * L) := Real.exp_le_exp.mpr (by linarith)
      have hL2 : L ^ 2 ≤ Real.exp (8 * L) := by
        have hs := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ 8 * L) 3
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
          Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add] at hs
        nlinarith
      calc c ^ 2 * L ^ 2 ≤ Real.exp (8 * L) * Real.exp (8 * L) := mul_le_mul hc2 hL2 (sq_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (16 * L) := by rw [← Real.exp_add]; ring_nf
    calc Real.exp (-η * (tauStar L / 2))
        ≤ (Nat.factorial 32 : ℝ) / ((η / (2 * π)) ^ 32 * Real.exp (16 * L - 16)) := by rwa [← hT32]
      _ = (Nat.factorial 32 : ℝ) * (2 * π / η) ^ 32 * Real.exp 16 * (Real.exp (16 * L))⁻¹ := by
          rw [Real.exp_sub, div_pow, div_pow]
          field_simp [hη.ne', Real.pi_ne_zero, (Real.exp_pos (16 * L)).ne', (Real.exp_pos 16).ne']
      _ ≤ (Nat.factorial 32 : ℝ) * (2 * π / η) ^ 32 * Real.exp 16 * (c ^ 2 * L ^ 2)⁻¹ := by
          gcongr
      _ = (Nat.factorial 32 : ℝ) * (2 * π / η) ^ 32 * Real.exp 16 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
          rw [mul_inv, rpow_neg_two_eq', rpow_neg_two_eq']; ring
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hpref_le : c ^ (-(1 / 2 : ℝ)) / (2 * π) ≤ 1 := by
    have h1 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h2 : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    exact (div_le_one (by positivity)).mpr (h1.trans h2)
  have hint_le : ‖∫ τ : ℝ, ((1 - smoothCutoff0 (τ / tauStar L) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ‖ ≤ (2 * C₀ / η) * Real.exp (-η * (tauStar L / 2)) :=
    (norm_integral_le_integral_norm _).trans ((integral_mono hint_f.norm hmaj_int.1 hpt).trans_eq hmaj_int.2)
  calc c ^ (-(1 / 2 : ℝ)) / (2 * π) * (π ^ 2 / 4 * |uctCAi|) * ‖∫ τ : ℝ, _‖
      ≤ 1 * (π ^ 2 / 4 * |uctCAi|) * ((2 * C₀ / η) * Real.exp (-η * (tauStar L / 2))) := by gcongr
    _ ≤ (π ^ 2 / 4 * |uctCAi|) * ((2 * C₀ / η) *
          ((Nat.factorial 32 : ℝ) * (2 * π / η) ^ 32 * Real.exp 16 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)))) := by
        rw [one_mul]; gcongr
    _ = K * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by dsimp [K]; ring
    _ ≤ max 1 K * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
        gcongr; exact le_max_right 1 K

/-- Helper for `far_outer_bound`: integrability and bound on the four outer majorant terms. -/
private lemma far_outer_majorant_integral {η ς T : ℝ} (hη : 0 < η) (hς : 0 < ς) (hς1 : ς ≤ 1) (hT : 2 ≤ T) :
    let E_half : ℝ → ℝ := fun τ => Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))
    let P_32 : ℝ → ℝ := fun τ => if ς / 2 ≤ |τ| then |τ| ^ (-(3 / 2 : ℝ)) else 0
    let P_52 : ℝ → ℝ := fun τ => if ς / 2 ≤ |τ| then |τ| ^ (-(5 / 2 : ℝ)) else 0
    let Ann : ℝ → ℝ := fun τ =>
      (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) +
      (if T / 2 ≤ |τ| ∧ |τ| ≤ T then T ^ (-(5 / 2 : ℝ)) else 0)
    Integrable (fun τ => E_half τ + P_32 τ + P_52 τ + Ann τ) ∧
    ∫ τ : ℝ, (E_half τ + P_32 τ + P_52 τ + Ann τ) ≤ (16 + 4 * (1 / √η)) * ς ^ (-(3 / 2 : ℝ)) := by
  intro E_half P_32 P_52 Ann
  have hT_pos : 0 < T := by linarith
  have hE_int : Integrable E_half ∧ ∫ τ : ℝ, E_half τ = 2 * √π / √η := by
    have hG : IntegrableOn (fun t : ℝ => Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))) (Ioi (0 : ℝ)) ∧
        ∫ t in Ioi (0 : ℝ), Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) = √π / √η := by
      have hG0 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
      have hEq := Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 1 / 2)
      rw [Real.Gamma_one_half_eq] at hEq
      have hcov_int : IntegrableOn (fun t : ℝ => Real.exp (-η * t) * (η * t) ^ (-(1 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
        have hcomp := (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
          (f := fun u : ℝ => Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) 0 hη).mpr
          (by simpa [mul_zero] using hG0)
        exact hcomp.congr_fun (fun t _ => by dsimp only; rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num, neg_mul]) measurableSet_Ioi
      have hint : IntegrableOn (fun t : ℝ => Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
        refine IntegrableOn.congr_fun (hcov_int.const_mul (η ^ (1 / 2 : ℝ))) (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
        rw [Real.mul_rpow hη.le ht.le]
        have hcancel : η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hη]; norm_num
        calc η ^ (1 / 2 : ℝ) * (Real.exp (-η * t) * (η ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ))))
            = (η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ))) * (Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))) := by ring
          _ = Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) := by rw [hcancel, one_mul]
      refine ⟨hint, ?_⟩
      have hcov := MeasureTheory.integral_comp_mul_left_Ioi
        (fun u : ℝ => Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) 0 hη
      rw [mul_zero, smul_eq_mul, ← hEq] at hcov
      have hstep : ∫ t in Ioi (0 : ℝ), Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) =
          η ^ (1 / 2 : ℝ) * ∫ t in Ioi (0 : ℝ), Real.exp (-(η * t)) * (η * t) ^ ((1 / 2 : ℝ) - 1) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
        rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num, Real.mul_rpow hη.le ht.le, show -η * t = -(η * t) by ring]
        have hcancel : η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hη]; norm_num
        calc Real.exp (-(η * t)) * t ^ (-(1 / 2 : ℝ))
            = (η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ))) * (Real.exp (-(η * t)) * t ^ (-(1 / 2 : ℝ))) := by rw [hcancel, one_mul]
          _ = _ := by ring
      rw [hstep, hcov]
      have hpow : η ^ (1 / 2 : ℝ) * η⁻¹ = (√η)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hη, Real.sqrt_eq_rpow, ← Real.rpow_neg hη.le]; norm_num
      calc η ^ (1 / 2 : ℝ) * (η⁻¹ * √π) = (η ^ (1 / 2 : ℝ) * η⁻¹) * √π := by ring
        _ = (√η)⁻¹ * √π := by rw [hpow]
        _ = √π / √η := by rw [div_eq_mul_inv, mul_comm]
    have hpos : IntegrableOn E_half (Ioi 0) :=
      hG.1.congr_fun (fun τ hτ => by dsimp [E_half]; rw [abs_of_pos hτ]) measurableSet_Ioi
    have hneg : IntegrableOn E_half (Iio 0) := by
      have hc' := hG.1.comp_neg
      have h1 : IntegrableOn (fun τ : ℝ => Real.exp (-η * (-τ)) * (-τ) ^ (-(1 / 2 : ℝ))) (Iio 0) := by
        convert hc' using 1
        ext x; simp only [mem_Iio, Set.mem_neg, mem_Ioi]; constructor <;> intro h <;> linarith
      exact h1.congr_fun (fun τ hτ => by dsimp [E_half]; rw [abs_of_neg hτ]) measurableSet_Iio
    have hU : (Iio (0 : ℝ) ∪ Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume] univ := by
      rw [show (Iio (0 : ℝ) ∪ Ioi (0 : ℝ) : Set ℝ) = ({0} : Set ℝ)ᶜ by
        ext x; simp only [mem_union, mem_Iio, mem_Ioi, mem_compl_iff, mem_singleton_iff]; exact lt_or_lt_iff_ne,
        ae_eq_univ]
      exact compl_mem_ae_iff.mpr (measure_singleton 0)
    have hint : Integrable E_half := by rw [← integrableOn_univ]; exact (hneg.union hpos).congr_set_ae hU.symm
    refine ⟨hint, ?_⟩
    rw [show ∫ τ : ℝ, E_half τ = 2 * ∫ t in Ioi (0 : ℝ), Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) from
      integral_comp_abs (f := fun t => Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))), hG.2]; ring
  have hP_int : ∀ (p : ℝ), p < -1 →
      Integrable (fun τ : ℝ => if ς / 2 ≤ |τ| then |τ| ^ p else 0) ∧
      ∫ τ : ℝ, (if ς / 2 ≤ |τ| then |τ| ^ p else 0) = 2 * (-(ς / 2) ^ (p + 1) / (p + 1)) := fun p hp => by
    have hpos : IntegrableOn (fun t : ℝ => t ^ p) (Ioi (ς / 2)) := integrableOn_Ioi_rpow_of_lt hp (half_pos hς)
    have heq : (fun τ : ℝ => if ς / 2 ≤ |τ| then |τ| ^ p else 0) =
        (Iic (-(ς / 2)) ∪ Ici (ς / 2)).indicator (fun τ => |τ| ^ p) := by
      ext τ; simp only [Set.indicator, mem_union, mem_Iic, mem_Ici]
      by_cases h : ς / 2 ≤ |τ|
      · have h' : τ ≤ -(ς / 2) ∨ ς / 2 ≤ τ := by
          rcases le_total 0 τ with ht | ht
          · rw [abs_of_nonneg ht] at h; exact Or.inr h
          · rw [abs_of_nonpos ht] at h; exact Or.inl (by linarith)
        simp [h, h']
      · have h' : ¬(τ ≤ -(ς / 2) ∨ ς / 2 ≤ τ) := by
          push Not; constructor <;> [linarith [neg_le_abs τ]; linarith [le_abs_self τ]]
        simp [h, h']
    have hdisj : Disjoint (Iic (-(ς / 2))) (Ici (ς / 2)) :=
      Set.disjoint_left.mpr fun τ h1 h2 => by linarith [mem_Iic.mp h1, mem_Ici.mp h2]
    have hint_R : IntegrableOn (fun τ : ℝ => |τ| ^ p) (Ici (ς / 2)) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact hpos.congr_fun (fun t (ht : ς / 2 < t) => by rw [abs_of_pos (lt_trans (half_pos hς) ht)]) measurableSet_Ioi
    have hint_L : IntegrableOn (fun τ : ℝ => |τ| ^ p) (Iic (-(ς / 2))) := by
      have hc' := hint_R.comp_neg
      have hset : -Ici (ς / 2) = Iic (-(ς / 2)) := by ext x; simp only [Set.mem_neg, mem_Iic, mem_Ici]; constructor <;> intro h <;> linarith
      rw [hset] at hc'
      exact hc'.congr_fun (fun τ _ => by simp [abs_neg]) measurableSet_Iic
    rw [heq]
    refine ⟨(integrable_indicator_iff (measurableSet_Iic.union measurableSet_Ici)).mpr (hint_L.union hint_R), ?_⟩
    rw [integral_indicator (measurableSet_Iic.union measurableSet_Ici),
      setIntegral_union hdisj measurableSet_Ici hint_L hint_R]
    have hR : ∫ τ in Ici (ς / 2), |τ| ^ p = -(ς / 2) ^ (p + 1) / (p + 1) := by
      rw [integral_Ici_eq_integral_Ioi]
      calc ∫ τ in Ioi (ς / 2), |τ| ^ p
          = ∫ τ in Ioi (ς / 2), τ ^ p :=
            setIntegral_congr_fun measurableSet_Ioi (fun t (ht : ς / 2 < t) => by rw [abs_of_pos (lt_trans (half_pos hς) ht)])
        _ = -(ς / 2) ^ (p + 1) / (p + 1) := integral_Ioi_rpow_of_lt hp (half_pos hς)
    have hL' : ∫ τ in Iic (-(ς / 2)), |τ| ^ p = ∫ τ in Ici (ς / 2), |τ| ^ p := by
      have hcomp := Measure.integral_comp_mul_left
        (g := fun τ : ℝ => (Iic (-(ς / 2))).indicator (fun x => |x| ^ p) τ) (a := (-1 : ℝ))
      simp only [abs_inv, abs_neg, abs_one, inv_one, one_smul, neg_one_mul] at hcomp
      rw [integral_indicator measurableSet_Iic] at hcomp
      rw [← hcomp]
      have hind : (fun τ : ℝ => (Iic (-(ς / 2))).indicator (fun x => |x| ^ p) (-τ)) =
          (Ici (ς / 2)).indicator (fun x => |x| ^ p) := by
        ext τ; simp only [Set.indicator, mem_Iic, mem_Ici, abs_neg]
        by_cases h : ς / 2 ≤ τ
        · simp [h, show -τ ≤ -(ς / 2) by linarith]
        · simp [h, show ¬(-τ ≤ -(ς / 2)) by linarith]
      rw [hind, integral_indicator measurableSet_Ici]
    rw [hL', hR]; ring
  have hAnn_s : ∀ s : ℝ, 0 < s →
      Integrable (fun τ : ℝ => if s / 2 ≤ |τ| ∧ |τ| ≤ s then s ^ (-(5 / 2 : ℝ)) else 0) ∧
      ∫ τ : ℝ, (if s / 2 ≤ |τ| ∧ |τ| ≤ s then s ^ (-(5 / 2 : ℝ)) else 0) = s ^ (-(3 / 2 : ℝ)) := fun s hs => by
    have hset : {τ : ℝ | s / 2 ≤ |τ| ∧ |τ| ≤ s} = Icc (-s) (-(s / 2)) ∪ Icc (s / 2) s := by
      ext τ; simp only [mem_ofPred_eq, mem_union, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩; rcases le_total 0 τ with hτ | hτ
        · rw [abs_of_nonneg hτ] at h1 h2; exact Or.inr ⟨h1, h2⟩
        · rw [abs_of_nonpos hτ] at h1 h2; exact Or.inl ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rw [abs_of_nonpos (by linarith)]; exact ⟨by linarith, by linarith⟩
        · rw [abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩
    have heq : (fun τ : ℝ => if s / 2 ≤ |τ| ∧ |τ| ≤ s then s ^ (-(5 / 2 : ℝ)) else 0) =
        (Icc (-s) (-(s / 2)) ∪ Icc (s / 2) s).indicator (fun _ => s ^ (-(5 / 2 : ℝ))) := by
      ext τ; simp only [Set.indicator]
      by_cases h : τ ∈ Icc (-s) (-(s / 2)) ∪ Icc (s / 2) s
      · have h' : s / 2 ≤ |τ| ∧ |τ| ≤ s := by simpa [← hset] using h
        simp [h, h']
      · have h' : ¬(s / 2 ≤ |τ| ∧ |τ| ≤ s) := by simpa [← hset] using h
        simp [h, h']
    rw [heq]
    have hdisj : Disjoint (Icc (-s) (-(s / 2))) (Icc (s / 2) s) :=
      Set.disjoint_left.mpr fun τ h1 h2 => by linarith [h1.2, h2.1]
    refine ⟨(integrable_indicator_iff (measurableSet_Icc.union measurableSet_Icc)).mpr
      (integrableOn_const (by rw [measure_union hdisj measurableSet_Icc]; simp)), ?_⟩
    rw [integral_indicator (measurableSet_Icc.union measurableSet_Icc),
      setIntegral_union hdisj measurableSet_Icc (integrableOn_const (by simp)) (integrableOn_const (by simp)),
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
      Measure.real, Measure.real, Real.volume_Icc, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    calc (-(s / 2) - -s) * s ^ (-(5 / 2 : ℝ)) + (s - s / 2) * s ^ (-(5 / 2 : ℝ))
        = s ^ (1 : ℝ) * s ^ (-(5 / 2 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = s ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hs]; norm_num
  have hP32 := hP_int (-(3 / 2 : ℝ)) (by norm_num)
  have hP52 := hP_int (-(5 / 2 : ℝ)) (by norm_num)
  have hAnn_int : Integrable Ann ∧ ∫ τ : ℝ, Ann τ = ς ^ (-(3 / 2 : ℝ)) + T ^ (-(3 / 2 : ℝ)) := by
    refine ⟨(hAnn_s ς hς).1.add (hAnn_s T hT_pos).1, ?_⟩
    rw [integral_add (hAnn_s ς hς).1 (hAnn_s T hT_pos).1, (hAnn_s ς hς).2, (hAnn_s T hT_pos).2]
  refine ⟨((hE_int.1.add hP32.1).add hP52.1).add hAnn_int.1, ?_⟩
  have hsum : ∫ τ : ℝ, (E_half τ + P_32 τ + P_52 τ + Ann τ) =
      2 * √π / √η + 4 * (ς / 2) ^ (-(1 / 2 : ℝ)) + (4 / 3) * (ς / 2) ^ (-(3 / 2 : ℝ)) +
      (ς ^ (-(3 / 2 : ℝ)) + T ^ (-(3 / 2 : ℝ))) := by
    rw [integral_add (f := fun τ => E_half τ + P_32 τ + P_52 τ) (g := Ann) ((hE_int.1.add hP32.1).add hP52.1) hAnn_int.1,
      integral_add (f := fun τ => E_half τ + P_32 τ) (g := P_52) (hE_int.1.add hP32.1) hP52.1,
      integral_add hE_int.1 hP32.1, hE_int.2, hP32.2, hP52.2, hAnn_int.2]
    norm_num; ring
  have h1_le : (1 : ℝ) ≤ ς ^ (-(3 / 2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hς hς1 (by norm_num)
  have hE_le : 2 * √π / √η ≤ 4 * (1 / √η) * ς ^ (-(3 / 2 : ℝ)) := by
    have hsqpi : √π ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; linarith [Real.pi_lt_four]
    have : 2 * √π / √η ≤ 4 * (1 / √η) := by rw [div_eq_mul_inv, one_div]; gcongr; linarith
    nlinarith [show 0 ≤ 4 * (1 / √η) by positivity]
  have h32_le : 4 * (ς / 2) ^ (-(1 / 2 : ℝ)) ≤ 8 * ς ^ (-(3 / 2 : ℝ)) := by
    have h1 : (ς / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 * ς ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, Real.mul_rpow hς.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
      have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        simpa using this
      gcongr
    have h2 : ς ^ (-(1 / 2 : ℝ)) ≤ ς ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hς hς1 (by norm_num)
    linarith
  have h52_le : (4 / 3 : ℝ) * (ς / 2) ^ (-(3 / 2 : ℝ)) ≤ 6 * ς ^ (-(3 / 2 : ℝ)) := by
    have h1 : (ς / 2) ^ (-(3 / 2 : ℝ)) ≤ 4 * ς ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, Real.mul_rpow hς.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
      have : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
        norm_num at this; exact this
      gcongr
    linarith
  have hT_le : T ^ (-(3 / 2 : ℝ)) ≤ ς ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hς (by linarith) (by norm_num)
  rw [hsum]; linarith

/-- Pointwise bound for `‖f''‖ + ‖f'‖ + ‖f‖` in `far_outer_bound`, extracted to keep heartbeat usage low. -/
private lemma far_outer_pointwise_bound {η Bχ CA ς T : ℝ} (hη : 0 < η) (hBχ_pos : 0 < Bχ)
    (hCA_nn : 0 ≤ CA) (hς_pos : 0 < ς) (hς_le1 : ς ≤ 1) (hT_ge2 : 2 ≤ T)
    {χ_out h : ℝ → ℂ} (hχ_cd : ContDiff ℝ 2 χ_out) (hh_cd : ContDiff ℝ 2 h)
    (hχ_bounds : ∀ τ : ℝ,
      ‖χ_out τ‖ ≤ (if ς / 2 ≤ |τ| then 1 else 0) ∧
      ‖deriv χ_out τ‖ ≤ (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) +
        (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T⁻¹ else 0) ∧
      ‖iteratedDeriv 2 χ_out τ‖ ≤ (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς ^ (-(2 : ℝ)) else 0) +
        (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T ^ (-(2 : ℝ)) else 0))
    (hh_bounds : ∀ τ : ℝ, τ ≠ 0 →
      ‖h τ‖ ≤ CA * Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) ∧
      ‖deriv h τ‖ ≤ 2 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) + |τ| ^ (-(3 / 2 : ℝ))) ∧
      ‖iteratedDeriv 2 h τ‖ ≤ 4 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) +
        |τ| ^ (-(3 / 2 : ℝ)) + |τ| ^ (-(5 / 2 : ℝ)))) :
    ∀ τ : ℝ, ‖iteratedDeriv 2 (fun t => χ_out t * h t) τ‖ +
        ‖deriv (fun t => χ_out t * h t) τ‖ + ‖χ_out τ * h τ‖ ≤
      38 * (1 + Bχ) * CA *
        (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) +
         (if ς / 2 ≤ |τ| then |τ| ^ (-(3 / 2 : ℝ)) else 0) +
         (if ς / 2 ≤ |τ| then |τ| ^ (-(5 / 2 : ℝ)) else 0) +
         ((if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) +
          (if T / 2 ≤ |τ| ∧ |τ| ≤ T then T ^ (-(5 / 2 : ℝ)) else 0))) := by
  intro τ
  have hT_pos : 0 < T := by linarith
  let E_half : ℝ → ℝ := fun t => Real.exp (-η * |t|) * |t| ^ (-(1 / 2 : ℝ))
  let P_32 : ℝ → ℝ := fun t => if ς / 2 ≤ |t| then |t| ^ (-(3 / 2 : ℝ)) else 0
  let P_52 : ℝ → ℝ := fun t => if ς / 2 ≤ |t| then |t| ^ (-(5 / 2 : ℝ)) else 0
  let Ann : ℝ → ℝ := fun t =>
    (if ς / 2 ≤ |t| ∧ |t| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) +
    (if T / 2 ≤ |t| ∧ |t| ≤ T then T ^ (-(5 / 2 : ℝ)) else 0)
  let f : ℝ → ℂ := fun t => χ_out t * h t
  show ‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖ ≤ 38 * (1 + Bχ) * CA * (E_half τ + P_32 τ + P_52 τ + Ann τ)
  by_cases hlt : |τ| < ς / 2
  · have h0 : ‖χ_out τ‖ = 0 := le_antisymm ((hχ_bounds τ).1.trans (by simp [not_le.mpr hlt])) (norm_nonneg _)
    have h1 : ‖deriv χ_out τ‖ = 0 := le_antisymm ((hχ_bounds τ).2.1.trans (by
      have hnt : ¬(T / 2 ≤ |τ| ∧ |τ| ≤ T) := fun hc' => by linarith [hc'.1]
      have hns : ¬(ς / 2 ≤ |τ| ∧ |τ| ≤ ς) := fun hc' => by linarith [hc'.1]
      simp [hns, hnt])) (norm_nonneg _)
    have h2 : ‖iteratedDeriv 2 χ_out τ‖ = 0 := le_antisymm ((hχ_bounds τ).2.2.trans (by
      have hnt : ¬(T / 2 ≤ |τ| ∧ |τ| ≤ T) := fun hc' => by linarith [hc'.1]
      have hns : ¬(ς / 2 ≤ |τ| ∧ |τ| ≤ ς) := fun hc' => by linarith [hc'.1]
      simp [hns, hnt])) (norm_nonneg _)
    have hf0 : ‖f τ‖ = 0 := by dsimp [f]; rw [norm_mul, h0, zero_mul]
    have hf1 : ‖deriv f τ‖ = 0 := le_antisymm ((deriv_mul_norm (hχ_cd.of_le (by decide)) (hh_cd.of_le (by decide)) τ).trans (by rw [h0, h1]; simp)) (norm_nonneg _)
    have hf2 : ‖iteratedDeriv 2 f τ‖ = 0 := le_antisymm ((leibniz_two_norm hχ_cd hh_cd τ).trans (by rw [h0, h1, h2]; simp)) (norm_nonneg _)
    rw [hf0, hf1, hf2, add_zero, add_zero]
    have h1 : 0 ≤ E_half τ := by dsimp [E_half]; positivity
    have h2 : 0 ≤ P_32 τ := by dsimp [P_32]; split_ifs <;> positivity
    have h3 : 0 ≤ P_52 τ := by dsimp [P_52]; split_ifs <;> positivity
    have h4 : 0 ≤ Ann τ := by dsimp [Ann]; positivity
    have h6 : 0 ≤ 38 * (1 + Bχ) * CA := by positivity
    exact mul_nonneg h6 (by linarith only [h1, h2, h3, h4])
  · have hge : ς / 2 ≤ |τ| := not_lt.mp hlt
    have hτ_ne : τ ≠ 0 := fun h0 => by rw [h0, abs_zero] at hge; linarith
    obtain ⟨hh0, hh1, hh2⟩ := hh_bounds τ hτ_ne
    obtain ⟨hχ0, hχ1, hχ2⟩ := hχ_bounds τ
    have hχ0' : ‖χ_out τ‖ ≤ 1 := hχ0.trans (by simp [hge])
    have hχ1_E : ‖deriv χ_out τ‖ * (CA * E_half τ) ≤ 2 * Bχ * CA * (E_half τ + Ann τ) := by
      have h1 : (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) * (CA * E_half τ) ≤
          2 * Bχ * CA * (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) := by
        split_ifs with hs
        · have he1 : Real.exp (-η * |τ|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hη, abs_nonneg τ])
          have hpow : |τ| ^ (-(1 / 2 : ℝ)) ≤ (ς / 2) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (half_pos hς_pos) hs.1 (by norm_num)
          have hhalf : (ς / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 * ς ^ (-(1 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.mul_rpow hς_pos.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
              Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
            have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
              have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
              simpa using this
            gcongr
          have hς_inv : ς⁻¹ * ς ^ (-(1 / 2 : ℝ)) ≤ ς ^ (-(5 / 2 : ℝ)) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hς_pos]
            exact Real.rpow_le_rpow_of_exponent_ge hς_pos hς_le1 (by norm_num)
          dsimp only [E_half]
          calc Bχ * ς⁻¹ * (CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))))
              ≤ Bχ * ς⁻¹ * (CA * (1 * (2 * ς ^ (-(1 / 2 : ℝ))))) := by gcongr; exact hpow.trans hhalf
            _ = 2 * Bχ * CA * (ς⁻¹ * ς ^ (-(1 / 2 : ℝ))) := by ring
            _ ≤ 2 * Bχ * CA * ς ^ (-(5 / 2 : ℝ)) := by gcongr
        · simp
      have h2 : (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T⁻¹ else 0) * (CA * E_half τ) ≤
          2 * Bχ * CA * E_half τ := by
        split_ifs with hT
        · have hTinv : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hT_ge2])
          have hEnn : 0 ≤ E_half τ := by dsimp [E_half]; positivity
          calc Bχ * T⁻¹ * (CA * E_half τ) ≤ Bχ * 1 * (CA * E_half τ) := by gcongr
            _ ≤ 2 * Bχ * CA * E_half τ := by
                have hnn : 0 ≤ Bχ * CA * E_half τ := by positivity
                linarith only [hnn]
        · rw [zero_mul]; dsimp [E_half]; positivity
      calc ‖deriv χ_out τ‖ * (CA * E_half τ)
          ≤ ((if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) +
             (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T⁻¹ else 0)) * (CA * E_half τ) :=
            mul_le_mul_of_nonneg_right hχ1 (by dsimp [E_half]; positivity)
        _ = (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) * (CA * E_half τ) +
            (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T⁻¹ else 0) * (CA * E_half τ) := add_mul _ _ _
        _ ≤ 2 * Bχ * CA * (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) +
            2 * Bχ * CA * E_half τ := add_le_add h1 h2
        _ ≤ 2 * Bχ * CA * (E_half τ + Ann τ) := by
            dsimp only [Ann]
            have hnn : 0 ≤ if T / 2 ≤ |τ| ∧ |τ| ≤ T then T ^ (-(5 / 2 : ℝ)) else 0 := by split_ifs <;> positivity
            have hbc : 0 ≤ 2 * Bχ * CA := by positivity
            nlinarith only [hnn, hbc]
    have hχ1_h0 : ‖deriv χ_out τ‖ * ‖h τ‖ ≤ 2 * Bχ * CA * (E_half τ + Ann τ) :=
      (mul_le_mul_of_nonneg_left hh0 (norm_nonneg _)).trans (by simpa [E_half, mul_assoc] using hχ1_E)
    have hχ1_h1 : ‖deriv χ_out τ‖ * ‖deriv h τ‖ ≤ 12 * Bχ * CA * (E_half τ + Ann τ) := by
      have hbd_s : ∀ s : ℝ, 0 < s → (if s / 2 ≤ |τ| ∧ |τ| ≤ s then Bχ * s⁻¹ else 0) * |τ| ^ (-(3 / 2 : ℝ)) ≤
          4 * Bχ * (if s / 2 ≤ |τ| ∧ |τ| ≤ s then s ^ (-(5 / 2 : ℝ)) else 0) := fun s hs => by
        split_ifs with hst
        · have hpow : |τ| ^ (-(3 / 2 : ℝ)) ≤ (s / 2) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (half_pos hs) hst.1 (by norm_num)
          have hhalf : (s / 2) ^ (-(3 / 2 : ℝ)) ≤ 4 * s ^ (-(3 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.mul_rpow hs.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
              Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
            have : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
              have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
              norm_num at this; exact this
            gcongr
          have hmul : s⁻¹ * s ^ (-(3 / 2 : ℝ)) = s ^ (-(5 / 2 : ℝ)) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hs]; norm_num
          calc Bχ * s⁻¹ * |τ| ^ (-(3 / 2 : ℝ)) ≤ Bχ * s⁻¹ * (4 * s ^ (-(3 / 2 : ℝ))) := by
                gcongr; exact hpow.trans hhalf
            _ = 4 * Bχ * (s⁻¹ * s ^ (-(3 / 2 : ℝ))) := by ring
            _ = 4 * Bχ * s ^ (-(5 / 2 : ℝ)) := by rw [hmul]
        · simp
      have hbd_32 : ‖deriv χ_out τ‖ * (CA * |τ| ^ (-(3 / 2 : ℝ))) ≤ 4 * Bχ * CA * Ann τ := by
        calc ‖deriv χ_out τ‖ * (CA * |τ| ^ (-(3 / 2 : ℝ)))
            ≤ ((if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) +
               (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T⁻¹ else 0)) * (CA * |τ| ^ (-(3 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_right hχ1 (by positivity)
          _ = CA * ((if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) * |τ| ^ (-(3 / 2 : ℝ)) +
                    (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T⁻¹ else 0) * |τ| ^ (-(3 / 2 : ℝ))) := by ring
          _ ≤ CA * (4 * Bχ * (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) +
                    4 * Bχ * (if T / 2 ≤ |τ| ∧ |τ| ≤ T then T ^ (-(5 / 2 : ℝ)) else 0)) :=
              mul_le_mul_of_nonneg_left (add_le_add (hbd_s ς hς_pos) (hbd_s T hT_pos)) hCA_nn
          _ = 4 * Bχ * CA * Ann τ := by dsimp [Ann]; ring
      calc ‖deriv χ_out τ‖ * ‖deriv h τ‖
          ≤ ‖deriv χ_out τ‖ * (2 * CA * (E_half τ + |τ| ^ (-(3 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left hh1 (norm_nonneg _)
        _ = 2 * (‖deriv χ_out τ‖ * (CA * E_half τ) + ‖deriv χ_out τ‖ * (CA * |τ| ^ (-(3 / 2 : ℝ)))) := by ring
        _ ≤ 2 * (2 * Bχ * CA * (E_half τ + Ann τ) + 4 * Bχ * CA * Ann τ) := by gcongr
        _ ≤ 12 * Bχ * CA * (E_half τ + Ann τ) := by
            have h1 : 0 ≤ Bχ * CA * E_half τ := by dsimp [E_half]; positivity
            have h2 : 0 ≤ Bχ * CA * Ann τ := by dsimp [Ann]; positivity
            linarith only [h1, h2]
    have hχ2_h0 : ‖iteratedDeriv 2 χ_out τ‖ * ‖h τ‖ ≤ 2 * Bχ * CA * Ann τ := by
      have hbd_s : ∀ s : ℝ, 0 < s → (if s / 2 ≤ |τ| ∧ |τ| ≤ s then Bχ * s ^ (-(2 : ℝ)) else 0) * |τ| ^ (-(1 / 2 : ℝ)) ≤
          2 * Bχ * (if s / 2 ≤ |τ| ∧ |τ| ≤ s then s ^ (-(5 / 2 : ℝ)) else 0) := fun s hs => by
        split_ifs with hst
        · have hpow : |τ| ^ (-(1 / 2 : ℝ)) ≤ (s / 2) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (half_pos hs) hst.1 (by norm_num)
          have hhalf : (s / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 * s ^ (-(1 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.mul_rpow hs.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
              Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
            have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
              have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
              simpa using this
            gcongr
          have hmul : s ^ (-(2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) = s ^ (-(5 / 2 : ℝ)) := by
            rw [← Real.rpow_add hs]; norm_num
          calc Bχ * s ^ (-(2 : ℝ)) * |τ| ^ (-(1 / 2 : ℝ))
              ≤ Bχ * s ^ (-(2 : ℝ)) * (2 * s ^ (-(1 / 2 : ℝ))) := by gcongr; exact hpow.trans hhalf
            _ = 2 * Bχ * (s ^ (-(2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) := by ring
            _ = 2 * Bχ * s ^ (-(5 / 2 : ℝ)) := by rw [hmul]
        · simp
      have hh0' : ‖h τ‖ ≤ CA * |τ| ^ (-(1 / 2 : ℝ)) := by
        have he1 : Real.exp (-η * |τ|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hη, abs_nonneg τ])
        exact hh0.trans (by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (by positivity) he1) hCA_nn)
      calc ‖iteratedDeriv 2 χ_out τ‖ * ‖h τ‖
          ≤ ((if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς ^ (-(2 : ℝ)) else 0) +
             (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T ^ (-(2 : ℝ)) else 0)) * (CA * |τ| ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul hχ2 hh0' (norm_nonneg _) (by positivity)
        _ = CA * ((if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς ^ (-(2 : ℝ)) else 0) * |τ| ^ (-(1 / 2 : ℝ)) +
                  (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T ^ (-(2 : ℝ)) else 0) * |τ| ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ CA * (2 * Bχ * (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) +
                  2 * Bχ * (if T / 2 ≤ |τ| ∧ |τ| ≤ T then T ^ (-(5 / 2 : ℝ)) else 0)) :=
            mul_le_mul_of_nonneg_left (add_le_add (hbd_s ς hς_pos) (hbd_s T hT_pos)) hCA_nn
        _ = 2 * Bχ * CA * Ann τ := by dsimp [Ann]; ring
    have hf0 : ‖f τ‖ ≤ CA * E_half τ := by
      dsimp [f]; rw [norm_mul]
      have hh0E : ‖h τ‖ ≤ CA * E_half τ := by simpa [E_half, mul_assoc] using hh0
      calc ‖χ_out τ‖ * ‖h τ‖ ≤ 1 * (CA * E_half τ) := mul_le_mul hχ0' hh0E (norm_nonneg _) zero_le_one
        _ = CA * E_half τ := one_mul _
    have hf1 : ‖deriv f τ‖ ≤ 2 * Bχ * CA * (E_half τ + Ann τ) + 2 * CA * (E_half τ + P_32 τ) := by
      have hd := deriv_mul_norm (hχ_cd.of_le (by decide)) (hh_cd.of_le (by decide)) τ
      have hP32 : |τ| ^ (-(3 / 2 : ℝ)) = P_32 τ := by simp [P_32, hge]
      rw [hP32] at hh1
      calc ‖deriv f τ‖ ≤ ‖deriv χ_out τ‖ * ‖h τ‖ + ‖χ_out τ‖ * ‖deriv h τ‖ := hd
        _ ≤ 2 * Bχ * CA * (E_half τ + Ann τ) + 1 * (2 * CA * (E_half τ + P_32 τ)) :=
            add_le_add hχ1_h0 (mul_le_mul hχ0' hh1 (norm_nonneg _) zero_le_one)
        _ = _ := by ring
    have hf2 : ‖iteratedDeriv 2 f τ‖ ≤ 2 * Bχ * CA * Ann τ + 24 * Bχ * CA * (E_half τ + Ann τ) +
        4 * CA * (E_half τ + P_32 τ + P_52 τ) := by
      have hd2 := leibniz_two_norm hχ_cd hh_cd τ
      have hP32 : |τ| ^ (-(3 / 2 : ℝ)) = P_32 τ := by simp [P_32, hge]
      have hP52 : |τ| ^ (-(5 / 2 : ℝ)) = P_52 τ := by simp [P_52, hge]
      rw [hP32, hP52] at hh2
      calc ‖iteratedDeriv 2 f τ‖
          ≤ ‖iteratedDeriv 2 χ_out τ‖ * ‖h τ‖ + 2 * ‖deriv χ_out τ‖ * ‖deriv h τ‖ +
            ‖χ_out τ‖ * ‖iteratedDeriv 2 h τ‖ := hd2
        _ ≤ 2 * Bχ * CA * Ann τ + 2 * (12 * Bχ * CA * (E_half τ + Ann τ)) +
            1 * (4 * CA * (E_half τ + P_32 τ + P_52 τ)) := by
            rw [mul_assoc 2]
            exact add_le_add (add_le_add hχ2_h0 (mul_le_mul_of_nonneg_left hχ1_h1 zero_le_two))
              (mul_le_mul hχ0' hh2 (norm_nonneg _) zero_le_one)
        _ = _ := by ring
    have hnnE : 0 ≤ CA * E_half τ := by dsimp [E_half]; positivity
    have hnn32 : 0 ≤ CA * P_32 τ := by dsimp [P_32]; positivity
    have hnn52 : 0 ≤ CA * P_52 τ := by dsimp [P_52]; positivity
    have hnnA : 0 ≤ CA * Ann τ := by dsimp [Ann]; positivity
    have hnnBE : 0 ≤ Bχ * (CA * E_half τ) := by positivity
    have hnnB32 : 0 ≤ Bχ * (CA * P_32 τ) := by positivity
    have hnnB52 : 0 ≤ Bχ * (CA * P_52 τ) := by positivity
    have hnnBA : 0 ≤ Bχ * (CA * Ann τ) := by positivity
    linarith only [hf0, hf1, hf2, hnnE, hnn32, hnn52, hnnA, hnnBE, hnnB32, hnnB52, hnnBA]

set_option maxHeartbeats 400000 in
/-- Piece 2: Outer piece `(χ_T - χ_ς) * A * R` is `O(c^{-2} L^{-2})` via `ibp_two_phase`. -/
private lemma far_outer_bound {η C₀ C₁ C₂ : ℝ} (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ L₁ C_out : ℝ, 6 ≤ L₁ ∧ 0 < C_out ∧ ∀ {c L : ℝ} {A : ℝ → ℂ},
      60 ≤ c → L₁ ≤ L → ContDiff ℝ 2 A →
      (∀ τ : ℝ, ‖A τ‖ ≤ C₀ * Real.exp (-η * |τ|)) →
      (∀ τ : ℝ, ‖deriv A τ‖ ≤ C₁ * Real.exp (-η * |τ|)) →
      (∀ τ : ℝ, ‖iteratedDeriv 2 A τ‖ ≤ C₂ * Real.exp (-η * |τ|)) →
      ‖((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ) *
        ∫ τ : ℝ, ((smoothCutoff0 (τ / tauStar L) - smoothCutoff0 (τ / c ^ (-(1 / 3 : ℝ))) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ‖ ≤
        C_out * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
  obtain ⟨M₁, M₂, M₃, hM₁, hM₂, hM₃, hθ⟩ := outerTheta_neg_deriv_uniform_bounds
  obtain ⟨Bχ, hBχ_pos, hBχ⟩ := smoothCutoff0_deriv_bounds
  let L₁ : ℝ := max 6 (M₁ + 1)
  let Kph : ℝ := 16 + 192 * (2 + M₂) + 768 * (2 + M₂) ^ 2 + 64 * (7 + M₃)
  let CA : ℝ := C₀ + C₁ + C₂
  let Kint : ℝ := 700 * (1 + Bχ) * (1 + CA) * (1 + 1 / √η)
  refine ⟨L₁, max 1 ((π ^ 2 / 4 * |uctCAi|) * Kph * Kint), le_max_left _ _,
    lt_of_lt_of_le one_pos (le_max_left _ _), fun {c L A} hc hL hA_cd hA0 hA1 hA2 => ?_⟩
  have hc0 : 0 < c := by linarith
  have h1c : 0 < 1 / c := by positivity
  have hL6 : 6 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  set ς : ℝ := c ^ (-(1 / 3 : ℝ))
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le1 : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  set T : ℝ := tauStar L
  have hT_ge2 : 2 ≤ T := by linarith [one_le_tauStar_half hL6]
  have hT_pos : 0 < T := by linarith
  have h2ς_le_T : 2 * ς ≤ T := by linarith
  let ψ : ℝ → ℝ := fun τ => c * edgePhi L τ - CtOuter.outerTheta (-1) τ
  have hψ_cd : ContDiff ℝ 3 ψ :=
    (contDiff_const.mul (edgePhi_contDiff3 L)).sub ((CtOuter.contDiff_outerTheta (-1)).of_le (by simp))
  have hψ1 : ∀ τ ∈ Icc (-T) T, c * L / 4 ≤ |deriv ψ τ| := fun τ hτ => by
    have hτ_abs : |τ| ≤ T := abs_le.mpr hτ
    have hd : deriv ψ τ = c * edgePhiDeriv L τ - deriv (CtOuter.outerTheta (-1)) τ := by
      have h1 := ((hasDerivAt_edgePhi L τ).const_mul c).sub
        (((CtOuter.contDiff_outerTheta (-1)).differentiable (by simp) τ).hasDerivAt)
      exact h1.deriv
    rw [hd]
    have hge : L / 2 ≤ edgePhiDeriv L τ := edgePhiDeriv_ge hL0 hτ_abs
    have hM1_le : M₁ ≤ c * L / 4 := by
      have : M₁ + 1 ≤ L := (le_max_right _ _).trans hL
      nlinarith
    have hpos : c * L / 4 ≤ c * edgePhiDeriv L τ - deriv (CtOuter.outerTheta (-1)) τ := by
      have hθ1 := (abs_le.mp (hθ τ).1).2
      nlinarith
    exact hpos.trans (le_abs_self _)
  have hψ2 : ∀ τ ∈ Icc (-T) T, |iteratedDeriv 2 ψ τ| ≤ (2 + M₂) * c := fun τ _ => by
    have hd2 : iteratedDeriv 2 ψ τ = c * edgePhiDeriv2 τ - iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ := by
      have h1 : ContDiff ℝ 2 (fun t => c * edgePhi L t) := contDiff_const.mul ((edgePhi_contDiff3 L).of_le (by decide))
      have h2 : ContDiff ℝ 2 (CtOuter.outerTheta (-1)) := (CtOuter.contDiff_outerTheta (-1)).of_le (by simp)
      rw [show ψ = fun t => c * edgePhi L t - CtOuter.outerTheta (-1) t from rfl,
        iteratedDeriv_fun_sub h1.contDiffAt h2.contDiffAt, iteratedDeriv_const_mul_field,
        (edgePhi_iteratedDeriv_eq L τ).2.1]
    rw [hd2]
    calc |c * edgePhiDeriv2 τ - iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ|
        ≤ |c * edgePhiDeriv2 τ| + |iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ| := abs_sub _ _
      _ ≤ c * 2 + M₂ := by
          rw [abs_mul, abs_of_pos hc0]
          exact add_le_add (mul_le_mul_of_nonneg_left (edgePhiDeriv2_abs_le_two τ) hc0.le) (hθ τ).2.1
      _ ≤ (2 + M₂) * c := by nlinarith
  have hψ3 : ∀ τ ∈ Icc (-T) T, |iteratedDeriv 3 ψ τ| ≤ (7 + M₃) * c := fun τ _ => by
    have hd3 : iteratedDeriv 3 ψ τ = c * iteratedDeriv 3 (edgePhi L) τ - iteratedDeriv 3 (CtOuter.outerTheta (-1)) τ := by
      have h1 : ContDiff ℝ 3 (fun t => c * edgePhi L t) := contDiff_const.mul (edgePhi_contDiff3 L)
      have h2 : ContDiff ℝ 3 (CtOuter.outerTheta (-1)) := (CtOuter.contDiff_outerTheta (-1)).of_le (by simp)
      rw [show ψ = fun t => c * edgePhi L t - CtOuter.outerTheta (-1) t from rfl,
        iteratedDeriv_fun_sub h1.contDiffAt h2.contDiffAt, iteratedDeriv_const_mul_field]
    rw [hd3]
    calc |c * iteratedDeriv 3 (edgePhi L) τ - iteratedDeriv 3 (CtOuter.outerTheta (-1)) τ|
        ≤ |c * iteratedDeriv 3 (edgePhi L) τ| + |iteratedDeriv 3 (CtOuter.outerTheta (-1)) τ| := abs_sub _ _
      _ ≤ c * 7 + M₃ := by
          rw [abs_mul, abs_of_pos hc0]
          exact add_le_add (mul_le_mul_of_nonneg_left (edgePhi_iteratedDeriv_eq L τ).2.2 hc0.le) (hθ τ).2.2
      _ ≤ (7 + M₃) * c := by nlinarith
  let χ_out : ℝ → ℂ := fun τ => ((smoothCutoff0 (τ / T) - smoothCutoff0 (τ / ς) : ℝ) : ℂ)
  let h : ℝ → ℂ := fun τ => A τ * regSqrt (1 / c) τ
  let f : ℝ → ℂ := fun τ => χ_out τ * h τ
  have hχ_cd : ContDiff ℝ 2 χ_out :=
    Complex.ofRealCLM.contDiff.comp (((contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const T)).sub
      ((contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const ς)))
  have hh_cd : ContDiff ℝ 2 h := hA_cd.mul (contDiff_regSqrt h1c)
  have hf_cd : ContDiff ℝ 2 f := hχ_cd.mul hh_cd
  have hf_supp : ∀ τ : ℝ, T ≤ |τ| → f τ = 0 := fun τ hτ => by
    have h1 : 1 ≤ |τ / T| := by rw [abs_div, abs_of_pos hT_pos, one_le_div hT_pos]; exact hτ
    have h2 : 1 ≤ |τ / ς| := by rw [abs_div, abs_of_pos hς_pos, one_le_div hς_pos]; linarith
    simp [f, χ_out, smoothCutoff0_eq_zero h1, smoothCutoff0_eq_zero h2]
  have hibp := ibp_two_phase hT_pos (by positivity : 0 < c * L / 4) (by positivity : 0 ≤ (2 + M₂) * c)
    (by positivity : 0 ≤ (7 + M₃) * c) hf_cd hψ_cd hf_supp hψ1 hψ2 hψ3
  -- Bound the IBP prefactor by `Kph * c^{-2} * L^{-2}`:
  have hKph_le : (c * L / 4) ^ (-(2 : ℝ)) + 3 * ((2 + M₂) * c) * (c * L / 4) ^ (-(3 : ℝ)) +
      3 * ((2 + M₂) * c) ^ 2 * (c * L / 4) ^ (-(4 : ℝ)) + ((7 + M₃) * c) * (c * L / 4) ^ (-(3 : ℝ)) ≤
      Kph * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
    have h2 : (c * L / 4) ^ (-(2 : ℝ)) = 16 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
      rw [rpow_neg_two_eq', rpow_neg_two_eq', rpow_neg_two_eq']; field_simp [hc0.ne', hL0.ne']; ring
    have h3 : c * (c * L / 4) ^ (-(3 : ℝ)) ≤ 64 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
      rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, rpow_neg_two_eq', rpow_neg_two_eq']
      have : (c * L / 4) ^ (3 : ℤ) = (c * L / 4) ^ 3 := by norm_cast
      rw [this]
      have hLge1 : 1 ≤ L := by linarith
      rw [show c * ((c * L / 4) ^ 3)⁻¹ = 64 * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ * L⁻¹ by field_simp [hc0.ne', hL0.ne']; ring]
      have hLinv : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLge1
      have : 0 ≤ 64 * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by positivity
      nlinarith
    have h4 : c ^ 2 * (c * L / 4) ^ (-(4 : ℝ)) ≤ 256 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
      rw [show (-(4 : ℝ)) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, rpow_neg_two_eq', rpow_neg_two_eq']
      have : (c * L / 4) ^ (4 : ℤ) = (c * L / 4) ^ 4 := by norm_cast
      rw [this]
      have hLge1 : 1 ≤ L ^ 2 := by nlinarith
      rw [show c ^ 2 * ((c * L / 4) ^ 4)⁻¹ = 256 * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ * (L ^ 2)⁻¹ by field_simp [hc0.ne', hL0.ne']; ring]
      have hLinv : (L ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLge1
      have : 0 ≤ 256 * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by positivity
      nlinarith
    dsimp only [Kph]
    nlinarith [show 3 * ((2 + M₂) * c) * (c * L / 4) ^ (-(3 : ℝ)) = 3 * (2 + M₂) * (c * (c * L / 4) ^ (-(3 : ℝ))) by ring,
      show 3 * ((2 + M₂) * c) ^ 2 * (c * L / 4) ^ (-(4 : ℝ)) = 3 * (2 + M₂) ^ 2 * (c ^ 2 * (c * L / 4) ^ (-(4 : ℝ))) by ring,
      show ((7 + M₃) * c) * (c * L / 4) ^ (-(3 : ℝ)) = (7 + M₃) * (c * (c * L / 4) ^ (-(3 : ℝ))) by ring]
  -- Now bound `∫_{-T}^T (‖f''‖ + ‖f'‖ + ‖f‖) ≤ Kint * ς^{-3/2}`:
  have hχ_bounds : ∀ τ : ℝ,
      ‖χ_out τ‖ ≤ (if ς / 2 ≤ |τ| then 1 else 0) ∧
      ‖deriv χ_out τ‖ ≤ (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) +
        (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T⁻¹ else 0) ∧
      ‖iteratedDeriv 2 χ_out τ‖ ≤ (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς ^ (-(2 : ℝ)) else 0) +
        (if T / 2 ≤ |τ| ∧ |τ| ≤ T then Bχ * T ^ (-(2 : ℝ)) else 0) := fun τ => by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [χ_out]; rw [Complex.norm_real, Real.norm_eq_abs]
      split_ifs with hτ
      · rw [abs_le]; constructor <;> linarith [smoothCutoff0_nonneg (τ / T), smoothCutoff0_le_one (τ / T),
          smoothCutoff0_nonneg (τ / ς), smoothCutoff0_le_one (τ / ς)]
      · push Not at hτ
        have h1 : |τ / ς| ≤ 1 / 2 := by rw [abs_div, abs_of_pos hς_pos, div_le_iff₀ hς_pos]; linarith
        have h2 : |τ / T| ≤ 1 / 2 := by rw [abs_div, abs_of_pos hT_pos, div_le_iff₀ hT_pos]; linarith
        rw [smoothCutoff0_eq_one h1, smoothCutoff0_eq_one h2, sub_self, abs_zero]
    · have hd : deriv χ_out τ = ((deriv (fun t => smoothCutoff0 (t / T)) τ -
          deriv (fun t => smoothCutoff0 (t / ς)) τ : ℝ) : ℂ) := by
        have h1 := ((contDiff_smoothCutoff0.differentiable (by decide)).comp (differentiable_id.div_const T) τ).hasDerivAt
        have h2 := ((contDiff_smoothCutoff0.differentiable (by decide)).comp (differentiable_id.div_const ς) τ).hasDerivAt
        exact (h1.sub h2).ofReal_comp.deriv
      rw [hd, Complex.norm_real, Real.norm_eq_abs, (smoothCutoff0_scale_derivs hT_pos τ).1,
        (smoothCutoff0_scale_derivs hς_pos τ).1]
      have hbd : ∀ (s : ℝ), 0 < s → |s⁻¹ * deriv smoothCutoff0 (τ / s)| ≤
          if s / 2 ≤ |τ| ∧ |τ| ≤ s then Bχ * s⁻¹ else 0 := fun s hs => by
        split_ifs with hτ
        · rw [abs_mul, abs_of_pos (inv_pos.mpr hs), mul_comm]
          exact mul_le_mul_of_nonneg_right (hBχ (τ / s)).1 (inv_nonneg.mpr hs.le)
        · push Not at hτ
          by_cases hlt : |τ| < s / 2
          · rw [((hBχ (τ / s)).2.2.1 (by rw [abs_div, abs_of_pos hs, div_lt_iff₀ hs]; linarith)).1, mul_zero, abs_zero]
          · rw [((hBχ (τ / s)).2.2.2 (by rw [abs_div, abs_of_pos hs, one_lt_div hs]; exact hτ (not_lt.mp hlt))).1, mul_zero, abs_zero]
      exact (abs_sub _ _).trans ((add_le_add (hbd T hT_pos) (hbd ς hς_pos)).trans_eq (add_comm _ _))
    · have hcdT : ContDiff ℝ 2 (fun t => smoothCutoff0 (t / T)) :=
        (contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const T)
      have hcdς : ContDiff ℝ 2 (fun t => smoothCutoff0 (t / ς)) :=
        (contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const ς)
      have hd : iteratedDeriv 2 χ_out τ = ((iteratedDeriv 2 (fun t => smoothCutoff0 (t / T)) τ -
          iteratedDeriv 2 (fun t => smoothCutoff0 (t / ς)) τ : ℝ) : ℂ) := by
        rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
          iteratedDeriv_succ, iteratedDeriv_one]
        have h1 : deriv χ_out = fun t => ((deriv (fun u => smoothCutoff0 (u / T)) t -
            deriv (fun u => smoothCutoff0 (u / ς)) t : ℝ) : ℂ) := funext fun t =>
          (((hcdT.differentiable (by decide)).differentiableAt.hasDerivAt.sub
            (hcdς.differentiable (by decide)).differentiableAt.hasDerivAt).ofReal_comp).deriv
        rw [h1]
        exact ((((contDiff_one_deriv_of_two' hcdT).differentiable (by decide)).differentiableAt.hasDerivAt.sub
          ((contDiff_one_deriv_of_two' hcdς).differentiable (by decide)).differentiableAt.hasDerivAt).ofReal_comp).deriv
      rw [hd, Complex.norm_real, Real.norm_eq_abs, (smoothCutoff0_scale_derivs hT_pos τ).2,
        (smoothCutoff0_scale_derivs hς_pos τ).2]
      have hbd : ∀ (s : ℝ), 0 < s → |s ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / s)| ≤
          if s / 2 ≤ |τ| ∧ |τ| ≤ s then Bχ * s ^ (-(2 : ℝ)) else 0 := fun s hs => by
        split_ifs with hτ
        · rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _), mul_comm]
          exact mul_le_mul_of_nonneg_right (hBχ (τ / s)).2.1 (by positivity)
        · push Not at hτ
          by_cases hlt : |τ| < s / 2
          · rw [((hBχ (τ / s)).2.2.1 (by rw [abs_div, abs_of_pos hs, div_lt_iff₀ hs]; linarith)).2, mul_zero, abs_zero]
          · rw [((hBχ (τ / s)).2.2.2 (by rw [abs_div, abs_of_pos hs, one_lt_div hs]; exact hτ (not_lt.mp hlt))).2, mul_zero, abs_zero]
      exact (abs_sub _ _).trans ((add_le_add (hbd T hT_pos) (hbd ς hς_pos)).trans_eq (add_comm _ _))
  -- Pointwise bounds on `h = A * R` for `τ ≠ 0`:
  have hh_bounds : ∀ τ : ℝ, τ ≠ 0 →
      ‖h τ‖ ≤ CA * Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) ∧
      ‖deriv h τ‖ ≤ 2 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) + |τ| ^ (-(3 / 2 : ℝ))) ∧
      ‖iteratedDeriv 2 h τ‖ ≤ 4 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) +
        |τ| ^ (-(3 / 2 : ℝ)) + |τ| ^ (-(5 / 2 : ℝ))) := fun τ hτ => by
    have hR0 : ‖regSqrt (1 / c) τ‖ ≤ |τ| ^ (-(1 / 2 : ℝ)) := norm_regSqrt_le_abs_rpow h1c hτ
    have hR1 : ‖deriv (regSqrt (1 / c)) τ‖ ≤ 2 * |τ| ^ (-(3 / 2 : ℝ)) :=
      (norm_deriv_regSqrt_le h1c τ).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hτ) (by linarith) (by norm_num)) (by norm_num))
    have hR2 : ‖iteratedDeriv 2 (regSqrt (1 / c)) τ‖ ≤ 3 * |τ| ^ (-(5 / 2 : ℝ)) :=
      (norm_iteratedDeriv2_regSqrt_le h1c τ).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hτ) (by linarith) (by norm_num)) (by norm_num))
    have he_le1 : Real.exp (-η * |τ|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ])
    have h0 : ‖h τ‖ ≤ CA * Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) := by
      dsimp [h]; rw [norm_mul]
      calc ‖A τ‖ * ‖regSqrt (1 / c) τ‖ ≤ (C₀ * Real.exp (-η * |τ|)) * |τ| ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul (hA0 τ) hR0 (norm_nonneg _) (by positivity)
        _ ≤ CA * Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) := by
            have : C₀ ≤ CA := by dsimp [CA]; linarith
            gcongr
    have h1 : ‖deriv h τ‖ ≤ 2 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) + |τ| ^ (-(3 / 2 : ℝ))) := by
      have hd := deriv_mul_norm (hA_cd.of_le (by decide)) ((contDiff_regSqrt h1c).of_le (by decide)) τ
      have hC1_le : C₁ ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₂]
      have hC0_le : C₀ ≤ CA := by dsimp [CA]; linarith only [hC₁, hC₂]
      have hA1' : ‖deriv A τ‖ ≤ CA * Real.exp (-η * |τ|) :=
        (hA1 τ).trans (mul_le_mul_of_nonneg_right hC1_le (Real.exp_pos _).le)
      have hA0' : ‖A τ‖ ≤ CA := (hA0 τ).trans ((mul_le_of_le_one_right hC₀ he_le1).trans hC0_le)
      have hterm1_nn : 0 ≤ CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) := by dsimp [CA]; positivity
      calc ‖deriv h τ‖ ≤ ‖deriv A τ‖ * ‖regSqrt (1 / c) τ‖ + ‖A τ‖ * ‖deriv (regSqrt (1 / c)) τ‖ := hd
        _ ≤ (CA * Real.exp (-η * |τ|)) * |τ| ^ (-(1 / 2 : ℝ)) + CA * (2 * |τ| ^ (-(3 / 2 : ℝ))) :=
            add_le_add (mul_le_mul hA1' hR0 (norm_nonneg _) (by dsimp [CA]; positivity))
              (mul_le_mul hA0' hR1 (norm_nonneg _) (by dsimp [CA]; positivity))
        _ ≤ 2 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) + |τ| ^ (-(3 / 2 : ℝ))) := by
            linarith only [hterm1_nn]
    have h2 : ‖iteratedDeriv 2 h τ‖ ≤ 4 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) +
        |τ| ^ (-(3 / 2 : ℝ)) + |τ| ^ (-(5 / 2 : ℝ))) := by
      have hd2 := leibniz_two_norm hA_cd (contDiff_regSqrt h1c) τ
      have hC2_le : C₂ ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₁]
      have hC1_le : C₁ ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₂]
      have hC0_le : C₀ ≤ CA := by dsimp [CA]; linarith only [hC₁, hC₂]
      have hA2' : ‖iteratedDeriv 2 A τ‖ ≤ CA * Real.exp (-η * |τ|) :=
        (hA2 τ).trans (mul_le_mul_of_nonneg_right hC2_le (Real.exp_pos _).le)
      have hA1' : ‖deriv A τ‖ ≤ CA := (hA1 τ).trans ((mul_le_of_le_one_right hC₁ he_le1).trans hC1_le)
      have hA0' : ‖A τ‖ ≤ CA := (hA0 τ).trans ((mul_le_of_le_one_right hC₀ he_le1).trans hC0_le)
      have hnn1 : 0 ≤ CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) := by dsimp [CA]; positivity
      have hnn3 : 0 ≤ CA * |τ| ^ (-(5 / 2 : ℝ)) := by dsimp [CA]; positivity
      calc ‖iteratedDeriv 2 h τ‖
          ≤ ‖iteratedDeriv 2 A τ‖ * ‖regSqrt (1 / c) τ‖ + 2 * ‖deriv A τ‖ * ‖deriv (regSqrt (1 / c)) τ‖ +
            ‖A τ‖ * ‖iteratedDeriv 2 (regSqrt (1 / c)) τ‖ := hd2
        _ ≤ (CA * Real.exp (-η * |τ|)) * |τ| ^ (-(1 / 2 : ℝ)) + 2 * CA * (2 * |τ| ^ (-(3 / 2 : ℝ))) +
            CA * (3 * |τ| ^ (-(5 / 2 : ℝ))) := by gcongr
        _ ≤ 4 * CA * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)) + |τ| ^ (-(3 / 2 : ℝ)) + |τ| ^ (-(5 / 2 : ℝ))) := by
            linarith only [hnn1, hnn3]
    exact ⟨h0, h1, h2⟩
  -- Build a simple integrable majorant `M_out` for `‖f''‖ + ‖f'‖ + ‖f‖`:
  let E_half : ℝ → ℝ := fun τ => Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))
  let P_32 : ℝ → ℝ := fun τ => if ς / 2 ≤ |τ| then |τ| ^ (-(3 / 2 : ℝ)) else 0
  let P_52 : ℝ → ℝ := fun τ => if ς / 2 ≤ |τ| then |τ| ^ (-(5 / 2 : ℝ)) else 0
  let Ann : ℝ → ℝ := fun τ =>
    (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then ς ^ (-(5 / 2 : ℝ)) else 0) +
    (if T / 2 ≤ |τ| ∧ |τ| ≤ T then T ^ (-(5 / 2 : ℝ)) else 0)
  let M_out : ℝ → ℝ := fun τ => 38 * (1 + Bχ) * CA * (E_half τ + P_32 τ + P_52 τ + Ann τ)
  have hpt_f : ∀ τ : ℝ, ‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖ ≤ M_out τ :=
    far_outer_pointwise_bound hη hBχ_pos (by dsimp [CA]; positivity) hς_pos hς_le1 hT_ge2
      hχ_cd hh_cd hχ_bounds hh_bounds
  -- Integrate `M_out` over `ℝ` via `far_outer_majorant_integral`:
  have hmaj := far_outer_majorant_integral hη hς_pos hς_le1 hT_ge2
  have hM_int : Integrable M_out := hmaj.1.const_mul _
  have hM_val : ∫ τ : ℝ, M_out τ ≤ Kint * ς ^ (-(3 / 2 : ℝ)) := by
    dsimp only [M_out, Kint]
    rw [integral_const_mul]
    have hnn : 0 ≤ 38 * (1 + Bχ) * CA := by dsimp [CA]; positivity
    have hpos : 0 ≤ ς ^ (-(3 / 2 : ℝ)) := by positivity
    have hCA_le : CA ≤ 1 + CA := by linarith
    have hcoef : 38 * (16 + 4 * (1 / √η)) ≤ 700 * (1 + 1 / √η) := by
      have : (0 : ℝ) ≤ 1 / √η := by positivity
      linarith only [this]
    calc 38 * (1 + Bχ) * CA * ∫ τ : ℝ, (E_half τ + P_32 τ + P_52 τ + Ann τ)
        ≤ 38 * (1 + Bχ) * CA * ((16 + 4 * (1 / √η)) * ς ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hmaj.2 hnn
      _ = (38 * (16 + 4 * (1 / √η))) * ((1 + Bχ) * CA * ς ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ (700 * (1 + 1 / √η)) * ((1 + Bχ) * (1 + CA) * ς ^ (-(3 / 2 : ℝ))) := by
          have h1 : 0 ≤ (1 + Bχ) * CA * ς ^ (-(3 / 2 : ℝ)) := by dsimp [CA]; positivity
          have h2 : (1 + Bχ) * CA * ς ^ (-(3 / 2 : ℝ)) ≤ (1 + Bχ) * (1 + CA) * ς ^ (-(3 / 2 : ℝ)) := by gcongr
          exact mul_le_mul hcoef h2 h1 (by positivity)
      _ = 700 * (1 + Bχ) * (1 + CA) * (1 + 1 / √η) * ς ^ (-(3 / 2 : ℝ)) := by ring
  have hint_f_le : ∫ τ in Icc (-T) T, (‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖) ≤ Kint * ς ^ (-(3 / 2 : ℝ)) := by
    have hf_cont : Continuous (fun τ => ‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖) :=
      ((hf_cd.continuous_iteratedDeriv 2 le_rfl).norm.add (hf_cd.continuous_deriv (by decide)).norm).add hf_cd.continuous.norm
    calc ∫ τ in Icc (-T) T, (‖iteratedDeriv 2 f τ‖ + ‖deriv f τ‖ + ‖f τ‖)
        ≤ ∫ τ in Icc (-T) T, M_out τ :=
          setIntegral_mono_on (hf_cont.continuousOn.integrableOn_compact isCompact_Icc) hM_int.integrableOn
            measurableSet_Icc (fun τ _ => hpt_f τ)
      _ ≤ ∫ τ : ℝ, M_out τ := setIntegral_le_integral hM_int (Eventually.of_forall fun τ => by
          have h1 : 0 ≤ E_half τ := by dsimp [E_half]; positivity
          have h2 : 0 ≤ P_32 τ := by dsimp [P_32]; split_ifs <;> positivity
          have h3 : 0 ≤ P_52 τ := by dsimp [P_52]; split_ifs <;> positivity
          have h4 : 0 ≤ Ann τ := by dsimp [Ann]; positivity
          have h5 : 0 ≤ 38 * (1 + Bχ) * CA := by dsimp [CA]; positivity
          exact mul_nonneg h5 (by linarith only [h1, h2, h3, h4]))
      _ ≤ Kint * ς ^ (-(3 / 2 : ℝ)) := hM_val
  have hς_c : c ^ (-(1 / 2 : ℝ)) * ς ^ (-(3 / 2 : ℝ)) = 1 := by
    dsimp [ς]; rw [← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hcongr_f : ∫ τ : ℝ, ((smoothCutoff0 (τ / T) - smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ = ∫ τ : ℝ, f τ * Complex.exp (Complex.I * (ψ τ : ℂ)) :=
    integral_congr_ae (Eventually.of_forall fun τ => by dsimp [f, χ_out, h, ψ]; ring)
  rw [hcongr_f, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have h2pi : (2 * π)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  calc c ^ (-(1 / 2 : ℝ)) / (2 * π) * (π ^ 2 / 4 * |uctCAi|) * ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * (ψ τ : ℂ))‖
      ≤ c ^ (-(1 / 2 : ℝ)) * (π ^ 2 / 4 * |uctCAi|) *
          ((Kph * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ))) * (Kint * ς ^ (-(3 / 2 : ℝ)))) := by
        have h1 : c ^ (-(1 / 2 : ℝ)) / (2 * π) ≤ c ^ (-(1 / 2 : ℝ)) := by
          rw [div_eq_mul_inv]; nlinarith [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
        have h2 : ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * (ψ τ : ℂ))‖ ≤
            (Kph * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ))) * (Kint * ς ^ (-(3 / 2 : ℝ))) :=
          hibp.trans (mul_le_mul hKph_le hint_f_le
            (setIntegral_nonneg measurableSet_Icc fun τ _ => by positivity) (by positivity))
        gcongr
    _ = ((π ^ 2 / 4 * |uctCAi|) * Kph * Kint) * (c ^ (-(1 / 2 : ℝ)) * ς ^ (-(3 / 2 : ℝ))) *
          c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by ring
    _ = ((π ^ 2 / 4 * |uctCAi|) * Kph * Kint) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by rw [hς_c, mul_one]
    _ ≤ max 1 ((π ^ 2 / 4 * |uctCAi|) * Kph * Kint) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
        gcongr; exact le_max_right 1 _

/-- Helper for `far_inner_diff_bound`: the five elementary integrals on `[-ς, ς]`. -/
private lemma far_inner_five_integrals {c : ℝ} (hc : 60 ≤ c) :
    let ς : ℝ := c ^ (-(1 / 3 : ℝ))
    IntegrableOn (fun τ : ℝ => (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) +
      c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ) +
      (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0)) (Icc (-ς) ς) ∧
    ∫ τ in Icc (-ς) ς,
      ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) +
       c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ) +
       (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0)) ≤ 17 * c ^ (1 / 2 : ℝ) := by
  intro ς
  have hc0 : 0 < c := by linarith
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le1 : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have heven_Icc : ∀ (φ : ℝ → ℝ), ContinuousOn φ (Icc 0 ς) →
      ∫ τ in Icc (-ς) ς, φ |τ| = 2 * ∫ t in (0 : ℝ)..ς, φ t := fun φ hφ => by
    have hcont_neg : ContinuousOn (fun τ : ℝ => φ |τ|) (Icc (-ς) 0) :=
      hφ.comp continuous_abs.continuousOn (fun τ hτ => ⟨abs_nonneg τ, by rw [abs_of_nonpos hτ.2]; linarith [hτ.1]⟩)
    have hcont_pos : ContinuousOn (fun τ : ℝ => φ |τ|) (Icc 0 ς) :=
      hφ.comp continuous_abs.continuousOn (fun τ hτ => ⟨abs_nonneg τ, by rw [abs_of_nonneg hτ.1]; exact hτ.2⟩)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hcont_neg.intervalIntegrable_of_Icc (by linarith))
        (hcont_pos.intervalIntegrable_of_Icc hς_pos.le)]
    have hpos : ∫ t in (0 : ℝ)..ς, φ |t| = ∫ t in (0 : ℝ)..ς, φ t :=
      intervalIntegral.integral_congr fun t ht => by rw [uIcc_of_le hς_pos.le] at ht; rw [abs_of_nonneg ht.1]
    have hneg : ∫ t in (-ς)..0, φ |t| = ∫ t in (0 : ℝ)..ς, φ t := by
      have hcomp := intervalIntegral.integral_comp_neg (f := fun t => φ |t|) (a := (0 : ℝ)) (b := ς)
      rw [neg_zero] at hcomp
      rw [← hcomp]
      exact intervalIntegral.integral_congr fun t ht => by rw [uIcc_of_le hς_pos.le] at ht; rw [abs_neg, abs_of_nonneg ht.1]
    rw [hpos, hneg]; ring
  have hI1 : ∫ τ in Icc (-ς) ς, (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) ≤ 8 * c ^ (1 / 2 : ℝ) := by
    have hc1 : ContinuousOn (fun t : ℝ => (1 / c + t) ^ (-(1 / 2 : ℝ))) (Icc 0 ς) :=
      ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id) (fun t ht => Or.inl (by linarith [ht.1, show (0 : ℝ) < 1 / c by positivity]))
    rw [heven_Icc _ hc1]
    have hd : ∀ t ∈ uIcc (0 : ℝ) ς, HasDerivAt (fun u => 2 * (1 / c + u) ^ (1 / 2 : ℝ)) ((1 / c + t) ^ (-(1 / 2 : ℝ))) t := by
      intro t ht; rw [uIcc_of_le hς_pos.le] at ht
      have h1 : HasDerivAt (fun u => 1 / c + u) 1 t := (hasDerivAt_id t).const_add (1 / c)
      have h2 := ((h1.rpow_const (p := (1 / 2 : ℝ)) (Or.inl (by linarith [ht.1, show (0 : ℝ) < 1 / c by positivity] : 1 / c + t ≠ 0))).const_mul 2)
      refine h2.congr_deriv ?_; norm_num; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc1.intervalIntegrable_of_Icc hς_pos.le)]
    have h1 : (1 / c + ς) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith [show 1 / c ≤ 1 by rw [div_le_one hc0]; linarith]) (by norm_num)
    have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      simpa using this
    have hc12 : 1 ≤ c ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hnn : 0 ≤ (1 / c + 0) ^ (1 / 2 : ℝ) := by positivity
    nlinarith only [h1, h2, hc12, hnn]
  have hI2 : ∫ τ in Icc (-ς) ς, (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) ≤ 4 * c ^ (1 / 2 : ℝ) := by
    have hc2 : ContinuousOn (fun t : ℝ => (1 / c + t) ^ (-(3 / 2 : ℝ))) (Icc 0 ς) :=
      ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id) (fun t ht => Or.inl (by linarith [ht.1, show (0 : ℝ) < 1 / c by positivity]))
    rw [heven_Icc _ hc2]
    have hd : ∀ t ∈ uIcc (0 : ℝ) ς, HasDerivAt (fun u => -2 * (1 / c + u) ^ (-(1 / 2 : ℝ))) ((1 / c + t) ^ (-(3 / 2 : ℝ))) t := by
      intro t ht; rw [uIcc_of_le hς_pos.le] at ht
      have h1 : HasDerivAt (fun u => 1 / c + u) 1 t := (hasDerivAt_id t).const_add (1 / c)
      have h2 := ((h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (by linarith [ht.1, show (0 : ℝ) < 1 / c by positivity] : 1 / c + t ≠ 0))).const_mul (-2))
      refine h2.congr_deriv ?_; norm_num; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.intervalIntegrable_of_Icc hς_pos.le)]
    have h0 : (1 / c + 0) ^ (-(1 / 2 : ℝ)) = c ^ (1 / 2 : ℝ) := by
      rw [add_zero, one_div, Real.inv_rpow hc0.le, Real.rpow_neg hc0.le, inv_inv]
    rw [h0]
    have hnn : 0 ≤ (1 / c + ς) ^ (-(1 / 2 : ℝ)) := by positivity
    linarith
  have hI3 : ∫ τ in Icc (-ς) ς, c * |τ| ^ (1 / 2 : ℝ) ≤ 2 * c ^ (1 / 2 : ℝ) := by
    rw [integral_const_mul]
    have hc3 : ContinuousOn (fun t : ℝ => t ^ (1 / 2 : ℝ)) (Icc 0 ς) :=
      (continuous_id.rpow_const (fun _ => Or.inr (by norm_num))).continuousOn
    rw [heven_Icc _ hc3, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2)),
      Real.zero_rpow (by norm_num), sub_zero]
    have hpow : c * ς ^ (1 / 2 + 1 : ℝ) = c ^ (1 / 2 : ℝ) := by
      dsimp [ς]; rw [← Real.rpow_mul hc0.le]
      conv_lhs => arg 1; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc0]; norm_num
    calc c * (2 * (ς ^ (1 / 2 + 1 : ℝ) / (1 / 2 + 1)))
        = (4 / 3) * (c * ς ^ (1 / 2 + 1 : ℝ)) := by ring
      _ = (4 / 3) * c ^ (1 / 2 : ℝ) := by rw [hpow]
      _ ≤ 2 * c ^ (1 / 2 : ℝ) := by nlinarith [Real.rpow_pos_of_pos hc0 (1 / 2 : ℝ)]
  have hI4 : ∫ τ in Icc (-ς) ς, c ^ 2 * |τ| ^ (7 / 2 : ℝ) ≤ c ^ (1 / 2 : ℝ) := by
    rw [integral_const_mul]
    have hc4 : ContinuousOn (fun t : ℝ => t ^ (7 / 2 : ℝ)) (Icc 0 ς) :=
      (continuous_id.rpow_const (fun _ => Or.inr (by norm_num))).continuousOn
    rw [heven_Icc _ hc4, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 7 / 2)),
      Real.zero_rpow (by norm_num), sub_zero]
    have hpow : c ^ 2 * ς ^ (7 / 2 + 1 : ℝ) = c ^ (1 / 2 : ℝ) := by
      dsimp [ς]; rw [← Real.rpow_mul hc0.le, ← Real.rpow_natCast c 2, ← Real.rpow_add hc0]; norm_num
    calc c ^ 2 * (2 * (ς ^ (7 / 2 + 1 : ℝ) / (7 / 2 + 1)))
        = (4 / 9) * (c ^ 2 * ς ^ (7 / 2 + 1 : ℝ)) := by ring
      _ = (4 / 9) * c ^ (1 / 2 : ℝ) := by rw [hpow]
      _ ≤ c ^ (1 / 2 : ℝ) := by nlinarith [Real.rpow_pos_of_pos hc0 (1 / 2 : ℝ)]
  have hI5_int : IntegrableOn (fun τ : ℝ => if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0) (Icc (-ς) ς) := by
    have hmeas : MeasurableSet {τ : ℝ | ς / 2 ≤ |τ|} := measurableSet_le measurable_const continuous_abs.measurable
    exact ((integrableOn_const (by simp) : IntegrableOn (fun _ : ℝ => ς ^ (-(5 / 2 : ℝ))) (Icc (-ς) ς)).indicator hmeas).congr_fun
      (fun τ _ => by simp only [Set.indicator, mem_ofPred_eq]; rfl) measurableSet_Icc
  have hI5 : ∫ τ in Icc (-ς) ς, (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0) ≤ 2 * c ^ (1 / 2 : ℝ) := by
    have hle : ∫ τ in Icc (-ς) ς, (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0) ≤
        ∫ τ in Icc (-ς) ς, ς ^ (-(5 / 2 : ℝ)) :=
      setIntegral_mono_on hI5_int (integrableOn_const (by simp)) measurableSet_Icc (fun τ _ => by split_ifs; exact le_rfl; positivity)
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)] at hle
    have hpow : (ς - -ς) * ς ^ (-(5 / 2 : ℝ)) = 2 * c ^ (1 / 2 : ℝ) := by
      have h1 : ς * ς ^ (-(5 / 2 : ℝ)) = ς ^ (-(3 / 2 : ℝ)) := by
        conv_lhs => arg 1; rw [← Real.rpow_one ς]
        rw [← Real.rpow_add hς_pos]; norm_num
      have h2 : ς ^ (-(3 / 2 : ℝ)) = c ^ (1 / 2 : ℝ) := by
        dsimp [ς]; rw [← Real.rpow_mul hc0.le]; norm_num
      calc (ς - -ς) * ς ^ (-(5 / 2 : ℝ)) = 2 * (ς * ς ^ (-(5 / 2 : ℝ))) := by ring
        _ = 2 * c ^ (1 / 2 : ℝ) := by rw [h1, h2]
    linarith
  have hi1 : IntegrableOn (fun τ : ℝ => (1 / c + |τ|) ^ (-(1 / 2 : ℝ))) (Icc (-ς) ς) :=
    (Continuous.rpow_const (continuous_const.add continuous_abs) (fun τ => Or.inl (by positivity : (0 : ℝ) < 1 / c + |τ|).ne')).continuousOn.integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun τ : ℝ => (1 / c + |τ|) ^ (-(3 / 2 : ℝ))) (Icc (-ς) ς) :=
    (Continuous.rpow_const (continuous_const.add continuous_abs) (fun τ => Or.inl (by positivity : (0 : ℝ) < 1 / c + |τ|).ne')).continuousOn.integrableOn_compact isCompact_Icc
  have hi3 : IntegrableOn (fun τ : ℝ => c * |τ| ^ (1 / 2 : ℝ)) (Icc (-ς) ς) :=
    (continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn.integrableOn_compact isCompact_Icc
  have hi4 : IntegrableOn (fun τ : ℝ => c ^ 2 * |τ| ^ (7 / 2 : ℝ)) (Icc (-ς) ς) :=
    (continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn.integrableOn_compact isCompact_Icc
  refine ⟨(((hi1.add hi2).add hi3).add hi4).add hI5_int, ?_⟩
  have h12 : IntegrableOn (fun τ : ℝ => (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ))) (Icc (-ς) ς) := hi1.add hi2
  have h123 : IntegrableOn (fun τ : ℝ => (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ)) (Icc (-ς) ς) := h12.add hi3
  have h1234 : IntegrableOn (fun τ : ℝ => (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ)) (Icc (-ς) ς) := h123.add hi4
  rw [integral_add h1234 hI5_int, integral_add h123 hi4, integral_add h12 hi3, integral_add hi1 hi2]
  linarith

/-- Derivative bounds for the inner amplitude difference `g(τ) = A(τ) exp(i ϕ(τ)) - A 0`,
extracted from `far_inner_diff_bound` to keep heartbeat usage low. -/
private lemma far_inner_g_bounds {C₀ C₁ C₂ M₂ c L : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hM₂ : 0 < M₂) (hθ2 : ∀ τ : ℝ, |iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ| ≤ M₂)
    (hc : 60 ≤ c) {A : ℝ → ℂ} (hA_cd : ContDiff ℝ 2 A)
    (hA0 : ∀ τ : ℝ, ‖A τ‖ ≤ C₀) (hA1 : ∀ τ : ℝ, ‖deriv A τ‖ ≤ C₁) (hA2 : ∀ τ : ℝ, ‖iteratedDeriv 2 A τ‖ ≤ C₂) :
    let θ₁ := CtOuter.ctTheta1 (-1)
    let ϕ : ℝ → ℝ := fun τ => c * (edgePhi L τ - L * τ) - (CtOuter.outerTheta (-1) τ - θ₁ * τ)
    let g : ℝ → ℂ := fun τ => A τ * Complex.exp (Complex.I * (ϕ τ : ℂ)) - A 0
    let Kg : ℝ := 20 * (1 + C₀ + C₁ + C₂) * (1 + M₂) ^ 2
    ContDiff ℝ 2 g ∧
    ∀ τ : ℝ, |τ| ≤ c ^ (-(1 / 3 : ℝ)) →
      ‖g τ‖ ≤ Kg * (|τ| + c * |τ| ^ 3) ∧
      ‖deriv g τ‖ ≤ Kg * (1 + c * τ ^ 2) ∧
      ‖iteratedDeriv 2 g τ‖ ≤ Kg * (1 + c * |τ| + c ^ 2 * τ ^ 4) := by
  intro θ₁ ϕ g Kg
  have hc0 : 0 < c := by linarith
  set ς : ℝ := c ^ (-(1 / 3 : ℝ))
  have hς_le1 : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  let CA : ℝ := 1 + C₀ + C₁ + C₂
  have hϕ_cd : ContDiff ℝ 2 ϕ :=
    (contDiff_const.mul (((edgePhi_contDiff3 L).of_le (by decide)).sub (contDiff_const.mul contDiff_id))).sub
      (((CtOuter.contDiff_outerTheta (-1)).of_le (by simp)).sub (contDiff_const.mul contDiff_id))
  have hθ_sub_bounds : ∀ τ : ℝ,
      |CtOuter.outerTheta (-1) τ - θ₁ * τ| ≤ M₂ * τ ^ 2 ∧
      |deriv (CtOuter.outerTheta (-1)) τ - θ₁| ≤ M₂ * |τ| := fun τ => by
    have hθ0 : CtOuter.outerTheta (-1) 0 = 0 := by
      have := (CtOuter.ct_outer_part2_structure (Or.inr rfl)).2.1 0; simp at this; linarith
    have hdθ0 : deriv (CtOuter.outerTheta (-1)) 0 = θ₁ :=
      CtOuter.deriv_outerTheta_zero_eq_ctTheta1 (Or.inr rfl)
    have h1 : ∀ t : ℝ, |deriv (CtOuter.outerTheta (-1)) t - θ₁| ≤ M₂ * |t| := fun t => by
      have hdiff : ∀ s : ℝ, HasDerivAt (fun u => deriv (CtOuter.outerTheta (-1)) u - θ₁)
          (iteratedDeriv 2 (CtOuter.outerTheta (-1)) s) s := fun s => by
        have h := ((CtOuter.contDiff_outerTheta (-1)).differentiable_iteratedDeriv 1 (by simp) s).hasDerivAt
        rw [iteratedDeriv_one] at h
        exact (h.sub_const θ₁).congr_deriv (by rw [iteratedDeriv_succ, iteratedDeriv_one])
      have hcont : Continuous (iteratedDeriv 2 (CtOuter.outerTheta (-1))) :=
        (CtOuter.contDiff_outerTheta (-1)).continuous_iteratedDeriv 2 (by simp)
      have hftc : deriv (CtOuter.outerTheta (-1)) t - θ₁ = ∫ s in (0 : ℝ)..t, iteratedDeriv 2 (CtOuter.outerTheta (-1)) s := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hdiff s) (hcont.intervalIntegrable 0 t),
          hdθ0, sub_self, sub_zero]
      rw [hftc]
      have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t) (C := M₂)
        (fun s _ => by rw [Real.norm_eq_abs]; exact hθ2 s)
      simpa [Real.norm_eq_abs] using hbd
    refine ⟨?_, h1 τ⟩
    have hdiff0 : ∀ s : ℝ, HasDerivAt (fun u => CtOuter.outerTheta (-1) u - θ₁ * u)
        (deriv (CtOuter.outerTheta (-1)) s - θ₁) s := fun s =>
      ((CtOuter.contDiff_outerTheta (-1)).differentiable (by simp) s).hasDerivAt.sub
        (((hasDerivAt_id s).const_mul θ₁).congr_deriv (mul_one θ₁))
    have hcont1 : Continuous (fun s => deriv (CtOuter.outerTheta (-1)) s - θ₁) :=
      ((CtOuter.contDiff_outerTheta (-1)).continuous_deriv (by simp)).sub continuous_const
    have hftc0 : CtOuter.outerTheta (-1) τ - θ₁ * τ = ∫ s in (0 : ℝ)..τ, (deriv (CtOuter.outerTheta (-1)) s - θ₁) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hdiff0 s) (hcont1.intervalIntegrable 0 τ),
        hθ0, mul_zero, sub_self, sub_zero]
    rw [hftc0]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := τ) (C := M₂ * |τ|)
      (fun s hs => by
        rw [Real.norm_eq_abs]
        have hs_le : |s| ≤ |τ| := by
          rw [Set.mem_uIoc] at hs
          rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [abs_of_pos ha, abs_of_pos (lt_of_lt_of_le ha hb)]; exact hb
          · rw [abs_of_nonpos hb, abs_of_neg (lt_of_lt_of_le ha hb)]; linarith
        exact (h1 s).trans (mul_le_mul_of_nonneg_left hs_le hM₂.le))
    rw [Real.norm_eq_abs, sub_zero] at hbd
    exact hbd.trans_eq (by rw [← sq_abs τ]; ring)
  have hϕ_bounds : ∀ τ : ℝ, |τ| ≤ ς →
      |ϕ τ| ≤ (2 + M₂) * (|τ| + c * |τ| ^ 3) ∧
      |deriv ϕ τ| ≤ (2 + M₂) * (1 + c * τ ^ 2) ∧
      |iteratedDeriv 2 ϕ τ| ≤ (2 + M₂) * (1 + c * |τ|) := fun τ hτ => by
    have hτ1 : |τ| ≤ 1 := hτ.trans hς_le1
    have hsq_le : τ ^ 2 ≤ |τ| := by rw [← sq_abs τ]; nlinarith only [hτ1, abs_nonneg τ]
    obtain ⟨hp0, hp1, hp2⟩ := edgePhi_sub_linear_bounds L τ
    obtain ⟨ht0, ht1⟩ := hθ_sub_bounds τ
    have hd1 : deriv ϕ τ = c * (edgePhiDeriv L τ - L) - (deriv (CtOuter.outerTheta (-1)) τ - θ₁) := by
      have h1 := ((hasDerivAt_edgePhi L τ).sub (((hasDerivAt_id τ).const_mul L).congr_deriv (mul_one L))).const_mul c
      have h2 := ((CtOuter.contDiff_outerTheta (-1)).differentiable (by simp) τ).hasDerivAt.sub
        (((hasDerivAt_id τ).const_mul θ₁).congr_deriv (mul_one θ₁))
      exact (h1.sub h2).deriv
    have hd2 : iteratedDeriv 2 ϕ τ = c * edgePhiDeriv2 τ - iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ := by
      have h1 : ContDiff ℝ 2 (fun t => c * (edgePhi L t - L * t)) :=
        contDiff_const.mul (((edgePhi_contDiff3 L).of_le (by decide)).sub (contDiff_const.mul contDiff_id))
      have h2 : ContDiff ℝ 2 (fun t => CtOuter.outerTheta (-1) t - θ₁ * t) :=
        ((CtOuter.contDiff_outerTheta (-1)).of_le (by simp)).sub (contDiff_const.mul contDiff_id)
      rw [show ϕ = fun t => c * (edgePhi L t - L * t) - (CtOuter.outerTheta (-1) t - θ₁ * t) from rfl,
        iteratedDeriv_fun_sub h1.contDiffAt h2.contDiffAt, iteratedDeriv_const_mul_field]
      have hl1 : iteratedDeriv 2 (fun t : ℝ => edgePhi L t - L * t) τ = edgePhiDeriv2 τ := by
        have hlin_cd : ContDiff ℝ 2 (fun t : ℝ => L * t) := (contDiff_const.mul contDiff_id).of_le le_top
        rw [iteratedDeriv_fun_sub ((edgePhi_contDiff3 L).of_le (by decide)).contDiffAt
          hlin_cd.contDiffAt, (edgePhi_iteratedDeriv_eq L τ).2.1]
        have hlin : iteratedDeriv 2 (fun t : ℝ => L * t) τ = 0 := by
          have hd : deriv (fun t : ℝ => L * t) = fun _ => L := funext fun s =>
            (((hasDerivAt_id s).const_mul L).congr_deriv (mul_one L)).deriv
          rw [iteratedDeriv_succ, iteratedDeriv_one, hd, deriv_const]
        rw [hlin, sub_zero]
      have hl2 : iteratedDeriv 2 (fun t : ℝ => CtOuter.outerTheta (-1) t - θ₁ * t) τ =
          iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ := by
        have hlin_cd : ContDiff ℝ 2 (fun t : ℝ => θ₁ * t) := (contDiff_const.mul contDiff_id).of_le le_top
        rw [iteratedDeriv_fun_sub ((CtOuter.contDiff_outerTheta (-1)).of_le (by simp)).contDiffAt
          hlin_cd.contDiffAt]
        have hlin : iteratedDeriv 2 (fun t : ℝ => θ₁ * t) τ = 0 := by
          have hd : deriv (fun t : ℝ => θ₁ * t) = fun _ => θ₁ := funext fun s =>
            (((hasDerivAt_id s).const_mul θ₁).congr_deriv (mul_one θ₁)).deriv
          rw [iteratedDeriv_succ, iteratedDeriv_one, hd, deriv_const]
        rw [hlin, sub_zero]
      rw [hl1, hl2]
    refine ⟨?_, ?_, ?_⟩
    · calc |ϕ τ| ≤ |c * (edgePhi L τ - L * τ)| + |CtOuter.outerTheta (-1) τ - θ₁ * τ| := abs_sub _ _
        _ ≤ c * (2 * |τ| ^ 3) + M₂ * τ ^ 2 := by rw [abs_mul, abs_of_pos hc0]; exact add_le_add (by gcongr) ht0
        _ ≤ (2 + M₂) * (|τ| + c * |τ| ^ 3) := by
            have h1 : M₂ * τ ^ 2 ≤ M₂ * |τ| := mul_le_mul_of_nonneg_left hsq_le hM₂.le
            have h2 : 0 ≤ c * |τ| ^ 3 := by positivity
            nlinarith only [h1, h2, hM₂, abs_nonneg τ]
    · rw [hd1]
      calc |c * (edgePhiDeriv L τ - L) - (deriv (CtOuter.outerTheta (-1)) τ - θ₁)|
          ≤ |c * (edgePhiDeriv L τ - L)| + |deriv (CtOuter.outerTheta (-1)) τ - θ₁| := abs_sub _ _
        _ ≤ c * (2 * τ ^ 2) + M₂ * |τ| := by rw [abs_mul, abs_of_pos hc0]; exact add_le_add (by gcongr) ht1
        _ ≤ (2 + M₂) * (1 + c * τ ^ 2) := by
            have h1 : M₂ * |τ| ≤ M₂ := by nlinarith only [hM₂, hτ1]
            have h2 : 0 ≤ c * τ ^ 2 := by positivity
            nlinarith only [h1, h2, hM₂]
    · rw [hd2]
      calc |c * edgePhiDeriv2 τ - iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ|
          ≤ |c * edgePhiDeriv2 τ| + |iteratedDeriv 2 (CtOuter.outerTheta (-1)) τ| := abs_sub _ _
        _ ≤ c * (2 * |τ|) + M₂ := by rw [abs_mul, abs_of_pos hc0]; exact add_le_add (by gcongr) (hθ2 τ)
        _ ≤ (2 + M₂) * (1 + c * |τ|) := by
            have h2 : 0 ≤ c * |τ| := by positivity
            nlinarith only [h2, hM₂]
  let E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * (ϕ τ : ℂ))
  have hE_cd : ContDiff ℝ 2 E :=
    Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hϕ_cd))
  refine ⟨(hA_cd.mul hE_cd).sub contDiff_const, fun τ hτ => ?_⟩
  obtain ⟨hϕ0, hϕ1, hϕ2⟩ := hϕ_bounds τ hτ
  have hE_norm : ‖E τ‖ = 1 := by
    dsimp [E]; rw [show Complex.I * (ϕ τ : ℂ) = (ϕ τ : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I]
  have hE_sub : ‖E τ - 1‖ ≤ |ϕ τ| := by
    dsimp [E]; rw [show Complex.I * (ϕ τ : ℂ) = (ϕ τ : ℂ) * Complex.I by ring]
    exact norm_exp_ofReal_mul_I_sub_one_le' (ϕ τ)
  have hE_d1 : deriv E τ = Complex.I * ((deriv ϕ τ : ℝ) : ℂ) * E τ := by
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * (ϕ t : ℂ)) (Complex.I * ((deriv ϕ τ : ℝ) : ℂ)) τ :=
      ((hϕ_cd.differentiable (by decide) τ).hasDerivAt.ofReal_comp).const_mul Complex.I
    exact (((Complex.hasDerivAt_exp _).comp τ h1).congr_deriv (by dsimp [E]; ring)).deriv
  have hE_d2 : iteratedDeriv 2 E τ = (Complex.I * ((iteratedDeriv 2 ϕ τ : ℝ) : ℂ) - ((deriv ϕ τ : ℝ) : ℂ) ^ 2) * E τ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have heq : deriv E = fun t => Complex.I * ((deriv ϕ t : ℝ) : ℂ) * E t := funext fun t => by
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * (ϕ s : ℂ)) (Complex.I * ((deriv ϕ t : ℝ) : ℂ)) t :=
        ((hϕ_cd.differentiable (by decide) t).hasDerivAt.ofReal_comp).const_mul Complex.I
      exact (((Complex.hasDerivAt_exp _).comp t h1).congr_deriv (by dsimp [E]; ring)).deriv
    rw [heq]
    have hϕ'_d : HasDerivAt (fun t : ℝ => Complex.I * ((deriv ϕ t : ℝ) : ℂ))
        (Complex.I * ((iteratedDeriv 2 ϕ τ : ℝ) : ℂ)) τ := by
      have h := (hϕ_cd.differentiable_iteratedDeriv 1 (by decide) τ).hasDerivAt
      rw [iteratedDeriv_one] at h
      exact (h.ofReal_comp.congr_deriv (by rw [iteratedDeriv_succ, iteratedDeriv_one])).const_mul Complex.I
    have hE_d : HasDerivAt E (Complex.I * ((deriv ϕ τ : ℝ) : ℂ) * E τ) τ := by
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * (ϕ s : ℂ)) (Complex.I * ((deriv ϕ τ : ℝ) : ℂ)) τ :=
        ((hϕ_cd.differentiable (by decide) τ).hasDerivAt.ofReal_comp).const_mul Complex.I
      exact ((Complex.hasDerivAt_exp _).comp τ h1).congr_deriv (by dsimp [E]; ring)
    refine (hϕ'_d.mul hE_d).deriv.trans ?_
    calc Complex.I * ((iteratedDeriv 2 ϕ τ : ℝ) : ℂ) * E τ +
          Complex.I * ((deriv ϕ τ : ℝ) : ℂ) * (Complex.I * ((deriv ϕ τ : ℝ) : ℂ) * E τ)
        = (Complex.I * ((iteratedDeriv 2 ϕ τ : ℝ) : ℂ) + (Complex.I * Complex.I) * ((deriv ϕ τ : ℝ) : ℂ) ^ 2) * E τ := by ring
      _ = (Complex.I * ((iteratedDeriv 2 ϕ τ : ℝ) : ℂ) - ((deriv ϕ τ : ℝ) : ℂ) ^ 2) * E τ := by rw [Complex.I_mul_I]; ring
  have hE1_norm : ‖deriv E τ‖ ≤ (2 + M₂) * (1 + c * τ ^ 2) := by
    rw [hE_d1, norm_mul, norm_mul, Complex.norm_I, one_mul, hE_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hϕ1
  have hE2_norm : ‖iteratedDeriv 2 E τ‖ ≤ (2 + M₂) * (1 + c * |τ|) + ((2 + M₂) * (1 + c * τ ^ 2)) ^ 2 := by
    rw [hE_d2, norm_mul, hE_norm, mul_one]
    calc ‖Complex.I * ((iteratedDeriv 2 ϕ τ : ℝ) : ℂ) - ((deriv ϕ τ : ℝ) : ℂ) ^ 2‖
        ≤ ‖Complex.I * ((iteratedDeriv 2 ϕ τ : ℝ) : ℂ)‖ + ‖((deriv ϕ τ : ℝ) : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = |iteratedDeriv 2 ϕ τ| + |deriv ϕ τ| ^ 2 := by
          rw [norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (2 + M₂) * (1 + c * |τ|) + ((2 + M₂) * (1 + c * τ ^ 2)) ^ 2 :=
          add_le_add hϕ2 (pow_le_pow_left₀ (abs_nonneg _) hϕ1 2)
  have hA_sub : ‖A τ - A 0‖ ≤ C₁ * |τ| := by
    have hftc : A τ - A 0 = ∫ s in (0 : ℝ)..τ, deriv A s :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => (hA_cd.differentiable (by decide) s).hasDerivAt)
        ((hA_cd.continuous_deriv (by decide)).intervalIntegrable 0 τ)).symm
    rw [hftc]
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := τ) (C := C₁) (fun s _ => hA1 s)
  have h2M : 2 + M₂ ≤ 2 * (1 + M₂) := by linarith only [hM₂]
  have h2M2 : (2 + M₂) ^ 2 ≤ 4 * (1 + M₂) ^ 2 := by nlinarith only [hM₂]
  have h1M2 : 1 + M₂ ≤ (1 + M₂) ^ 2 := by nlinarith only [hM₂]
  have hsq_ct : (1 + c * τ ^ 2) ^ 2 ≤ 2 * (1 + c ^ 2 * τ ^ 4) := by
    have : 2 * (c * τ ^ 2) ≤ 1 + (c * τ ^ 2) ^ 2 := by nlinarith only [sq_nonneg (c * τ ^ 2 - 1)]
    nlinarith only [this]
  refine ⟨?_, ?_, ?_⟩
  · have hdecomp : g τ = (A τ - A 0) * E τ + A 0 * (E τ - 1) := by dsimp [g, E]; ring
    rw [hdecomp]
    calc ‖(A τ - A 0) * E τ + A 0 * (E τ - 1)‖
        ≤ ‖A τ - A 0‖ * ‖E τ‖ + ‖A 0‖ * ‖E τ - 1‖ := (norm_add_le _ _).trans (by simp only [norm_mul]; exact le_rfl)
      _ ≤ C₁ * |τ| * 1 + C₀ * ((2 + M₂) * (|τ| + c * |τ| ^ 3)) := by
          rw [hE_norm]; gcongr; exact hA0 0; exact hE_sub.trans hϕ0
      _ ≤ Kg * (|τ| + c * |τ| ^ 3) := by
          have hC1_le : C₁ ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₂]
          have hC0_le : C₀ ≤ CA := by dsimp [CA]; linarith only [hC₁, hC₂]
          have hCA_nn : 0 ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₁, hC₂]
          have hc3_nn : 0 ≤ c * |τ| ^ 3 := by positivity
          have hS_nn : 0 ≤ |τ| + c * |τ| ^ 3 := by linarith only [abs_nonneg τ, hc3_nn]
          have hT1 : C₁ * |τ| * 1 ≤ CA * (|τ| + c * |τ| ^ 3) := by
            nlinarith only [hC1_le, hCA_nn, abs_nonneg τ, hc3_nn]
          have hT2 : C₀ * ((2 + M₂) * (|τ| + c * |τ| ^ 3)) ≤
              (CA * (2 * (1 + M₂))) * (|τ| + c * |τ| ^ 3) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (mul_le_mul hC0_le h2M (by linarith only [hM₂]) hCA_nn) hS_nn
          have h2 : CA + CA * (2 * (1 + M₂)) ≤ Kg := by
            dsimp [Kg, CA]; nlinarith only [hC₀, hC₁, hC₂, h1M2, hM₂]
          calc C₁ * |τ| * 1 + C₀ * ((2 + M₂) * (|τ| + c * |τ| ^ 3))
              ≤ (CA + CA * (2 * (1 + M₂))) * (|τ| + c * |τ| ^ 3) := by linarith only [hT1, hT2]
            _ ≤ Kg * (|τ| + c * |τ| ^ 3) := mul_le_mul_of_nonneg_right h2 hS_nn
  · have hd : deriv g τ = deriv (fun t => A t * E t) τ := by
      dsimp [g, E]; exact (((hA_cd.mul hE_cd).differentiable (by decide) τ).hasDerivAt.sub_const (A 0)).deriv
    rw [hd]
    calc ‖deriv (fun t => A t * E t) τ‖
        ≤ ‖deriv A τ‖ * ‖E τ‖ + ‖A τ‖ * ‖deriv E τ‖ :=
          deriv_mul_norm (hA_cd.of_le (by decide)) (hE_cd.of_le (by decide)) τ
      _ ≤ C₁ * 1 + C₀ * ((2 + M₂) * (1 + c * τ ^ 2)) := by rw [hE_norm]; gcongr; exact hA1 τ; exact hA0 τ
      _ ≤ Kg * (1 + c * τ ^ 2) := by
          have hC1_le : C₁ ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₂]
          have hC0_le : C₀ ≤ CA := by dsimp [CA]; linarith only [hC₁, hC₂]
          have hCA_nn : 0 ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₁, hC₂]
          have hc2_nn : 0 ≤ c * τ ^ 2 := by positivity
          have hS_nn : 0 ≤ 1 + c * τ ^ 2 := by linarith only [hc2_nn]
          have hT1 : C₁ * 1 ≤ CA * (1 + c * τ ^ 2) := by nlinarith only [hC1_le, hCA_nn, hc2_nn]
          have hT2 : C₀ * ((2 + M₂) * (1 + c * τ ^ 2)) ≤ (CA * (2 * (1 + M₂))) * (1 + c * τ ^ 2) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (mul_le_mul hC0_le h2M (by linarith only [hM₂]) hCA_nn) hS_nn
          have h2 : CA + CA * (2 * (1 + M₂)) ≤ Kg := by
            dsimp [Kg, CA]; nlinarith only [hC₀, hC₁, hC₂, h1M2, hM₂]
          calc C₁ * 1 + C₀ * ((2 + M₂) * (1 + c * τ ^ 2))
              ≤ (CA + CA * (2 * (1 + M₂))) * (1 + c * τ ^ 2) := by linarith only [hT1, hT2]
            _ ≤ Kg * (1 + c * τ ^ 2) := mul_le_mul_of_nonneg_right h2 hS_nn
  · have hd2 : iteratedDeriv 2 g τ = iteratedDeriv 2 (fun t => A t * E t) τ := by
      dsimp [g, E]
      rw [iteratedDeriv_fun_sub (hA_cd.mul hE_cd).contDiffAt contDiff_const.contDiffAt,
        iteratedDeriv_const]; norm_num; rfl
    rw [hd2]
    calc ‖iteratedDeriv 2 (fun t => A t * E t) τ‖
        ≤ ‖iteratedDeriv 2 A τ‖ * ‖E τ‖ + 2 * ‖deriv A τ‖ * ‖deriv E τ‖ + ‖A τ‖ * ‖iteratedDeriv 2 E τ‖ :=
          leibniz_two_norm hA_cd hE_cd τ
      _ ≤ C₂ * 1 + 2 * C₁ * ((2 + M₂) * (1 + c * τ ^ 2)) +
          C₀ * ((2 + M₂) * (1 + c * |τ|) + ((2 + M₂) * (1 + c * τ ^ 2)) ^ 2) := by
          rw [hE_norm]; gcongr; exact hA2 τ; exact hA1 τ; exact hA0 τ
      _ ≤ Kg * (1 + c * |τ| + c ^ 2 * τ ^ 4) := by
          have hct2 : c * τ ^ 2 ≤ c * |τ| := by
            have hτ1 : |τ| ≤ 1 := hτ.trans hς_le1
            have : τ ^ 2 ≤ |τ| := by rw [← sq_abs τ]; nlinarith only [hτ1, abs_nonneg τ]
            exact mul_le_mul_of_nonneg_left this hc0.le
          have hc_abs : 0 ≤ c * |τ| := by positivity
          have hc2_t4 : 0 ≤ c ^ 2 * τ ^ 4 := by positivity
          have hE2_le : (2 + M₂) * (1 + c * |τ|) + ((2 + M₂) * (1 + c * τ ^ 2)) ^ 2 ≤
              10 * (1 + M₂) ^ 2 * (1 + c * |τ| + c ^ 2 * τ ^ 4) := by
            have hsq : ((2 + M₂) * (1 + c * τ ^ 2)) ^ 2 = (2 + M₂) ^ 2 * (1 + c * τ ^ 2) ^ 2 := mul_pow _ _ 2
            rw [hsq]
            have h1 : (2 + M₂) ^ 2 * (1 + c * τ ^ 2) ^ 2 ≤ 8 * (1 + M₂) ^ 2 * (1 + c ^ 2 * τ ^ 4) := by
              have := mul_le_mul h2M2 hsq_ct (sq_nonneg _) (by positivity)
              linarith only [this]
            have h2 : (2 + M₂) * (1 + c * |τ|) ≤ 2 * (1 + M₂) ^ 2 * (1 + c * |τ|) := by
              have : 2 + M₂ ≤ 2 * (1 + M₂) ^ 2 := by nlinarith only [h2M, h1M2]
              exact mul_le_mul_of_nonneg_right this (by linarith only [hc_abs])
            nlinarith only [h1, h2, hc_abs, hc2_t4, sq_nonneg (1 + M₂)]
          have hC2_le : C₂ ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₁]
          have hC1_le : C₁ ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₂]
          have hC0_le : C₀ ≤ CA := by dsimp [CA]; linarith only [hC₁, hC₂]
          have hCA_nn : 0 ≤ CA := by dsimp [CA]; linarith only [hC₀, hC₁, hC₂]
          have h1_le_M : 1 ≤ (1 + M₂) ^ 2 := by nlinarith only [hM₂]
          have h2M_sq : 2 + M₂ ≤ 2 * (1 + M₂) ^ 2 := by nlinarith only [h2M, h1M2]
          have hT0 : C₂ * 1 ≤ CA * (1 + M₂) ^ 2 * (1 + c * |τ| + c ^ 2 * τ ^ 4) := by
            have h1 : C₂ ≤ CA * (1 + M₂) ^ 2 := by nlinarith only [hC2_le, hCA_nn, h1_le_M]
            have h2 : 1 ≤ 1 + c * |τ| + c ^ 2 * τ ^ 4 := by linarith only [hc_abs, hc2_t4]
            have h3 := mul_le_mul h1 h2 zero_le_one (by positivity)
            linarith only [h3]
          have hT1 : 2 * C₁ * ((2 + M₂) * (1 + c * τ ^ 2)) ≤
              4 * CA * (1 + M₂) ^ 2 * (1 + c * |τ| + c ^ 2 * τ ^ 4) := by
            have ha : 1 + c * τ ^ 2 ≤ 1 + c * |τ| + c ^ 2 * τ ^ 4 := by linarith only [hct2, hc2_t4]
            have hb : (2 + M₂) * (1 + c * τ ^ 2) ≤ 2 * (1 + M₂) ^ 2 * (1 + c * |τ| + c ^ 2 * τ ^ 4) :=
              mul_le_mul h2M_sq ha (by positivity) (by positivity)
            have hc' : 2 * C₁ ≤ 2 * CA := by linarith only [hC1_le]
            have hd' := mul_le_mul hc' hb (by positivity) (by linarith only [hCA_nn])
            linarith only [hd']
          have hT2 : C₀ * ((2 + M₂) * (1 + c * |τ|) + ((2 + M₂) * (1 + c * τ ^ 2)) ^ 2) ≤
              10 * CA * (1 + M₂) ^ 2 * (1 + c * |τ| + c ^ 2 * τ ^ 4) := by
            have hd' := mul_le_mul hC0_le hE2_le (by positivity) hCA_nn
            linarith only [hd']
          have hprod_nn : 0 ≤ CA * (1 + M₂) ^ 2 * (1 + c * |τ| + c ^ 2 * τ ^ 4) := by positivity
          dsimp [Kg, CA]
          linarith only [hT0, hT1, hT2, hprod_nn]

set_option maxHeartbeats 400000 in
/-- Piece 3: Inner difference `χ_ς * R * g` is `O(c^{-2} L^{-2})` via `ibp_two_linear`. -/
private lemma far_inner_diff_bound {C₀ C₁ C₂ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C_in : ℝ, 0 < C_in ∧ ∀ {c L : ℝ} {A : ℝ → ℂ},
      60 ≤ c → 6 ≤ L → ContDiff ℝ 2 A →
      (∀ τ : ℝ, ‖A τ‖ ≤ C₀) → (∀ τ : ℝ, ‖deriv A τ‖ ≤ C₁) → (∀ τ : ℝ, ‖iteratedDeriv 2 A τ‖ ≤ C₂) →
      ‖((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ) *
        (∫ τ : ℝ, ((smoothCutoff0 (τ / c ^ (-(1 / 3 : ℝ))) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) * A τ -
           Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) * A 0) *
          regSqrt (1 / c) τ)‖ ≤
        C_in * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
  obtain ⟨M₁, M₂, M₃, hM₁, hM₂, hM₃, hθ⟩ := outerTheta_neg_deriv_uniform_bounds
  obtain ⟨Bχ, hBχ_pos, hBχ⟩ := smoothCutoff0_deriv_bounds
  let CA : ℝ := 1 + C₀ + C₁ + C₂
  let Kg : ℝ := 20 * CA * (1 + M₂) ^ 2
  let Kin : ℝ := 850 * (1 + Bχ) * Kg
  refine ⟨max 1 (4 * (π ^ 2 / 4 * |uctCAi|) * Kin), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun {c L A} hc hL hA_cd hA0 hA1 hA2 => ?_⟩
  have hc0 : 0 < c := by linarith
  have h1c : 0 < 1 / c := by positivity
  have hL0 : 0 < L := by linarith
  set ς : ℝ := c ^ (-(1 / 3 : ℝ))
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le1 : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hcς3 : c * ς ^ 3 = 1 := by
    dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, show -(1 / 3 : ℝ) * (3 : ℕ) = -1 by norm_num,
      Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
  have hcς2 : c * ς ^ 2 = ς⁻¹ := by
    have : (c * ς ^ 2) * ς = 1 := by linear_combination hcς3
    exact eq_inv_of_mul_eq_one_left this
  set θ₁ : ℝ := CtOuter.ctTheta1 (-1)
  set Ltilde : ℝ := L - θ₁ / c
  have hLtilde_ge : L / 2 ≤ Ltilde := by
    have hθle : θ₁ ≤ 12 := ctTheta1_neg_le
    have hdiv : θ₁ / c ≤ 1 / 5 := by rw [div_le_iff₀ hc0]; linarith
    dsimp [Ltilde]; linarith
  set ω : ℝ := c * Ltilde
  have hω_ge : c * L / 2 ≤ ω := by dsimp [ω]; nlinarith
  have hω_pos : 0 < ω := by linarith [mul_pos hc0 hL0]
  -- Phase difference `ϕ(τ) = c (Φ(L, τ) - L τ) - (θ_-(τ) - θ₁ τ)` and amplitude difference `g`:
  let ϕ : ℝ → ℝ := fun τ => c * (edgePhi L τ - L * τ) - (CtOuter.outerTheta (-1) τ - θ₁ * τ)
  let E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * (ϕ τ : ℂ))
  let g : ℝ → ℂ := fun τ => A τ * E τ - A 0
  obtain ⟨hg_cd, hg_bounds⟩ := far_inner_g_bounds hC₀ hC₁ hC₂ hM₂ (fun τ => (hθ τ).2.1) hc (L := L) hA_cd hA0 hA1 hA2
  -- Now let `f(τ) = χ_ς(τ) * (R(τ) * g(τ))`:
  let χς : ℝ → ℂ := fun τ => ((smoothCutoff0 (τ / ς) : ℝ) : ℂ)
  let h : ℝ → ℂ := fun τ => regSqrt (1 / c) τ * g τ
  let f : ℝ → ℂ := fun τ => χς τ * h τ
  have hχ_cd : ContDiff ℝ 2 χς :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const ς))
  have hh_cd : ContDiff ℝ 2 h := (contDiff_regSqrt h1c).mul hg_cd
  have hf_cd : ContDiff ℝ 2 f := hχ_cd.mul hh_cd
  have hf_supp : ∀ τ : ℝ, ς ≤ |τ| → f τ = 0 := fun τ hτ => by
    have h1 : 1 ≤ |τ / ς| := by rw [abs_div, abs_of_pos hς_pos, one_le_div hς_pos]; exact hτ
    simp [f, χς, smoothCutoff0_eq_zero h1]
  have hibp := ibp_two_linear hς_pos hω_pos.ne' hf_cd hf_supp
  -- Pointwise bound on `‖iteratedDeriv 2 f τ‖` on `[-ς, ς]`:
  have hpt : ∀ τ ∈ Icc (-ς) ς, ‖iteratedDeriv 2 f τ‖ ≤
      50 * (1 + Bχ) * Kg *
        ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) +
         c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ) +
         (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0)) := fun τ hτ => by
    have hτ_le : |τ| ≤ ς := abs_le.mpr hτ
    obtain ⟨hg0, hg1, hg2⟩ := hg_bounds τ hτ_le
    have hR0 : ‖regSqrt (1 / c) τ‖ ≤ 2 * (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) :=
      (norm_regSqrt_le_sum h1c τ).trans (mul_le_mul_of_nonneg_right
        (by have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 4 : ℝ) ≤ 1); simpa using this)
        (by positivity))
    have hR1 : ‖deriv (regSqrt (1 / c)) τ‖ ≤ 2 * (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) := norm_deriv_regSqrt_le h1c τ
    have hR2 : ‖iteratedDeriv 2 (regSqrt (1 / c)) τ‖ ≤ 3 * (1 / c + |τ|) ^ (-(5 / 2 : ℝ)) := norm_iteratedDeriv2_regSqrt_le h1c τ
    have hd_pos : 0 < 1 / c + |τ| := by positivity
    have h_abs_le : |τ| ≤ 1 / c + |τ| := by linarith
    -- Helper: `(1/c + |τ|)^{-p} * |τ|^q ≤ (1/c + |τ|)^{q - p}` when `0 ≤ q`:
    have hshift : ∀ (p q : ℝ), 0 ≤ q → (1 / c + |τ|) ^ (-p) * |τ| ^ q ≤ (1 / c + |τ|) ^ (q - p) := fun p q hq => by
      calc (1 / c + |τ|) ^ (-p) * |τ| ^ q
          ≤ (1 / c + |τ|) ^ (-p) * (1 / c + |τ|) ^ q :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) h_abs_le hq) (by positivity)
        _ = (1 / c + |τ|) ^ (q - p) := by rw [← Real.rpow_add hd_pos]; congr 1; ring
    have h_abs_rpow_le : ∀ (q : ℝ), 0 < q → (1 / c + |τ|) ^ (-q) * |τ| ^ (q + 1 / 2 : ℝ) ≤ |τ| ^ (1 / 2 : ℝ) := fun q hq => by
      by_cases h0 : τ = 0
      · subst h0; rw [abs_zero, Real.zero_rpow (by linarith), mul_zero, Real.zero_rpow (by norm_num)]
      · have ha : 0 < |τ| := abs_pos.mpr h0
        have h1 : (1 / c + |τ|) ^ (-q) ≤ |τ| ^ (-q) := Real.rpow_le_rpow_of_nonpos ha h_abs_le (by linarith)
        calc (1 / c + |τ|) ^ (-q) * |τ| ^ (q + 1 / 2 : ℝ)
            ≤ |τ| ^ (-q) * |τ| ^ (q + 1 / 2 : ℝ) := mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = |τ| ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add ha]; congr 1; ring
    -- Bound `‖h τ‖`, `‖deriv h τ‖`, `‖iteratedDeriv 2 h τ‖`:
    have hχ0 : ‖χς τ‖ ≤ 1 := by
      dsimp [χς]; rw [Complex.norm_real, Real.norm_of_nonneg (smoothCutoff0_nonneg _)]; exact smoothCutoff0_le_one _
    have hχ1 : ‖deriv χς τ‖ ≤ if ς / 2 ≤ |τ| then Bχ * ς⁻¹ else 0 := by
      have hd : deriv χς τ = ((ς⁻¹ * deriv smoothCutoff0 (τ / ς) : ℝ) : ℂ) := by
        rw [← (smoothCutoff0_scale_derivs hς_pos τ).1]
        exact (((contDiff_smoothCutoff0.differentiable (by decide)).comp (differentiable_id.div_const ς)).differentiableAt.hasDerivAt.ofReal_comp).deriv
      rw [hd, Complex.norm_real, Real.norm_eq_abs]
      split_ifs with hge
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hς_pos), mul_comm]
        exact mul_le_mul_of_nonneg_right (hBχ (τ / ς)).1 (inv_nonneg.mpr hς_pos.le)
      · rw [((hBχ (τ / ς)).2.2.1 (by rw [abs_div, abs_of_pos hς_pos, div_lt_iff₀ hς_pos]; linarith [not_le.mp hge])).1,
          mul_zero, abs_zero]
    have hχ2 : ‖iteratedDeriv 2 χς τ‖ ≤ if ς / 2 ≤ |τ| then Bχ * ς ^ (-(2 : ℝ)) else 0 := by
      have hcdς : ContDiff ℝ 2 (fun t => smoothCutoff0 (t / ς)) :=
        (contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const ς)
      have hd : iteratedDeriv 2 χς τ = ((ς ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / ς) : ℝ) : ℂ) := by
        rw [← (smoothCutoff0_scale_derivs hς_pos τ).2, iteratedDeriv_succ, iteratedDeriv_one,
          iteratedDeriv_succ, iteratedDeriv_one]
        have h1 : deriv χς = fun t => ((deriv (fun u => smoothCutoff0 (u / ς)) t : ℝ) : ℂ) := funext fun t =>
          ((hcdς.differentiable (by decide)).differentiableAt.hasDerivAt.ofReal_comp).deriv
        rw [h1]
        exact ((contDiff_one_deriv_of_two' hcdς).differentiable (by decide)).differentiableAt.hasDerivAt.ofReal_comp.deriv
      rw [hd, Complex.norm_real, Real.norm_eq_abs]
      split_ifs with hge
      · rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hς_pos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hBχ (τ / ς)).2.1 (by positivity)
      · rw [((hBχ (τ / ς)).2.2.1 (by rw [abs_div, abs_of_pos hς_pos, div_lt_iff₀ hς_pos]; linarith [not_le.mp hge])).2,
          mul_zero, abs_zero]
    -- Bound the three Leibniz terms of `f'' = χ'' h + 2 χ' h' + χ h''`:
    have hh2_bd : ‖iteratedDeriv 2 h τ‖ ≤ 10 * Kg *
        ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) +
         c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ)) := by
      have hL := leibniz_two_norm (contDiff_regSqrt h1c) hg_cd τ
      have hT1 : ‖iteratedDeriv 2 (regSqrt (1 / c)) τ‖ * ‖g τ‖ ≤
          3 * Kg * ((1 / c + |τ|) ^ (-(3 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ)) := by
        have h1 : (1 / c + |τ|) ^ (-(5 / 2 : ℝ)) * |τ| ≤ (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) := by
          have := hshift (5 / 2) 1 zero_le_one
          rw [Real.rpow_one, show (1 : ℝ) - 5 / 2 = -(3 / 2 : ℝ) by norm_num] at this; exact this
        have h2 : (1 / c + |τ|) ^ (-(5 / 2 : ℝ)) * |τ| ^ 3 ≤ |τ| ^ (1 / 2 : ℝ) := by
          have := h_abs_rpow_le (5 / 2) (by norm_num)
          rw [show (5 / 2 : ℝ) + 1 / 2 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this; exact this
        calc ‖iteratedDeriv 2 (regSqrt (1 / c)) τ‖ * ‖g τ‖
            ≤ (3 * (1 / c + |τ|) ^ (-(5 / 2 : ℝ))) * (Kg * (|τ| + c * |τ| ^ 3)) :=
              mul_le_mul hR2 hg0 (norm_nonneg _) (by positivity)
          _ = 3 * Kg * ((1 / c + |τ|) ^ (-(5 / 2 : ℝ)) * |τ| + c * ((1 / c + |τ|) ^ (-(5 / 2 : ℝ)) * |τ| ^ 3)) := by ring
          _ ≤ 3 * Kg * ((1 / c + |τ|) ^ (-(3 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ)) := by gcongr
      have hT2 : 2 * ‖deriv (regSqrt (1 / c)) τ‖ * ‖deriv g τ‖ ≤
          4 * Kg * ((1 / c + |τ|) ^ (-(3 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ)) := by
        have h2 : (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) * τ ^ 2 ≤ |τ| ^ (1 / 2 : ℝ) := by
          rw [← sq_abs τ]
          have := h_abs_rpow_le (3 / 2) (by norm_num)
          rw [show (3 / 2 : ℝ) + 1 / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this; exact this
        calc 2 * ‖deriv (regSqrt (1 / c)) τ‖ * ‖deriv g τ‖
            ≤ 2 * (2 * (1 / c + |τ|) ^ (-(3 / 2 : ℝ))) * (Kg * (1 + c * τ ^ 2)) := by gcongr
          _ = 4 * Kg * ((1 / c + |τ|) ^ (-(3 / 2 : ℝ)) + c * ((1 / c + |τ|) ^ (-(3 / 2 : ℝ)) * τ ^ 2)) := by ring
          _ ≤ 4 * Kg * ((1 / c + |τ|) ^ (-(3 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ)) := by gcongr
      have hT3 : ‖regSqrt (1 / c) τ‖ * ‖iteratedDeriv 2 g τ‖ ≤
          2 * Kg * ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ)) := by
        have h1 : (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) * |τ| ≤ |τ| ^ (1 / 2 : ℝ) := by
          have := h_abs_rpow_le (1 / 2) (by norm_num)
          rw [show (1 / 2 : ℝ) + 1 / 2 = (1 : ℝ) by norm_num, Real.rpow_one] at this; exact this
        have h2 : (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) * τ ^ 4 ≤ |τ| ^ (7 / 2 : ℝ) := by
          by_cases h0 : τ = 0
          · subst h0; simp [Real.zero_rpow (by norm_num : (7 / 2 : ℝ) ≠ 0)]
          · have ha : 0 < |τ| := abs_pos.mpr h0
            have hle : (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) ≤ |τ| ^ (-(1 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos ha h_abs_le (by norm_num)
            have h4 : τ ^ 4 = |τ| ^ (4 : ℝ) := by
              rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, show |τ| ^ 4 = (|τ| ^ 2) ^ 2 by ring,
                sq_abs]; ring
            rw [h4]
            calc (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) * |τ| ^ (4 : ℝ)
                ≤ |τ| ^ (-(1 / 2 : ℝ)) * |τ| ^ (4 : ℝ) := mul_le_mul_of_nonneg_right hle (by positivity)
              _ = |τ| ^ (7 / 2 : ℝ) := by rw [← Real.rpow_add ha]; norm_num
        calc ‖regSqrt (1 / c) τ‖ * ‖iteratedDeriv 2 g τ‖
            ≤ (2 * (1 / c + |τ|) ^ (-(1 / 2 : ℝ))) * (Kg * (1 + c * |τ| + c ^ 2 * τ ^ 4)) :=
              mul_le_mul hR0 hg2 (norm_nonneg _) (by positivity)
          _ = 2 * Kg * ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + c * ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) * |τ|) +
                c ^ 2 * ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) * τ ^ 4)) := by ring
          _ ≤ 2 * Kg * ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ)) := by gcongr
      have hKg_nn : 0 ≤ Kg := by dsimp [Kg, CA]; positivity
      have hn1 : 0 ≤ Kg * (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) := mul_nonneg hKg_nn (Real.rpow_nonneg hd_pos.le _)
      have hn2 : 0 ≤ Kg * (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) := mul_nonneg hKg_nn (Real.rpow_nonneg hd_pos.le _)
      have hn3 : 0 ≤ Kg * (c * |τ| ^ (1 / 2 : ℝ)) := mul_nonneg hKg_nn (by positivity)
      have hn4 : 0 ≤ Kg * (c ^ 2 * |τ| ^ (7 / 2 : ℝ)) := mul_nonneg hKg_nn (by positivity)
      linarith only [hL, hT1, hT2, hT3, hn1, hn2, hn3, hn4]
    have hχ_terms : ‖iteratedDeriv 2 χς τ‖ * ‖h τ‖ + 2 * ‖deriv χς τ‖ * ‖deriv h τ‖ ≤
        44 * Bχ * Kg * (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0) := by
      split_ifs with hge
      · have hτ_pos : 0 < |τ| := lt_of_lt_of_le (half_pos hς_pos) hge
        have hR0' : ‖regSqrt (1 / c) τ‖ ≤ 2 * ς ^ (-(1 / 2 : ℝ)) := by
          have h1 := norm_regSqrt_le_abs_rpow h1c (abs_pos.mp hτ_pos)
          have h2 : |τ| ^ (-(1 / 2 : ℝ)) ≤ (ς / 2) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (half_pos hς_pos) hge (by norm_num)
          have h3 : (ς / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 * ς ^ (-(1 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.mul_rpow hς_pos.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
              Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
            have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
              have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
              simpa using this
            gcongr
          exact h1.trans (h2.trans h3)
        have hR1' : ‖deriv (regSqrt (1 / c)) τ‖ ≤ 8 * ς ^ (-(3 / 2 : ℝ)) := by
          have h1 : ‖deriv (regSqrt (1 / c)) τ‖ ≤ 2 * |τ| ^ (-(3 / 2 : ℝ)) :=
            hR1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hτ_pos h_abs_le (by norm_num)) (by norm_num))
          have h2 : |τ| ^ (-(3 / 2 : ℝ)) ≤ (ς / 2) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (half_pos hς_pos) hge (by norm_num)
          have h3 : (ς / 2) ^ (-(3 / 2 : ℝ)) ≤ 4 * ς ^ (-(3 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.mul_rpow hς_pos.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
              Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
            have : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
              have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
              norm_num at this; exact this
            gcongr
          linarith only [h1, h2, h3]
        have hg0' : ‖g τ‖ ≤ 2 * Kg := by
          have hc3 : c * |τ| ^ 3 ≤ 1 := by
            have h3 : |τ| ^ 3 ≤ ς ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hτ_le 3
            have := mul_le_mul_of_nonneg_left h3 hc0.le
            linarith only [this, hcς3]
          have hKg_nn : 0 ≤ Kg := by dsimp [Kg, CA]; positivity
          have h1 : |τ| + c * |τ| ^ 3 ≤ 2 := by linarith only [hτ_le.trans hς_le1, hc3]
          exact hg0.trans (by nlinarith only [h1, hKg_nn])
        have hg1' : ‖deriv g τ‖ ≤ 2 * Kg * ς⁻¹ := by
          have hsq : c * τ ^ 2 ≤ ς⁻¹ := by
            rw [← sq_abs τ]
            have h2 : |τ| ^ 2 ≤ ς ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hτ_le 2
            have := mul_le_mul_of_nonneg_left h2 hc0.le
            linarith only [this, hcς2]
          have h1_le : 1 ≤ ς⁻¹ := one_le_inv₀ hς_pos |>.mpr hς_le1
          have hKg_nn : 0 ≤ Kg := by dsimp [Kg, CA]; positivity
          have hsum : 1 + c * τ ^ 2 ≤ 2 * ς⁻¹ := by linarith only [h1_le, hsq]
          exact hg1.trans (by nlinarith only [hsum, hKg_nn])
        have hh0' : ‖h τ‖ ≤ 4 * Kg * ς ^ (-(1 / 2 : ℝ)) := by
          dsimp [h]; rw [norm_mul]
          calc ‖regSqrt (1 / c) τ‖ * ‖g τ‖ ≤ (2 * ς ^ (-(1 / 2 : ℝ))) * (2 * Kg) :=
                mul_le_mul hR0' hg0' (norm_nonneg _) (by positivity)
            _ = 4 * Kg * ς ^ (-(1 / 2 : ℝ)) := by ring
        have hh1' : ‖deriv h τ‖ ≤ 20 * Kg * ς ^ (-(3 / 2 : ℝ)) := by
          have hd := deriv_mul_norm ((contDiff_regSqrt h1c).of_le (by decide)) (hg_cd.of_le (by decide)) τ
          have hm : ς ^ (-(1 / 2 : ℝ)) * ς⁻¹ = ς ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hς_pos]; norm_num
          calc ‖deriv h τ‖ ≤ ‖deriv (regSqrt (1 / c)) τ‖ * ‖g τ‖ + ‖regSqrt (1 / c) τ‖ * ‖deriv g τ‖ := hd
            _ ≤ (8 * ς ^ (-(3 / 2 : ℝ))) * (2 * Kg) + (2 * ς ^ (-(1 / 2 : ℝ))) * (2 * Kg * ς⁻¹) :=
                add_le_add (mul_le_mul hR1' hg0' (norm_nonneg _) (by positivity))
                  (mul_le_mul hR0' hg1' (norm_nonneg _) (by positivity))
            _ = 16 * Kg * ς ^ (-(3 / 2 : ℝ)) + 4 * Kg * (ς ^ (-(1 / 2 : ℝ)) * ς⁻¹) := by ring
            _ = 20 * Kg * ς ^ (-(3 / 2 : ℝ)) := by rw [hm]; ring
        rw [if_pos hge] at hχ1 hχ2
        have hm1 : ς ^ (-(2 : ℝ)) * ς ^ (-(1 / 2 : ℝ)) = ς ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hς_pos]; norm_num
        have hm2 : ς⁻¹ * ς ^ (-(3 / 2 : ℝ)) = ς ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_neg_one, ← Real.rpow_add hς_pos]; norm_num
        calc ‖iteratedDeriv 2 χς τ‖ * ‖h τ‖ + 2 * ‖deriv χς τ‖ * ‖deriv h τ‖
            ≤ (Bχ * ς ^ (-(2 : ℝ))) * (4 * Kg * ς ^ (-(1 / 2 : ℝ))) +
              2 * (Bχ * ς⁻¹) * (20 * Kg * ς ^ (-(3 / 2 : ℝ))) :=
              add_le_add (mul_le_mul hχ2 hh0' (norm_nonneg _) (by positivity))
                (mul_le_mul (mul_le_mul_of_nonneg_left hχ1 zero_le_two) hh1' (norm_nonneg _) (by positivity))
          _ = 4 * Bχ * Kg * (ς ^ (-(2 : ℝ)) * ς ^ (-(1 / 2 : ℝ))) +
              40 * Bχ * Kg * (ς⁻¹ * ς ^ (-(3 / 2 : ℝ))) := by ring
          _ = 44 * Bχ * Kg * ς ^ (-(5 / 2 : ℝ)) := by rw [hm1, hm2]; ring
      · rw [if_neg hge] at hχ1 hχ2
        have h1 : ‖deriv χς τ‖ = 0 := le_antisymm hχ1 (norm_nonneg _)
        have h2 : ‖iteratedDeriv 2 χς τ‖ = 0 := le_antisymm hχ2 (norm_nonneg _)
        rw [h1, h2]; simp
    have hL := leibniz_two_norm hχ_cd hh_cd τ
    have hKg_nn : 0 ≤ Kg := by dsimp [Kg, CA]; positivity
    calc ‖iteratedDeriv 2 f τ‖
        ≤ (‖iteratedDeriv 2 χς τ‖ * ‖h τ‖ + 2 * ‖deriv χς τ‖ * ‖deriv h τ‖) + ‖χς τ‖ * ‖iteratedDeriv 2 h τ‖ := by
          linarith
      _ ≤ 44 * Bχ * Kg * (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0) +
          1 * (10 * Kg * ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) +
            c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ))) :=
          add_le_add hχ_terms (mul_le_mul hχ0 hh2_bd (norm_nonneg _) zero_le_one)
      _ ≤ _ := by
          set S4 : ℝ := (1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) +
              c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ)
          set T5 : ℝ := if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0
          have hS4 : 0 ≤ S4 := by dsimp [S4]; positivity
          have hT5 : 0 ≤ T5 := by dsimp [T5]; split_ifs <;> positivity
          have hn1 : 0 ≤ Kg * S4 := mul_nonneg hKg_nn hS4
          have hn2 : 0 ≤ Bχ * (Kg * S4) := mul_nonneg hBχ_pos.le hn1
          have hn3 : 0 ≤ Kg * T5 := mul_nonneg hKg_nn hT5
          have hn4 : 0 ≤ Bχ * (Kg * T5) := mul_nonneg hBχ_pos.le hn3
          linarith only [hn1, hn2, hn3, hn4]
  -- Now integrate the 5 elementary terms on `Icc (-ς) ς` via `far_inner_five_integrals`:
  have hfive := far_inner_five_integrals hc
  have hint_f2 : ∫ τ in Icc (-ς) ς, ‖iteratedDeriv 2 f τ‖ ≤ Kin * c ^ (1 / 2 : ℝ) := by
    calc ∫ τ in Icc (-ς) ς, ‖iteratedDeriv 2 f τ‖
        ≤ ∫ τ in Icc (-ς) ς, 50 * (1 + Bχ) * Kg *
            ((1 / c + |τ|) ^ (-(1 / 2 : ℝ)) + (1 / c + |τ|) ^ (-(3 / 2 : ℝ)) +
             c * |τ| ^ (1 / 2 : ℝ) + c ^ 2 * |τ| ^ (7 / 2 : ℝ) +
             (if ς / 2 ≤ |τ| then ς ^ (-(5 / 2 : ℝ)) else 0)) :=
          setIntegral_mono_on ((hf_cd.continuous_iteratedDeriv 2 le_rfl).norm.continuousOn.integrableOn_compact isCompact_Icc)
            (hfive.1.const_mul _) measurableSet_Icc hpt
      _ = 50 * (1 + Bχ) * Kg * ∫ τ in Icc (-ς) ς, _ := integral_const_mul _ _
      _ ≤ 50 * (1 + Bχ) * Kg * (17 * c ^ (1 / 2 : ℝ)) := by
          have : 0 ≤ 50 * (1 + Bχ) * Kg := by dsimp [Kg, CA]; positivity
          exact mul_le_mul_of_nonneg_left hfive.2 this
      _ = Kin * c ^ (1 / 2 : ℝ) := by dsimp [Kin]; ring
  have hcongr_f : ∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) * A τ -
         Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) * A 0) *
        regSqrt (1 / c) τ =
      ∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    dsimp only [f, χς, h, g, E, ϕ, ω, Ltilde, θ₁]
    have hphase : Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((c * (edgePhi L τ - L * τ) - (CtOuter.outerTheta (-1) τ - CtOuter.ctTheta1 (-1) * τ) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1
      have : c * (edgePhi L τ - L * τ) - (CtOuter.outerTheta (-1) τ - CtOuter.ctTheta1 (-1) * τ) +
          c * (L - CtOuter.ctTheta1 (-1) / c) * τ = c * edgePhi L τ - CtOuter.outerTheta (-1) τ := by
        field_simp [hc0.ne']; ring
      push_cast; field_simp [show (c : ℂ) ≠ 0 by exact_mod_cast hc0.ne']; ring
    rw [hphase]; ring
  rw [hcongr_f, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hc_cancel : c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hc0]; norm_num
  have hω2 : ω ^ (-(2 : ℝ)) ≤ 4 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
    rw [rpow_neg_two_eq', rpow_neg_two_eq', rpow_neg_two_eq']
    have hsq : (c * L / 2) ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (by positivity) hω_ge 2
    have hinv := inv_anti₀ (by positivity : 0 < (c * L / 2) ^ 2) hsq
    exact hinv.trans_eq (by field_simp [hc0.ne', hL0.ne']; ring)
  have h2pi : (2 * π)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  calc c ^ (-(1 / 2 : ℝ)) / (2 * π) * (π ^ 2 / 4 * |uctCAi|) *
        ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖
      ≤ c ^ (-(1 / 2 : ℝ)) * (π ^ 2 / 4 * |uctCAi|) * (ω ^ (-(2 : ℝ)) * (Kin * c ^ (1 / 2 : ℝ))) := by
        have h1 : c ^ (-(1 / 2 : ℝ)) / (2 * π) ≤ c ^ (-(1 / 2 : ℝ)) := by
          rw [div_eq_mul_inv]; nlinarith [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
        have h2 : ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ ≤
            ω ^ (-(2 : ℝ)) * (Kin * c ^ (1 / 2 : ℝ)) :=
          hibp.trans (mul_le_mul_of_nonneg_left hint_f2 (by positivity))
        gcongr
    _ = (π ^ 2 / 4 * |uctCAi|) * Kin * (c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ)) * ω ^ (-(2 : ℝ)) := by ring
    _ = (π ^ 2 / 4 * |uctCAi|) * Kin * ω ^ (-(2 : ℝ)) := by rw [hc_cancel, mul_one]
    _ ≤ (π ^ 2 / 4 * |uctCAi|) * Kin * (4 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ))) := by
        have : 0 ≤ (π ^ 2 / 4 * |uctCAi|) * Kin := by dsimp [Kin, Kg, CA]; positivity
        exact mul_le_mul_of_nonneg_left hω2 this
    _ = (4 * (π ^ 2 / 4 * |uctCAi|) * Kin) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by ring
    _ ≤ max 1 (4 * (π ^ 2 / 4 * |uctCAi|) * Kin) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
        gcongr; exact le_max_right 1 _

/-- Piece 4: Linear reference `A 0 * χ_ς * R` against `A 0 * c⁻¹ * uctIflHhat (L - θ_1^- / c)`. -/
private lemma far_linear_ref_bound :
    ∃ C_ref : ℝ, 0 < C_ref ∧ ∀ {c L : ℝ} (A0 : ℂ),
      60 ≤ c → 6 ≤ L →
      ‖((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ) *
          (∫ τ : ℝ, ((smoothCutoff0 (τ / c ^ (-(1 / 3 : ℝ))) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) *
            A0 * regSqrt (1 / c) τ) -
        A0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)‖ ≤
        C_ref * ‖A0‖ * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
  obtain ⟨C0, hC0_pos, hfour⟩ := regSqrt_cutoff_fourier
  refine ⟨max 1 (4 * (π ^ 2 / 4 * |uctCAi|) * C0), lt_of_lt_of_le one_pos (le_max_left _ _), fun {c L} A0 hc hL => ?_⟩
  have hc0 : 0 < c := by linarith
  have h1c : 0 < 1 / c := by positivity
  have hL0 : 0 < L := by linarith
  set ς : ℝ := c ^ (-(1 / 3 : ℝ))
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  set Ltilde : ℝ := L - CtOuter.ctTheta1 (-1) / c
  have hLtilde_ge : L / 2 ≤ Ltilde := by
    have hθle : CtOuter.ctTheta1 (-1) ≤ 12 := ctTheta1_neg_le
    have hdiv : CtOuter.ctTheta1 (-1) / c ≤ 1 / 5 := by rw [div_le_iff₀ hc0]; linarith
    dsimp [Ltilde]; linarith
  have hLtilde_pos : 0 < Ltilde := by linarith
  set ω : ℝ := c * Ltilde
  have hω_pos : 0 < ω := mul_pos hc0 hLtilde_pos
  have hω_ge : c * L / 2 ≤ ω := by dsimp [ω]; nlinarith
  have hstep := hfour h1c hω_pos hς_pos
  have hrew : ((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ) *
        (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * A0 * regSqrt (1 / c) τ) -
      A0 * ((c⁻¹ * uctIflHhat Ltilde : ℝ) : ℂ) =
      A0 * ((c ^ (-(1 / 2 : ℝ)) * (π ^ 2 / 4 * |uctCAi|) : ℝ) : ℂ) *
        (((1 / (2 * π) : ℝ) : ℂ) *
          (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) * regSqrt (1 / c) τ *
            Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) -
         (((1 / √π) * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / c) * ω) : ℝ) : ℂ)) := by
    have hint_eq : ∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * A0 * regSqrt (1 / c) τ =
        A0 * ∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) * regSqrt (1 / c) τ *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => by ring)
    rw [hint_eq, ← linear_ref_eq_uctIflHhat hc0 hLtilde_pos]
    dsimp only [ω]
    push_cast; ring
  rw [hrew, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hς_c : c ^ (-(1 / 2 : ℝ)) * ς ^ (-(3 / 2 : ℝ)) = 1 := by
    dsimp [ς]; rw [← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hω2 : ω ^ (-(2 : ℝ)) ≤ 4 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
    rw [rpow_neg_two_eq', rpow_neg_two_eq', rpow_neg_two_eq']
    have hsq : (c * L / 2) ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (by positivity) hω_ge 2
    have hinv := inv_anti₀ (by positivity : 0 < (c * L / 2) ^ 2) hsq
    exact hinv.trans_eq (by field_simp [hc0.ne', hL0.ne']; ring)
  calc ‖A0‖ * (c ^ (-(1 / 2 : ℝ)) * (π ^ 2 / 4 * |uctCAi|)) * ‖_‖
      ≤ ‖A0‖ * (c ^ (-(1 / 2 : ℝ)) * (π ^ 2 / 4 * |uctCAi|)) * (C0 * ω ^ (-(2 : ℝ)) * ς ^ (-(3 / 2 : ℝ))) := by gcongr
    _ = (π ^ 2 / 4 * |uctCAi|) * C0 * ‖A0‖ * (c ^ (-(1 / 2 : ℝ)) * ς ^ (-(3 / 2 : ℝ))) * ω ^ (-(2 : ℝ)) := by ring
    _ = (π ^ 2 / 4 * |uctCAi|) * C0 * ‖A0‖ * ω ^ (-(2 : ℝ)) := by rw [hς_c, mul_one]
    _ ≤ (π ^ 2 / 4 * |uctCAi|) * C0 * ‖A0‖ * (4 * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ))) := by gcongr
    _ = (4 * (π ^ 2 / 4 * |uctCAi|) * C0) * ‖A0‖ * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by ring
    _ ≤ max 1 (4 * (π ^ 2 / 4 * |uctCAi|) * C0) * ‖A0‖ * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
        gcongr; exact le_max_right 1 _

/-! ### Section 5: Main far-band theorems (`uct:ce-band` (1)) -/

/-- **Lemma `uct:ce-band` (1), far-band asymptotic (general `A(0)`):**
Given `η > 0` and `C₀, C₁, C₂ ≥ 0`, there exists `C_far > 0` such that for all `c ≥ 60`,
`L ≥ (1/4) log c`, and `A ∈ C²(ℝ, ℂ)` with `‖A^{(j)}(τ)‖ ≤ C_j e^{-η|τ|}` (`j = 0, 1, 2`),
`‖h_norm^{ĥ}(L) - A(0) c⁻¹ I_fl^{ĥ}(L - θ_1^- / c)‖ ≤ C_far c⁻² L⁻²`.

Scope: full far-band statement of Lemma `uct:ce-band` (1) (both general `A(0)` and `A(0) = 1`),
uniformly in `c ≥ 60` and `L ≥ (1/4) log c`. -/
theorem uct_ce_band_far {η C₀ C₁ C₂ : ℝ} (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C_far : ℝ, 0 < C_far ∧ ∀ {c L : ℝ} {A : ℝ → ℂ},
      60 ≤ c → (1 / 4 : ℝ) * Real.log c ≤ L →
      ContDiff ℝ 2 A →
      (∀ τ : ℝ, ‖A τ‖ ≤ C₀ * Real.exp (-η * |τ|)) →
      (∀ τ : ℝ, ‖deriv A τ‖ ≤ C₁ * Real.exp (-η * |τ|)) →
      (∀ τ : ℝ, ‖iteratedDeriv 2 A τ‖ ≤ C₂ * Real.exp (-η * |τ|)) →
      ‖uctHnormCE c L A - A 0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)‖ ≤
        C_far * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
  obtain ⟨C_tail, hC_tail, htail⟩ := far_tail_bound hη hC₀
  obtain ⟨L₁, C_out, hL₁6, hC_out, hout⟩ := far_outer_bound hη hC₀ hC₁ hC₂
  obtain ⟨C_in, hC_in, hin⟩ := far_inner_diff_bound hC₀ hC₁ hC₂
  obtain ⟨C_ref, hC_ref, href⟩ := far_linear_ref_bound
  let C_large : ℝ := C_tail + C_out + C_in + C_ref * C₀
  let C_small : ℝ := ((π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) + C₀ * (2 * uctAlphaHhat)) *
    (Real.exp (8 * L₁) * L₁ ^ 2)
  refine ⟨max C_large (max 1 C_small), lt_of_lt_of_le (by positivity) (le_max_left _ _),
    fun {c L A} hc hLlog hA_cd hA0 hA1 hA2 => ?_⟩
  have hc0 : 0 < c := by linarith
  have h1c : 0 < 1 / c := by positivity
  have hL_ge1 : 1 ≤ L := by
    have hlog60 : 4 ≤ Real.log 60 := by
      have : Real.exp 4 ≤ 60 := by
        have h1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
        calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.72 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
          _ ≤ 60 := by norm_num
      rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) this
    have hlogc : 4 ≤ Real.log c := hlog60.trans (Real.log_le_log (by norm_num) hc)
    linarith
  have hL0 : 0 < L := by linarith
  have hA0_le : ‖A 0‖ ≤ C₀ := by simpa using hA0 0
  by_cases hL : L₁ ≤ L
  · -- Large `L ≥ L₁ ≥ 6`: split `uctHnormCE` into the 4 pieces!
    have hL6 : 6 ≤ L := hL₁6.trans hL
    set ς : ℝ := c ^ (-(1 / 3 : ℝ))
    have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
    set T : ℝ := tauStar L
    have hT_pos : 0 < T := by linarith [one_le_tauStar_half hL6]
    have hA0_unif : ∀ τ : ℝ, ‖A τ‖ ≤ C₀ := fun τ =>
      (hA0 τ).trans (mul_le_of_le_one_right hC₀ (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ])))
    have hA1_unif : ∀ τ : ℝ, ‖deriv A τ‖ ≤ C₁ := fun τ =>
      (hA1 τ).trans (mul_le_of_le_one_right hC₁ (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ])))
    have hA2_unif : ∀ τ : ℝ, ‖iteratedDeriv 2 A τ‖ ≤ C₂ := fun τ =>
      (hA2 τ).trans (mul_le_of_le_one_right hC₂ (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ])))
    have hint_main := (uct_ce_band_global_bound hC₀ hη hA_cd.continuous hA0 hc0 L).1
    have hint_compact : ∀ (s : ℝ), 0 < s → ∀ (F : ℝ → ℂ), Continuous F →
        Integrable (fun τ : ℝ => ((smoothCutoff0 (τ / s) : ℝ) : ℂ) * F τ) := fun s hs F hF => by
      refine ((Complex.continuous_ofReal.comp (contDiff_smoothCutoff0.continuous.comp (continuous_id.div_const s))).mul hF).integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -s) (b := s)) fun τ hτ => ?_
      rw [Function.mem_support] at hτ
      by_contra hnot
      have hge : s ≤ |τ| := by
        simp only [mem_Icc, not_and_or, not_le] at hnot
        rcases hnot with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact hτ (by
        simp only [Pi.mul_apply, Function.comp_apply, id_eq]
        rw [smoothCutoff0_eq_zero (by rw [abs_div, abs_of_pos hs, one_le_div hs]; exact hge), Complex.ofReal_zero, zero_mul])
    have hcont_AR : Continuous (fun τ : ℝ =>
        Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
        A τ * regSqrt (1 / c) τ) :=
      ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_const.mul (edgePhi_contDiff3 L).continuous).sub (CtOuter.contDiff_outerTheta (-1)).continuous)))).mul
        hA_cd.continuous).mul (contDiff_regSqrt h1c).continuous
    have hcont_lin : Continuous (fun τ : ℝ =>
        Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) *
        A 0 * regSqrt (1 / c) τ) :=
      ((Complex.continuous_exp.comp (by fun_prop)).mul continuous_const).mul (contDiff_regSqrt h1c).continuous
    have hint_T : Integrable (fun τ : ℝ => ((smoothCutoff0 (τ / T) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ)) := hint_compact T hT_pos _ hcont_AR
    have hint_ς : Integrable (fun τ : ℝ => ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ)) := hint_compact ς hς_pos _ hcont_AR
    have hint_lin : Integrable (fun τ : ℝ => ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) *
          A 0 * regSqrt (1 / c) τ)) := hint_compact ς hς_pos _ hcont_lin
    have hsplit : ∫ τ : ℝ, Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ =
        (∫ τ : ℝ, ((1 - smoothCutoff0 (τ / T) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ) +
        (∫ τ : ℝ, ((smoothCutoff0 (τ / T) - smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ) +
        (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) * A τ -
           Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) * A 0) *
          regSqrt (1 / c) τ) +
        (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) *
          A 0 * regSqrt (1 / c) τ) := by
      let f1 : ℝ → ℂ := fun τ => ((1 - smoothCutoff0 (τ / T) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ
      let f2 : ℝ → ℂ := fun τ => ((smoothCutoff0 (τ / T) - smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ
      let f3 : ℝ → ℂ := fun τ => ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) * A τ -
           Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) * A 0) *
          regSqrt (1 / c) τ
      let f4 : ℝ → ℂ := fun τ => ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) *
          A 0 * regSqrt (1 / c) τ
      have hi1 : Integrable f1 :=
        (hint_main.sub hint_T).congr (Eventually.of_forall fun τ => by dsimp [f1]; push_cast; ring)
      have hi2 : Integrable f2 :=
        (hint_T.sub hint_ς).congr (Eventually.of_forall fun τ => by dsimp [f2]; push_cast; ring)
      have hi3 : Integrable f3 :=
        (hint_ς.sub hint_lin).congr (Eventually.of_forall fun τ => by dsimp [f3]; ring)
      have hi4 : Integrable f4 :=
        hint_lin.congr (Eventually.of_forall fun τ => by dsimp [f4]; ring)
      have h12 : Integrable (fun τ => f1 τ + f2 τ) := hi1.add hi2
      have h123 : Integrable (fun τ => f1 τ + f2 τ + f3 τ) := h12.add hi3
      calc ∫ τ : ℝ, Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
              A τ * regSqrt (1 / c) τ
          = ∫ τ : ℝ, (f1 τ + f2 τ + f3 τ + f4 τ) :=
            integral_congr_ae (Eventually.of_forall fun τ => by dsimp [f1, f2, f3, f4]; push_cast; ring)
        _ = (∫ τ : ℝ, (f1 τ + f2 τ + f3 τ)) + (∫ τ : ℝ, f4 τ) := integral_add h123 hi4
        _ = ((∫ τ : ℝ, (f1 τ + f2 τ)) + (∫ τ : ℝ, f3 τ)) + (∫ τ : ℝ, f4 τ) := by rw [integral_add h12 hi3]
        _ = (((∫ τ : ℝ, f1 τ) + (∫ τ : ℝ, f2 τ)) + (∫ τ : ℝ, f3 τ)) + (∫ τ : ℝ, f4 τ) := by rw [integral_add hi1 hi2]
    let P : ℂ := ((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ)
    have hdecomp : uctHnormCE c L A - A 0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ) =
        P * (∫ τ : ℝ, ((1 - smoothCutoff0 (τ / T) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ) +
        P * (∫ τ : ℝ, ((smoothCutoff0 (τ / T) - smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ) +
        P * (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) * A τ -
           Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) * A 0) *
          regSqrt (1 / c) τ) +
        (P * (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) *
          A 0 * regSqrt (1 / c) τ) -
          A 0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)) := by
      unfold uctHnormCE; rw [hsplit]; dsimp [P]; ring
    rw [hdecomp]
    have h1 := htail hc hLlog hL6 hA_cd.continuous hA0
    have h2 := hout hc hL hA_cd hA0 hA1 hA2
    have h3 := hin hc hL6 hA_cd hA0_unif hA1_unif hA2_unif
    have h4 : ‖P * (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c * (L - CtOuter.ctTheta1 (-1) / c) * τ : ℝ) : ℂ)) *
          A 0 * regSqrt (1 / c) τ) -
          A 0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)‖ ≤
        C_ref * C₀ * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) :=
      (href (A 0) hc hL6).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA0_le hC_ref.le) (by positivity)) (by positivity))
    calc ‖_‖ ≤ ‖P * _ + P * _ + P * _‖ + ‖P * _ - _‖ := norm_add_le _ _
      _ ≤ (‖P * _ + P * _‖ + ‖P * _‖) + ‖P * _ - _‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖P * _‖ + ‖P * _‖) + ‖P * _‖) + ‖P * _ - _‖ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ ≤ ((C_tail * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) + C_out * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ))) +
            C_in * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ))) +
            C_ref * C₀ * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
          exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
      _ = C_large * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by dsimp [C_large]; ring
      _ ≤ max C_large (max 1 C_small) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
          gcongr; exact le_max_left _ _
  · -- Finite region `1 ≤ L < L₁` (hence `60 ≤ c ≤ exp(4 L₁)`): trivial from `uct_ce_band_global_bound`!
    have hL_lt : L < L₁ := not_le.mp hL
    have hc_le : c ≤ Real.exp (4 * L₁) := by
      rw [← Real.exp_log hc0]
      exact Real.exp_le_exp.mpr (by linarith)
    have hglob := (uct_ce_band_global_bound hC₀ hη hA_cd.continuous hA0 hc0 L).2
    have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hLtilde_ge : 1 / 2 ≤ L - CtOuter.ctTheta1 (-1) / c := by
      have hdiv : CtOuter.ctTheta1 (-1) / c ≤ 1 / 5 := by rw [div_le_iff₀ hc0]; linarith [ctTheta1_neg_le]
      linarith
    have hIfl_le : |c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c)| ≤ 2 * uctAlphaHhat := by
      unfold uctIflHhat
      have halpha_nn : 0 ≤ uctAlphaHhat := by unfold uctAlphaHhat; positivity
      have hpos_val : 0 ≤ c⁻¹ * (uctAlphaHhat * (L - CtOuter.ctTheta1 (-1) / c) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(L - CtOuter.ctTheta1 (-1) / c))) := by positivity
      rw [abs_of_nonneg hpos_val]
      have hc_inv : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hexp : Real.exp (-(L - CtOuter.ctTheta1 (-1) / c)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hpow : (L - CtOuter.ctTheta1 (-1) / c) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
        calc (L - CtOuter.ctTheta1 (-1) / c) ^ (-(1 / 2 : ℝ))
            ≤ (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hLtilde_ge (by norm_num)
          _ = (2 : ℝ) ^ (1 / 2 : ℝ) := by rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
          _ ≤ 2 := by
              have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
              simpa using this
      calc c⁻¹ * (uctAlphaHhat * (L - CtOuter.ctTheta1 (-1) / c) ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(L - CtOuter.ctTheta1 (-1) / c)))
          ≤ 1 * (uctAlphaHhat * 2 * 1) := by gcongr
        _ = 2 * uctAlphaHhat := by ring
    have h1_le : 1 ≤ (Real.exp (8 * L₁) * L₁ ^ 2) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
      rw [rpow_neg_two_eq', rpow_neg_two_eq']
      have hc2 : c ^ 2 ≤ Real.exp (8 * L₁) := by
        calc c ^ 2 ≤ (Real.exp (4 * L₁)) ^ 2 := pow_le_pow_left₀ hc0.le hc_le 2
          _ = Real.exp (8 * L₁) := by rw [← Real.exp_nat_mul]; congr 1; ring
      have hL2 : L ^ 2 ≤ L₁ ^ 2 := pow_le_pow_left₀ hL0.le hL_lt.le 2
      have hmul : c ^ 2 * L ^ 2 ≤ Real.exp (8 * L₁) * L₁ ^ 2 := mul_le_mul hc2 hL2 (sq_nonneg _) (Real.exp_pos _).le
      rw [show Real.exp (8 * L₁) * L₁ ^ 2 * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ =
        (Real.exp (8 * L₁) * L₁ ^ 2) / (c ^ 2 * L ^ 2) by ring, one_le_div (by positivity)]
      exact hmul
    have hbound1 : ‖uctHnormCE c L A - A 0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)‖ ≤
        (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) + C₀ * (2 * uctAlphaHhat) := by
      calc ‖uctHnormCE c L A - A 0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)‖
          ≤ ‖uctHnormCE c L A‖ + ‖A 0‖ * |c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c)| := by
            refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) * 1 + C₀ * (2 * uctAlphaHhat) := by
            refine add_le_add (hglob.trans (mul_le_mul_of_nonneg_left hc12 (by positivity))) ?_
            exact mul_le_mul hA0_le hIfl_le (abs_nonneg _) hC₀
        _ = _ := by ring
    calc ‖uctHnormCE c L A - A 0 * ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)‖
        ≤ ((π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) + C₀ * (2 * uctAlphaHhat)) * 1 := by linarith
      _ ≤ ((π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) + C₀ * (2 * uctAlphaHhat)) *
            ((Real.exp (8 * L₁) * L₁ ^ 2) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ))) := by
          have : 0 ≤ (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) + C₀ * (2 * uctAlphaHhat) := by
            unfold uctAlphaHhat; positivity
          exact mul_le_mul_of_nonneg_left h1_le this
      _ = C_small * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by dsimp [C_small]; ring
      _ ≤ max C_large (max 1 C_small) * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
          gcongr; exact (le_max_right 1 C_small).trans (le_max_right _ _)

/-- **Lemma `uct:ce-band` (1), far-band asymptotic (`A(0) = 1` case):**
Specialization of `uct_ce_band_far` to `A(0) = 1`, matching the displayed equation in `uct:ce-band` (1). -/
theorem uct_ce_band_far_unit {η C₀ C₁ C₂ : ℝ} (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C_far : ℝ, 0 < C_far ∧ ∀ {c L : ℝ} {A : ℝ → ℂ},
      60 ≤ c → (1 / 4 : ℝ) * Real.log c ≤ L →
      ContDiff ℝ 2 A → A 0 = 1 →
      (∀ τ : ℝ, ‖A τ‖ ≤ C₀ * Real.exp (-η * |τ|)) →
      (∀ τ : ℝ, ‖deriv A τ‖ ≤ C₁ * Real.exp (-η * |τ|)) →
      (∀ τ : ℝ, ‖iteratedDeriv 2 A τ‖ ≤ C₂ * Real.exp (-η * |τ|)) →
      ‖uctHnormCE c L A - ((c⁻¹ * uctIflHhat (L - CtOuter.ctTheta1 (-1) / c) : ℝ) : ℂ)‖ ≤
        C_far * c ^ (-(2 : ℝ)) * L ^ (-(2 : ℝ)) := by
  obtain ⟨C_far, hC_pos, hfar⟩ := uct_ce_band_far hη hC₀ hC₁ hC₂
  refine ⟨C_far, hC_pos, fun {c L A} hc hL hA_cd hA00 hA0 hA1 hA2 => ?_⟩
  simpa [hA00] using hfar hc hL hA_cd hA0 hA1 hA2

/-- info: 'FormalResearch.SignUncertainty.uct_ce_band_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_ce_band_far

/-- info: 'FormalResearch.SignUncertainty.uct_ce_band_far_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_ce_band_far_unit

end FormalResearch.SignUncertainty
