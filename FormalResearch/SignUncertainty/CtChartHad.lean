module

public import FormalResearch.SignUncertainty.CtChartAmp

/-!
# The Hadamard quotient at the saddle curve `y = y_*(β) = d(β)²β` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (`M = 1 + (s²+a) Q_geo`, `θ∘T - sψ = s(s²+a) h̃`).  **Proved.**
For `F` `C^∞` over `ℂ` near `(0,0)`: `F(y,β) - F(y_*(β),β) = (y - y_*(β)) Q(y,β)` with `Q` `C^∞` and `Q(0,0) = ∂_y F(0,0)`.
Also `E₁(w) = (e^w - 1)/w = ∫₀¹ e^{tw} dt`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The saddle curve `y_*(β) = d(β)² β = -a(β)`. -/
noncomputable def ysF (β : ℂ) : ℂ := dC β ^ 2 * β

lemma ysF_zero : ysF 0 = 0 := by simp [ysF]

lemma contDiffAt_ysF : ContDiffAt ℂ ∞' ysF 0 := (contDiffAt_dC.pow 2).mul contDiffAt_id

lemma aC_eq : aC = fun β => -ysF β := by funext β; simp [aC, ysF]

/-- First partial derivative `∂_y F`. -/
noncomputable def dyF (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ := fderiv ℂ F p (1, 0)

lemma contDiffAt_dyF {F : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (h : ContDiffAt ℂ ∞' F x) : ContDiffAt ℂ ∞' (dyF F) x := by
  unfold dyF
  exact (h.fderiv_right (m := ∞') (by exact le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add]; simp))).clm_apply
    contDiffAt_const

/-- The Hadamard quotient `∫₀¹ ∂_y F(y_* + t (y - y_*), β) dt`. -/
noncomputable def hadY (F : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, dyF F (ysF q.2 + (t : ℂ) * (q.1 - ysF q.2), q.2)

lemma contDiffAt_hadY {F : ℂ × ℂ → ℂ} (h : ContDiffAt ℂ ∞' F (0, 0)) : ContDiffAt ℂ ∞' (hadY F) (0, 0) := by
  unfold hadY
  refine contDiffAt_segInt (F := fun (q : ℂ × ℂ) w => dyF F (ysF q.2 + w * (q.1 - ysF q.2), q.2)) ?_
  intro t ht
  have hd : ContDiffAt ℂ ∞' (dyF F) ((fun p : (ℂ × ℂ) × ℂ => (ysF p.1.2 + p.2 * (p.1.1 - ysF p.1.2), p.1.2)) ((0, 0), (t : ℂ))) := by
    simpa [ysF_zero] using contDiffAt_dyF h
  have hy : ContDiffAt ℂ ∞' (fun p : (ℂ × ℂ) × ℂ => ysF p.1.2) ((0, 0), (t : ℂ)) :=
    ContDiffAt.comp (g := ysF) (f := fun p : (ℂ × ℂ) × ℂ => p.1.2) ((0, 0), (t : ℂ)) (by simpa using contDiffAt_ysF)
      (contDiff_snd.comp contDiff_fst).contDiffAt
  have hin : ContDiffAt ℂ ∞' (fun p : (ℂ × ℂ) × ℂ => (ysF p.1.2 + p.2 * (p.1.1 - ysF p.1.2), p.1.2)) ((0, 0), (t : ℂ)) :=
    (hy.add (contDiff_snd.contDiffAt.mul ((contDiff_fst.comp contDiff_fst).contDiffAt.sub hy))).prodMk
      (contDiff_snd.comp contDiff_fst).contDiffAt
  exact ContDiffAt.comp (g := dyF F) (f := fun p : (ℂ × ℂ) × ℂ => (ysF p.1.2 + p.2 * (p.1.1 - ysF p.1.2), p.1.2))
    ((0, 0), (t : ℂ)) hd hin

lemma hadY_zero (F : ℂ × ℂ → ℂ) : hadY F (0, 0) = dyF F (0, 0) := by
  unfold hadY
  simp [ysF_zero]

lemma hadY_identity {F : ℂ × ℂ → ℂ} (h : ContDiffAt ℂ ∞' F (0, 0)) :
    ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), F q - F (ysF q.2, q.2) = (q.1 - ysF q.2) * hadY F q := by
  have h2 : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), ContDiffAt ℂ 2 F p := (h.of_le (by simp)).eventually (by simp)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp h2
  have hys : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), ‖ysF q.2‖ < r := by
    have : ContinuousAt (fun q : ℂ × ℂ => ysF q.2) (0, 0) :=
      ContinuousAt.comp (g := ysF) (f := fun q : ℂ × ℂ => q.2) (by simpa using contDiffAt_ysF.continuousAt)
        continuous_snd.continuousAt
    have h0 : (fun q : ℂ × ℂ => ysF q.2) (0, 0) = 0 := by simp [ysF_zero]
    have hb1 : Metric.ball (0 : ℂ) r ∈ 𝓝 ((fun q : ℂ × ℂ => ysF q.2) (0, 0)) := by
      rw [h0]; exact Metric.ball_mem_nhds _ hr
    filter_upwards [this.preimage_mem_nhds hb1] with q hq
    simpa [mem_ball_zero_iff] using hq
  have hq : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), ‖q‖ < r := by
    have hb0 : Metric.ball ((0 : ℂ), (0 : ℂ)) r ∈ 𝓝 ((0 : ℂ), (0 : ℂ)) := Metric.ball_mem_nhds _ hr
    filter_upwards [hb0] with q hq
    have e0 : ((0 : ℂ), (0 : ℂ)) = (0 : ℂ × ℂ) := rfl
    rw [e0, mem_ball_zero_iff] at hq
    exact hq
  filter_upwards [hys, hq] with q hq1 hq2
  obtain ⟨y, β⟩ := q
  simp only at hq1 hq2 ⊢
  have hβ : ‖β‖ < r := lt_of_le_of_lt (le_max_right _ _) hq2
  have hy : ‖y‖ < r := lt_of_le_of_lt (le_max_left _ _) hq2
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖(ysF β + (t : ℂ) * (y - ysF β), β)‖ < r := by
    intro t ht
    have e : ysF β + (t : ℂ) * (y - ysF β) = (1 - (t : ℂ)) * ysF β + (t : ℂ) * y := by ring
    have h1 : ‖ysF β + (t : ℂ) * (y - ysF β)‖ < r := by
      rw [e]
      calc ‖(1 - (t : ℂ)) * ysF β + (t : ℂ) * y‖ ≤ ‖(1 - (t : ℂ)) * ysF β‖ + ‖(t : ℂ) * y‖ := norm_add_le _ _
        _ = (1 - t) * ‖ysF β‖ + t * ‖y‖ := by
          rw [norm_mul, norm_mul]
          have a1 : ‖(1 - (t : ℂ))‖ = 1 - t := by
            rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith [ht.2])]
          have a2 : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
          rw [a1, a2]
        _ < r := by
          have hm : 0 < min (r - ‖ysF β‖) (r - ‖y‖) := lt_min (by linarith) (by linarith)
          have m1 := min_le_left (r - ‖ysF β‖) (r - ‖y‖)
          have m2 := min_le_right (r - ‖ysF β‖) (r - ‖y‖)
          nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr m1),
            mul_nonneg ht.1 (sub_nonneg.mpr m2), hm]
    exact max_lt h1 hβ
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (ysF β + (t : ℂ) * (y - ysF β), β) ∈ Metric.ball ((0 : ℂ), (0 : ℂ)) r := by
    intro t ht
    have e0 : ((0 : ℂ), (0 : ℂ)) = (0 : ℂ × ℂ) := rfl
    rw [e0, mem_ball_zero_iff]; exact hseg t ht
  have hT := taylor1_seg (p := fun y' : ℂ => F (y', β)) (p1 := fun y' : ℂ => dyF F (y', β)) (z := y) (β := ysF β)
    (fun t ht => by
      have hc := hb _ (hmem t ht)
      exact hasDerivAt_slice1 (q := (ysF β + (t : ℂ) * (y - ysF β), β)) (hc.differentiableAt (by simp)))
    (by
      intro t ht
      have hc := (hb _ (hmem t ht))
      have h1 : ContinuousAt (dyF F) (ysF β + (t : ℂ) * (y - ysF β), β) := by
        unfold dyF
        have := (hc.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiffAt_const (c := ((1 : ℂ), (0 : ℂ))))
        exact (this.continuousAt)
      have h3 : ContinuousAt (fun s : ℝ => (ysF β + (s : ℂ) * (y - ysF β), β)) t := by fun_prop
      exact (ContinuousAt.comp (g := dyF F) (f := fun s : ℝ => (ysF β + (s : ℂ) * (y - ysF β), β)) h1 h3).continuousWithinAt)
  unfold hadY
  simpa using hT

/-- `E₁(w) = (e^w - 1)/w = ∫₀¹ e^{tw} dt`. -/
noncomputable def E1 (w : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, Complex.exp ((t : ℂ) * w)

lemma contDiffAt_E1 (w0 : ℂ) : ContDiffAt ℂ ∞' E1 w0 := by
  unfold E1
  refine contDiffAt_segInt (F := fun (w : ℂ) (t : ℂ) => Complex.exp (t * w)) ?_
  intro t ht
  exact (Complex.contDiff_exp.comp (contDiff_snd.mul contDiff_fst)).contDiffAt

lemma E1_zero : E1 0 = 1 := by simp [E1]

lemma exp_sub_one_eq (w : ℂ) : Complex.exp w - 1 = w * E1 w := by
  unfold E1
  have := taylor1_seg (p := Complex.exp) (p1 := Complex.exp) (z := w) (β := 0)
    (fun t _ => by simpa using Complex.hasDerivAt_exp _) (by
      simp only [zero_add, sub_zero]
      exact (Complex.continuous_exp.comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * w)).continuousOn)
  simp only [Complex.exp_zero, sub_zero] at this
  rw [this]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [mul_comm]

end FormalResearch.SignUncertainty.CtChart
