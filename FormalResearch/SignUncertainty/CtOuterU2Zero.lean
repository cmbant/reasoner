module

public import FormalResearch.SignUncertainty.CtOuterU2

/-!
# The value `u_r''(0) = -7π²/60 - 1`

Support for the cubic coefficient of `ct:outer` (2) (the constant `7π²/30` in `c_{3,mp}`).  **Proved**:
from the local factorization `u_r = ½(Log 6T(πz) - Log Q(πz) - Log(1+z²))` with `T(w) = 1/6 + w²T₂(w)`,
`Q(w) = 1 + w²T(w)` (`sinhT₂ 0 = 1/120`), and the Taylor expansion of the even smooth function `u_r`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `(sinh w - w - w³/6)/w⁵` as a power series (value `1/120` at `0`). -/
noncomputable def sinhT2 (w : ℂ) : ℂ := ∑' n : ℕ, w ^ (2 * n) / ((2 * n + 5).factorial : ℂ)

private lemma norm_term_T2_le (w : ℂ) (n : ℕ) :
    ‖w ^ (2 * n) / ((2 * n + 5).factorial : ℂ)‖ ≤ ‖w‖ ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have h1 : ((2 * n).factorial : ℝ) ≤ ((2 * n + 5).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have h0 : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_le_div_of_nonneg_left (by positivity) h0 h1

private lemma summable_cosh_real' (r : ℝ) : Summable (fun n : ℕ => r ^ (2 * n) / ((2 * n).factorial : ℝ)) :=
  (Real.hasSum_cosh r).summable

lemma hasSum_sinhT2 (w : ℂ) :
    HasSum (fun n : ℕ => w ^ (2 * n) / ((2 * n + 5).factorial : ℂ)) (sinhT2 w) :=
  (Summable.of_norm_bounded (summable_cosh_real' ‖w‖) (norm_term_T2_le w)).hasSum

lemma sinhT_sub_sixth (w : ℂ) : sinhT w - 1 / 6 = w ^ 2 * sinhT2 w := by
  have h := hasSum_sinhT w
  have h1 := (hasSum_nat_add_iff' (f := fun n : ℕ => w ^ (2 * n) / ((2 * n + 3).factorial : ℂ)) 1).mpr h
  have h2 := (hasSum_sinhT2 w).mul_left (w ^ 2)
  simp only [Finset.range_one, Finset.sum_singleton] at h1
  have e : sinhT w - w ^ (2 * 0) / ((2 * 0 + 3).factorial : ℂ) = sinhT w - 1 / 6 := by
    norm_num [Nat.factorial]
  rw [e] at h1
  refine h1.unique ?_
  convert h2 using 1
  ext n
  simp only [mul_add, mul_one, pow_add]
  ring_nf

lemma sinhT2_zero : sinhT2 0 = 1 / 120 := by
  have h := hasSum_sinhT2 0
  have : (fun n : ℕ => (0 : ℂ) ^ (2 * n) / ((2 * n + 5).factorial : ℂ)) =
      fun n => if n = 0 then (1 / 120 : ℂ) else 0 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [Nat.factorial]
    · have : (2 * n) ≠ 0 := by omega
      simp [this, hn.ne']
  rw [this] at h
  exact h.unique (hasSum_ite_eq (0 : ℕ) (1 / 120 : ℂ))

lemma differentiable_sinhT2 : Differentiable ℂ sinhT2 := by
  intro w
  have hU : IsOpen (ball (0 : ℂ) (‖w‖ + 1)) := isOpen_ball
  have h : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, z ^ (2 * n) / ((2 * n + 5).factorial : ℂ))
      (ball 0 (‖w‖ + 1)) := by
    refine differentiableOn_tsum_of_summable_norm (summable_cosh_real' (‖w‖ + 1)) ?_ hU ?_
    · intro n; fun_prop
    · intro n z hz
      refine (norm_term_T2_le z n).trans ?_
      have : ‖z‖ ≤ ‖w‖ + 1 := (mem_ball_zero_iff.mp hz).le
      gcongr
  exact h.differentiableAt (hU.mem_nhds (by simp [mem_ball]))

/-- `Log(1 + z² g(z)) / z² → g(0)`. -/
lemma tendsto_log_one_add_sq_mul {g : ℂ → ℂ} (hg : ContinuousAt g 0) :
    Tendsto (fun z : ℂ => Complex.log (1 + z ^ 2 * g z) / z ^ 2) (𝓝[≠] 0) (𝓝 (g 0)) := by
  set f : ℂ → ℂ := fun y => Complex.log (1 + y) with hf
  have hdiff : DifferentiableAt ℂ f 0 := by
    have : DifferentiableAt ℂ (fun y : ℂ => 1 + y) 0 := by fun_prop
    exact this.clog (by simp)
  have hD : ContinuousAt (dslope f 0) 0 := continuousAt_dslope_same.2 hdiff
  have hD0 : dslope f 0 0 = 1 := by
    rw [dslope_same]
    have : HasDerivAt f (1 / (1 + 0)) 0 := by
      have h1 : HasDerivAt (fun y : ℂ => 1 + y) 1 0 := by simpa using (hasDerivAt_id (0 : ℂ)).const_add 1
      exact h1.clog (by simp) |>.congr_deriv (by simp)
    simpa using this.deriv
  have hz2 : Tendsto (fun z : ℂ => z ^ 2 * g z) (𝓝 0) (𝓝 0) := by
    have : ContinuousAt (fun z : ℂ => z ^ 2 * g z) 0 := (continuousAt_id.pow 2).mul hg
    simpa using this.tendsto
  have hDt : Tendsto (fun z : ℂ => dslope f 0 (z ^ 2 * g z)) (𝓝 0) (𝓝 1) := by
    have := hD.tendsto.comp hz2
    rwa [hD0] at this
  have hlim := (hg.tendsto.mul hDt).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ 0 := hz
  have h := sub_smul_dslope f 0 (z ^ 2 * g z)
  simp only [sub_zero, smul_eq_mul, hf, add_zero, Complex.log_one] at h
  rw [show (1 : ℂ) + z ^ 2 * g z = 1 + (z ^ 2 * g z) from rfl]
  have : Complex.log (1 + z ^ 2 * g z) = z ^ 2 * g z * dslope f 0 (z ^ 2 * g z) := by
    rw [h]
  rw [this]
  field_simp


/-- The constant `c₂ = (π²/20 - π²/6 - 1)/2`. -/
noncomputable def cU2 : ℝ := (π ^ 2 / 20 - π ^ 2 / 6 - 1) / 2

lemma tendsto_utilde0_div_sq :
    Tendsto (fun z : ℂ => utilde0 z / z ^ 2) (𝓝[≠] 0) (𝓝 ((cU2 : ℝ) : ℂ)) := by
  have hpi : ContinuousAt (fun z : ℂ => (π : ℂ) * z) 0 := by fun_prop
  have hT2 : ContinuousAt (fun z : ℂ => sinhT2 ((π : ℂ) * z)) 0 :=
    (differentiable_sinhT2.continuous.continuousAt).comp (f := fun z : ℂ => (π : ℂ) * z) hpi
  have hT : ContinuousAt (fun z : ℂ => sinhT ((π : ℂ) * z)) 0 :=
    (differentiable_sinhT.continuous.continuousAt).comp (f := fun z : ℂ => (π : ℂ) * z) hpi
  have gA := tendsto_log_one_add_sq_mul (g := fun z : ℂ => 6 * (π : ℂ) ^ 2 * sinhT2 ((π : ℂ) * z))
    (continuousAt_const.mul hT2)
  have gB := tendsto_log_one_add_sq_mul (g := fun z : ℂ => (π : ℂ) ^ 2 * sinhT ((π : ℂ) * z))
    (continuousAt_const.mul hT)
  have gC := tendsto_log_one_add_sq_mul (g := fun _ : ℂ => (1 : ℂ)) continuousAt_const
  have hlim := ((gA.sub gB).sub gC).const_mul (1 / 2 : ℂ)
  have e0 : (1 / 2 : ℂ) * (6 * (π : ℂ) ^ 2 * sinhT2 ((π : ℂ) * 0) - (π : ℂ) ^ 2 * sinhT ((π : ℂ) * 0) - 1) =
      ((cU2 : ℝ) : ℂ) := by
    rw [mul_zero, sinhT2_zero, sinhT_zero]
    unfold cU2
    push_cast
    ring
  rw [e0] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ 0 := hz
  have hA : 6 * sinhT ((π : ℂ) * z) = 1 + z ^ 2 * (6 * (π : ℂ) ^ 2 * sinhT2 ((π : ℂ) * z)) := by
    have := sinhT_sub_sixth ((π : ℂ) * z)
    linear_combination 6 * this
  have hB : sinhQ ((π : ℂ) * z) = 1 + z ^ 2 * ((π : ℂ) ^ 2 * sinhT ((π : ℂ) * z)) := by
    have := sinhQ_sub_one ((π : ℂ) * z)
    linear_combination this
  unfold utilde0
  rw [hA, hB]
  field_simp


lemma tendsto_uR_div_sq : Tendsto (fun t : ℝ => uR t / t ^ 2) (𝓝[≠] 0) (𝓝 cU2) := by
  have hmap : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr (by simp)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_utilde0_div_sq.comp hmap)
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  have hn : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| < 3 / 5 := by
    have := Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 3 / 5 by norm_num)
    exact nhdsWithin_le_nhds (by filter_upwards [this] with t ht using by simpa [Real.dist_eq] using ht)
  filter_upwards [hn] with t ht
  simp only [Function.comp]
  rw [utilde0_ofReal ht]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Fourth-order Taylor expansion of the even smooth function `u_r`:
`|u_r(x) - u_r''(0) x²/2| ≤ C x⁴` for `|x| ≤ 1/2`. -/
lemma uR_taylor4 : ∃ C : ℝ, ∀ x : ℝ, |x| ≤ 1 / 2 → |uR x - uR2 0 / 2 * x ^ 2| ≤ C * x ^ 4 := by
  obtain ⟨C, hC⟩ := uR2_quad
  have hC0 : 0 ≤ C := by
    have := hC (1 / 2) (by norm_num [abs_of_pos])
    have h2 : 0 ≤ |uR2 (1 / 2) - uR2 0| := abs_nonneg _
    nlinarith only [this, h2]
  set c : ℝ := uR2 0 with hc
  refine ⟨C, fun x hx => ?_⟩
  have hg2 : ∀ s : ℝ, |s| ≤ 1 / 2 → |uR1 s - c * s| ≤ C * |s| ^ 3 := by
    intro s hs
    have hd : ∀ t, HasDerivAt (fun s => uR1 s - c * s) (uR2 t - c) t := fun t =>
      (hasDerivAt_uR1 t).sub (by simpa using (hasDerivAt_id t).const_mul c)
    have := abs_sub_le_of_deriv hd (r := |s|) (K := C * s ^ 2) (x := s) (fun y hy => by
      have hy' : |y| ≤ |s| := abs_le.mpr ⟨by linarith [hy.1, neg_abs_le s], hy.2⟩
      calc |uR2 y - c| ≤ C * y ^ 2 := hC y (by linarith)
        _ ≤ C * s ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC0
          rw [← sq_abs y, ← sq_abs s]
          exact pow_le_pow_left₀ (abs_nonneg _) hy' 2) le_rfl
    have e0 : uR1 0 = 0 := by
      have := uR1_neg 0
      simp only [neg_zero] at this
      linarith only [this]
    simp only [e0, mul_zero, sub_zero] at this
    calc |uR1 s - c * s| ≤ C * s ^ 2 * |s| := this
      _ = C * |s| ^ 3 := by rw [← sq_abs s]; ring
  have hd : ∀ t, HasDerivAt (fun s => uR s - c / 2 * s ^ 2) (uR1 t - c * t) t := fun t => by
    have h1 := (hasDerivAt_pow 2 t).const_mul (c / 2)
    exact ((hasDerivAt_uR t).sub h1).congr_deriv (by simp; ring)
  have := abs_sub_le_of_deriv hd (r := |x|) (K := C * |x| ^ 3) (x := x) (fun y hy => by
    have hy' : |y| ≤ |x| := abs_le.mpr ⟨by linarith [hy.1, neg_abs_le x], hy.2⟩
    calc |uR1 y - c * y| ≤ C * |y| ^ 3 := hg2 y (by linarith)
      _ ≤ C * |x| ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy' 3) hC0) le_rfl
  simp only [uR_zero, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  calc |uR x - c / 2 * x ^ 2| ≤ C * |x| ^ 3 * |x| := this
    _ = C * x ^ 4 := by
        have : |x| ^ 4 = x ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
        rw [← this]; ring

/-- **`u_r''(0) = -7π²/60 - 1`.** -/
theorem uR2_zero : uR2 0 = -(7 * π ^ 2 / 60) - 1 := by
  obtain ⟨C, hC⟩ := uR_taylor4
  have h1 := tendsto_uR_div_sq
  have h2 : Tendsto (fun t : ℝ => uR t / t ^ 2) (𝓝[≠] 0) (𝓝 (uR2 0 / 2)) := by
    have hz : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
        (continuous_const.mul (continuous_id.pow 2)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hb : ∀ᶠ t : ℝ in 𝓝[≠] 0, |uR t / t ^ 2 - uR2 0 / 2| ≤ C * t ^ 2 := by
      have hn : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| ≤ 1 / 2 := by
        have := Metric.closedBall_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)
        exact nhdsWithin_le_nhds (by filter_upwards [this] with t ht using by simpa [Real.dist_eq] using ht)
      filter_upwards [hn, self_mem_nhdsWithin] with t ht ht0
      have ht0' : t ≠ 0 := ht0
      have := hC t ht
      have e : uR t / t ^ 2 - uR2 0 / 2 = (uR t - uR2 0 / 2 * t ^ 2) / t ^ 2 := by field_simp
      rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
      calc |uR t - uR2 0 / 2 * t ^ 2| ≤ C * t ^ 4 := this
        _ = C * t ^ 2 * t ^ 2 := by ring
    have : Tendsto (fun t : ℝ => uR t / t ^ 2 - uR2 0 / 2) (𝓝[≠] 0) (𝓝 0) :=
      squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hb) hz
    simpa using this.add_const (uR2 0 / 2)
  have : uR2 0 / 2 = cU2 := tendsto_nhds_unique h2 h1
  unfold cU2 at this
  linarith only [this]

/-- info: 'FormalResearch.SignUncertainty.CtOuter.uR2_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uR2_zero

end FormalResearch.SignUncertainty.CtOuter
