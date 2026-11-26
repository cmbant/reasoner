module

public import FormalResearch.SignUncertainty.UctBumpReflEll
public import FormalResearch.SignUncertainty.UctEnv2
public import FormalResearch.SignUncertainty.CtDualIdBinet
public import FormalResearch.CohnElkies.MellinKernel

/-!
# The amplitude of `K₀(iτ, ξ)` and its `C²` envelope (F2a helper for `uct:bump-symbol`, reflected density)

`mellinK0 c (iτ) ξ = a_c(τ) e^{i c L τ}` with `L = log(π² ξ)` and
`a_c(τ) = (1 - iτ)^{-1/2} e^{B_c(iτ)} e^{i c N(τ)}`, `N(τ) = ∫₀^τ log(tanh(πu/2)/(πu/2)) du` (`mellinK0_imag_eq`).
`kernel_amp_env2`: for `c ≥ 2`, `a_c` has the `Env2` envelope `C_a (1+c)² (1+|τ|)⁴` with `C_a` absolute
(`(1-iτ)^{-1/2}`: constant envelope 1, `e^{B_c(iτ)}`: constant envelope by `ct:binet-decay`, `e^{icN}`: `|N'| ≤ |τ|`, `|N''| ≤ 1`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### `(1 - iτ)^q` -/

lemma norm_cpow_le_one {w : ℂ} (hw : 1 ≤ ‖w‖) {z : ℂ} (hre : z.re ≤ 0) (him : z.im = 0) : ‖w ^ z‖ ≤ 1 := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  rw [Complex.norm_cpow_of_ne_zero hw0]
  simp only [him, mul_zero, Real.exp_zero, div_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos hw hre

lemma one_sub_I_slit (τ : ℝ) : (1 - (τ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  left; simp

lemma one_le_norm_one_sub_I (τ : ℝ) : 1 ≤ ‖(1 - (τ : ℂ) * Complex.I)‖ := by
  have := Complex.re_le_norm (1 - (τ : ℂ) * Complex.I)
  simpa using this

noncomputable def cpowI (q : ℂ) (τ : ℝ) : ℂ := (1 - (τ : ℂ) * Complex.I) ^ q

lemma hasDerivAt_cpowI (q : ℂ) (τ : ℝ) : HasDerivAt (cpowI q) (-(Complex.I * q) * cpowI (q - 1) τ) τ := by
  have hin : HasDerivAt (fun z : ℂ => 1 - z * Complex.I) (-Complex.I) (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).mul_const Complex.I).const_sub 1
  have e1 := hin.cpow_const (c := q) (one_sub_I_slit τ)
  have e2 := e1.comp_ofReal
  refine e2.congr_deriv ?_
  unfold cpowI; ring

lemma deriv_cpowI (q : ℂ) : deriv (cpowI q) = fun τ => -(Complex.I * q) * cpowI (q - 1) τ :=
  funext fun τ => (hasDerivAt_cpowI q τ).deriv

lemma contDiff_cpowI (n : ℕ) : ∀ q : ℂ, ContDiff ℝ n (cpowI q) := by
  induction n with
  | zero =>
    intro q
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_cpowI q τ).continuousAt)
  | succ n ih =>
    intro q
    have h : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (cpowI q) := by
      refine (contDiff_succ_iff_deriv (𝕜 := ℝ)).mpr ⟨fun τ => (hasDerivAt_cpowI q τ).differentiableAt, by simp, ?_⟩
      rw [deriv_cpowI]
      exact contDiff_const.mul (ih (q - 1))
    exact_mod_cast h

lemma env2_cpowI_half : Env2 (cpowI (-(1 / 2 : ℂ))) (fun _ => 1) := by
  refine ⟨contDiff_cpowI 2 _, fun τ => ⟨?_, ?_, ?_⟩⟩
  · exact norm_cpow_le_one (one_le_norm_one_sub_I τ) (by simp) (by simp)
  · rw [deriv_cpowI, norm_mul]
    have h1 : ‖cpowI (-(1 / 2 : ℂ) - 1) τ‖ ≤ 1 := by
      unfold cpowI; exact norm_cpow_le_one (one_le_norm_one_sub_I τ) (by norm_num) (by norm_num)
    have h2 : ‖-(Complex.I * -(1 / 2 : ℂ))‖ ≤ 1 := by simp <;> norm_num
    nlinarith [norm_nonneg (cpowI (-(1 / 2 : ℂ) - 1) τ), norm_nonneg (-(Complex.I * -(1 / 2 : ℂ)))]
  · rw [deriv_cpowI]
    have hfun : deriv (fun τ => -(Complex.I * -(1 / 2 : ℂ)) * cpowI (-(1 / 2 : ℂ) - 1) τ) =
        fun τ => -(Complex.I * -(1 / 2 : ℂ)) * (-(Complex.I * (-(1 / 2 : ℂ) - 1)) * cpowI (-(1 / 2 : ℂ) - 1 - 1) τ) := by
      funext τ
      exact (((hasDerivAt_cpowI (-(1 / 2 : ℂ) - 1) τ).const_mul _)).deriv
    rw [hfun, norm_mul, norm_mul]
    have h1 : ‖cpowI (-(1 / 2 : ℂ) - 1 - 1) τ‖ ≤ 1 := by
      unfold cpowI; exact norm_cpow_le_one (one_le_norm_one_sub_I τ) (by norm_num) (by norm_num)
    have h2 : ‖-(Complex.I * -(1 / 2 : ℂ))‖ = 1 / 2 := by simp <;> norm_num
    have h3 : ‖-(Complex.I * (-(1 / 2 : ℂ) - 1))‖ = 3 / 2 := by simp <;> norm_num
    rw [h2, h3]
    nlinarith [norm_nonneg (cpowI (-(1 / 2 : ℂ) - 1 - 1) τ)]

/-! ### `e^{B_c(iτ)}` -/

lemma contDiff_real_line {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hmem : ∀ τ : ℝ, (τ : ℂ) ∈ U) : ContDiff ℝ 2 (fun τ : ℝ => F (τ : ℂ)) := by
  have hFc : ContDiffOn ℝ 2 F U := ((hF.contDiffOn hU).restrict_scalars ℝ).of_le (by exact_mod_cast le_top)
  exact hFc.comp_contDiff Complex.ofRealCLM.contDiff hmem

lemma norm_binetDiff_le (c : ℝ) (hc : 2 ≤ c) (τ : ℝ) :
    ‖FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))‖ ≤ 1 := by
  unfold FormalResearch.Asymptotics.binetDiff
  have hc0 : 0 < c := by linarith
  have h1 := FormalResearch.SignUncertainty.BinetDecay.binetRem_iteratedDeriv_decay 0
    (w := (c : ℂ) * (1 - Complex.I * (τ : ℂ))) (by simpa using hc0)
  have h2 := FormalResearch.SignUncertainty.BinetDecay.binetRem_iteratedDeriv_decay 0 (w := (c : ℂ)) (by simpa using hc0)
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_one] at h1 h2
  have hw1 : c ≤ ‖(c : ℂ) * (1 - Complex.I * (τ : ℂ))‖ := by
    have := Complex.re_le_norm ((c : ℂ) * (1 - Complex.I * (τ : ℂ)))
    simpa using this
  have hw2 : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc0.le]
  have hnw : 0 < ‖(c : ℂ) * (1 - Complex.I * (τ : ℂ))‖ := lt_of_lt_of_le hc0 hw1
  have e1 : (2 : ℝ) ^ 2 / (8 * ‖(c : ℂ) * (1 - Complex.I * (τ : ℂ))‖) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have e2 : (2 : ℝ) ^ 2 / (8 * ‖(c : ℂ)‖) ≤ 1 / 2 := by
    rw [hw2, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  exact (norm_sub_le _ _).trans (by linarith)

theorem env2_binet_exp : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 2 ≤ c →
    Env2 (fun τ : ℝ => Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)))) (fun _ => K) := by
  obtain ⟨⟨C1, h1⟩, hdiff, -⟩ : (∃ C : ℝ, ∀ c : ℝ, 2 ≤ c → ∀ τ : ℝ,
        ‖iteratedDeriv 1 (fun τ : ℝ => FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) τ‖ ≤ C / (c * (1 + |τ|) ^ (1 + 1))) ∧
      (∀ c : ℝ, 2 ≤ c → DifferentiableOn ℂ (fun τ : ℂ => FormalResearch.Asymptotics.binetDiff c (Complex.I * τ)) {τ : ℂ | -1 < τ.im}) ∧ True :=
    ⟨(ct_dual_id_part1.1 1 le_rfl), ct_dual_id_part1.2.1, trivial⟩
  obtain ⟨C2, h2⟩ := ct_dual_id_part1.1 2 (by norm_num)
  set P : ℝ := 1 + |C1| + |C2| with hP
  have hP0 : 0 ≤ P := by positivity
  refine ⟨Real.exp 1 * (1 + 2 * P + P ^ 2), by positivity, fun c hc => ?_⟩
  have hc0 : 0 < c := by linarith
  set f : ℝ → ℂ := fun τ => FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)) with hf
  have hcd : ContDiff ℝ 2 f :=
    contDiff_real_line (F := fun τ : ℂ => FormalResearch.Asymptotics.binetDiff c (Complex.I * τ))
      (isOpen_lt continuous_const Complex.continuous_im) (hdiff c hc) (fun τ => by simp)
  have hG : Env2 (fun τ => -f τ) (fun _ => P) := by
    have hd1 : deriv (fun τ => -f τ) = fun τ => -deriv f τ := by
      funext τ; exact (deriv.neg)
    have hd2 : deriv (deriv (fun τ => -f τ)) = fun τ => -deriv (deriv f) τ := by
      rw [hd1]; funext τ; exact deriv.neg
    refine ⟨hcd.neg, fun τ => ⟨?_, ?_, ?_⟩⟩
    · rw [norm_neg]; exact (norm_binetDiff_le c hc τ).trans (by linarith [abs_nonneg C1, abs_nonneg C2])
    · rw [hd1, norm_neg]
      have := h1 c hc τ
      rw [iteratedDeriv_one] at this
      refine this.trans ?_
      have hx : 1 ≤ (1 + |τ|) ^ (1 + 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
      calc C1 / (c * (1 + |τ|) ^ (1 + 1)) ≤ |C1| / (c * (1 + |τ|) ^ (1 + 1)) := by gcongr; exact le_abs_self _
        _ ≤ |C1| / 2 := by
            apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num); nlinarith
        _ ≤ P := by rw [hP]; linarith [abs_nonneg C1, abs_nonneg C2]
    · rw [hd2, norm_neg]
      have := h2 c hc τ
      rw [show iteratedDeriv 2 f τ = deriv (deriv f) τ by rw [iteratedDeriv_succ, iteratedDeriv_one]] at this
      refine this.trans ?_
      have hx : 1 ≤ (1 + |τ|) ^ (2 + 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
      calc C2 / (c * (1 + |τ|) ^ (2 + 1)) ≤ |C2| / (c * (1 + |τ|) ^ (2 + 1)) := by gcongr; exact le_abs_self _
        _ ≤ |C2| / 2 := by
            apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num); nlinarith
        _ ≤ P := by rw [hP]; linarith [abs_nonneg C1, abs_nonneg C2]
  have hb : ∀ τ, ‖Complex.exp (-(-f τ))‖ ≤ (fun _ => Real.exp 1) τ := fun τ => by
    rw [neg_neg, Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (norm_binetDiff_le c hc τ))
  have := Env2.exp_neg hG (fun _ => Real.exp 1) hb
  simpa only [neg_neg] using this

/-! ### The phase `e^{i c N(τ)}` -/

lemma env2_phase (c : ℝ) (hc : 0 ≤ c) :
    Env2 (fun τ : ℝ => Complex.exp (Complex.I * ((c * ellN τ : ℝ) : ℂ)))
      (fun τ => (1 + 4 * (c * (1 + |τ|) ^ 2)) ^ 2) := by
  set f : ℝ → ℝ := fun τ => c * ellN τ with hf
  have hfc : ContDiff ℝ 2 f := contDiff_const.mul (contDiff_ellN.of_le (by norm_num))
  have hfd : deriv f = fun τ => c * ellFun τ := by
    funext τ
    exact (((hasDerivAt_ellN τ).const_mul c)).deriv
  have hfd2 : deriv (deriv f) = fun τ => c * deriv ellFun τ := by
    rw [hfd]; funext τ
    have hd : Differentiable ℝ ellFun := contDiff_ellFun.differentiable (by simp)
    exact ((hd τ).hasDerivAt.const_mul c).deriv
  have hx : ∀ τ : ℝ, 1 ≤ (1 + |τ|) ^ 2 := fun τ => one_le_pow₀ (by linarith [abs_nonneg τ])
  have hE := Env2.ofReal hfc (fun τ => c * (1 + |τ|) ^ 2)
    (fun τ => by
      show |c * ellN τ| ≤ _
      rw [abs_mul, abs_of_nonneg hc]
      have := abs_ellN_le τ
      have h2 : τ ^ 2 ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ, sq_abs τ]
      exact mul_le_mul_of_nonneg_left (this.trans h2) hc)
    (fun τ => by
      rw [hfd]; show |c * ellFun τ| ≤ _
      rw [abs_mul, abs_of_nonneg hc]
      have := abs_ellFun_le τ
      have h2 : |τ| ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ]
      exact mul_le_mul_of_nonneg_left (this.trans h2) hc)
    (fun τ => by
      rw [hfd2]; show |c * deriv ellFun τ| ≤ _
      rw [abs_mul, abs_of_nonneg hc]
      exact mul_le_mul (le_refl c) ((deriv_ellFun_bound τ).trans (hx τ)) (abs_nonneg _) hc)
  have hG := hE.const_mul (-Complex.I)
  have hb : ∀ τ, ‖Complex.exp (-(-Complex.I * ((f τ : ℝ) : ℂ)))‖ ≤ (fun _ => (1 : ℝ)) τ := fun τ => by
    have : -(-Complex.I * ((f τ : ℝ) : ℂ)) = Complex.I * ((f τ : ℝ) : ℂ) := by ring
    rw [this, Complex.norm_exp_I_mul_ofReal]
  have := Env2.exp_neg hG (fun _ => 1) hb
  have e : ∀ τ : ℝ, -(-Complex.I * ((f τ : ℝ) : ℂ)) = Complex.I * ((c * ellN τ : ℝ) : ℂ) := fun τ => by
    simp only [hf]; ring
  simp only [e] at this
  refine this.mono fun τ => ?_
  simp only [norm_neg, Complex.norm_I]
  nlinarith [mul_nonneg hc (sq_nonneg (1 + |τ|))]

/-! ### The amplitude of `K₀(iτ, ξ)` -/

noncomputable def kernelAmp (c : ℝ) (τ : ℝ) : ℂ :=
  cpowI (-(1 / 2 : ℂ)) τ * Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
    Complex.exp (Complex.I * ((c * ellN τ : ℝ) : ℂ))

theorem mellinK0_imag_eq {c ξ : ℝ} (hξ : 0 < ξ) (τ : ℝ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ =
      kernelAmp c τ * Complex.exp (Complex.I * ((c * Real.log (Real.pi ^ 2 * ξ) * τ : ℝ) : ℂ)) := by
  have hlog : Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) = ((Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  unfold mellinK0 mellinPhi kernelAmp
  rw [stripS0Tilde_imag, hlog, mul_comm (τ : ℂ) Complex.I]
  have hN : (∫ u in (0 : ℝ)..τ, Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2))) = ellN τ := rfl
  rw [hN]
  have : Complex.exp ((c : ℂ) * (Complex.I * (ellN τ : ℂ) + Complex.I * (τ : ℂ) * ((Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((c * ellN τ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((c * Real.log (Real.pi ^ 2 * ξ) * τ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]
  unfold cpowI
  ring

theorem kernel_amp_env2 : ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ c : ℝ, 2 ≤ c →
    Env2 (kernelAmp c) (fun τ => Ca * (1 + c) ^ 2 * (1 + |τ|) ^ 4) := by
  obtain ⟨K, hK0, hK⟩ := env2_binet_exp
  refine ⟨256 * K, by positivity, fun c hc => ?_⟩
  have hc0 : 0 ≤ c := by linarith
  have h1 := env2_cpowI_half.mul (hK c hc)
  have h2 := h1.mul (env2_phase c hc0)
  refine (h2.mono fun τ => ?_)
  have hx : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have hP : 1 + 4 * (c * (1 + |τ|) ^ 2) ≤ 4 * (1 + c) * (1 + |τ|) ^ 2 := by
    have : 1 ≤ (1 + |τ|) ^ 2 := one_le_pow₀ hx
    nlinarith
  have hP0 : 0 ≤ 1 + 4 * (c * (1 + |τ|) ^ 2) := by positivity
  have hsq : (1 + 4 * (c * (1 + |τ|) ^ 2)) ^ 2 ≤ (4 * (1 + c) * (1 + |τ|) ^ 2) ^ 2 := pow_le_pow_left₀ hP0 hP 2
  show 4 * (4 * 1 * K) * (1 + 4 * (c * (1 + |τ|) ^ 2)) ^ 2 ≤ 256 * K * (1 + c) ^ 2 * (1 + |τ|) ^ 4
  have : (4 * (1 + c) * (1 + |τ|) ^ 2) ^ 2 = 16 * (1 + c) ^ 2 * (1 + |τ|) ^ 4 := by ring
  rw [this] at hsq
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 16 * K)]

/-- info: 'FormalResearch.SignUncertainty.kernel_amp_env2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_amp_env2

/-- info: 'FormalResearch.SignUncertainty.mellinK0_imag_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinK0_imag_eq

end FormalResearch.SignUncertainty
