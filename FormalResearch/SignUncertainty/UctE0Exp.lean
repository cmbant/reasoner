module

public import FormalResearch.SignUncertainty.UctWExp
public import FormalResearch.SignUncertainty.UctBumpReflAmp
public import FormalResearch.SignUncertainty.UctBumpReflEll
public import FormalResearch.SignUncertainty.BinetSmall

/-!
# The weighted expansion of the kernel amplitude `E₀ = kernelAmp - 1` (F2a, `uct:bump-weighted`)

With `h = c^{-1/2}`, `τ = h v`, `c = h⁻²`: `kernelAmp c τ = (1-iτ)^{-1/2} e^{B_c(iτ)} e^{icN(τ)}` is, for `1 ≤ N ≤ 7`, a weighted expansion
`1 + ∑_{1 ≤ n < N} h^n p_n(v) + O((h(1+|v|)^3)^N)` with `deg p_n ≤ 3n` (`WExp`); `E0_wexp` is the statement for `E₀`.
Ingredients: `(1-iτ)^{-1/2}` smooth (`WExp.of_smooth`); `B_c(iτ) = (i/12) h³ v (1-ihv)^{-1} + O(h⁷|v|)` (`binetDiff_small`);
`cN(hv) = h^{-2} N(hv)` with `N = O(τ³)` (`WExp.of_smooth_inv_sq`); `WExp.exp` and `WExp.mul`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

lemma contDiff_cpowI_top (q : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (cpowI q) :=
  contDiff_infty.mpr fun n => contDiff_cpowI n q

lemma deriv_ellFun_zero : deriv ellFun 0 = 0 := by
  have h1 : (fun x : ℝ => ellFun (-x)) = ellFun := funext ellFun_even
  have h2 : deriv (fun x : ℝ => ellFun (-x)) 0 = -deriv ellFun (-0) := deriv_comp_neg ellFun 0
  rw [h1] at h2
  simp only [neg_zero] at h2
  linarith

lemma ellN_zero : ellN 0 = 0 := by simp [ellN]

lemma contDiff_ellN_top : ContDiff ℝ (⊤ : ℕ∞) ellN := by
  refine contDiff_infty_iff_deriv.mpr ⟨fun τ => (hasDerivAt_ellN τ).differentiableAt, ?_⟩
  rw [deriv_ellN]
  exact contDiff_ellFun

/-- `g₃(z) = i N(z)` vanishes to order `3` at `0`. -/
noncomputable def ellG3 (z : ℝ) : ℂ := Complex.I * ((ellN z : ℝ) : ℂ)

lemma contDiff_ellG3 : ContDiff ℝ (⊤ : ℕ∞) ellG3 :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_ellN_top)

lemma ellG3_iteratedDeriv_zero : ∀ l < 3, iteratedDeriv l ellG3 0 = 0 := by
  have hd1 : deriv ellG3 = fun z => Complex.I * ((ellFun z : ℝ) : ℂ) := by
    funext z
    have : HasDerivAt ellG3 (Complex.I * ((ellFun z : ℝ) : ℂ)) z := by
      have h := ((hasDerivAt_ellN z).ofReal_comp).const_mul Complex.I
      exact h
    exact this.deriv
  intro l hl
  interval_cases l
  · simp [ellG3, ellN_zero]
  · rw [iteratedDeriv_one, hd1]; simp [ellFun_zero]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hd1]
    have : HasDerivAt (fun z : ℝ => Complex.I * ((ellFun z : ℝ) : ℂ)) (Complex.I * ((deriv ellFun 0 : ℝ) : ℂ)) 0 := by
      have hd : HasDerivAt ellFun (deriv ellFun 0) 0 :=
        (contDiff_ellFun.differentiable (by simp) 0).hasDerivAt
      exact hd.ofReal_comp.const_mul Complex.I
    rw [this.deriv, deriv_ellFun_zero]; simp

lemma cpowI_zero (q : ℂ) : cpowI q 0 = 1 := by simp [cpowI]

lemma cpowI_neg_one (τ : ℝ) : cpowI (-1) τ = (1 - (τ : ℂ) * Complex.I)⁻¹ := by
  simp [cpowI, Complex.cpow_neg_one]

/-- The Binet factor: `B_c(i h v) = (i/12) h³ v (1-ihv)⁻¹ + O(x^N)` (`N ≤ 7`). -/
lemma binet_wexp {N : ℕ} (hN : 1 ≤ N) (hN7 : N ≤ 7) :
    WExp N 1 0 (fun h v => binetDiff ((h ^ 2)⁻¹) (Complex.I * ((h * v : ℝ) : ℂ))) := by
  have hm : WExp N 1 0 (fun h v => (Complex.I / 12) * (h : ℂ) ^ 3 * (v : ℂ) ^ 1) :=
    WExp.wmono_fun (by norm_num) (fun h => by omega) (by norm_num) _
  have hp : WExp N 1 (cpowI (-1) 0) (fun h v => cpowI (-1) (h * v)) :=
    WExp.of_smooth (contDiff_cpowI_top _) hN one_pos
  have hmain := hm.mul (by norm_num) hp
  rw [zero_mul] at hmain
  have hrem : WExp N 1 0 (fun h v => binetDiff ((h ^ 2)⁻¹) (Complex.I * ((h * v : ℝ) : ℂ)) -
      (Complex.I / 12) * (h : ℂ) ^ 3 * (v : ℂ) ^ 1 * cpowI (-1) (h * v)) := by
    refine WExp.bound (C := 8) (fun h v hr => ?_) (by norm_num)
    have hh := hr.1
    have hc : 0 < (h ^ 2)⁻¹ := by positivity
    have := BinetDecay.binetDiff_small hc (h * v)
    have e : Complex.I * ((h * v : ℝ) : ℂ) / (12 * (((h ^ 2)⁻¹ : ℝ) : ℂ) * (1 - Complex.I * ((h * v : ℝ) : ℂ))) =
        (Complex.I / 12) * (h : ℂ) ^ 3 * (v : ℂ) ^ 1 * cpowI (-1) (h * v) := by
      rw [cpowI_neg_one]
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have h1 : (1 - ((h * v : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp at this
      have h2 : (1 - Complex.I * ((h * v : ℝ) : ℂ)) ≠ 0 := by
        intro h0; apply h1; rw [← h0]; ring
      push_cast at h1 h2 ⊢
      field_simp
    rw [e] at this
    refine this.trans ?_
    have h7 : 8 * |h * v| / ((h ^ 2)⁻¹) ^ 3 = 8 * (h ^ 7 * |v| ^ 1) := by
      rw [abs_mul, abs_of_pos hh]; field_simp
    rw [h7]
    have hx0 : 0 ≤ wx h v := wx_nonneg hh
    have hx1 : wx h v ≤ 1 := hr.wx_le
    have := WExp.pow_abs_le_wx v hh 1 7 (by norm_num)
    have h8 : wx h v ^ 7 ≤ wx h v ^ N := pow_le_pow_of_le_one hx0 hx1 hN7
    nlinarith
  have := hmain.add hrem
  rw [add_zero] at this
  exact this.congr fun h v _ => by ring

/-- **Weighted expansion of the kernel amplitude** (`1 ≤ N ≤ 7`, region `h (1+|v|)³ ≤ 1`, `c = h⁻²`, `τ = h v`). -/
theorem kernelAmp_wexp {N : ℕ} (hN : 1 ≤ N) (hN7 : N ≤ 7) :
    WExp N 1 1 (fun h v => kernelAmp ((h ^ 2)⁻¹) (h * v)) := by
  have h1 : WExp N 1 (cpowI (-(1 / 2 : ℂ)) 0) (fun h v => cpowI (-(1 / 2 : ℂ)) (h * v)) :=
    WExp.of_smooth (contDiff_cpowI_top _) hN one_pos
  rw [cpowI_zero] at h1
  have h3 : WExp N 1 0 (fun h v => (((h ^ 2)⁻¹ : ℝ) : ℂ) * ellG3 (h * v)) :=
    WExp.of_smooth_inv_sq contDiff_ellG3 hN one_pos ellG3_iteratedDeriv_zero
  have hE2 := WExp.exp (by norm_num) hN (binet_wexp hN hN7)
  have hE3 := WExp.exp (by norm_num) hN h3
  have hprod := (h1.mul (by norm_num) hE2).mul (by norm_num) hE3
  rw [one_mul, one_mul] at hprod
  refine hprod.congr fun h v _ => ?_
  unfold kernelAmp
  congr 2
  unfold ellG3
  push_cast
  ring

/-- `E₀ = kernelAmp - 1` is a weighted expansion with zero constant term. -/
theorem E0_wexp {N : ℕ} (hN : 1 ≤ N) (hN7 : N ≤ 7) :
    WExp N 1 0 (fun h v => kernelAmp ((h ^ 2)⁻¹) (h * v) - 1) := by
  have := (kernelAmp_wexp hN hN7).add (WExp.const (N := N) (k0 := 1) (-1 : ℂ))
  rw [show (1 : ℂ) + -1 = 0 by norm_num] at this
  exact this.congr fun h v _ => by ring

/-- info: 'FormalResearch.SignUncertainty.kernelAmp_wexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelAmp_wexp

/-- info: 'FormalResearch.SignUncertainty.E0_wexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E0_wexp

end FormalResearch.SignUncertainty
