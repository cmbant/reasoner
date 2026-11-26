/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymbolsMono
public import FormalResearch.SignUncertainty.CtAiryId

/-!
# Lemma `fct:inner-symbols` (FCT.5b) (a), closed form `𝒮[1] = G_0`: reduction to the initial values at `û = 0`

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (a), last sentence.  Proved here (given `FctInnerSymbolsMono`):

* the limiting ODE `½ g_0 - iû g_1 - (i/4) g_3 = 0` for `g_k = 𝒮[u^k]` (`gk_ode`: `fctSEps_ode` and `ε 𝒮_ε[u²] → 0`, by the uniform bound `gk_bound`);
* with `g_k = i^k ∂^k g_0` this is `g_0''' = 4û g_0' + 2 g_0` (the first-order system `P_0 = g_0`, `P_1 = -i g_1`, `P_2 = -g_2`);
* `fctG0 = -2√π · conj(G_0)` with `G_0 = CtAiry.G0 = HH0 = -π(Ai² + i Ai Bi)` (`CtAiryId`), so `fctG0` solves the same system (`conj` commutes with `d/dû` on `ℝ`);
* uniqueness (`CtAiry.ode3_eq_zero`): `𝒮[1] = fctG0` as soon as the three initial values agree.

Named input (strictly smaller than `FctInnerSymbolsG0`): `FctInnerSymbolsG0Init`, the three initial values at `û = 0`.
Proved: `fctInnerSymbolsG0_of_init : FctInnerSymbolsG0Init → FctInnerSymbolsG0`.

Class: proved (reduction); the initial values are a named input.
-/
@[expose] public section
open Set Filter Topology MeasureTheory
open scoped Real ContDiff Interval

namespace FormalResearch.SignUncertainty

/-- **Initial values of `fct:inner-symbols` (a), closed form** (named input).  With `c = -2√π` and `G_j = CtAiry.Gj` (`G_j(0)` are the Gamma values of `CtAiry.gI_zero`),
`𝒮[u^j](0) = i^j · c · conj(G_j(0))`, `j = 0, 1, 2`; equivalently `𝒮[u^j](0) = i^j G_0^{(j)}(0)` with the paper's `G_0^{(j)}(0) = 12^{(j+1/2)/3}/3 · Γ((j+1/2)/3) e^{-iπ/4 - iπj/2 - iπ(j+1/2)/6}`.
(Paper proof: rotate the contour of the regularised integral by `arg u = -π/6` and evaluate the Gamma integrals.) -/
def FctInnerSymbolsG0Init : Prop :=
  fctS 0 (fun u => (u : ℂ) ^ 0) = (-(2 * ((√π : ℝ) : ℂ))) * star (CtAiry.G0 0) ∧
  fctS 0 (fun u => (u : ℂ) ^ 1) = Complex.I * ((-(2 * ((√π : ℝ) : ℂ))) * star (CtAiry.G1 0)) ∧
  fctS 0 (fun u => (u : ℂ) ^ 2) = Complex.I ^ 2 * ((-(2 * ((√π : ℝ) : ℂ))) * star (CtAiry.G2 0))

namespace FctSymA

/-- Limiting ODE identity `½ g_0 - iû g_1 - (i/4) g_3 = 0`. -/
lemma gk_ode (û : ℝ) :
    (1 / 2 : ℂ) * gk û 0 - Complex.I * û * gk û 1 - (Complex.I / 4) * gk û 3 = 0 := by
  obtain ⟨C, hC0, hC⟩ := gk_bound 2 (|û| + 1) (by positivity)
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hlim : Tendsto (fun ε : ℝ => (1 / 2 : ℂ) * fctSEps û ε (fun u => (u : ℂ) ^ 0) -
      Complex.I * û * fctSEps û ε (fun u => (u : ℂ) ^ 1) - (Complex.I / 4) * fctSEps û ε (fun u => (u : ℂ) ^ 3)
        - 2 * (ε : ℂ) * fctSEps û ε (fun u => (u : ℂ) ^ 2)) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℂ) * gk û 0 - Complex.I * û * gk û 1 - (Complex.I / 4) * gk û 3 - 0)) := by
    refine ((((gk_limit 0 û).const_mul _).sub ((gk_limit 1 û).const_mul _)).sub ((gk_limit 3 û).const_mul _)).sub ?_
    have h0 : Tendsto (fun ε : ℝ => (2 * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => (2 * (ε : ℂ))) (𝓝 0) (𝓝 (2 * ((0 : ℝ) : ℂ))) :=
        (continuous_const.mul Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hb : Tendsto (fun ε : ℝ => (2 * (ε : ℂ)) * fctSEps û ε (fun u => (u : ℂ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun ε : ℝ => 2 * ε * C) ?_ ?_
      · filter_upwards [hmem] with ε hε
        rw [norm_mul]
        have h2 : ‖(2 * (ε : ℂ))‖ = 2 * ε := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.1.le]; simp
        rw [h2]
        exact mul_le_mul_of_nonneg_left ((hC û (by linarith [abs_nonneg û])).2 ε hε) (by linarith [hε.1])
      · have : Tendsto (fun ε : ℝ => 2 * ε * C) (𝓝 0) (𝓝 (2 * 0 * C)) :=
          ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
    simpa [mul_assoc] using hb
  have hzero : Tendsto (fun ε : ℝ => (1 / 2 : ℂ) * fctSEps û ε (fun u => (u : ℂ) ^ 0) -
      Complex.I * û * fctSEps û ε (fun u => (u : ℂ) ^ 1) - (Complex.I / 4) * fctSEps û ε (fun u => (u : ℂ) ^ 3)
        - 2 * (ε : ℂ) * fctSEps û ε (fun u => (u : ℂ) ^ 2)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (by filter_upwards [hmem] with ε hε; exact (fctSEps_ode hε.1 û).symm)
  simpa using tendsto_nhds_unique hlim hzero

/-- `fctG0 = -2√π · conj(CtAiry.G0)`. -/
lemma fctG0_eq (u : ℝ) : fctG0 u = (-(2 * ((√π : ℝ) : ℂ))) * star (CtAiry.G0 u) := by
  rw [(CtAiry.G_eq_HH u).1]
  unfold fctG0 CtAiry.HH0
  have h : π ^ (3 / 2 : ℝ) = π * √π := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' Real.pi_pos.le (by norm_num)]; norm_num
  rw [h]
  simp only [star_mul', star_neg, star_add, star_pow, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring


end FctSymA

/-- **Reduction of `fct:inner-symbols` (a), closed form:** the initial values at `û = 0` imply `𝒮[1] = G_0`. -/
theorem fctInnerSymbolsG0_of_init (h : FctInnerSymbolsG0Init) : FctInnerSymbolsG0 := by
  obtain ⟨i0, i1, i2⟩ := h
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = -(2 * ((√π : ℝ) : ℂ)) := ⟨_, rfl⟩
  rw [← hc] at i0 i1 i2
  have fG : ∀ u : ℝ, fctG0 u = c * star (CtAiry.G0 u) := fun u => by rw [hc]; exact FctSymA.fctG0_eq u
  have hQ0 : ∀ u : ℝ, HasDerivAt fctG0 (c * star (CtAiry.G1 u)) u := by
    intro u
    have : fctG0 = fun u => c * star (CtAiry.G0 u) := funext fG
    rw [this]
    exact ((CtAiry.hasDerivAt_G0 u).star).const_mul c
  have hQ1 : ∀ u : ℝ, HasDerivAt (fun u => c * star (CtAiry.G1 u)) (c * star (CtAiry.G2 u)) u := fun u =>
    ((CtAiry.hasDerivAt_G1 u).star).const_mul c
  have hQ2 : ∀ u : ℝ, HasDerivAt (fun u => c * star (CtAiry.G2 u))
      (4 * (u : ℂ) * (c * star (CtAiry.G1 u)) + 2 * fctG0 u) u := by
    intro u
    have := ((CtAiry.hasDerivAt_G2 u).star).const_mul c
    refine this.congr_deriv ?_
    have hu : star ((u : ℂ)) = (u : ℂ) := Complex.conj_ofReal u
    rw [fG u]
    simp only [star_add, star_mul', star_ofNat, hu]
    ring
  have hP0 : ∀ u : ℝ, HasDerivAt (fun w => FctSymA.gk w 0) (-Complex.I * FctSymA.gk u 1) u := fun u => FctSymA.hasDerivAt_gk 0 u
  have hP1 : ∀ u : ℝ, HasDerivAt (fun w => -Complex.I * FctSymA.gk w 1) (-FctSymA.gk u 2) u := by
    intro u
    refine ((FctSymA.hasDerivAt_gk 1 u).const_mul (-Complex.I)).congr_deriv ?_
    ring_nf; simp [Complex.I_sq]
  have hP2 : ∀ u : ℝ, HasDerivAt (fun w => -FctSymA.gk w 2) (Complex.I * FctSymA.gk u 3) u := by
    intro u
    refine (FctSymA.hasDerivAt_gk 2 u).neg.congr_deriv ?_
    ring
  have key := CtAiry.ode3_eq_zero
    (D0 := fun w => FctSymA.gk w 0 - fctG0 w) (D1 := fun w => -Complex.I * FctSymA.gk w 1 - c * star (CtAiry.G1 w))
    (D2 := fun w => -FctSymA.gk w 2 - c * star (CtAiry.G2 w))
    (fun u => by
      refine ((hP0 u).sub (hQ0 u)).congr_deriv ?_
      ring)
    (fun u => by
      refine ((hP1 u).sub (hQ1 u)).congr_deriv ?_
      ring)
    (fun u => by
      refine ((hP2 u).sub (hQ2 u)).congr_deriv ?_
      have := FctSymA.gk_ode u
      linear_combination (-4 : ℂ) * this)
    (by
      have i0' : FctSymA.gk 0 0 = c * star (CtAiry.G0 0) := i0
      have e := fG 0
      show FctSymA.gk 0 0 - fctG0 0 = 0
      linear_combination i0' - e)
    (by
      have i1' : FctSymA.gk 0 1 = Complex.I * (c * star (CtAiry.G1 0)) := i1
      show -Complex.I * FctSymA.gk 0 1 - c * star (CtAiry.G1 0) = 0
      linear_combination (-Complex.I) * i1' - (c * star (CtAiry.G1 0)) * Complex.I_sq)
    (by
      have i2' : FctSymA.gk 0 2 = Complex.I ^ 2 * (c * star (CtAiry.G2 0)) := i2
      show -FctSymA.gk 0 2 - c * star (CtAiry.G2 0) = 0
      linear_combination (-1 : ℂ) * i2' - (c * star (CtAiry.G2 0)) * Complex.I_sq)
  intro û
  have e : fctS û (fun _ => (1 : ℂ)) = fctG0 û := by
    have := key û
    simp only [FctSymA.gk] at this
    simpa [sub_eq_zero] using this
  have hl := FctSymA.gk_limit 0 û
  simp only [FctSymA.gk] at hl
  simp only [pow_zero] at hl
  rw [← e]
  exact hl

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsG0_of_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsG0_of_init

end FormalResearch.SignUncertainty
