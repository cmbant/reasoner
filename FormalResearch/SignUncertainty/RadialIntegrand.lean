module

public import FormalResearch.SignUncertainty.RadialXiMain
public import FormalResearch.SignUncertainty.RadialDomination

/-!
# The integrand `K_c W_c` on `Re w = 1` (`lem:radial-compactness`, Step 3)

`K_c(w,s) W_c(w) = Γ(c(1-ζ)) Γ(c)^{-1} (2π c ξ)^{c ζ} M̃_f(c(1-ζ))`, `ζ = ε_c w` (`radialK_mul_radialW`): the
exponentials `e^{±cℋ}` cancel.  Hence `v ↦ K_c(1+iv,s) W_c(1+iv)` is continuous (`continuous_radialKW`) and
bounded by the domination of `radialK_norm_le` times `‖W_c‖` (`radialKW_norm_le`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma radialK_mul_radialW {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) {s : ℝ} (hξ : 0 < radialXi c s) {w : ℂ}
    (hw0 : 0 ≤ w.re) (hw1 : radialEps c * w.re < 1) :
    radialK c w s * radialW c f w =
      Complex.Gamma ((c : ℂ) * (1 - (radialEps c : ℂ) * w)) / Complex.Gamma (c : ℂ) *
        (2 * (Real.pi : ℂ) * (c : ℂ) * (radialXi c s : ℂ)) ^ ((c : ℂ) * ((radialEps c : ℂ) * w)) *
          mellinStrip f ((c : ℂ) * (1 - (radialEps c : ℂ) * w)) := by
  have he0 := radialEps_pos hc
  set ζ : ℂ := (radialEps c : ℂ) * w with hζ
  have hζre : ζ.re = radialEps c * w.re := by simp [hζ]
  have hkern := mellin_strip_kernel_eq (c := c) (ξ := radialXi c s) hc hξ (ζ := ζ)
    (by rw [hζre]; positivity) (by rw [hζre]; exact hw1)
  have hH : hInt ζ = stripH ζ := hInt_eq_stripH (by rw [hζre]; positivity) (by rw [hζre]; exact hw1)
  have hK : radialK c w s = mellinK0 c ζ (radialXi c s) := rfl
  have hW : radialW c f w = Complex.exp (-((c : ℂ) * stripH ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ)) := by
    show Complex.exp (-((c : ℂ) * hInt ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ)) = _
    rw [hH]
  rw [hK, hW, ← hkern]
  have hexp : Complex.exp ((c : ℂ) * stripH ζ) * Complex.exp (-((c : ℂ) * stripH ζ)) = 1 := by
    rw [← Complex.exp_add]; simp
  calc _ = Complex.Gamma ((c : ℂ) * (1 - ζ)) / Complex.Gamma (c : ℂ) *
        (2 * (Real.pi : ℂ) * (c : ℂ) * (radialXi c s : ℂ)) ^ ((c : ℂ) * ζ) *
        (Complex.exp ((c : ℂ) * stripH ζ) * Complex.exp (-((c : ℂ) * stripH ζ))) *
        mellinStrip f ((c : ℂ) * (1 - ζ)) := by ring
    _ = _ := by rw [hexp]; ring

lemma continuous_radialKW {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {s : ℝ}
    (hξ : 0 < radialXi c s) :
    Continuous fun v : ℝ => radialK c (1 + (v : ℂ) * Complex.I) s * radialW c f (1 + (v : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have he0 := radialEps_pos hc0
  have he1 := radialEps_lt_one (by linarith : 1 < c)
  have hform : (fun v : ℝ => radialK c (1 + (v : ℂ) * Complex.I) s * radialW c f (1 + (v : ℂ) * Complex.I)) =
      fun v : ℝ => Complex.Gamma ((c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) /
        Complex.Gamma (c : ℂ) *
        (2 * (Real.pi : ℂ) * (c : ℂ) * (radialXi c s : ℂ)) ^ ((c : ℂ) * ((radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) *
          mellinStrip f ((c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) := by
    funext v
    exact radialK_mul_radialW hc0 f hξ (by simp) (by simpa using he1)
  rw [hform]
  have hz : Continuous fun v : ℝ => (c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I)) := by
    fun_prop
  have hzre : ∀ v : ℝ, ((c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))).re = c * (1 - radialEps c) := by
    intro v; simp
  have hG : Continuous fun v : ℝ => Complex.Gamma ((c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) := by
    rw [continuous_iff_continuousAt]
    intro v
    have hre : 0 < ((c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))).re := by
      rw [hzre]; exact mul_pos hc0 (by linarith)
    have hne : ∀ m : ℕ, ((c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      rw [hzre] at this
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_pos hc0 (by linarith : 0 < 1 - radialEps c)]
    exact ContinuousAt.comp (g := Complex.Gamma)
      (f := fun v : ℝ => (c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) (x := v)
      (Complex.differentiableAt_Gamma _ hne).continuousAt hz.continuousAt
  have hpow : Continuous fun v : ℝ => (2 * (Real.pi : ℂ) * (c : ℂ) * (radialXi c s : ℂ)) ^
      ((c : ℂ) * ((radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) := by
    refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
    have : (2 * (Real.pi : ℂ) * (c : ℂ) * (radialXi c s : ℂ)) = ((2 * Real.pi * c * radialXi c s : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]; exact_mod_cast (by positivity : (2 * Real.pi * c * radialXi c s) ≠ 0)
  have hM : Continuous fun v : ℝ => mellinStrip f ((c : ℂ) * (1 - (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I))) := by
    refine ((differentiableOn_mellinStrip hc0 hf).continuousOn).comp_continuous hz (fun v => ?_)
    refine ⟨?_, ?_⟩ <;> simp only [hzre] <;> nlinarith [mul_pos hc0 he0]
  exact (hG.div_const _ |>.mul hpow).mul hM

/-- info: 'FormalResearch.SignUncertainty.continuous_radialKW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_radialKW

end FormalResearch.SignUncertainty
