module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroDatum
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroXbEdge

/-!
# Derivatives at the tip (FIVE-0, `ctu:jets` for `g₁`, step 1)

Derivatives at `z = 0` of the elementary ingredients of `G_out`: `sInv' (0) = 4/π`, `mC'(0) = 2√2`, `uC'(0) = 0`,
`tipE'(0) = -1`, hence `tipExt'(0) = -2√2/arsinh 1` and `tipExt'(0)/tipExt(0) = -4√2/π`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma hasDerivAt_sInv_zero : HasDerivAt sInv ((4 / π : ℝ) : ℂ) 0 := by
  have hq : HasDerivAt (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) (2 * Complex.I) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => 1 + z * Complex.I) Complex.I 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const Complex.I).const_add 1
    have h2 : HasDerivAt (fun z : ℂ => 1 - z * Complex.I) (-Complex.I) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const Complex.I).const_sub 1
    have := h1.div h2 (by simp)
    convert this using 1
    simp; ring
  have hl : HasDerivAt (fun z : ℂ => Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I)))
      (2 * Complex.I / ((1 + (0 : ℂ) * Complex.I) / (1 - (0 : ℂ) * Complex.I))) 0 := by
    refine hq.clog ?_
    simp
  have := (hl.const_mul (-Complex.I / 2)).const_mul (4 / (π : ℂ))
  unfold sInv Complex.arctan
  convert this using 1
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hI := Complex.I_sq
  push_cast
  field_simp
  linear_combination hI

lemma sInt_one_eq : sInt 1 = ((Real.arsinh 1 : ℝ) : ℂ) := by
  have := sInt_pos_real (c := 1) one_pos
  simpa using this

lemma hasDerivAt_mC_zero : HasDerivAt mC (2 * ((√2 : ℝ) : ℂ)) 0 := by
  have h1 : HasDerivAt (fun z : ℂ => (2 * ((√2 : ℝ) : ℂ)) * z) (2 * ((√2 : ℝ) : ℂ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (2 * ((√2 : ℝ) : ℂ))
  have h2 : HasDerivAt (fun z : ℂ => 1 + z ^ 2) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℂ)).const_add 1)
  have := h1.div h2 (by simp)
  unfold mC
  convert this using 1
  simp

lemma hasDerivAt_uC_zero : HasDerivAt uC 0 0 := by
  have hm := hasDerivAt_mC_zero
  have h1 : HasDerivAt (fun z : ℂ => 1 - mC z ^ 2) 0 0 := by
    have := (hm.pow 2).const_sub 1
    convert this using 1
    simp [mC_zero]
  refine h1.congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun z : ℂ => 1 + z ^ 2) 0 := by fun_prop
  have : ∀ᶠ z : ℂ in 𝓝 0, 1 + z ^ 2 ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [this] with z hz
  exact uC_eq_one_sub_mC_sq hz

lemma hasDerivAt_tipE_zero : HasDerivAt tipE (-1) 0 := by
  have hS : DifferentiableAt ℂ sInt (-((0 : ℂ) ^ 2)) :=
    differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (by
      rintro ⟨_, h⟩; simp at h; linarith))
  have h1 : HasDerivAt (fun m : ℂ => sInt (-(m ^ 2))) (deriv sInt (-((0 : ℂ) ^ 2)) * (-(2 * 0))) 0 := by
    have hin : HasDerivAt (fun m : ℂ => -(m ^ 2)) (-(2 * 0)) 0 := by
      have := (hasDerivAt_pow 2 (0 : ℂ)).neg
      convert this using 1
      simp
    exact (hS.hasDerivAt).comp (0 : ℂ) hin
  have hN : HasDerivAt (fun m : ℂ => (π : ℂ) / 2 - m * sInt (-(m ^ 2)))
      (-(1 * sInt (-((0 : ℂ) ^ 2)) + 0 * (deriv sInt (-((0 : ℂ) ^ 2)) * (-(2 * 0))))) 0 := by
    exact ((hasDerivAt_id (0 : ℂ)).mul h1).const_sub _ |>.congr_deriv (by simp)
  have hD : HasDerivAt (fun m : ℂ => (1 - m ^ 2) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 - (0 : ℂ) ^ 2) ^ ((1 / 2 : ℂ) - 1) * (-(2 * 0))) 0 := by
    have hin : HasDerivAt (fun m : ℂ => 1 - m ^ 2) (-(2 * 0)) 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℂ)).const_sub 1)
    exact hin.cpow_const (by simp)
  have := hN.div hD (by simp)
  unfold tipE
  convert this using 1
  simp [sInt_zero']

lemma hasDerivAt_tipExt_zero :
    HasDerivAt tipExt (-(2 * ((√2 : ℝ) : ℂ)) / ((Real.arsinh 1 : ℝ) : ℂ)) 0 := by
  have h1 : HasDerivAt (fun z : ℂ => tipE (mC z)) (-1 * (2 * ((√2 : ℝ) : ℂ))) 0 := by
    have : HasDerivAt tipE (-1) (mC 0) := by rw [mC_zero]; exact hasDerivAt_tipE_zero
    exact this.comp (0 : ℂ) hasDerivAt_mC_zero
  have hS : DifferentiableAt ℂ sInt (uC 0) :=
    differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (by
      rw [uC_zero]; rintro ⟨_, h⟩; simp at h; linarith))
  have h2 : HasDerivAt (fun z : ℂ => sInt (uC z)) (deriv sInt (uC 0) * 0) 0 :=
    hS.hasDerivAt.comp (0 : ℂ) hasDerivAt_uC_zero
  have hne : sInt (uC 0) ≠ 0 := by
    rw [uC_zero, sInt_one_eq]
    exact_mod_cast arsinh_one_pos.ne'
  have := h1.div h2 hne
  unfold tipExt
  convert this using 1
  rw [uC_zero, sInt_one_eq, mC_zero, tipE_zero]
  have : ((Real.arsinh 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast arsinh_one_pos.ne'
  field_simp
  ring

lemma tipExt_logderiv :
    (-(2 * ((√2 : ℝ) : ℂ)) / ((Real.arsinh 1 : ℝ) : ℂ)) / tipExt 0 = -(4 * ((√2 : ℝ) : ℂ)) / (π : ℂ) := by
  rw [tipExt_zero]
  have : ((Real.arsinh 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast arsinh_one_pos.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp
  ring

end FormalResearch.ModularBootstrap.FiveTerm
