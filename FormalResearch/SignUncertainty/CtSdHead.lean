module

public import FormalResearch.SignUncertainty.CtSdDeform

/-!
# The head `∫₀^{τ₁}`: change of variables `τ = T(s)` and scaling `s = λ w` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("Split (ct:Keps) at `τ₁`", "Set `w = c^{1/3}s`").
**Proved.**  If the real amplitude `B` and phase `ϕ` pull back under the increasing map `T` to `N_c s^{1/2} g(s)` and `a s + s³/3`, then
`∫₀^{T(s₁)} B e^{icϕ} dτ = N₁ ∫_{[0,R]} w^{1/2} g(λ w) e^{iPh_U(w)} dw` with `s₁ = λR`, `κ U = a/λ²`, `N_c λ^{3/2} = N₁`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtSd

lemma csr_mul_ofReal {r : ℝ} (hr : 0 ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    csr (((r * t : ℝ)) : ℂ) = (Real.sqrt r : ℂ) * csr (t : ℂ) := by
  unfold csr
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr ht]
  congr 1
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr, Real.sqrt_eq_rpow]

/-- Change of variables on `[0,s₁]` for a complex integrand. -/
lemma subst_head {s1 : ℝ} (hs1 : 0 < s1) {T T1 : ℝ → ℝ} {g : ℝ → ℂ}
    (hT : ∀ s ∈ Icc 0 s1, HasDerivAt T (T1 s) s) (hT1 : ∀ s ∈ Icc 0 s1, 0 < T1 s) (hT0 : T 0 = 0)
    (hgc : ContinuousOn g (Ioi 0)) (hgint : IntegrableOn g (Ioc 0 (T s1)))
    (hF : IntegrableOn (fun s => ((T1 s : ℝ) : ℂ) * g (T s)) (Icc 0 s1)) :
    ∫ s in (0 : ℝ)..s1, ((T1 s : ℝ) : ℂ) * g (T s) = ∫ τ in (0 : ℝ)..T s1, g τ := by
  have hcont : ContinuousOn T (Icc 0 s1) := fun s hs => (hT s hs).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn T (Icc 0 s1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 s1) hcont ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Icc 0 s1 := ⟨hx.1.le, hx.2.le⟩
    rw [(hT x hx').deriv]; exact hT1 x hx'
  have hTpos : ∀ s ∈ Ioc 0 s1, 0 < T s := by
    intro s hs
    have := hmono ⟨le_rfl, hs1.le⟩ ⟨hs.1.le, hs.2⟩ hs.1
    rwa [hT0] at this
  have hTs1 : 0 < T s1 := hTpos s1 ⟨hs1, le_rfl⟩
  have himg : T '' Icc 0 s1 ⊆ Icc 0 (T s1) := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨?_, hmono.monotoneOn hs ⟨hs1.le, le_rfl⟩ hs.2⟩
    have := hmono.monotoneOn ⟨le_rfl, hs1.le⟩ hs hs.1
    rwa [hT0] at this
  have key := intervalIntegral.integral_deriv_smul_comp''' (f := T) (f' := T1) (g := g) (a := 0) (b := s1)
    (by rwa [uIcc_of_le hs1.le]) (fun x hx => by
      rw [min_eq_left hs1.le, max_eq_right hs1.le] at hx
      exact (hT x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt)
    (by
      rw [min_eq_left hs1.le, max_eq_right hs1.le]
      refine hgc.mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hTpos x ⟨hx.1, hx.2.le⟩)
    (by
      rw [uIcc_of_le hs1.le]
      exact (((integrableOn_Icc_iff_integrableOn_Ioc (by exact eNorm_ne_top)).2 hgint).mono_set himg))
    (by
      rw [uIcc_of_le hs1.le]
      simpa [Complex.real_smul] using hF)
  simpa [Complex.real_smul, hT0] using key

/-- The head integral in the `w`-plane. -/
theorem head_eq {c lam s1 R a U KB : ℝ} {T T1 : ℝ → ℝ} {B : ℝ → ℂ} {ϕ : ℝ → ℝ} {gs : ℂ → ℂ} {Nc N1 : ℂ}
    (hc : 0 < c) (hlam : 0 < lam) (hlc : c * lam ^ 3 = 1) (hs1 : 0 < s1) (hsR : s1 = lam * R)
    (hU : a = kap * U * lam ^ 2) (hNc : Nc * ((lam * Real.sqrt lam : ℝ) : ℂ) = N1)
    (hT : ∀ s ∈ Icc 0 s1, HasDerivAt T (T1 s) s) (hT1 : ∀ s ∈ Icc 0 s1, 0 < T1 s) (hT0 : T 0 = 0)
    (hBc : ContinuousOn B (Ioi 0)) (hϕc : ContinuousOn ϕ (Ioi 0)) (hKB : 0 ≤ KB)
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hBT : ∀ s ∈ Ioc (0 : ℝ) s1, B (T s) * ((T1 s : ℝ) : ℂ) = Nc * csr (s : ℂ) * gs (s : ℂ))
    (hϕT : ∀ s ∈ Icc (0 : ℝ) s1, ϕ (T s) = a * s + s ^ 3 / 3)
    (hgs : ContinuousOn (fun s : ℝ => gs (s : ℂ)) (Icc 0 s1)) :
    ∫ τ in (0 : ℝ)..T s1, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ)) =
      N1 * lineInt 0 1 0 R (fun w => csr w * gs ((lam : ℂ) * w) *
        Complex.exp (Complex.I * PhU U w)) := by
  set g : ℝ → ℂ := fun τ => B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ)) with hg
  have hmono : StrictMonoOn T (Icc 0 s1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 s1)
      (fun s hs => (hT s hs).continuousAt.continuousWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Icc 0 s1 := ⟨hx.1.le, hx.2.le⟩
    rw [(hT x hx').deriv]; exact hT1 x hx'
  have hTs1 : 0 < T s1 := by
    have := hmono ⟨le_rfl, hs1.le⟩ ⟨hs1.le, le_rfl⟩ hs1
    rwa [hT0] at this
  have hgc : ContinuousOn g (Ioi 0) := by
    refine hBc.mul ?_
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn hϕc
  have hgint : IntegrableOn g (Ioc 0 (T s1)) := by
    have hdom : IntegrableOn (fun τ : ℝ => KB * τ ^ (-1 / 2 : ℝ)) (Ioc 0 (T s1)) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T s1) (r := -1 / 2) (by norm_num))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTs1.le] at this
      exact this.const_mul KB
    refine Integrable.mono' hdom ((hgc.mono (fun x (hx : x ∈ Ioc 0 (T s1)) => hx.1)).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
    simp only [hg, norm_mul]
    have hn : ‖Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ = 1 := by
      have : Complex.I * (c : ℂ) * (ϕ τ : ℂ) = Complex.I * ((c * ϕ τ : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact Complex.norm_exp_I_mul_ofReal _
    rw [hn, mul_one]
    refine (hbB τ hτ.1).trans ?_
    have h1 : τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (-1 / 2 : ℝ) := by
      calc τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (1 / 2 : ℝ) / τ :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg hτ.1.le _) hτ.1 (by linarith)
        _ = τ ^ (-1 / 2 : ℝ) := by
            rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub_one hτ.1.ne']
    calc KB * τ ^ (1 / 2 : ℝ) / (1 + τ) = KB * (τ ^ (1 / 2 : ℝ) / (1 + τ)) := by ring
      _ ≤ KB * τ ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h1 hKB
  -- the pulled-back integrand
  set F : ℝ → ℂ := fun s => Nc * csr (s : ℂ) * gs (s : ℂ) * Complex.exp (Complex.I * c * ((a * s + s ^ 3 / 3 : ℝ) : ℂ))
    with hF
  have hpt : ∀ s ∈ Ioc (0 : ℝ) s1, ((T1 s : ℝ) : ℂ) * g (T s) = F s := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) s1 := ⟨hs.1.le, hs.2⟩
    simp only [hg, hF]
    rw [hϕT s hs', ← hBT s hs]
    ring
  have hFc : ContinuousOn F (Icc 0 s1) := by
    simp only [hF]
    refine ((continuousOn_const.mul ?_).mul hgs).mul ?_
    · intro s hs
      exact ((continuousAt_csr (Or.inl (by simpa using hs.1))).comp (f := fun s : ℝ => (s : ℂ))
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
      exact Complex.continuous_ofReal.comp_continuousOn (by fun_prop)
  have hFint : IntegrableOn (fun s => ((T1 s : ℝ) : ℂ) * g (T s)) (Icc 0 s1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc (by exact eNorm_ne_top)]
    exact (hFc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun (fun s hs => (hpt s hs).symm) measurableSet_Ioc
  have h1 := subst_head hs1 hT hT1 hT0 hgc hgint hFint
  have h2 : ∫ s in (0 : ℝ)..s1, ((T1 s : ℝ) : ℂ) * g (T s) = ∫ s in (0 : ℝ)..s1, F s := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
    rw [uIoc_of_le hs1.le] at hs
    exact hpt s hs
  simp only [hg] at h1
  rw [← h1, h2]
  -- scaling `s = lam * w`
  have h3 := intervalIntegral.integral_comp_mul_left (a := 0) (b := R) F hlam.ne'
  rw [mul_zero, ← hsR] at h3
  have h4 : ∫ s in (0 : ℝ)..s1, F s = (lam : ℂ) * ∫ x in (0 : ℝ)..R, F (lam * x) := by
    rw [h3, Complex.real_smul]
    have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    simp only [Complex.ofReal_inv]
    field_simp
  rw [h4]
  unfold lineInt
  have hlcC : (c : ℂ) * (lam : ℂ) ^ 3 = 1 := by exact_mod_cast hlc
  have h5 : ∀ x ∈ Set.uIcc (0 : ℝ) R, (lam : ℂ) * F (lam * x) =
      N1 * (csr (0 + (x : ℂ) * 1) * gs ((lam : ℂ) * (0 + (x : ℂ) * 1)) *
        Complex.exp (Complex.I * PhU U (0 + (x : ℂ) * 1)) * 1) := by
    intro x hx
    rw [uIcc_of_le (by nlinarith [hs1, hsR, hlam] : (0 : ℝ) ≤ R)] at hx
    simp only [hF, zero_add, mul_one]
    rw [csr_mul_ofReal hlam.le hx.1, Complex.ofReal_mul, ← hNc]
    have hexp : Complex.I * (c : ℂ) * (((a * (lam * x) + (lam * x) ^ 3 / 3 : ℝ)) : ℂ) =
        Complex.I * PhU U (x : ℂ) := by
      unfold PhU
      rw [hU]
      push_cast
      linear_combination (Complex.I * ((kap : ℂ) * U * x + (x : ℂ) ^ 3 / 3)) * hlcC
    rw [hexp]
    push_cast
    ring
  calc (lam : ℂ) * ∫ x in (0 : ℝ)..R, F (lam * x)
      = ∫ x in (0 : ℝ)..R, (lam : ℂ) * F (lam * x) := (intervalIntegral.integral_const_mul _ _).symm
    _ = ∫ x in (0 : ℝ)..R, N1 * (csr (0 + (x : ℂ) * 1) * gs ((lam : ℂ) * (0 + (x : ℂ) * 1)) *
        Complex.exp (Complex.I * PhU U (0 + (x : ℂ) * 1)) * 1) := intervalIntegral.integral_congr h5
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- info: 'FormalResearch.SignUncertainty.CtSd.head_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms head_eq

end FormalResearch.SignUncertainty.CtSd
