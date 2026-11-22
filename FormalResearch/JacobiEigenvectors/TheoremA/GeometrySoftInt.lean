module

public import Mathlib

/-!
# Paper J, Layer 2 (L2.G4 (d)): smoothness of a weighted parametric integral

Auxiliary analysis for the Morse coordinate of lem:tha-geom (d).  For `phi : R -> R`, `a : R` and `k : N` put
`wint k phi a x = int_0^1 (1 - s) s^k phi(a + s x) ds`.  If `phi` is `C^n` on an open set `U` containing
`[a - rho, a + rho]`, then `x |-> wint k phi a x` is `C^n` on `(-rho, rho)`, and its derivative there is
`wint (k + 1) phi' a`.  (Mathlib at this pin has no general `C^n` theorem for parametric integrals; the proof is an
induction on `n` through `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.)

Differences from the paper: none (the paper differentiates under the integral sign in one line, `app_smooth`).
Not formalised: nothing; this is a self-contained lemma.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.SoftInt

open Set Filter Topology MeasureTheory intervalIntegral

/-- `int_0^1 (1 - s) s^k phi(a + s x) ds`. -/
def wint (k : ℕ) (φ : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, (1 - s) * s ^ k * φ (a + s * x)

lemma affine_mem {a ρ x s : ℝ} (hx : x ∈ Ioo (-ρ) ρ) (hs : s ∈ Icc (0 : ℝ) 1) :
    a + s * x ∈ Icc (a - ρ) (a + ρ) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hs
  constructor <;> nlinarith

lemma continuousOn_wint {a ρ : ℝ} {U : Set ℝ} (hUρ : Icc (a - ρ) (a + ρ) ⊆ U) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ U) (k : ℕ) : ContinuousOn (wint k φ a) (Ioo (-ρ) ρ) := by
  set φc : ℝ → ℝ := fun u => φ (max (a - ρ) (min u (a + ρ))) with hφc
  rcases isEmpty_or_nonempty (Ioo (-ρ) ρ) with hemp | hne
  · rw [Set.isEmpty_coe_sort] at hemp
    rw [hemp]; exact continuousOn_empty _
  have hle : a - ρ ≤ a + ρ := by
    obtain ⟨x, hx⟩ := hne
    linarith [hx.1, hx.2]
  have hcl : Continuous φc := by
    have hmaps : ∀ u : ℝ, max (a - ρ) (min u (a + ρ)) ∈ Icc (a - ρ) (a + ρ) := fun u =>
      ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
    have : ContinuousOn φ (Icc (a - ρ) (a + ρ)) := hφ.mono hUρ
    have hc2 : Continuous (fun u : ℝ => max (a - ρ) (min u (a + ρ))) := by fun_prop
    exact (this.comp_continuous hc2 hmaps)
  have hcont : Continuous (fun x : ℝ => ∫ s in (0 : ℝ)..1, (1 - s) * s ^ k * φc (a + s * x)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have : Continuous (fun p : ℝ × ℝ => (1 - p.2) * p.2 ^ k * φc (a + p.2 * p.1)) := by fun_prop
    exact this
  refine hcont.continuousOn.congr (fun x hx => ?_)
  unfold wint
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  have := affine_mem (a := a) hx hs
  simp only [hφc]
  rw [min_eq_left this.2, max_eq_right this.1]

lemma hasDerivAt_wint {a ρ : ℝ} {U : Set ℝ} (hU : IsOpen U) (hUρ : Icc (a - ρ) (a + ρ) ⊆ U) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ U) (k : ℕ) {x0 : ℝ} (hx0 : x0 ∈ Ioo (-ρ) ρ) :
    HasDerivAt (wint k φ a) (wint (k + 1) (deriv φ) a x0) x0 := by
  have hφc : ContinuousOn φ U := hφ.continuousOn
  have hφ'c : ContinuousOn (deriv φ) U := hφ.continuousOn_deriv_of_isOpen hU (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a - ρ) (b := a + ρ)).exists_bound_of_continuousOn (hφ'c.mono hUρ)
  have hmeas : ∀ x ∈ Ioo (-ρ) ρ, ContinuousOn (fun s : ℝ => (1 - s) * s ^ k * φ (a + s * x)) (uIcc 0 1) := by
    intro x hx
    have hsub : ContinuousOn (fun s : ℝ => φ (a + s * x)) (uIcc 0 1) := by
      refine hφc.comp (by fun_prop : Continuous (fun s : ℝ => a + s * x)).continuousOn ?_
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      exact hUρ (affine_mem hx hs)
    exact (by fun_prop : Continuous (fun s : ℝ => (1 - s) * s ^ k)).continuousOn.mul hsub
  have hmeas' : ContinuousOn (fun s : ℝ => (1 - s) * s ^ (k + 1) * deriv φ (a + s * x0)) (uIcc 0 1) := by
    have hsub : ContinuousOn (fun s : ℝ => deriv φ (a + s * x0)) (uIcc 0 1) := by
      refine hφ'c.comp (by fun_prop : Continuous (fun s : ℝ => a + s * x0)).continuousOn ?_
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      exact hUρ (affine_mem hx0 hs)
    exact (by fun_prop : Continuous (fun s : ℝ => (1 - s) * s ^ (k + 1))).continuousOn.mul hsub
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1)
    (F := fun x s => (1 - s) * s ^ k * φ (a + s * x))
    (F' := fun x s => (1 - s) * s ^ (k + 1) * deriv φ (a + s * x))
    (x₀ := x0) (s := Ioo (-ρ) ρ) (bound := fun _ => C) (isOpen_Ioo.mem_nhds hx0)
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx0) (fun x hx =>
      ((hmeas x hx).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc))
    ((hmeas x0 hx0).intervalIntegrable)
    ((hmeas'.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall (fun s hs x hx => by
      rw [uIoc_of_le zero_le_one] at hs
      have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
      have hmem := affine_mem (a := a) hx hsI
      have hb := hC (a + s * x) hmem
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hsI.1, hsI.2]
      have h2 : |s ^ (k + 1)| ≤ 1 := by
        rw [abs_pow, abs_of_nonneg hsI.1]; exact pow_le_one₀ hsI.1 hsI.2
      have h3 : |deriv φ (a + s * x)| ≤ C := by simpa using hb
      calc |1 - s| * |s ^ (k + 1)| * |deriv φ (a + s * x)| ≤ 1 * 1 * C := by gcongr
        _ = C := by ring))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun s hs x hx => by
      rw [uIoc_of_le zero_le_one] at hs
      have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
      have hmem := hUρ (affine_mem (a := a) hx hsI)
      have hd : DifferentiableAt ℝ φ (a + s * x) :=
        (hφ.differentiableOn (by norm_num) _ hmem).differentiableAt (hU.mem_nhds hmem)
      have hin : HasDerivAt (fun y : ℝ => a + s * y) s x := by
        simpa using ((hasDerivAt_id x).const_mul s).const_add a
      have hc := hd.hasDerivAt.comp x hin
      have := hc.const_mul ((1 - s) * s ^ k)
      convert this using 1
      · rfl
      · rw [pow_succ]; ring))
  exact key.2

/-- `x |-> int_0^1 (1 - s) s^k phi(a + s x) ds` is `C^n` on `(-rho, rho)` when `phi` is `C^n` on an open set containing
`[a - rho, a + rho]`. -/
theorem contDiffOn_wint {a ρ : ℝ} {U : Set ℝ} (hU : IsOpen U) (hUρ : Icc (a - ρ) (a + ρ) ⊆ U) :
    ∀ (n : ℕ) (φ : ℝ → ℝ), ContDiffOn ℝ (n : WithTop ℕ∞) φ U → ∀ k : ℕ,
      ContDiffOn ℝ (n : WithTop ℕ∞) (wint k φ a) (Ioo (-ρ) ρ) := by
  intro n
  induction n with
  | zero =>
    intro φ hφ k
    have : ContinuousOn φ U := by simpa using hφ
    simpa using continuousOn_wint hUρ this k
  | succ n ih =>
    intro φ hφ k
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast] at hφ ⊢
    have hφ1 : ContDiffOn ℝ 1 φ U := hφ.of_le (by
      have : (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) + 1 := le_add_self
      exact this)
    have hdφ : ContDiffOn ℝ (n : WithTop ℕ∞) (deriv φ) U :=
      ((contDiffOn_succ_iff_deriv_of_isOpen hU).1 hφ).2.2
    have hderiv : ∀ x ∈ Ioo (-ρ) ρ, HasDerivAt (wint k φ a) (wint (k + 1) (deriv φ) a x) x :=
      fun x hx => hasDerivAt_wint hU hUρ hφ1 k hx
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine (ih (deriv φ) hdφ (k + 1)).congr (fun x hx => ?_)
    exact (hderiv x hx).deriv

end FormalResearch.JacobiEigenvectors.TheoremA.SoftInt

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.SoftInt.contDiffOn_wint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.SoftInt.contDiffOn_wint
