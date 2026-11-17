module

public import FormalResearch.Special.LatticeIBP

/-!
# `∫ w · sawH(t₀)` through the Fourier series of `sawH` and the contour shift

For `w` holomorphic on `|Re s| ≤ X, |Im s| ≤ y₁` with `|w| ≤ C_w e^{-κ|Re s|}`:
`‖∫_{-X}^{X} w(s) sawH(t₀(s)) ds‖ ≤ (1/12)·(2 C_w y₁ e^{-κX} + (2C_w/κ) e^{-2π m y₁})`.

Proof: interchange `∑_n` and `∫` (dominated convergence; the series of `sawH` converges absolutely),
write `cos = (e^{+} + e^{-})/2` and apply `contour_shift_le` to each of the two exponentials; the
`n`-sum is `∑ 1/(2π² n²) = 1/12` (Mathlib's `hasSum_zeta_two`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

theorem integral_w_sawH_le {τ0 : ℂ → ℂ} {X y0 m M K : ℝ} (h : CalPhase τ0 X y0 m M K)
    {w : ℂ → ℂ} {Cw κ y1 : ℝ} (hκ : 0 < κ) (hCw : 0 ≤ Cw) (hy1 : 0 < y1) (hy10 : y1 ≤ y0)
    (hwd : DifferentiableOn ℂ w {s | |s.re| ≤ X ∧ |s.im| ≤ y1})
    (hwb : ∀ s : ℂ, |s.re| ≤ X → |s.im| ≤ y1 → ‖w s‖ ≤ Cw * Real.exp (-κ * |s.re|)) :
    ‖∫ s in (-X)..X, w (s : ℂ) * ((sawH (realPhase τ0 s) : ℝ) : ℂ)‖ ≤
      1 / 12 * (2 * Cw * y1 * Real.exp (-κ * X) + 2 * Cw / κ * Real.exp (-(2 * Real.pi * m * y1))) := by
  have hX := h.hX
  have hm := h.hm
  have hpi := Real.pi_pos
  set Bc : ℝ := 2 * Cw * y1 * Real.exp (-κ * X) + 2 * Cw / κ * Real.exp (-(2 * Real.pi * m * y1)) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  have hmemw : ∀ s : ℝ, s ∈ Icc (-X) X → (s : ℂ) ∈ {s : ℂ | |s.re| ≤ X ∧ |s.im| ≤ y1} := fun s hs =>
    ⟨by simpa using abs_le.mpr hs, by simpa using hy1.le⟩
  have hwc : ContinuousOn (fun s : ℝ => w (s : ℂ)) (Icc (-X) X) :=
    ContinuousOn.comp hwd.continuousOn Complex.continuous_ofReal.continuousOn hmemw
  have hsub : Icc (-X) X ⊆ Icc (-(X + 1)) (X + 1) := Icc_subset_Icc (by linarith) (by linarith)
  have ht0c : ContinuousOn (realPhase τ0) (Icc (-X) X) := h.continuousOn_realPhase.mono hsub
  set F : ℕ → ℝ → ℂ := fun n s => w (s : ℂ) *
    ((Real.cos (2 * Real.pi * n * realPhase τ0 s) / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) with hF
  have hFc : ∀ n, ContinuousOn (F n) (Icc (-X) X) := fun n =>
    hwc.mul (Complex.continuous_ofReal.comp_continuousOn
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (2 * Real.pi * n * t) /
        (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)).comp_continuousOn ht0c))
  have hbound0 : ∀ s ∈ Icc (-X) X, ‖w (s : ℂ)‖ ≤ Cw := fun s hs => by
    have := hwb (s : ℂ) (by simpa using abs_le.mpr hs) (by simpa using hy1.le)
    simp only [Complex.ofReal_re] at this
    refine this.trans ?_
    have : Real.exp (-κ * |s|) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg s]
    nlinarith
  set u : ℕ → ℝ := fun n => 1 / (2 * Real.pi ^ 2) * (1 / (n : ℝ) ^ 2) with hu
  have hFb : ∀ n, ∀ s ∈ Icc (-X) X, ‖F n s‖ ≤ Cw * u n := fun n s hs => by
    simp only [hF]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.cos (2 * Real.pi * n * realPhase τ0 s) / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)| ≤ u n := by
      rw [abs_div]
      by_cases hn : n = 0
      · simp [hn, hu]
      · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        rw [abs_of_pos (by positivity : 0 < 2 * Real.pi ^ 2 * (n : ℝ) ^ 2)]
        calc _ ≤ 1 / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) :=
              div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
          _ = u n := by simp only [hu]; field_simp
    exact mul_le_mul (hbound0 s hs) h1 (abs_nonneg _) hCw
  have hlim : ∀ s : ℝ, HasSum (fun n => F n s) (w (s : ℂ) * ((sawH (realPhase τ0 s) : ℝ) : ℂ)) := fun s => by
    have := (hasSum_sawH (realPhase τ0 s)).mapL Complex.ofRealCLM
    have h2 := this.mul_left (w (s : ℂ))
    simpa only [hF, Complex.ofRealCLM_apply] using h2
  have hbs : Summable (fun n : ℕ => Cw * u n) := summable_sawH_terms.mul_left Cw
  have hHS := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -X) (b := X)
    (F := F) (f := fun s : ℝ => w (s : ℂ) * ((sawH (realPhase τ0 s) : ℝ) : ℂ))
    (fun n s => Cw * u n)
    (fun n => by
      rw [uIoc_of_le (by linarith)]
      exact (hFc n).mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)
    (fun n => Filter.Eventually.of_forall (fun s hs => by
      rw [uIoc_of_le (by linarith)] at hs
      exact hFb n s ⟨hs.1.le, hs.2⟩))
    (Filter.Eventually.of_forall (fun s _ => hbs))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun s _ => hlim s))
  -- norm of each coefficient integral
  have hnorm : ∀ n : ℕ, ‖∫ s in (-X)..X, F n s‖ ≤ Bc * u n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have : ∀ s : ℝ, F 0 s = 0 := fun s => by simp [hF]
      simp [this, hu]
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    set cn : ℝ := 1 / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) with hcn
    have hcn0 : 0 ≤ cn := by positivity
    set Ep : ℝ → ℂ := fun x => w (x : ℂ) * Complex.exp (((1 : ℝ) : ℂ) * (2 * Real.pi * I * n) * τ0 x) with hEp
    set Em : ℝ → ℂ := fun x => w (x : ℂ) * Complex.exp (((-1 : ℝ) : ℂ) * (2 * Real.pi * I * n) * τ0 x) with hEm
    have hFeq : ∀ s : ℝ, F n s = ((cn / 2 : ℝ) : ℂ) * (Ep s + Em s) := by
      intro s
      have hτ := h.ofReal_eq s
      have h2 := Complex.two_cos (x := ((2 * Real.pi * n * realPhase τ0 s : ℝ) : ℂ))
      simp only [hF, hEp, hEm, hτ]
      have : (((Real.cos (2 * Real.pi * n * realPhase τ0 s) / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) =
          ((cn : ℝ) : ℂ) * Complex.cos ((2 * Real.pi * n * realPhase τ0 s : ℝ) : ℂ) := by
        rw [Complex.ofReal_div, ← Complex.ofReal_cos, hcn]
        push_cast
        ring
      rw [this]
      have h3 : Complex.cos ((2 * Real.pi * n * realPhase τ0 s : ℝ) : ℂ) =
          (Complex.exp (((2 * Real.pi * n * realPhase τ0 s : ℝ) : ℂ) * I) +
            Complex.exp (-((2 * Real.pi * n * realPhase τ0 s : ℝ) : ℂ) * I)) / 2 := by
        rw [← h2]; ring
      rw [h3]
      push_cast
      have e1 : (1 : ℂ) * (2 * (Real.pi : ℂ) * I * n) * (realPhase τ0 s : ℂ) =
          2 * (Real.pi : ℂ) * n * (realPhase τ0 s : ℂ) * I := by ring
      have e2 : (-1 : ℂ) * (2 * (Real.pi : ℂ) * I * n) * (realPhase τ0 s : ℂ) =
          -(2 * (Real.pi : ℂ) * n * (realPhase τ0 s : ℂ)) * I := by ring
      rw [e1, e2]
      ring
    have hcont : ∀ σ : ℝ, ContinuousOn (fun x : ℝ => w (x : ℂ) *
        Complex.exp ((σ : ℂ) * (2 * Real.pi * I * n) * τ0 x)) (Icc (-X) X) := fun σ => by
      refine hwc.mul ?_
      have : (fun x : ℝ => Complex.exp ((σ : ℂ) * (2 * Real.pi * I * n) * τ0 x)) =
          fun x : ℝ => Complex.exp ((σ : ℂ) * (2 * Real.pi * I * n) * ((realPhase τ0 x : ℝ) : ℂ)) := by
        ext x; rw [h.ofReal_eq x]
      rw [this]
      exact (Complex.continuous_exp.comp_continuousOn
        ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ht0c))))
    have hIp : IntervalIntegrable Ep volume (-X) X := (hcont 1).intervalIntegrable_of_Icc (by linarith)
    have hIm : IntervalIntegrable Em volume (-X) X := (hcont (-1)).intervalIntegrable_of_Icc (by linarith)
    have hint : ∫ s in (-X)..X, F n s = ((cn / 2 : ℝ) : ℂ) *
        ((∫ s in (-X)..X, Ep s) + ∫ s in (-X)..X, Em s) := by
      simp_rw [hFeq]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hIp hIm]
    have hJp := contour_shift_le h hκ hCw hy1 hy10 hn' (σ := 1) (Or.inl rfl) hwd hwb
    have hJm := contour_shift_le h hκ hCw hy1 hy10 hn' (σ := -1) (Or.inr rfl) hwd hwb
    have hexp : Real.exp (-(2 * Real.pi * n * m * y1)) ≤ Real.exp (-(2 * Real.pi * m * y1)) := by
      apply Real.exp_le_exp.mpr
      have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have : 0 < 2 * Real.pi * m * y1 := by positivity
      nlinarith
    have hBn : 2 * Cw * y1 * Real.exp (-κ * X) + 2 * Cw / κ * Real.exp (-(2 * Real.pi * n * m * y1)) ≤ Bc := by
      rw [hBc]
      have := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2 * Cw / κ)
      linarith
    rw [hint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsum := norm_add_le (∫ s in (-X)..X, Ep s) (∫ s in (-X)..X, Em s)
    have hu' : u n = cn := by simp only [hu, hcn]; field_simp
    rw [hu']
    have : ‖∫ s in (-X)..X, Ep s‖ + ‖∫ s in (-X)..X, Em s‖ ≤ 2 * Bc := by
      have a1 : ‖∫ s in (-X)..X, Ep s‖ ≤ Bc := le_trans hJp hBn
      have a2 : ‖∫ s in (-X)..X, Em s‖ ≤ Bc := le_trans hJm hBn
      linarith
    nlinarith
  have hg : HasSum (fun n : ℕ => Bc * u n) (Bc / 12) := by
    have := hasSum_zeta_two.mul_left (Bc / (2 * Real.pi ^ 2))
    convert this using 1
    · ext n; simp only [hu]; ring
    · field_simp; ring
  exact (hHS.norm_le_of_bounded hg hnorm).trans (le_of_eq (by rw [hBc]; ring))

end FormalResearch.Special.Lattice
