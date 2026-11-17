module

public import Mathlib

/-!
# Phase calculus for the Hermite Plancherel–Rotach formula

This module proves the elementary phase identities used in W1, Lemma PR(a):
for fixed x₀, ∂ᵣ tᵣ = cot(tᵣ)/(2r+1), ∂ᵣ Φᵣ = tᵣ, and the corresponding
integral formula on an interval contained in the oscillatory domain. The phase is
the one in Szegő, Theorem 8.22.8 (also DLMF §18.15(iv)). This is calculus only;
the identification of this phase with the phase of the Hermite function and the
asymptotic expansion are `hermite_bulk_PR` (`HermiteBulkMain`).
-/

@[expose] public section

open Real MeasureTheory

namespace FormalResearch.Special

/-- The oscillatory angle at a real index r. -/
noncomputable def hpr_angle (x₀ r : ℝ) : ℝ := Real.arccos (x₀ / √(2 * r + 1))

/-- The Plancherel–Rotach phase at a real index r. -/
noncomputable def hpr_phase (x₀ r : ℝ) : ℝ :=
  (2 * r + 1) / 4 * (2 * hpr_angle x₀ r - Real.sin (2 * hpr_angle x₀ r)) - π / 4

private lemma hpr_angle_deriv_core (x₀ r : ℝ) (hr : 0 < r)
    (hx : |x₀| < √(2 * r + 1)) :
    HasDerivAt (hpr_angle x₀)
      ((1 / √(1 - (x₀ / √(2 * r + 1)) ^ 2)) *
        (x₀ / (√(2 * r + 1)) ^ 3)) r := by
  let u : ℝ → ℝ := fun s => 2 * s + 1
  let z : ℝ → ℝ := fun s => x₀ / √(u s)
  have hu : HasDerivAt u 2 r := by
    have h := (hasDerivAt_id r).const_mul 2 |>.add_const 1
    convert h using 1 <;> norm_num [u, Function.comp_def]
  have hu0 : u r ≠ 0 := by dsimp [u]; linarith
  have hsqrt := (Real.hasDerivAt_sqrt hu0).comp r hu
  have hsqrtpos : 0 < √(u r) := Real.sqrt_pos.2 (by dsimp [u]; linarith)
  have hz : HasDerivAt z (-(x₀ / (√(u r))^3)) r := by
    have hdiv := (hasDerivAt_const r x₀).div hsqrt hsqrtpos.ne'
    have hsq : (√(u r)) ^ 2 = u r := Real.sq_sqrt (by dsimp [u]; linarith)
    convert hdiv using 1
    · funext s
      simp [z]
    · dsimp [u] at *
      rw [hsq]
      field_simp
      rw [hsq]
      ring
  have hzrange : |z r| < 1 := by
    dsimp [z]
    rw [abs_div, abs_of_pos hsqrtpos]
    rw [div_lt_one hsqrtpos]
    simpa [u] using hx
  have hzabs := abs_lt.mp hzrange
  have ht := (Real.hasDerivAt_arccos (ne_of_gt hzabs.1) (ne_of_lt hzabs.2)).comp r hz
  convert ht.congr_deriv ?_ using 1
  · change (fun s => Real.arccos (z s)) = hpr_angle x₀
    funext s
    rfl
  · simp [z, u]

/-- Derivative of the angle in the oscillatory region (equivalent to cot(t)/(2r+1)). -/
theorem hpr_hasDerivAt_angle (x₀ r : ℝ) (hr : 0 < r)
    (hx : |x₀| < √(2 * r + 1)) :
    HasDerivAt (hpr_angle x₀) (Real.cos (hpr_angle x₀ r) /
      (Real.sin (hpr_angle x₀ r) * (2 * r + 1))) r := by
  have h := hpr_angle_deriv_core x₀ r hr hx
  have harg : |x₀ / √(2 * r + 1)| < 1 := by
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by linarith : 0 < 2 * r + 1))]
    rw [div_lt_one (Real.sqrt_pos.2 (by linarith : 0 < 2 * r + 1))]
    exact hx
  have hc : Real.cos (hpr_angle x₀ r) = x₀ / √(2 * r + 1) := by
    exact Real.cos_arccos (le_of_lt (abs_lt.mp harg).1) (le_of_lt (abs_lt.mp harg).2)
  have hs : Real.sin (hpr_angle x₀ r) =
      √(1 - (x₀ / √(2 * r + 1)) ^ 2) := by
    change Real.sin (Real.arccos _) = _
    rw [Real.sin_arccos]
  have hroot : (√(2 * r + 1)) ^ 2 = 2 * r + 1 := Real.sq_sqrt (by linarith)
  convert h using 1
  · rw [hc, hs]
    field_simp
    rw [hroot]

/-- Derivative of the Hermite Plancherel–Rotach phase. -/
theorem hpr_hasDerivAt_phase (x₀ r : ℝ) (hr : 0 < r)
    (hx : |x₀| < √(2 * r + 1)) :
    HasDerivAt (hpr_phase x₀) (hpr_angle x₀ r) r := by
  let t := hpr_angle x₀ r
  have ht := hpr_hasDerivAt_angle x₀ r hr hx
  have hA : HasDerivAt (fun s : ℝ => 2 * s + 1) 2 r := by
    have h := (hasDerivAt_id r).const_mul 2 |>.add_const 1
    convert h using 1 <;> norm_num [Function.comp_def]
  have h2t : HasDerivAt (fun s : ℝ => 2 * hpr_angle x₀ s) (2 * deriv (hpr_angle x₀) r) r := by
    convert ht.const_mul 2 using 1
    · rw [ht.deriv]
  have hsin := (Real.hasDerivAt_sin (2 * t)).comp r h2t
  have hB : HasDerivAt (fun s : ℝ => 2 * hpr_angle x₀ s - Real.sin (2 * hpr_angle x₀ s))
      (2 * deriv (hpr_angle x₀) r - Real.cos (2 * t) * (2 * deriv (hpr_angle x₀) r)) r := by
    convert h2t.sub hsin using 1
    · funext s
      simp [Function.comp_def]
  have hprod := hA.div_const 4 |>.mul hB
  have hphase : HasDerivAt (hpr_phase x₀)
      ((2 * r + 1) / 4 * (2 * deriv (hpr_angle x₀) r - Real.cos (2 * t) * (2 * deriv (hpr_angle x₀) r)) +
       (2 / 4) * (2 * t - Real.sin (2 * t))) r := by
    convert (hprod.sub_const (π / 4)) using 1
    · funext s
      simp [hpr_phase]
    · ring
  have hsinpos : Real.sin t ≠ 0 := by
    have hz : |x₀ / √(2 * r + 1)| < 1 := by
      rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by linarith : 0 < 2 * r + 1))]
      rw [div_lt_one (Real.sqrt_pos.2 (by linarith : 0 < 2 * r + 1))]
      exact hx
    rw [show t = Real.arccos (x₀ / √(2 * r + 1)) by rfl, Real.sin_arccos]
    exact (Real.sqrt_pos.2 (by nlinarith [sq_nonneg (x₀ / √(2 * r + 1)), abs_lt.mp hz])).ne'
  have hcos : Real.cos t = x₀ / √(2 * r + 1) := by
    have hz : |x₀ / √(2 * r + 1)| < 1 := by
      rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by linarith : 0 < 2 * r + 1))]
      rw [div_lt_one (Real.sqrt_pos.2 (by linarith : 0 < 2 * r + 1))]
      exact hx
    exact Real.cos_arccos (le_of_lt (abs_lt.mp hz).1) (le_of_lt (abs_lt.mp hz).2)
  have hdouble : Real.cos (2 * t) = 2 * (Real.cos t)^2 - 1 := by rw [cos_two_mul]
  have hderiv : deriv (hpr_phase x₀) r = hpr_angle x₀ r := by
    have htD := ht.deriv
    have hsin2 : Real.sin (2 * t) = 2 * Real.sin t * Real.cos t := by rw [sin_two_mul]
    rw [hphase.deriv]
    rw [htD, hdouble, hsin2]
    change (2 * r + 1) / 4 *
      (2 * (Real.cos t / (Real.sin t * (2 * r + 1))) -
        (2 * Real.cos t ^ 2 - 1) * (2 * (Real.cos t / (Real.sin t * (2 * r + 1))))) +
      2 / 4 * (2 * t - 2 * Real.sin t * Real.cos t) = t
    field_simp [hsinpos]
    rw [← Real.sin_sq_add_cos_sq t]
    ring
  apply hphase.congr_deriv
  calc
    _ = deriv (hpr_phase x₀) r := hphase.deriv.symm
    _ = hpr_angle x₀ r := hderiv

/-- The phase increment is the integral of the angle on any admissible interval. -/
theorem hpr_phase_sub_eq_integral (x₀ n m : ℝ) (hn : 0 < n) (hnm : n ≤ m)
    (hx : |x₀| < √(2 * n + 1)) :
    hpr_phase x₀ m - hpr_phase x₀ n = ∫ r in n..m, hpr_angle x₀ r := by
  have hseg : ∀ r ∈ Set.Icc n m, |x₀| < √(2 * r + 1) := by
    intro r hr
    apply lt_of_lt_of_le hx
    exact Real.sqrt_le_sqrt (by nlinarith [hr.1])
  have hargcont : ContinuousOn (fun r => x₀ / √(2 * r + 1)) (Set.Icc n m) := by
    apply ContinuousOn.div continuousOn_const
    · have hl : Continuous (fun r : ℝ => 2 * r + 1) := by fun_prop
      have hs : Continuous (fun r : ℝ => √(2 * r + 1)) := by
        convert Real.continuous_sqrt.comp hl using 1
        funext r
        congr 1
      exact hs.continuousOn
    · intro r hr
      exact (Real.sqrt_pos.2 (by nlinarith [hr.1, hn])).ne'
  have hargmem : Set.MapsTo (fun r => x₀ / √(2 * r + 1)) (Set.Icc n m) (Set.Icc (-1) 1) := by
    intro r hr
    have h := hseg r hr
    have hs : 0 < √(2 * r + 1) := Real.sqrt_pos.2 (by nlinarith [hr.1, hn])
    constructor
    · rw [neg_le]
      change -(x₀ / √(2 * r + 1)) ≤ 1
      rw [← neg_div, div_le_one hs]
      have habs := abs_le.mp (le_of_lt h)
      linarith
    · change x₀ / √(2 * r + 1) ≤ 1
      rw [div_le_one hs]
      exact (abs_le.mp (le_of_lt h)).2
  have hanglecont : ContinuousOn (hpr_angle x₀) (Set.Icc n m) := by
    change ContinuousOn (Real.arccos ∘ fun r => x₀ / √(2 * r + 1)) (Set.Icc n m)
    exact Real.continuous_arccos.continuousOn.comp hargcont hargmem
  have hcont : ContinuousOn (hpr_phase x₀) (Set.Icc n m) := by
    unfold hpr_phase
    fun_prop
  have hderiv : ∀ r ∈ Set.Ioo n m, HasDerivAt (hpr_phase x₀) (hpr_angle x₀ r) r := by
    intro r hr
    exact hpr_hasDerivAt_phase x₀ r (lt_trans hn hr.1) (hseg r (Set.Ioo_subset_Icc_self hr))
  have hint : IntervalIntegrable (hpr_angle x₀) volume n m :=
    hanglecont.intervalIntegrable_of_Icc hnm
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hnm hcont hderiv hint]

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hpr_hasDerivAt_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hpr_hasDerivAt_angle

/-- info: 'FormalResearch.Special.hpr_hasDerivAt_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hpr_hasDerivAt_phase

/-- info: 'FormalResearch.Special.hpr_phase_sub_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hpr_phase_sub_eq_integral
