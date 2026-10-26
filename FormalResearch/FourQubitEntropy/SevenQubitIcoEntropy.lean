import FormalResearch.FourQubitEntropy.SevenQubitIcoSpectrum

/-!
# Mean entropy on the seven-qubit icosahedral family

With the spectra of `SevenQubitIcoSpectrum`, the mean von Neumann entropy `E₃` (in nats) of the 35
three-qubit marginals of `ψ_x` is the function `E3 x` below (`cor:ico-entropy-separation` of
`icosahedral_state.tex`; the paper's bits are `E3 / ln 2`). This file proves, by calculus, that
`E3` has a unique maximiser `c` on `[0, 1/2]`, that `0 < c < 37/524`, and that
`E3 (37/524) < E3 c`, so the purity minimiser `x = 37/524` is not the entropy maximiser even within
the family.
-/

open Real

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- Mean three-qubit entropy (nats) of `ψ_x`, from the spectra. -/
noncomputable def E3 (x : ℝ) : ℝ :=
  (195 * negMulLog (4 * u x) + 40 * negMulLog (3 * u x + x) +
    15 * negMulLog (8 * u x) + 30 * negMulLog (u x + x)) / 35

/-- Its derivative: `(52 ln 4u − 32 ln(3u+x) + 8 ln 8u − 28 ln(u+x)) / 35`. -/
noncomputable def E3d (x : ℝ) : ℝ :=
  (52 * log (4 * u x) - 32 * log (3 * u x + x) + 8 * log (8 * u x) - 28 * log (u x + x)) / 35

/-- The mean entropy of the state is `E3`. -/
theorem meanTripleEntropy_eq_E3 (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanTripleEntropy alpha beta = E3 x :=
  meanTripleEntropy_family x alpha beta hα hβ

theorem hasDerivAt_u (x : ℝ) : HasDerivAt u (-1 / 15) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)).div_const 30
  convert h using 1
  · ext y; simp [u]
  · ring

theorem hasDerivAt_aff (p q x : ℝ) : HasDerivAt (fun y => p * u y + q * y) (p * (-1 / 15) + q) x := by
  have h := ((hasDerivAt_u x).const_mul p).add ((hasDerivAt_id x).const_mul q)
  simp only [mul_one] at h
  exact h

theorem hasDerivAt_negMulLog_aff (p q x : ℝ) (h : p * u x + q * x ≠ 0) :
    HasDerivAt (fun y => negMulLog (p * u y + q * y))
      ((-log (p * u x + q * x) - 1) * (p * (-1 / 15) + q)) x := by
  have := HasDerivAt.comp x (hasDerivAt_negMulLog h) (hasDerivAt_aff p q x)
  exact this

theorem hasDerivAt_log_aff (p q x : ℝ) (h : p * u x + q * x ≠ 0) :
    HasDerivAt (fun y => log (p * u y + q * y)) ((p * (-1 / 15) + q) / (p * u x + q * x)) x :=
  (hasDerivAt_aff p q x).log h

theorem u_pos {x : ℝ} (h : x < 1 / 2) : 0 < u x := by unfold u; linarith

theorem hasDerivAt_E3 {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) : HasDerivAt E3 (E3d x) x := by
  have hu := u_pos h1
  have d1 := hasDerivAt_negMulLog_aff 4 0 x (by simp; positivity)
  have d2 := hasDerivAt_negMulLog_aff 3 1 x (by positivity)
  have d3 := hasDerivAt_negMulLog_aff 8 0 x (by simp; positivity)
  have d4 := hasDerivAt_negMulLog_aff 1 1 x (by positivity)
  simp only [zero_mul, add_zero, one_mul] at d1 d2 d3 d4
  have := (((d1.const_mul 195).add (d2.const_mul 40)).add (d3.const_mul 15)).add (d4.const_mul 30)
  have := this.div_const 35
  convert this using 1
  · ext y; simp [E3]
  · simp only [E3d]; ring


/-- The derivative of `E3d`; every term is negative. -/
noncomputable def E3dd (x : ℝ) : ℝ :=
  (-(52 * (4 / 15) / (4 * u x)) - 32 * (4 / 5) / (3 * u x + x) - 8 * (8 / 15) / (8 * u x) -
    28 * (14 / 15) / (u x + x)) / 35

theorem hasDerivAt_E3d {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) : HasDerivAt E3d (E3dd x) x := by
  have hu := u_pos h1
  have d1 := hasDerivAt_log_aff 4 0 x (by simp; positivity)
  have d2 := hasDerivAt_log_aff 3 1 x (by positivity)
  have d3 := hasDerivAt_log_aff 8 0 x (by simp; positivity)
  have d4 := hasDerivAt_log_aff 1 1 x (by positivity)
  simp only [zero_mul, add_zero, one_mul] at d1 d2 d3 d4
  have := ((((d1.const_mul 52).sub (d2.const_mul 32)).add (d3.const_mul 8)).sub
    (d4.const_mul 28)).div_const 35
  convert this using 1
  · ext y; simp [E3d]
  · simp only [E3dd]; ring

theorem E3dd_neg {x : ℝ} (h1 : x < 1 / 2) (h0 : 0 ≤ x) : E3dd x < 0 := by
  have hu := u_pos h1
  unfold E3dd
  have a : 0 < 52 * (4 / 15) / (4 * u x) := by positivity
  have b : 0 < 32 * (4 / 5) / (3 * u x + x) := by positivity
  have c : 0 < 8 * (8 / 15) / (8 * u x) := by positivity
  have d : 0 < 28 * (14 / 15) / (u x + x) := by positivity
  linarith

theorem E3d_strictAntiOn : StrictAntiOn E3d (Set.Ico 0 (1 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 (1 / 2))
  · intro x hx
    exact (hasDerivAt_E3d hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    rw [(hasDerivAt_E3d hx.1.le hx.2).deriv]
    exact E3dd_neg hx.2 hx.1.le

theorem E3d_eq_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) :
    E3d x = log ((4 * u x) ^ 52 * (8 * u x) ^ 8 / ((3 * u x + x) ^ 32 * (u x + x) ^ 28)) / 35 := by
  have hu := u_pos h1
  have h1' : 0 < 4 * u x := by positivity
  have h2' : 0 < 3 * u x + x := by positivity
  have h3' : 0 < 8 * u x := by positivity
  have h4' : 0 < u x + x := by positivity
  have e : log ((4 * u x) ^ 52 * (8 * u x) ^ 8 / ((3 * u x + x) ^ 32 * (u x + x) ^ 28)) =
      52 * log (4 * u x) + 8 * log (8 * u x) - 32 * log (3 * u x + x) - 28 * log (u x + x) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (x := (4 * u x) ^ 52) (y := (8 * u x) ^ 8) (by positivity) (by positivity),
      Real.log_mul (x := (3 * u x + x) ^ 32) (y := (u x + x) ^ 28) (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [e]
  unfold E3d
  ring

theorem E3d_zero_pos : 0 < E3d 0 := by
  rw [E3d_eq_log le_rfl (by norm_num)]
  apply div_pos _ (by norm_num)
  apply Real.log_pos
  rw [one_lt_div (by unfold u; positivity)]
  unfold u
  norm_num

theorem E3d_ico_neg : E3d (37 / 524) < 0 := by
  rw [E3d_eq_log (by norm_num) (by norm_num)]
  apply div_neg_of_neg_of_pos _ (by norm_num)
  apply Real.log_neg (by unfold u; positivity)
  rw [div_lt_one (by unfold u; positivity)]
  unfold u
  norm_num


theorem continuous_E3 : Continuous E3 := by
  unfold E3 u
  fun_prop

/-- `E3d` has a unique zero `c` on `[0, 1/2)`, and it lies strictly between `0` and `37/524`. -/
theorem exists_zero_E3d : ∃ c, 0 < c ∧ c < 37 / 524 ∧ E3d c = 0 := by
  have hcont : ContinuousOn E3d (Set.Icc 0 (37 / 524)) := fun x hx =>
    (hasDerivAt_E3d hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 37 / 524) hcont
    ⟨E3d_ico_neg.le, E3d_zero_pos.le⟩
  refine ⟨c, ?_, ?_, hc0⟩
  · rcases hc.1.eq_or_lt with h | h
    · rw [← h] at hc0; exact absurd hc0 E3d_zero_pos.ne'
    · exact h
  · rcases hc.2.eq_or_lt with h | h
    · rw [h] at hc0; exact absurd hc0 E3d_ico_neg.ne
    · exact h

/-- **The entropy maximiser of the family.** `E3` has a unique maximiser `c` on `[0, 1/2]`; it lies
strictly between `0` and the purity minimiser `37/524`, and `E3` decreases strictly on
`[c, 1/2]`. In particular `E3 (37/524) < E3 c`: the icosahedral state `x = 37/524` is not the entropy
maximiser even within the family, and decreasing `x` from `37/524` increases `E3`. -/
theorem E3_unique_max : ∃ c, 0 < c ∧ c < 37 / 524 ∧ (∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧
    (∀ y, c ≤ y → y < 37 / 524 → E3 (37 / 524) < E3 y) ∧ E3 (37 / 524) < E3 c := by
  obtain ⟨c, hc0, hc1, hcz⟩ := exists_zero_E3d
  have hc2 : c < 1 / 2 := by linarith
  have hpos : ∀ x ∈ Set.Ico 0 c, 0 < E3d x := fun x hx => by
    have := E3d_strictAntiOn ⟨hx.1, by linarith [hx.2]⟩ ⟨hc0.le, hc2⟩ hx.2
    rwa [hcz] at this
  have hneg : ∀ x ∈ Set.Ioo c (1 / 2), E3d x < 0 := fun x hx => by
    have := E3d_strictAntiOn ⟨hc0.le, hc2⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1
    rwa [hcz] at this
  have hmono : StrictMonoOn E3 (Set.Icc 0 c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 c) continuous_E3.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_E3 hx.1.le (by linarith [hx.2])).deriv]
    exact hpos x ⟨hx.1.le, hx.2⟩
  have hanti : StrictAntiOn E3 (Set.Icc c (1 / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c (1 / 2)) continuous_E3.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_E3 (by linarith [hx.1]) hx.2).deriv]
    exact hneg x hx
  refine ⟨c, hc0, hc1, ?_, ?_, ?_⟩
  · intro y hy hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hmono ⟨hy.1, h.le⟩ ⟨hc0.le, le_rfl⟩ h
    · exact hanti ⟨le_rfl, hc2.le⟩ ⟨h.le, hy.2⟩ h
  · intro y hy1 hy2
    exact hanti ⟨hy1, by linarith⟩ ⟨by linarith, by norm_num⟩ hy2
  · exact hanti ⟨le_rfl, hc2.le⟩ ⟨hc1.le, by norm_num⟩ hc1


/-- `E3` is strictly concave on `[0, 1/2]`. -/
theorem E3_strictConcaveOn : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) (1 / 2)) E3 := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 (1 / 2)) continuous_E3.continuousOn ?_
  rw [interior_Icc]
  intro x hx y hy hxy
  simp only [Set.mem_Ioo] at hx hy
  rw [(hasDerivAt_E3 hx.1.le hx.2).deriv, (hasDerivAt_E3 hy.1.le hy.2).deriv]
  exact E3d_strictAntiOn ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ hxy

end FormalResearch.FourQubitEntropy.SevenQubitIco
