import Mathlib

/-!
# A Stieltjes representation of `x^q`, `1 < q < 2`

Paper E, `lem:fqe-renyi-determinant` (`sup_renyi.tex`, `sec:sup-determinant`).  The paper proves that
`H_q` is increasing in the spectral determinant at fixed `e₁, e₂, e₃` by differentiating the roots of
`z⁴ - z³ + e₂z² - e₃z + d` and using positivity of a third divided difference of `x^{q-1}`.
Here the same monotonicity is obtained without roots, from the Stieltjes (Bernstein) representation

`x^q · I(q) = ∫₀^∞ s^{q-2} x²/(x+s) ds`,  `I(q) = ∫₀^∞ u^{q-2}/(1+u) du ∈ (0, ∞)`,

for `1 < q < 2` and `x ≥ 0` (`stieltjes_rpow`): the kernel is a mixture of `x²/(x+s)`, whose sum over the
four eigenvalues depends on the spectrum only through the determinant (`RenyiFullDetMono.lean`).
-/

open MeasureTheory Set

namespace FormalResearch.FourQubitEntropy.RenyiFull

/-- The Stieltjes kernel `u^{q-2}/(1+u)`. -/
noncomputable def stKer (q u : ℝ) : ℝ := u ^ (q - 2) / (1 + u)

theorem stKer_meas (q : ℝ) : Measurable (stKer q) :=
  (measurable_id.pow_const (q - 2)).div (measurable_const.add measurable_id)

theorem stKer_nonneg (q : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ stKer q u := by
  unfold stKer
  have : 0 ≤ u ^ (q - 2) := Real.rpow_nonneg hu _
  positivity

theorem stKer_integrableOn {q : ℝ} (h1 : 1 < q) (h2 : q < 2) :
    IntegrableOn (stKer q) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hu; by_cases h : u ≤ 1
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr (not_le.1 h)
    · rintro (⟨hu, -⟩ | hu); exact hu; linarith
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun u : ℝ => u ^ (q - 2)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine Integrable.mono' hi (stKer_meas q).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := hu.1
    rw [Real.norm_of_nonneg (stKer_nonneg q hu0.le)]
    unfold stKer
    have : 0 ≤ u ^ (q - 2) := Real.rpow_nonneg hu0.le _
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · have hi : IntegrableOn (fun u : ℝ => u ^ (q - 3)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    refine Integrable.mono' hi (stKer_meas q).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := by have := hu.out; linarith
    rw [Real.norm_of_nonneg (stKer_nonneg q hu0.le)]
    unfold stKer
    have e : u ^ (q - 3) = u ^ (q - 2) / u := by
      rw [show q - 3 = (q - 2) - 1 by ring, Real.rpow_sub hu0, Real.rpow_one]
    rw [e]
    have : 0 ≤ u ^ (q - 2) := Real.rpow_nonneg hu0.le _
    apply div_le_div_of_nonneg_left this hu0 (by linarith)


/-- `I(q) = ∫₀^∞ u^{q-2}/(1+u) du`. -/
noncomputable def stI (q : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), stKer q u

theorem stI_pos {q : ℝ} (h1 : 1 < q) (h2 : q < 2) : 0 < stI q := by
  unfold stI
  have hint := stKer_integrableOn h1 h2
  rw [integral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu =>
      stKer_nonneg q (le_of_lt hu))) hint]
  have : Function.support (stKer q) ⊇ Ioi 0 := by
    intro u hu
    have hu0 : 0 < u := hu
    simp only [Function.mem_support, stKer]
    have : 0 < u ^ (q - 2) := Real.rpow_pos_of_pos hu0 _
    positivity
  have h3 : (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) ≤ (volume.restrict (Ioi (0 : ℝ))) (Function.support (stKer q)) :=
    measure_mono this
  have h4 : (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) = volume (Ioi (0 : ℝ)) := by
    rw [Measure.restrict_apply_self]
  rw [h4] at h3
  have h5 : volume (Ioi (0 : ℝ)) = ⊤ := by simp
  rw [h5] at h3
  exact lt_of_lt_of_le (by simp) h3

/-- The Stieltjes integrand `s^{q-2} x²/(x+s)`. -/
noncomputable def stInt (q x s : ℝ) : ℝ := s ^ (q - 2) * (x ^ 2 / (x + s))

theorem stInt_comp {q x : ℝ} (hx : 0 < x) {u : ℝ} (hu : 0 < u) :
    stInt q x (x * u) = x ^ (q - 1) * stKer q u := by
  unfold stInt stKer
  rw [Real.mul_rpow hx.le hu.le]
  have hxq : x ^ (q - 2) = x ^ (q - 1) / x := by
    rw [show q - 2 = (q - 1) - 1 by ring, Real.rpow_sub hx, Real.rpow_one]
  rw [hxq]
  field_simp

theorem stInt_integrableOn {q x : ℝ} (h1 : 1 < q) (h2 : q < 2) (hx : 0 < x) :
    IntegrableOn (stInt q x) (Ioi 0) := by
  have h := stKer_integrableOn h1 h2
  have : IntegrableOn (fun u => stInt q x (x * u)) (Ioi 0) := by
    have h' : IntegrableOn (fun u => x ^ (q - 1) * stKer q u) (Ioi 0) := h.const_mul _
    refine h'.congr_fun (fun u hu => (stInt_comp hx hu).symm) measurableSet_Ioi
  have := (integrableOn_Ioi_comp_mul_left_iff (stInt q x) 0 hx).1 this
  simpa using this

/-- **Stieltjes representation**: for `1 < q < 2` and `x > 0`,
`x^q · I(q) = ∫₀^∞ s^{q-2} x²/(x+s) ds`. -/
theorem stieltjes_rpow {q x : ℝ} (h1 : 1 < q) (h2 : q < 2) (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), stInt q x s = x ^ q * stI q := by
  have h := integral_comp_mul_left_Ioi (stInt q x) 0 hx
  simp only [mul_zero] at h
  have e : ∫ u in Ioi (0 : ℝ), stInt q x (x * u) = x ^ (q - 1) * stI q := by
    unfold stI
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => stInt_comp hx hu)
  rw [e, smul_eq_mul] at h
  have : ∫ s in Ioi (0 : ℝ), stInt q x s = x * (x ^ (q - 1) * stI q) := by
    field_simp at h ⊢
    linarith
  rw [this]
  have : x * x ^ (q - 1) = x ^ q := by
    rw [← Real.rpow_one_add' hx.le (by linarith)]; ring_nf
  rw [← mul_assoc, this]

theorem stInt_zero (q s : ℝ) : stInt q 0 s = 0 := by unfold stInt; simp


/-- `stieltjes_rpow` for `x ≥ 0` (both sides vanish at `x = 0`). -/
theorem stieltjes_rpow_nonneg {q x : ℝ} (h1 : 1 < q) (h2 : q < 2) (hx : 0 ≤ x) :
    ∫ s in Ioi (0 : ℝ), stInt q x s = x ^ q * stI q := by
  rcases hx.eq_or_lt with h | h
  · subst h
    simp only [stInt_zero, integral_zero]
    rw [Real.zero_rpow (by linarith)]; simp
  · exact stieltjes_rpow h1 h2 h

theorem stInt_integrableOn_nonneg {q x : ℝ} (h1 : 1 < q) (h2 : q < 2) (hx : 0 ≤ x) :
    IntegrableOn (stInt q x) (Ioi 0) := by
  rcases hx.eq_or_lt with h | h
  · subst h
    have : stInt q 0 = fun _ => 0 := funext (stInt_zero q)
    rw [this]
    exact integrableOn_zero
  · exact stInt_integrableOn h1 h2 h


theorem stieltjes_alg_aux {a b c d s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hs : 0 < s) :
    a ^ 2 / (a + s) + b ^ 2 / (b + s) + c ^ 2 / (c + s) + d ^ 2 / (d + s) =
      (a + b + c + d - 4 * s) +
        s ^ 2 * ((b + s) * (c + s) * (d + s) + (a + s) * (c + s) * (d + s) +
          (a + s) * (b + s) * (d + s) + (a + s) * (b + s) * (c + s)) /
          ((a + s) * (b + s) * (c + s) * (d + s)) := by
  have h1 : a + s ≠ 0 := by positivity
  have h2 : b + s ≠ 0 := by positivity
  have h3 : c + s ≠ 0 := by positivity
  have h4 : d + s ≠ 0 := by positivity
  field_simp
  ring

end FormalResearch.FourQubitEntropy.RenyiFull
