module

public import FormalResearch.Special.LatticeGamma

/-!
# Exponential tails

`tail_integral_le` : if `f` is continuous with `‖f s‖ ≤ D e^{-a|s|}`, then `f` is integrable and
`‖∫_ℝ f - ∫_{-X}^{X} f‖ ≤ 2 D e^{-aX}/a`.  (The tail estimates `∫_ℝ φ = ∫_{-X}^X φ + O(e^{-κX})` of the
proof of `lem:latticesum`.)  `exp_neg_rpow_le` : `e^{-a L^c} ≤ C L^{-p}` (an exponential beats every power).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

theorem tail_integral_le {f : ℝ → ℂ} (hf : Continuous f) {D a X : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hX : 0 ≤ X) (hb : ∀ s, ‖f s‖ ≤ D * Real.exp (-a * |s|)) :
    Integrable f ∧ ‖(∫ s, f s) - ∫ s in (-X)..X, f s‖ ≤ 2 * D * Real.exp (-a * X) / a := by
  set g : ℝ → ℝ := fun s => D * Real.exp (-a * |s|) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hIic : IntegrableOn g (Iic (-X)) := by
    have this : IntegrableOn (fun x => D * Real.exp (a * x)) (Iic (-X)) :=
      (integrableOn_exp_mul_Iic ha (-X)).const_mul D
    refine this.congr_fun (fun s hs => ?_) measurableSet_Iic
    have : s ≤ 0 := le_trans hs (by linarith)
    simp only [hg, abs_of_nonpos this]; ring_nf
  have hIoi : IntegrableOn g (Ioi X) := by
    have this : IntegrableOn (fun x => D * Real.exp (-a * x)) (Ioi X) :=
      (integrableOn_exp_mul_Ioi (a := -a) (by linarith) X).const_mul D
    refine this.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have : 0 ≤ s := le_trans hX hs.le
    simp only [hg, abs_of_nonneg this]
  have hIoc : IntegrableOn g (Ioc (-X) X) := hgc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgi : Integrable g := by
    have h1 : IntegrableOn g (Iic (-X) ∪ Ioc (-X) X ∪ Ioi X) := (hIic.union hIoc).union hIoi
    have : Iic (-X) ∪ Ioc (-X) X ∪ Ioi X = univ := by
      ext x; simp only [mem_union, mem_Iic, mem_Ioc, mem_Ioi, mem_univ, iff_true]
      by_cases h1 : x ≤ -X
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : x ≤ X
        · exact Or.inl (Or.inr ⟨not_le.mp h1, h2⟩)
        · exact Or.inr (not_le.mp h2)
    rw [this, integrableOn_univ] at h1; exact h1
  have hfi : Integrable f := hgi.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hfi, ?_⟩
  have hsplit := integral_add_compl (measurableSet_Ioc (a := -X) (b := X)) hfi
  rw [compl_Ioc] at hsplit
  have hdisj : Disjoint (Iic (-X)) (Ioi X) := by
    rw [Set.disjoint_left]; intro x h1 h2; simp only [mem_Iic, mem_Ioi] at h1 h2; linarith
  rw [setIntegral_union hdisj measurableSet_Ioi hfi.integrableOn hfi.integrableOn] at hsplit
  rw [intervalIntegral.integral_of_le (by linarith)]
  have e : (∫ s, f s) - ∫ s in Ioc (-X) X, f s = (∫ s in Iic (-X), f s) + ∫ s in Ioi X, f s := by
    rw [← hsplit]; ring
  rw [e]
  have n1 : ‖∫ s in Iic (-X), f s‖ ≤ D * Real.exp (-a * X) / a := by
    refine (norm_integral_le_of_norm_le hIic (ae_restrict_of_forall_mem measurableSet_Iic
      (fun s _ => hb s))).trans (le_of_eq ?_)
    have : ∫ s in Iic (-X), g s = D * ∫ s in Iic (-X), Real.exp (a * s) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Iic (fun s hs => ?_)
      have : s ≤ 0 := le_trans hs (by linarith)
      simp only [hg, abs_of_nonpos this]; ring_nf
    rw [this, integral_exp_mul_Iic ha]
    ring_nf
  have n2 : ‖∫ s in Ioi X, f s‖ ≤ D * Real.exp (-a * X) / a := by
    refine (norm_integral_le_of_norm_le hIoi (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun s _ => hb s))).trans (le_of_eq ?_)
    have : ∫ s in Ioi X, g s = D * ∫ s in Ioi X, Real.exp ((-a) * s) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      have : 0 ≤ s := le_trans hX hs.le
      simp only [hg, abs_of_nonneg this]
    rw [this, integral_exp_mul_Ioi (by linarith : -a < 0)]
    field_simp
  calc _ ≤ ‖∫ s in Iic (-X), f s‖ + ‖∫ s in Ioi X, f s‖ := norm_add_le _ _
    _ ≤ _ := by
        have : 2 * D * Real.exp (-a * X) / a = D * Real.exp (-a * X) / a + D * Real.exp (-a * X) / a := by
          ring
        linarith

/-- An exponential beats every power: `e^{-a L^c} ≤ C L^{-p}` for `L ≥ 1`. -/
theorem exp_neg_rpow_le {a c p : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → Real.exp (-(a * L ^ c)) ≤ C * L ^ (-p) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (p / c)
  refine ⟨(n.factorial : ℝ) / a ^ n, by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have h1 : (a * L ^ c) ^ n / n.factorial ≤ Real.exp (a * L ^ c) := by
    have := Real.pow_div_factorial_le_exp (a * L ^ c) (by positivity) n
    exact this
  have h2 : L ^ p ≤ L ^ (c * n) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    have := (div_lt_iff₀ hc).mp hn
    nlinarith
  have h3 : (a * L ^ c) ^ n = a ^ n * L ^ (c * n) := by
    rw [mul_pow, ← Real.rpow_natCast (L ^ c) n, ← Real.rpow_mul hL0.le]
  have hfac : (0 : ℝ) < n.factorial := by positivity
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  have h4 : 1 ≤ (n.factorial : ℝ) / a ^ n * L ^ (-p) * Real.exp (a * L ^ c) := by
    have hLp : L ^ (-p) = (L ^ p)⁻¹ := Real.rpow_neg hL0.le p
    have h5 : a ^ n * L ^ p / n.factorial ≤ Real.exp (a * L ^ c) := by
      refine le_trans ?_ h1
      rw [h3]; apply div_le_div_of_nonneg_right _ hfac.le
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hLp]
    have hLpp : 0 < L ^ p := Real.rpow_pos_of_pos hL0 p
    calc (1 : ℝ) = (n.factorial : ℝ) / a ^ n * (L ^ p)⁻¹ * (a ^ n * L ^ p / n.factorial) := by
          field_simp
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left h5 (by positivity)
  linarith

end FormalResearch.Special.Lattice
