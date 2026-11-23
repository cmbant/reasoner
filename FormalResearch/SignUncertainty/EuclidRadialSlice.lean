module

public import FormalResearch.SignUncertainty.EuclidSplit
public import FormalResearch.Special.BesselPoisson

/-!
# One-dimensional reductions for the radial Fourier transform

* `poissonW n t = (1-t²)^{(n-2)/2}`, the Poisson weight of `ℝ^n`;
* `sinpow_exp_integral`: `∫_{(0,π)} sin^{n-1}θ e^{-i a cos θ} dθ = ∫_{(-1,1)} w(t) e^{-i a t} dt`;
* `poissonW_exp_integral`: `∫_{(-1,1)} w(t) e^{-i a t} dt = ∫_{-1}^1 w(t) cos(a t) dt` (the odd part vanishes).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The Poisson weight `(1 - t²)^{(n-2)/2}` (`n ≥ 1`). -/
noncomputable def poissonW (n : ℕ) (t : ℝ) : ℝ := (1 - t ^ 2) ^ (((n : ℝ) - 2) / 2)

lemma poissonW_even (n : ℕ) (t : ℝ) : poissonW n (-t) = poissonW n t := by
  simp [poissonW]

/-- The substitution `t = cos θ`: `∫_{(0,π)} sin^{n-1}θ e^{-i a cos θ} dθ = ∫_{(-1,1)} (1-t²)^{(n-2)/2} e^{-i a t} dt`. -/
lemma sinpow_exp_integral (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    ∫ θ in Ioo (0 : ℝ) Real.pi, ((Real.sin θ ^ (n - 1) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (a : ℂ) * (Real.cos θ : ℂ))) =
      ∫ t in Ioo (-1 : ℝ) 1, (poissonW n t : ℂ) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ))) := by
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, HasDerivWithinAt Real.cos (-Real.sin θ) (Ioo 0 Real.pi) θ :=
    fun θ _ => (Real.hasDerivAt_cos θ).hasDerivWithinAt
  have hinj : InjOn Real.cos (Ioo (0 : ℝ) Real.pi) := fun x hx y hy hxy =>
    Real.injOn_cos (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy
  have him : Real.cos '' Ioo (0 : ℝ) Real.pi = Ioo (-1 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have h0 := Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩ (Ioo_subset_Icc_self hθ) hθ.1
      have h1 := Real.strictAntiOn_cos (Ioo_subset_Icc_self hθ) ⟨Real.pi_pos.le, le_refl _⟩ hθ.2
      rw [Real.cos_zero] at h0
      rw [Real.cos_pi] at h1
      exact ⟨h1, h0⟩
    · intro ht
      refine ⟨Real.arccos t, ⟨Real.arccos_pos.mpr ht.2, Real.arccos_lt_pi.mpr ht.1⟩, ?_⟩
      exact Real.cos_arccos ht.1.le ht.2.le
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun t : ℝ => (poissonW n t : ℂ) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ))))
  rw [him] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  simp only [abs_neg, abs_of_pos hsin, Complex.real_smul, poissonW]
  have e1 : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by rw [Real.sin_sq]
  rw [e1]
  have e2 : (Real.sin θ ^ 2) ^ (((n : ℝ) - 2) / 2) = Real.sin θ ^ ((n : ℝ) - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hsin.le]; congr 1; push_cast; ring
  have e3 : Real.sin θ * Real.sin θ ^ ((n : ℝ) - 2) = Real.sin θ ^ (n - 1) := by
    have : Real.sin θ * Real.sin θ ^ ((n : ℝ) - 2) = Real.sin θ ^ ((n : ℝ) - 2 + 1) := by
      rw [mul_comm]; exact (Real.rpow_add_one hsin.ne' _).symm
    rw [this, show (n : ℝ) - 2 + 1 = ((n - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hn]; push_cast; ring, Real.rpow_natCast]
  rw [e2, ← e3]
  push_cast
  ring

lemma intervalIntegrable_poissonW (n : ℕ) (hn : 1 ≤ n) : IntervalIntegrable (poissonW n) volume (-1) 1 := by
  have ha : (-1 : ℝ) < ((n : ℝ) - 2) / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact FormalResearch.Special.intervalIntegrable_one_sub_sq_rpow_neg ha

/-- The odd part vanishes: `∫_{-1}^1 w(t) sin(a t) dt = 0`. -/
lemma integral_poissonW_sin (n : ℕ) (a : ℝ) :
    ∫ t in (-1 : ℝ)..1, poissonW n t * Real.sin (a * t) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun t : ℝ => poissonW n t * Real.sin (a * t))
  simp only [neg_neg, poissonW_even, mul_neg, Real.sin_neg] at h
  have h2 : ∫ t in (-1 : ℝ)..1, -(poissonW n t * Real.sin (a * t)) =
      -∫ t in (-1 : ℝ)..1, poissonW n t * Real.sin (a * t) := intervalIntegral.integral_neg
  have h3 : (∫ t in (-1 : ℝ)..1, -(poissonW n t * Real.sin (a * t))) =
      ∫ t in (-1 : ℝ)..1, poissonW n t * Real.sin (a * t) := by
    exact h
  linarith

lemma poissonW_exp_integral (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    ∫ t in Ioo (-1 : ℝ) 1, (poissonW n t : ℂ) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ))) =
      ((∫ t in (-1 : ℝ)..1, poissonW n t * Real.cos (a * t) : ℝ) : ℂ) := by
  have hw := intervalIntegrable_poissonW n hn
  have hc : IntervalIntegrable (fun t : ℝ => poissonW n t * Real.cos (a * t)) volume (-1) 1 :=
    hw.mul_continuousOn (g := fun t : ℝ => Real.cos (a * t)) (by fun_prop)
  have hs : IntervalIntegrable (fun t : ℝ => poissonW n t * Real.sin (a * t)) volume (-1) 1 :=
    hw.mul_continuousOn (g := fun t : ℝ => Real.sin (a * t)) (by fun_prop)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  have hpt : ∀ t : ℝ, (poissonW n t : ℂ) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ))) =
      ((poissonW n t * Real.cos (a * t) : ℝ) : ℂ) - Complex.I * ((poissonW n t * Real.sin (a * t) : ℝ) : ℂ) := by
    intro t
    have : -(Complex.I * (a : ℂ) * (t : ℂ)) = ((-(a * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have h1 : IntervalIntegrable (fun t : ℝ => ((poissonW n t * Real.cos (a * t) : ℝ) : ℂ)) volume (-1) 1 := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hc |>.ofReal (𝕜 := ℂ))
  have h2 : IntervalIntegrable (fun t : ℝ => ((poissonW n t * Real.sin (a * t) : ℝ) : ℂ)) volume (-1) 1 := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hs |>.ofReal (𝕜 := ℂ))
  have h2' : IntervalIntegrable (fun t : ℝ => Complex.I * ((poissonW n t * Real.sin (a * t) : ℝ) : ℂ))
      volume (-1) 1 := h2.const_mul Complex.I
  have e1 : ∫ t in (-1 : ℝ)..1, ((poissonW n t * Real.cos (a * t) : ℝ) : ℂ) =
      ((∫ t in (-1 : ℝ)..1, poissonW n t * Real.cos (a * t) : ℝ) : ℂ) := intervalIntegral.integral_ofReal
  have e2 : ∫ t in (-1 : ℝ)..1, ((poissonW n t * Real.sin (a * t) : ℝ) : ℂ) =
      ((∫ t in (-1 : ℝ)..1, poissonW n t * Real.sin (a * t) : ℝ) : ℂ) := intervalIntegral.integral_ofReal
  have e3 : ∫ t in (-1 : ℝ)..1, Complex.I * ((poissonW n t * Real.sin (a * t) : ℝ) : ℂ) =
      Complex.I * ((∫ t in (-1 : ℝ)..1, poissonW n t * Real.sin (a * t) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_const_mul, e2]
  have e4 : ∫ t in (-1 : ℝ)..1, (poissonW n t : ℂ) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ))) =
      ∫ t in (-1 : ℝ)..1, (((poissonW n t * Real.cos (a * t) : ℝ) : ℂ) -
        Complex.I * ((poissonW n t * Real.sin (a * t) : ℝ) : ℂ)) :=
    intervalIntegral.integral_congr (fun t _ => hpt t)
  rw [e4, intervalIntegral.integral_sub h1 h2', e1, e3, integral_poissonW_sin n a]
  simp

end FormalResearch.SignUncertainty
