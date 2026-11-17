module

public import FormalResearch.Special.LatticePsi

/-!
# Properties of the phase `arg Γ(½ + is)` used by the lattice lemma

Source: `constants.tex`, proof of `lem:latticesum`.  For `A = argGammaHalf` and `p(s) = (ψ(½+is)+ψ(½-is))/2`:

* `argGammaHalf_neg`, `argGammaHalf_real` : `A` is odd and real on `ℝ`;
* `hasDerivAt_phaseDeriv` : `p` is differentiable on `|Im s| < ½` with derivative of norm `≤ 16 ∑ k⁻²`
  on `|Im s| ≤ ¼` (this is the bound on `τ₀''` needed by the contour shift);
* `phaseDeriv_real` : `p(x) = Re ψ(½+ix)` for real `x`;
* `re_phaseDeriv_ge`, `re_phaseDeriv_le` : `Re p ≥ -3` on `ℝ` and `Re p(u+iv) ≤ log(1+|u|) + 5` on `|v| ≤ ¼`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes

local notation "γ" => Real.eulerMascheroniConstant

/-- `p(s) = (ψ(½+is)+ψ(½-is))/2 = (arg Γ(½+is))'`. -/
noncomputable def phaseDeriv (s : ℂ) : ℂ := (digamma (1 / 2 + I * s) + digamma (1 / 2 - I * s)) / 2

lemma conj_two : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2

lemma phTerm_neg (k : ℕ) (s : ℂ) : phTerm k (-s) = -phTerm k s := by
  unfold phTerm
  have h1 : (k : ℂ) + 1 / 2 + I * -s = (k : ℂ) + 1 / 2 - I * s := by ring
  have h2 : (k : ℂ) + 1 / 2 - I * -s = (k : ℂ) + 1 / 2 + I * s := by ring
  rw [h1, h2]; ring

theorem argGammaHalf_neg (s : ℂ) : argGammaHalf (-s) = -argGammaHalf s := by
  unfold argGammaHalf
  simp_rw [phTerm_neg]
  rw [tsum_neg]; ring

lemma arg_ne_pi_of_re_pos {z : ℂ} (hz : 0 < z.re) : z.arg ≠ Real.pi := by
  intro h
  have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [h, abs_of_pos Real.pi_pos] at this
  linarith [Real.pi_pos]

lemma conj_phTerm_real (k : ℕ) (x : ℝ) : starRingEnd ℂ (phTerm k x) = phTerm k x := by
  unfold phTerm
  have hp : 0 < (((k : ℂ) + 1 / 2 + I * x)).re := by simp; positivity
  have hm : 0 < (((k : ℂ) + 1 / 2 - I * x)).re := by simp; positivity
  have c1 : starRingEnd ℂ ((k : ℂ) + 1 / 2 + I * x) = (k : ℂ) + 1 / 2 - I * x := by
    simp [Complex.conj_ofReal, conj_two, sub_eq_add_neg]
  have c2 : starRingEnd ℂ ((k : ℂ) + 1 / 2 - I * x) = (k : ℂ) + 1 / 2 + I * x := by
    simp [Complex.conj_ofReal, conj_two]
  have l1 : starRingEnd ℂ (Complex.log ((k : ℂ) + 1 / 2 + I * x)) =
      Complex.log ((k : ℂ) + 1 / 2 - I * x) := by
    rw [← c1, ← Complex.log_conj _ (arg_ne_pi_of_re_pos hp)]
  have l2 : starRingEnd ℂ (Complex.log ((k : ℂ) + 1 / 2 - I * x)) =
      Complex.log ((k : ℂ) + 1 / 2 + I * x) := by
    rw [← c2, ← Complex.log_conj _ (arg_ne_pi_of_re_pos hm)]
  have hc : starRingEnd ℂ (1 / (2 * I)) = -(1 / (2 * I)) := by
    simp [map_div₀, conj_two]
  rw [map_sub, map_mul, map_sub, l1, l2, hc]
  have : starRingEnd ℂ ((x : ℂ) / ((k : ℂ) + 1)) = (x : ℂ) / ((k : ℂ) + 1) := by
    simp [map_div₀, conj_two]
  rw [this]; ring

theorem argGammaHalf_real (x : ℝ) : (argGammaHalf x).im = 0 := by
  have : starRingEnd ℂ (argGammaHalf x) = argGammaHalf x := by
    unfold argGammaHalf
    rw [map_add, map_mul, RCLike.conj_tsum]
    simp_rw [conj_phTerm_real]
    simp [Complex.conj_ofReal, conj_two]
  exact Complex.conj_eq_iff_im.mp this

lemma re_pos_one_half_add {s : ℂ} (hs : |s.im| < 1 / 2) : 0 < (1 / 2 + I * s).re := by
  have := (abs_lt.mp hs).2; simp; linarith

lemma re_pos_one_half_sub {s : ℂ} (hs : |s.im| < 1 / 2) : 0 < (1 / 2 - I * s).re := by
  have := (abs_lt.mp hs).1; simp; linarith

theorem phaseDeriv_real (x : ℝ) : phaseDeriv x = ((digamma (1 / 2 + I * x)).re : ℂ) := by
  have hz : 0 < (1 / 2 + I * (x : ℂ)).re := by simp
  have hc : (1 / 2 - I * (x : ℂ)) = starRingEnd ℂ (1 / 2 + I * (x : ℂ)) := by
    simp [Complex.conj_ofReal, conj_two, sub_eq_add_neg]
  unfold phaseDeriv
  rw [hc, digamma_conj hz]
  apply Complex.ext <;> simp

theorem hasDerivAt_argGammaHalf' {s : ℂ} (hs : |s.im| < 1 / 2) :
    HasDerivAt argGammaHalf (phaseDeriv s) s := hasDerivAt_argGammaHalf hs

/-- Derivatives of the terms of the derivative series. -/
noncomputable def phTermDeriv2 (k : ℕ) (s : ℂ) : ℂ :=
  (I / 2) * (1 / ((k : ℂ) + 1 / 2 + I * s) ^ 2 - 1 / ((k : ℂ) + 1 / 2 - I * s) ^ 2)

lemma hasDerivAt_phTermDeriv (k : ℕ) {s : ℂ} (hs : |s.im| < 1 / 2) :
    HasDerivAt (phTermDeriv k) (phTermDeriv2 k s) s := by
  have h1 : HasDerivAt (fun s : ℂ => (k : ℂ) + 1 / 2 + I * s) I s :=
    (((hasDerivAt_id s).const_mul I).const_add _).congr_deriv (by simp)
  have h2 : HasDerivAt (fun s : ℂ => (k : ℂ) + 1 / 2 - I * s) (-I) s :=
    (((hasDerivAt_id s).const_mul I).const_sub _).congr_deriv (by simp)
  have e1 := slitPlane_ne_zero (mem_slit_plus (k := k) hs)
  have e2 := slitPlane_ne_zero (mem_slit_minus (k := k) hs)
  have i1 := h1.inv e1
  have i2 := h2.inv e2
  have h3 := ((i1.add i2).const_mul (1 / 2 : ℂ)).const_sub (1 / ((k : ℂ) + 1))
  have : phTermDeriv k = fun s : ℂ => 1 / ((k : ℂ) + 1) - (1 / 2 : ℂ) *
      (((k : ℂ) + 1 / 2 + I * s)⁻¹ + ((k : ℂ) + 1 / 2 - I * s)⁻¹) := by
    ext w; unfold phTermDeriv; simp [one_div]
  rw [this]
  refine h3.congr_deriv ?_
  unfold phTermDeriv2
  field_simp
  ring

lemma norm_phTermDeriv2_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ}
    (hs : |s.im| ≤ 1 / 2 - δ) (k : ℕ) :
    ‖phTermDeriv2 k s‖ ≤ 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have him := abs_le.mp hs
  have key : ∀ z : ℂ, δ * ((k : ℝ) + 1) ≤ z.re → ‖1 / z ^ 2‖ ≤ 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro z hz
    have hzn : δ * ((k : ℝ) + 1) ≤ ‖z‖ := le_trans hz (Complex.re_le_norm _)
    rw [norm_div, norm_pow, norm_one]
    have hpos : 0 < δ * ((k : ℝ) + 1) := by positivity
    calc 1 / ‖z‖ ^ 2 ≤ 1 / (δ * ((k : ℝ) + 1)) ^ 2 := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_left₀ hpos.le hzn 2
      _ = 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by field_simp
  have e1 := key ((k : ℂ) + 1 / 2 + I * s) (by rw [re_add_I_mul]; nlinarith [him.1, him.2])
  have e2 := key ((k : ℂ) + 1 / 2 - I * s) (by rw [re_sub_I_mul]; nlinarith [him.1, him.2])
  unfold phTermDeriv2
  rw [norm_mul, norm_div, Complex.norm_I]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have := norm_sub_le (1 / ((k : ℂ) + 1 / 2 + I * s) ^ 2) (1 / ((k : ℂ) + 1 / 2 - I * s) ^ 2)
  have hnn : 0 ≤ 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by positivity
  calc 1 / 2 * ‖1 / ((k : ℂ) + 1 / 2 + I * s) ^ 2 - 1 / ((k : ℂ) + 1 / 2 - I * s) ^ 2‖
      ≤ 1 / 2 * (1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) + 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    _ = _ := by ring

lemma phaseDeriv_eq_series {s : ℂ} (hs : |s.im| < 1 / 2) :
    phaseDeriv s = -(γ : ℂ) + ∑' k : ℕ, phTermDeriv k s := by
  have hre1 := re_pos_one_half_add hs
  have hre2 := re_pos_one_half_sub hs
  unfold phaseDeriv
  rw [digamma_eq_series hre1, digamma_eq_series hre2]
  have s1 : Summable (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 / 2 + I * s))) :=
    summable_psiTerm hre1.le
  have s2 : Summable (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 / 2 - I * s))) :=
    summable_psiTerm hre2.le
  simp_rw [phTermDeriv_eq]
  rw [tsum_mul_left, Summable.tsum_add s1 s2]
  ring

/-- Second derivative of the phase: termwise differentiation of the derivative series. -/
theorem hasDerivAt_phaseDeriv {s : ℂ} (hs : |s.im| < 1 / 2) :
    HasDerivAt phaseDeriv (∑' k : ℕ, phTermDeriv2 k s) s := by
  set δ : ℝ := min (1 / 4) ((1 / 2 - |s.im|) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ (1 / 2 - |s.im|) / 2 := min_le_right _ _
  have hδ4 : δ ≤ 1 / 4 := min_le_left _ _
  set U : Set ℂ := {w | |w.im| < 1 / 2 - δ}
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hUc : Convex ℝ U := by
    have : U = {w : ℂ | w.im ∈ Ioo (-(1 / 2 - δ)) (1 / 2 - δ)} := by
      ext w; simp [U, abs_lt]
    rw [this]
    exact (convex_Ioo _ _).linear_preimage Complex.imLm
  have hzU : s ∈ U := by show |s.im| < 1 / 2 - δ; linarith
  have h0U : (0 : ℂ) ∈ U := by show |(0 : ℂ).im| < 1 / 2 - δ; simp; linarith
  have hUs : ∀ w ∈ U, |w.im| < 1 / 2 := fun w hw => by have : |w.im| < 1 / 2 - δ := hw; linarith
  have hsum : Summable (fun k : ℕ => 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
    refine Summable.mul_left _ ?_
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hder : ∀ (k : ℕ), ∀ y ∈ U, HasDerivAt (phTermDeriv k) (phTermDeriv2 k y) y :=
    fun k y hy => hasDerivAt_phTermDeriv k (hUs y hy)
  have hbd : ∀ (k : ℕ), ∀ y ∈ U, ‖phTermDeriv2 k y‖ ≤ 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) :=
    fun k y hy => norm_phTermDeriv2_le hδ0 hδ1 (le_of_lt hy) k
  have h0sum : Summable (fun k : ℕ => phTermDeriv k 0) := by
    have h1 := summable_psiTerm (z := (1 / 2 : ℂ)) (by simp)
    have : (fun k : ℕ => phTermDeriv k 0) = fun k => psiTerm (1 / 2 : ℂ) k := by
      ext k; unfold phTermDeriv psiTerm
      simp only [mul_zero, add_zero, sub_zero]; ring
    rw [this]; exact h1
  have hd := hasDerivAt_tsum_of_isPreconnected hsum hUo hUc.isPreconnected hder hbd h0U h0sum hzU
  refine (hd.const_add (-(γ : ℂ))).congr_of_eventuallyEq ?_
  filter_upwards [hUo.mem_nhds hzU] with w hw
  exact phaseDeriv_eq_series (hUs w hw)

/-- `‖(arg Γ)'' ‖ ≤ 16 ∑ k⁻²` on `|Im s| ≤ ¼`. -/
theorem norm_phaseDeriv2_le {s : ℂ} (hs : |s.im| ≤ 1 / 4) :
    ‖∑' k : ℕ, phTermDeriv2 k s‖ ≤ 16 * invSqSum := by
  have hsum : Summable (fun k : ℕ => 1 / (1 / 4 : ℝ) ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
    refine Summable.mul_left _ ?_
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have h := tsum_of_norm_bounded (f := fun k => phTermDeriv2 k s) hsum.hasSum
    (fun k => norm_phTermDeriv2_le (δ := 1 / 4) (by norm_num) (by norm_num) (by norm_num; exact hs) k)
  refine h.trans (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold invSqSum
  norm_num

lemma re_one_half_add_I_mul {s : ℂ} : (1 / 2 + I * s).re = 1 / 2 - s.im := by simp [sub_eq_add_neg]
lemma im_one_half_add_I_mul {s : ℂ} : (1 / 2 + I * s).im = s.re := by simp

/-- Lower bound on the real axis: `p(x) = Re ψ(½ + ix) ≥ -3`. -/
theorem re_phaseDeriv_ge (x : ℝ) : -3 ≤ (phaseDeriv x).re := by
  rw [phaseDeriv_real]
  simp only [Complex.ofReal_re]
  have := re_digamma_half_line_ge x
  have e : (1 / 2 + (x : ℂ) * I) = 1 / 2 + I * x := by ring
  rw [e] at this; exact this

/-- Upper bound near the real axis: `Re p(u + iv) ≤ log(1+|u|) + 5` for `|v| ≤ ¼`. -/
theorem re_phaseDeriv_le {s : ℂ} (hs : |s.im| ≤ 1 / 4) :
    (phaseDeriv s).re ≤ Real.log (1 + |s.re|) + 5 := by
  have him := abs_le.mp hs
  have hs' : |s.im| < 1 / 2 := by linarith
  have e1 : (1 / 2 + I * s) = (((1 / 2 - s.im : ℝ) : ℂ) + (s.re : ℂ) * I) := by
    apply Complex.ext <;> simp [sub_eq_add_neg]
  have e2 : (1 / 2 - I * s) = starRingEnd ℂ (((1 / 2 + s.im : ℝ) : ℂ) + (s.re : ℂ) * I) := by
    apply Complex.ext <;> simp
  have hpos : 0 < (((1 / 2 + s.im : ℝ) : ℂ) + (s.re : ℂ) * I).re := by simp; linarith
  have u1 := re_digamma_upper (x := 1 / 2 - s.im) (y := s.re) (by linarith) (by linarith)
  have u2 := re_digamma_upper (x := 1 / 2 + s.im) (y := s.re) (by linarith) (by linarith)
  unfold phaseDeriv
  rw [e2, digamma_conj hpos, e1]
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.conj_re]
  linarith

end FormalResearch.Special.Lattice
