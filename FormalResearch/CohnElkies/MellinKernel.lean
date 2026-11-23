module

public import FormalResearch.Asymptotics.BinetRemainder
public import FormalResearch.Special.ComplexStirlingBinet
public import FormalResearch.CohnElkies.MellinPhaseBounds

/-!
# Mellin-Strip Kernel, Edge Remainder, and Phase Corollaries (Lemmas T.1(a), T.2(1), T.4(b), (P2)/(P4))

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`,
Lemma T.1(a) (`mat:T1`), Lemma T.2(1) (`mat:T2`, `(e33)`), Lemma T.4(b) (`(e34)`),
and the `(P2)`/`(P4)` corollaries from Lemma T.4(e).

## Main definitions
* `stripG`, `stripS0Tilde`, `stripHIntegrand`, `stripH`: Mellin-strip functions `g`, `S̃₀`, and `ℋ`.
* `mellinPhi`, `mellinK0`: the phase `Φ_Mel(ζ; ξ)` and Mellin-strip kernel `K₀(ζ, ξ)` of `(e33)`.
* `edgeR5`: the fifth-order edge remainder `R̃₅(i τ) = S̃₀(i τ) - (π² / 36) (i τ)³`.

## Main results
* `binetRem_eq_binetB`, `binetLogGamma_eq_stirling_add_binetRem`, `exp_stirling_add_binetRem_eq_gamma`:
  Lemma T.1(a) bridge between `Asymptotics.binetRem` and `ComplexStirling.binetLogGamma` / `Complex.Gamma`.
* `stripH_eq`, `mellin_strip_kernel_eq`: Lemma T.2(1) exact Mellin-strip kernel identity `(e33)`.
* `stripS0Tilde_imag`, `norm_mellinK0_imag_le`, `edgeR5_eq_imag_integral`, `norm_edgeR5_le`,
  `norm_exp_edgeR5_sub_one_le`, `one_sub_imag_rpow_neg_half_approx`: Lemma T.4(b) (`(e34)`).
* `edgePhiDeriv_phase_floor_P2`, `integral_abs_edgePhiDeriv2_le`: `(P2)`/`(P4)` phase corollaries.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace FormalResearch.CohnElkies

/-! ### Lemma T.1(a) bridge: `binetRem` ↔ `binetLogGamma` / `Complex.Gamma` -/

/-- Exact equality between `FormalResearch.Asymptotics.binetRem` and
`FormalResearch.Special.ComplexStirling.binetB` on `Re z > 0`. -/
theorem binetRem_eq_binetB {z : ℂ} (_hz : 0 < z.re) :
    FormalResearch.Asymptotics.binetRem z = FormalResearch.Special.ComplexStirling.binetB z := by
  unfold FormalResearch.Asymptotics.binetRem FormalResearch.Special.ComplexStirling.binetB
    FormalResearch.Special.ComplexStirling.lap
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : t ≠ 0 := ne_of_gt (mem_Ioi.mp ht)
  have hkern : FormalResearch.Asymptotics.muBin t =
      FormalResearch.Special.ComplexStirling.binetKernelDiv t := by
    unfold FormalResearch.Asymptotics.muBin FormalResearch.Special.ComplexStirling.binetKernelDiv
      FormalResearch.Special.ComplexStirling.binetKernel
    simp only [ht0, ↓reduceIte]
    ring
  rw [hkern, neg_mul]

/-- Stirling expansion of `binetLogGamma` in terms of `binetRem` (`mat:T1`(a)). -/
theorem binetLogGamma_eq_stirling_add_binetRem {z : ℂ} (hz : 0 < z.re) :
    FormalResearch.Special.ComplexStirling.binetLogGamma z =
      (z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetRem z := by
  rw [FormalResearch.Special.ComplexStirling.binetLogGamma, binetRem_eq_binetB hz]

/-- `exp` of Stirling's formula plus `binetRem` equals `Complex.Gamma` on `Re z > 0` (`mat:T1`(a)). -/
theorem exp_stirling_add_binetRem_eq_gamma {z : ℂ} (hz : 0 < z.re) :
    Complex.exp ((z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetRem z) = Complex.Gamma z := by
  rw [← binetLogGamma_eq_stirling_add_binetRem hz,
    FormalResearch.Special.ComplexStirling.exp_binetLogGamma hz]

/-! ### Lemma T.2(1): Exact Mellin-strip kernel identity `(e33)` -/

/-- Strip function `g(ζ) = log(tan(π ζ / 2) / (π ζ / 2))` (`0` at `ζ = 0`). -/
noncomputable def stripG (ζ : ℂ) : ℂ :=
  if ζ = 0 then 0 else Complex.log (Complex.tan (Real.pi * ζ / 2) / (Real.pi * ζ / 2))

/-- Integrated strip function `S̃₀(ζ) = ∫₀¹ g(s ζ) ζ ds`. -/
noncomputable def stripS0Tilde (ζ : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, stripG ((s : ℂ) * ζ) * ζ

/-- Integrand of `ℋ(ζ)`: `log((1 - t) tan(π t / 2) / t)` (`log(π / 2)` at `t = 0`). -/
noncomputable def stripHIntegrand (t : ℂ) : ℂ :=
  if t = 0 then Complex.log (Real.pi / 2)
  else Complex.log ((1 - t) * Complex.tan (Real.pi * t / 2) / t)

/-- `ℋ(ζ) = ∫₀¹ ℋ'(s ζ) ζ ds`. -/
noncomputable def stripH (ζ : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, stripHIntegrand ((s : ℂ) * ζ) * ζ

/-- Mellin-strip phase `Φ_Mel(ζ; ξ) = S̃₀(ζ) + ζ log(π² ξ)`. -/
noncomputable def mellinPhi (ζ : ℂ) (ξ : ℝ) : ℂ :=
  stripS0Tilde ζ + ζ * Complex.log (Real.pi ^ 2 * ξ)

/-- Mellin-strip kernel `K₀(ζ, ξ) = (1 - ζ)^{-1/2} exp(B_c(ζ)) exp(c Φ_Mel(ζ; ξ))` (`(e33)`). -/
noncomputable def mellinK0 (c : ℝ) (ζ : ℂ) (ξ : ℝ) : ℂ :=
  (1 - ζ) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ) *
    Complex.exp (c * mellinPhi ζ ξ)

private lemma real_tanh_mul_nonneg (y : ℝ) : 0 ≤ Real.tanh y * y := by
  rcases le_or_gt 0 y with hy | hy
  · rcases eq_or_lt_of_le hy with rfl | hy'
    · simp
    · exact mul_nonneg (tanh_pos_of_pos hy').le hy'.le
  · have hy' : 0 < -y := neg_pos.mpr hy
    have hneg : Real.tanh y * y = Real.tanh (-y) * (-y) := by rw [Real.tanh_neg]; ring
    rw [hneg]
    exact mul_nonneg (tanh_pos_of_pos hy').le hy'.le

private lemma re_div_pos_of_pos_mul {u w : ℂ} (hw : w ≠ 0)
    (hpos : 0 < u.re * w.re + u.im * w.im) : 0 < (u / w).re := by
  have hns : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  have hid : u.re * (w.re / Complex.normSq w) - u.im * (-w.im / Complex.normSq w) =
      (u.re * w.re + u.im * w.im) / Complex.normSq w := by
    field_simp
    ring
  rw [hid]
  exact div_pos hpos hns

private lemma tan_div_self_re_pos {t : ℂ} (ht0 : 0 ≤ t.re) (ht1 : t.re < 1) (hne : t ≠ 0) :
    0 < (Complex.tan (Real.pi * t / 2) / (Real.pi * t / 2)).re := by
  set x : ℝ := Real.pi * t.re / 2
  set y : ℝ := Real.pi * t.im / 2
  set w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hw_eq : (Real.pi : ℂ) * t / 2 = w := by
    apply Complex.ext <;> simp [w, x, y]
  have hw_ne : w ≠ 0 := by
    rw [← hw_eq]
    exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hne) two_ne_zero
  rw [hw_eq]
  rcases eq_or_lt_of_le ht0 with hre0 | hre_pos
  · have hx0 : x = 0 := by simp [x, ← hre0]
    have hy0 : y ≠ 0 := by
      intro hy0
      apply hw_ne
      apply Complex.ext <;> simp [w, hx0, hy0]
    have hw_eq' : w = (y : ℂ) * Complex.I := by simp [w, hx0]
    rw [hw_eq', Complex.tan_mul_I]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hcy : Complex.tanh (y : ℂ) = (Real.tanh y : ℂ) := by
      simp [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
        Complex.ofReal_sinh, Complex.ofReal_cosh]
    rw [mul_div_mul_right _ _ hI, hcy, ← Complex.ofReal_div, Complex.ofReal_re]
    rcases lt_or_gt_of_ne hy0 with hy_neg | hy_pos
    · have heq : Real.tanh y / y = Real.tanh (-y) / (-y) := by rw [Real.tanh_neg, neg_div_neg_eq]
      rw [heq]
      exact div_pos (tanh_pos_of_pos (neg_pos.mpr hy_neg)) (neg_pos.mpr hy_neg)
    · exact div_pos (tanh_pos_of_pos hy_pos) hy_pos
  · have hx0 : 0 < x := by dsimp [x]; positivity
    have hx_pi : x < Real.pi / 2 := by dsimp [x]; nlinarith [Real.pi_pos]
    have htan_cond : (∀ k : ℤ, (x : ℂ) ≠ (2 * k + 1) * Real.pi / 2) ∧
        ∀ l : ℤ, (y : ℂ) * Complex.I ≠ (2 * l + 1) * Real.pi / 2 := by
      constructor
      · intro k hk
        have hre := congr_arg Complex.re hk
        simp at hre
        have hk_int : (1 : ℝ) ≤ |2 * (k : ℝ) + 1| := by
          have : (2 * k + 1 : ℤ) ≠ 0 := by omega
          exact_mod_cast Int.one_le_abs this
        have hpi : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
        have h2 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
        have hbound : Real.pi / 2 ≤ |(2 * (k : ℝ) + 1) * Real.pi / 2| := by
          rw [abs_div, abs_mul, hpi, h2]
          nlinarith [Real.pi_pos]
        have hx_abs : |x| = |(2 * (k : ℝ) + 1) * Real.pi / 2| := congrArg abs hre
        rw [abs_of_pos hx0] at hx_abs
        linarith
      · intro l hl
        have hre := congr_arg Complex.re hl
        simp at hre
        have h_ne0 : (2 * (l : ℝ) + 1) ≠ 0 := by
          have : (2 * l + 1 : ℤ) ≠ 0 := by omega
          exact_mod_cast this
        have hne : (2 * (l : ℝ) + 1) * Real.pi / 2 ≠ 0 := by positivity
        exact hne hre.symm
    have htan_z : Complex.tan w = (Complex.tan (x : ℂ) + Complex.tanh (y : ℂ) * Complex.I) /
        (1 - Complex.tan (x : ℂ) * Complex.tanh (y : ℂ) * Complex.I) :=
      Complex.tan_add_mul_I (Or.inl htan_cond)
    set a : ℝ := Real.tan x
    set b : ℝ := Real.tanh y
    have ha : 0 < a := Real.tan_pos_of_pos_of_lt_pi_div_two hx0 hx_pi
    have hcosh_y : 0 < Real.cosh y := Real.cosh_pos y
    have hb1 : 1 - b ^ 2 = (Real.cosh y)⁻¹ ^ 2 := by
      dsimp [b]
      rw [Real.tanh_eq_sinh_div_cosh]
      have hch0 : Real.cosh y ≠ 0 := hcosh_y.ne'
      have hid := Real.cosh_sq_sub_sinh_sq y
      field_simp
      linarith
    have h1b2 : 0 < 1 - b ^ 2 := by rw [hb1]; positivity
    have hden_pos : 0 < 1 + a ^ 2 * b ^ 2 := by positivity
    have hw_parts : Complex.tan w =
        ((a * (1 - b ^ 2) / (1 + a ^ 2 * b ^ 2) : ℝ) : ℂ) +
          ((b * (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) : ℝ) : ℂ) * Complex.I := by
      rw [htan_z]
      have h1ab : (1 : ℂ) - ((a : ℂ) * (b : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congr_arg Complex.re h
        simp at hre
      have hcx : Complex.tan (x : ℂ) = (a : ℂ) := by simp [a, Complex.ofReal_tan]
      have hcy : Complex.tanh (y : ℂ) = (b : ℂ) := by
        simp [b, Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          Complex.ofReal_sinh, Complex.ofReal_cosh]
      rw [hcx, hcy, div_eq_iff h1ab]
      set r1 : ℝ := a * (1 - b ^ 2) / (1 + a ^ 2 * b ^ 2)
      set r2 : ℝ := b * (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2)
      have hden0 : 1 + a ^ 2 * b ^ 2 ≠ 0 := hden_pos.ne'
      have hre_id : a = r1 + a * b * r2 := by dsimp [r1, r2]; field_simp; ring
      have him_id : b = r2 - a * b * r1 := by dsimp [r1, r2]; field_simp; ring
      apply Complex.ext <;> simp <;> linarith
    refine re_div_pos_of_pos_mul hw_ne ?_
    rw [hw_parts]
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      add_zero, Complex.add_im, Complex.mul_I_im, zero_add]
    have hterm1 : 0 < a * (1 - b ^ 2) / (1 + a ^ 2 * b ^ 2) * x := by positivity
    have hterm2 : 0 ≤ b * (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) * y := by
      have hby : 0 ≤ b * y := real_tanh_mul_nonneg y
      have hfac : 0 < (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) := by positivity
      calc b * (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) * y
          = (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) * (b * y) := by ring
        _ ≥ 0 := mul_nonneg hfac.le hby
    linarith

private lemma tan_div_t_re_pos {t : ℂ} (ht0 : 0 ≤ t.re) (ht1 : t.re < 1) (hne : t ≠ 0) :
    0 < (Complex.tan (Real.pi * t / 2) / t).re := by
  have heq : Complex.tan (Real.pi * t / 2) / t =
      ((Real.pi / 2 : ℝ) : ℂ) * (Complex.tan (Real.pi * t / 2) / (Real.pi * t / 2)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (by positivity) (tan_div_self_re_pos ht0 ht1 hne)

/-- `stripHIntegrand t = log (1 - t) + stripG t + log (π / 2)` on `0 ≤ Re t < 1`. -/
lemma stripHIntegrand_eq {t : ℂ} (ht0 : 0 ≤ t.re) (ht1 : t.re < 1) :
    stripHIntegrand t = Complex.log (1 - t) + stripG t + Complex.log (Real.pi / 2) := by
  by_cases ht : t = 0
  · subst ht
    simp [stripHIntegrand, stripG]
  · simp only [stripHIntegrand, stripG, ht, ↓reduceIte]
    set z₁ : ℂ := 1 - t
    set z₂ : ℂ := Complex.tan (Real.pi * t / 2) / t
    set z₃ : ℂ := Complex.tan (Real.pi * t / 2) / (Real.pi * t / 2)
    have hz₁_re : 0 < z₁.re := by simp [z₁]; linarith
    have hz₂_re : 0 < z₂.re := tan_div_t_re_pos ht0 ht1 ht
    have hz₃_re : 0 < z₃.re := tan_div_self_re_pos ht0 ht1 ht
    have hz₁_ne : z₁ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz₁_re; exact lt_irrefl 0 hz₁_re
    have hz₂_ne : z₂ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz₂_re; exact lt_irrefl 0 hz₂_re
    have hz₃_ne : z₃ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz₃_re; exact lt_irrefl 0 hz₃_re
    have harg1 : |z₁.arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz₁_re)
    have harg2 : |z₂.arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz₂_re)
    have hmem12 : z₁.arg + z₂.arg ∈ Ioc (-Real.pi) Real.pi := by
      have h1 := abs_lt.mp harg1
      have h2 := abs_lt.mp harg2
      exact ⟨by linarith, by linarith⟩
    have hmul12 : Complex.log (z₁ * z₂) = Complex.log z₁ + Complex.log z₂ :=
      Complex.log_mul hz₁_ne hz₂_ne hmem12
    have hz₂_eq : z₂ = ((Real.pi / 2 : ℝ) : ℂ) * z₃ := by
      dsimp [z₂, z₃]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
    have hpi2_c : ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 := by push_cast; rfl
    have hmul23 : Complex.log z₂ = Complex.log ((Real.pi : ℂ) / 2) + Complex.log z₃ := by
      rw [hz₂_eq, Complex.log_ofReal_mul (by positivity) hz₃_ne, Complex.ofReal_log (by positivity),
        hpi2_c]
    have hlhs : (1 - t) * Complex.tan (Real.pi * t / 2) / t = z₁ * z₂ := by
      dsimp [z₁, z₂]; ring
    rw [hlhs, hmul12, hmul23]
    ring

private lemma one_sub_mul_re_pos {s : ℝ} {ζ : ℂ} (hs : s ∈ Icc (0 : ℝ) 1) (hζ1 : ζ.re < 1) :
    0 < (1 - (s : ℂ) * ζ).re := by
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  by_cases hs0 : s = 0
  · simp [hs0]
  · have hs_pos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hprod : 0 < s * (1 - ζ.re) := mul_pos hs_pos (sub_pos.mpr hζ1)
    linarith [hs.2]

private lemma tendsto_nhds_of_tendsto_nhdsNE {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {a : ℝ} {b : E} (hf : Tendsto f (𝓝[≠] a) (𝓝 b)) (hfa : f a = b) :
    Tendsto f (𝓝 a) (𝓝 b) := by
  intro s hs
  change f ⁻¹' s ∈ 𝓝 a
  obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hf hs)
  refine Filter.mem_of_superset hu fun x hx => ?_
  by_cases hxa : x = a
  · subst hxa; exact (hfa ▸ mem_of_mem_nhds hs : f x ∈ s)
  · exact hus ⟨hx, hxa⟩

/-- `s ↦ stripG (s ζ)` is continuous on `[0, 1]` for `0 ≤ Re ζ < 1`. -/
lemma continuousOn_stripG_unit {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) :
    ContinuousOn (fun s : ℝ => stripG ((s : ℂ) * ζ)) (Icc 0 1) := by
  by_cases hζ : ζ = 0
  · subst hζ
    simpa [stripG] using continuousOn_const
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      have hlim : Tendsto (fun u : ℝ => stripG ((u : ℂ) * ζ)) (𝓝 0) (𝓝 0) := by
        have hmul : Tendsto (fun u : ℝ => (Real.pi : ℂ) * ((u : ℂ) * ζ) / 2) (𝓝[≠] (0 : ℝ))
            (𝓝[≠] (0 : ℂ)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have hc : Continuous (fun u : ℝ => (Real.pi : ℂ) * ((u : ℂ) * ζ) / 2) := by fun_prop
            simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with u hu
            exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
              (mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) hζ)) two_ne_zero
        have htan : Tendsto (fun u : ℝ => Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) /
            (Real.pi * ((u : ℂ) * ζ) / 2)) (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
          Complex.tendsto_tan_div_nhdsNE_zero.comp hmul
        have hlog : Tendsto (fun u : ℝ => Complex.log (Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) /
            (Real.pi * ((u : ℂ) * ζ) / 2))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
          have h1 : (1 : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl one_pos)
          have hcomp : Tendsto (Complex.log ∘ fun u : ℝ =>
              Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) / (Real.pi * ((u : ℂ) * ζ) / 2))
              (𝓝[≠] (0 : ℝ)) (𝓝 (Complex.log 1)) :=
            (Complex.hasDerivAt_log h1).continuousAt.tendsto.comp htan
          simpa [Function.comp_def, Complex.log_one] using hcomp
        have hcongr : (fun u : ℝ => stripG ((u : ℂ) * ζ)) =ᶠ[𝓝[≠] (0 : ℝ)]
            fun u => Complex.log (Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) /
              (Real.pi * ((u : ℂ) * ζ) / 2)) := by
          filter_upwards [self_mem_nhdsWithin] with u hu
          have hne : (u : ℂ) * ζ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) hζ
          simp [stripG, hne]
        have hne : Tendsto (fun u : ℝ => stripG ((u : ℂ) * ζ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
          hlog.congr' hcongr.symm
        exact tendsto_nhds_of_tendsto_nhdsNE hne (by simp [stripG])
      have hcont0 : ContinuousAt (fun u : ℝ => stripG ((u : ℂ) * ζ)) 0 := by
        rw [ContinuousAt]
        simpa [stripG] using hlim
      exact hcont0.continuousWithinAt
    · have hsz_ne : (s : ℂ) * ζ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hs0) hζ
      have hsz_re0 : 0 ≤ ((s : ℂ) * ζ).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_nonneg hs.1 hζ0
      have hsz_re1 : ((s : ℂ) * ζ).re < 1 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        by_cases h0 : s = 0
        · contradiction
        · have hs_pos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h0)
          nlinarith [hs.2, mul_pos hs_pos (sub_pos.mpr hζ1)]
      have hre_pos : 0 < (Complex.tan (Real.pi * ((s : ℂ) * ζ) / 2) /
          (Real.pi * ((s : ℂ) * ζ) / 2)).re :=
        tan_div_self_re_pos hsz_re0 hsz_re1 hsz_ne
      have hcos_ne : Complex.cos (Real.pi * ((s : ℂ) * ζ) / 2) ≠ 0 := by
        intro hc
        have ht0 := Complex.tan_eq_zero_of_cos_eq_zero hc
        rw [ht0, zero_div, Complex.zero_re] at hre_pos
        exact lt_irrefl 0 hre_pos
      have harg_cont : ContinuousAt (fun u : ℝ => (Real.pi : ℂ) * ((u : ℂ) * ζ) / 2) s :=
        ((Complex.continuous_ofReal.continuousAt.mul continuousAt_const).const_mul
          (Real.pi : ℂ)).div_const 2
      have htan_cont : ContinuousAt
          (fun u : ℝ => Complex.tan ((Real.pi : ℂ) * ((u : ℂ) * ζ) / 2)) s :=
        ContinuousAt.comp (g := Complex.tan) (f := fun u : ℝ => (Real.pi : ℂ) * ((u : ℂ) * ζ) / 2)
          (Complex.continuousAt_tan.mpr hcos_ne) harg_cont
      have hq_cont : ContinuousAt (fun u : ℝ => Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) /
          (Real.pi * ((u : ℂ) * ζ) / 2)) s := by
        refine ContinuousAt.div htan_cont harg_cont ?_
        exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hsz_ne)
          two_ne_zero
      have hlog_cont : ContinuousAt (fun u : ℝ => Complex.log (Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) /
          (Real.pi * ((u : ℂ) * ζ) / 2))) s :=
        ContinuousAt.comp (g := Complex.log)
          (f := fun u : ℝ => Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) /
            (Real.pi * ((u : ℂ) * ζ) / 2))
          (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hre_pos))).continuousAt
          hq_cont
      have hev : (fun u : ℝ => stripG ((u : ℂ) * ζ)) =ᶠ[𝓝 s]
          fun u => Complex.log (Complex.tan (Real.pi * ((u : ℂ) * ζ) / 2) /
            (Real.pi * ((u : ℂ) * ζ) / 2)) := by
        filter_upwards [IsOpen.mem_nhds isOpen_ne hs0] with u hu
        have hu_ne : (u : ℂ) * ζ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) hζ
        simp [stripG, hu_ne]
      exact (hlog_cont.congr hev.symm).continuousWithinAt

/-- `s ↦ log (1 - s ζ)` is continuous on `[0, 1]` for `Re ζ < 1`. -/
lemma continuousOn_log_one_sub_mul {ζ : ℂ} (hζ1 : ζ.re < 1) :
    ContinuousOn (fun s : ℝ => Complex.log (1 - (s : ℂ) * ζ)) (Icc 0 1) := by
  intro s hs
  have hslit : 1 - (s : ℂ) * ζ ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (one_sub_mul_re_pos hs hζ1))
  have hc : ContinuousAt (fun u : ℝ => Complex.log (1 - (u : ℂ) * ζ)) s :=
    ContinuousAt.comp (g := Complex.log) (f := fun u : ℝ => 1 - (u : ℂ) * ζ)
      (Complex.hasDerivAt_log hslit).continuousAt (by fun_prop)
  exact hc.continuousWithinAt

private lemma integral_log_one_sub_mul_eq {ζ : ℂ} (hζ1 : ζ.re < 1) :
    ∫ s in (0 : ℝ)..1, Complex.log (1 - (s : ℂ) * ζ) * ζ =
      -((1 - ζ) * Complex.log (1 - ζ) + ζ) := by
  let F : ℝ → ℂ := fun s => -((1 - (s : ℂ) * ζ) * Complex.log (1 - (s : ℂ) * ζ) + (s : ℂ) * ζ)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt F (Complex.log (1 - (s : ℂ) * ζ) * ζ) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hslit : 1 - (s : ℂ) * ζ ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (one_sub_mul_re_pos hs hζ1))
    have hne : 1 - (s : ℂ) * ζ ≠ 0 := Complex.slitPlane_ne_zero hslit
    have hinner : HasDerivAt (fun u : ℝ => 1 - (u : ℂ) * ζ) (-ζ) s := by
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * ζ) ζ s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ζ
      exact ((hasDerivAt_const s (1 : ℂ)).sub h1).congr_deriv (by simp)
    have hlog : HasDerivAt (fun u : ℝ => Complex.log (1 - (u : ℂ) * ζ))
        (-ζ / (1 - (s : ℂ) * ζ)) s := by
      change HasDerivAt (Complex.log ∘ fun u : ℝ => 1 - (u : ℂ) * ζ) _ s
      exact ((Complex.hasDerivAt_log hslit).comp s hinner).congr_deriv (by ring)
    have hprod := hinner.mul hlog
    have hlin : HasDerivAt (fun u : ℝ => (u : ℂ) * ζ) ζ s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ζ
    have hF := (hprod.add hlin).neg
    refine hF.congr_deriv ?_
    calc -(-ζ * Complex.log (1 - (s : ℂ) * ζ) +
          (1 - (s : ℂ) * ζ) * (-ζ / (1 - (s : ℂ) * ζ)) + ζ)
        = ζ * Complex.log (1 - (s : ℂ) * ζ) +
            ζ * ((1 - (s : ℂ) * ζ) / (1 - (s : ℂ) * ζ)) - ζ := by ring
      _ = ζ * Complex.log (1 - (s : ℂ) * ζ) + ζ * 1 - ζ := by rw [div_self hne]
      _ = Complex.log (1 - (s : ℂ) * ζ) * ζ := by ring
  have hint : IntervalIntegrable (fun s : ℝ => Complex.log (1 - (s : ℂ) * ζ) * ζ) volume 0 1 :=
    ((continuousOn_log_one_sub_mul hζ1).mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [F]

/-- Exact relation `ℋ(ζ) = -((1 - ζ) log(1 - ζ) + ζ) + S̃₀(ζ) + ζ log(π / 2)` on `0 ≤ Re ζ < 1`. -/
theorem stripH_eq {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) :
    stripH ζ = -((1 - ζ) * Complex.log (1 - ζ) + ζ) + stripS0Tilde ζ +
      ζ * Complex.log (Real.pi / 2) := by
  have hint1 : IntervalIntegrable (fun s : ℝ => Complex.log (1 - (s : ℂ) * ζ) * ζ) volume 0 1 :=
    ((continuousOn_log_one_sub_mul hζ1).mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
  have hint2 : IntervalIntegrable (fun s : ℝ => stripG ((s : ℂ) * ζ) * ζ) volume 0 1 :=
    ((continuousOn_stripG_unit hζ0 hζ1).mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
  have hint3 : IntervalIntegrable (fun _ : ℝ => Complex.log (Real.pi / 2) * ζ) volume 0 1 :=
    intervalIntegrable_const
  have hcongr : stripH ζ =
      ∫ s in (0 : ℝ)..1, (Complex.log (1 - (s : ℂ) * ζ) * ζ + stripG ((s : ℂ) * ζ) * ζ +
        Complex.log (Real.pi / 2) * ζ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hsre0 : 0 ≤ ((s : ℂ) * ζ).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg hs.1 hζ0
    have hsre1 : ((s : ℂ) * ζ).re < 1 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      by_cases hs0 : s = 0
      · simp [hs0]
      · have hs_pos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        nlinarith [hs.2, mul_pos hs_pos (sub_pos.mpr hζ1)]
    rw [stripHIntegrand_eq hsre0 hsre1]
    ring
  rw [hcongr, intervalIntegral.integral_add (hint1.add hint2) hint3,
    intervalIntegral.integral_add hint1 hint2, integral_log_one_sub_mul_eq hζ1]
  simp [stripS0Tilde, mul_comm]

/-- **Lemma T.2(1) (`mat:T2`, `(e33)`):** Exact Mellin-strip kernel identity on `0 ≤ Re ζ < 1`
for `c > 0`, `ξ > 0`:
`Γ(c(1 - ζ)) / Γ(c) * (2 π c ξ)^{c ζ} * exp(c ℋ(ζ)) = K₀(ζ, ξ)`. -/
theorem mellin_strip_kernel_eq {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) {ζ : ℂ}
    (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) :
    Complex.Gamma ((c : ℂ) * (1 - ζ)) / Complex.Gamma (c : ℂ) *
        ((2 * Real.pi * c * ξ : ℂ) ^ ((c : ℂ) * ζ)) * Complex.exp ((c : ℂ) * stripH ζ) =
      mellinK0 c ζ ξ := by
  have hw1 : 0 < ((c : ℂ) * (1 - ζ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.one_re, zero_mul, sub_zero]
    exact mul_pos hc (sub_pos.mpr hζ1)
  have hw2 : 0 < (c : ℂ).re := by simpa using hc
  have h1z_re : 0 < (1 - ζ).re := by simp [sub_pos.mpr hζ1]
  have h1z_ne : 1 - ζ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1z_re; exact lt_irrefl 0 h1z_re
  have hlog_mul : Complex.log ((c : ℂ) * (1 - ζ)) = Complex.log (c : ℂ) + Complex.log (1 - ζ) := by
    rw [Complex.log_ofReal_mul hc h1z_ne, Complex.ofReal_log hc.le]
  have hgam1 := (exp_stirling_add_binetRem_eq_gamma hw1).symm
  have hgam2 := (exp_stirling_add_binetRem_eq_gamma hw2).symm
  have hbase_pos : 0 < 2 * Real.pi * c * ξ := by positivity
  have hbase_ne : (2 * Real.pi * c * ξ : ℂ) ≠ 0 := by exact_mod_cast hbase_pos.ne'
  rw [hgam1, hgam2, ← Complex.exp_sub, Complex.cpow_def_of_ne_zero hbase_ne, ← Complex.exp_add,
    ← Complex.exp_add]
  have hcpow_1z : (1 - ζ) ^ (-(1 / 2 : ℂ)) = Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 - ζ)) := by
    rw [Complex.cpow_def_of_ne_zero h1z_ne, mul_comm]
  rw [mellinK0, hcpow_1z, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [stripH_eq hζ0 hζ1, hlog_mul]
  have hlog_c : Complex.log (c : ℂ) = ((Real.log c : ℝ) : ℂ) :=
    (Complex.ofReal_log hc.le).symm
  have hp2 : 0 < Real.pi / 2 := by positivity
  have h2px : 0 < 2 * Real.pi * ξ := by positivity
  have hppx : 0 < Real.pi ^ 2 * ξ := by positivity
  have hlog_p2 : Complex.log (Real.pi / 2 : ℂ) = ((Real.log (Real.pi / 2) : ℝ) : ℂ) := by
    rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hp2.le]
  have hlog_2px : Complex.log (2 * Real.pi * ξ : ℂ) = ((Real.log (2 * Real.pi * ξ) : ℝ) : ℂ) := by
    rw [show (2 * Real.pi * ξ : ℂ) = ((2 * Real.pi * ξ : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log h2px.le]
  have hlog_ppx : Complex.log (Real.pi ^ 2 * ξ : ℂ) = ((Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) := by
    rw [show (Real.pi ^ 2 * ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hppx.le]
  have hlog_base : Complex.log (2 * Real.pi * c * ξ : ℂ) =
      ((Real.log c : ℝ) : ℂ) + Complex.log (2 * Real.pi * ξ : ℂ) := by
    have heq : (2 * Real.pi * c * ξ : ℂ) = ((c * (2 * Real.pi * ξ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [heq, ← Complex.ofReal_log (by positivity), Real.log_mul hc.ne' h2px.ne',
      Complex.ofReal_add, hlog_2px]
  have hlog_pi : Complex.log (Real.pi / 2 : ℂ) + Complex.log (2 * Real.pi * ξ : ℂ) =
      Complex.log (Real.pi ^ 2 * ξ : ℂ) := by
    rw [hlog_p2, hlog_2px, hlog_ppx, ← Complex.ofReal_add, ← Real.log_mul hp2.ne' h2px.ne']
    congr 2
    ring
  simp only [mellinPhi, FormalResearch.Asymptotics.binetDiff]
  rw [hlog_base, hlog_c]
  linear_combination (c : ℂ) * ζ * hlog_pi

/-! ### Lemma T.4(b) (`(e34)`): Purely imaginary edge phase and remainder -/

private lemma continuous_log_tanh_div :
    Continuous (fun u : ℝ => Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2))) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    have heven : ∀ x : ℝ, Real.log (Real.tanh (-x) / (-x)) = Real.log (Real.tanh x / x) := by
      intro x
      rw [Real.tanh_neg, neg_div_neg_eq]
    have hlim_pos : Tendsto (fun x : ℝ => Real.log (Real.tanh x / x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcongr : (fun x : ℝ => Real.log (Real.tanh x / x)) =ᶠ[𝓝[>] (0 : ℝ)]
          fun x => -ceEll x := by
        filter_upwards [self_mem_nhdsWithin] with x _
        unfold ceEll
        rw [← Real.log_inv, inv_div]
      simpa using ceEll_tendsto_zero.neg.congr' hcongr.symm
    have hlim_neg : Tendsto (fun x : ℝ => Real.log (Real.tanh x / x)) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
      have hneg : Tendsto (fun x : ℝ => -x) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with x hx
          exact neg_pos.mpr hx
      have h1 : Tendsto (fun x : ℝ => Real.log (Real.tanh (-x) / (-x))) (𝓝[<] (0 : ℝ)) (𝓝 0) :=
        hlim_pos.comp hneg
      exact h1.congr (fun x => heven x)
    have hlim_x : Tendsto (fun x : ℝ => Real.log (Real.tanh x / x)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      rw [← nhdsLT_sup_nhdsGT]
      exact hlim_neg.sup hlim_pos
    have hmul : Tendsto (fun v : ℝ => Real.pi * v / 2) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun v : ℝ => Real.pi * v / 2) := by fun_prop
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hv) two_ne_zero
    have hne : Tendsto (fun v : ℝ => Real.log (Real.tanh (Real.pi * v / 2) / (Real.pi * v / 2)))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := hlim_x.comp hmul
    have h0 : Real.log (Real.tanh (Real.pi * 0 / 2) / (Real.pi * 0 / 2)) = 0 := by simp
    rw [ContinuousAt, h0]
    exact tendsto_nhds_of_tendsto_nhdsNE hne (by simp)
  · have hx0 : Real.pi * u / 2 ≠ 0 := div_ne_zero (mul_ne_zero Real.pi_ne_zero hu) two_ne_zero
    have ht_pos : 0 < Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2) := by
      rcases lt_or_gt_of_ne hu with hlt | hgt
      · have hneg : 0 < -(Real.pi * u / 2) := by nlinarith [Real.pi_pos]
        have heq : Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2) =
            Real.tanh (-(Real.pi * u / 2)) / (-(Real.pi * u / 2)) := by
          rw [Real.tanh_neg, neg_div_neg_eq]
        rw [heq]
        exact div_pos (tanh_pos_of_pos hneg) hneg
      · have hpos : 0 < Real.pi * u / 2 := by positivity
        exact div_pos (tanh_pos_of_pos hpos) hpos
    have htanh_cont : Continuous Real.tanh := by
      rw [show Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x from funext Real.tanh_eq_sinh_div_cosh]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
    have hnum_cont : ContinuousAt (fun v : ℝ => Real.tanh (Real.pi * v / 2)) u :=
      ContinuousAt.comp (g := Real.tanh) (f := fun v : ℝ => Real.pi * v / 2)
        htanh_cont.continuousAt (by fun_prop)
    have hq_cont : ContinuousAt (fun v : ℝ => Real.tanh (Real.pi * v / 2) / (Real.pi * v / 2)) u :=
      hnum_cont.div (by fun_prop) hx0
    exact ContinuousAt.comp (g := Real.log)
      (f := fun v : ℝ => Real.tanh (Real.pi * v / 2) / (Real.pi * v / 2))
      (Real.continuousAt_log ht_pos.ne') hq_cont

/-- On the imaginary axis `ζ = i τ`, `S̃₀(i τ)` is purely imaginary (`mat:T4`(b)):
`S̃₀(i τ) = i ∫₀^τ log(tanh(π u / 2) / (π u / 2)) du`. -/
theorem stripS0Tilde_imag (τ : ℝ) :
    stripS0Tilde ((τ : ℂ) * Complex.I) =
      Complex.I * ∫ u in (0 : ℝ)..τ, Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2)) := by
  by_cases hτ : τ = 0
  · subst hτ
    simp [stripS0Tilde, stripG]
  · have hcongr : stripS0Tilde ((τ : ℂ) * Complex.I) =
        Complex.I * ((∫ s in (0 : ℝ)..1,
          Real.log (Real.tanh (Real.pi * (s * τ) / 2) / (Real.pi * (s * τ) / 2)) * τ : ℝ) : ℂ) := by
      unfold stripS0Tilde
      have hfun : ∀ s ∈ uIcc (0 : ℝ) 1,
          stripG ((s : ℂ) * ((τ : ℂ) * Complex.I)) * ((τ : ℂ) * Complex.I) =
            Complex.I * ((Real.log (Real.tanh (Real.pi * (s * τ) / 2) /
              (Real.pi * (s * τ) / 2)) * τ : ℝ) : ℂ) := by
        intro s _
        by_cases hs : s = 0
        · subst hs
          simp [stripG]
        · have hne : (s : ℂ) * ((τ : ℂ) * Complex.I) ≠ 0 :=
            mul_ne_zero (Complex.ofReal_ne_zero.mpr hs)
              (mul_ne_zero (Complex.ofReal_ne_zero.mpr hτ) Complex.I_ne_zero)
          simp only [stripG, hne, ↓reduceIte]
          set x : ℝ := Real.pi * (s * τ) / 2
          have hx0 : x ≠ 0 := div_ne_zero (mul_ne_zero Real.pi_ne_zero (mul_ne_zero hs hτ)) two_ne_zero
          have harg : (Real.pi : ℂ) * ((s : ℂ) * ((τ : ℂ) * Complex.I)) / 2 = (x : ℂ) * Complex.I := by
            push_cast [x]; ring
          rw [harg, Complex.tan_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero]
          have hcy : Complex.tanh (x : ℂ) = (Real.tanh x : ℂ) := by
            simp [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
              Complex.ofReal_sinh, Complex.ofReal_cosh]
          have hpos : 0 < Real.tanh x / x := by
            rcases lt_or_gt_of_ne hx0 with hlt | hgt
            · rw [← neg_div_neg_eq, ← Real.tanh_neg]
              exact div_pos (tanh_pos_of_pos (neg_pos.mpr hlt)) (neg_pos.mpr hlt)
            · exact div_pos (tanh_pos_of_pos hgt) hgt
          rw [hcy, ← Complex.ofReal_div, ← Complex.ofReal_log hpos.le]
          push_cast
          ring
      rw [intervalIntegral.integral_congr hfun, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal]
    rw [hcongr]
    congr 2
    rw [intervalIntegral.integral_mul_const]
    have hcomp := intervalIntegral.integral_comp_mul_right
      (fun u : ℝ => Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2))) hτ (a := 0) (b := 1)
    simp only [zero_mul, one_mul, smul_eq_mul] at hcomp
    rw [hcomp, mul_comm, mul_inv_cancel_left₀ hτ]

/-- Exact norm and vertical-comparison bound for `K₀(i τ, ξ)` (`mat:T4`(b)):
`‖K₀(i τ, ξ)‖ = (1 + τ²)⁻¹/⁴ exp(Re B_c(i τ)) ≤ (1 + τ²)⁻¹/⁴`. -/
theorem norm_mellinK0_imag_le {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (τ : ℝ) :
    ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ =
        (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) *
          Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re ∧
      ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  have hS0_re : (stripS0Tilde ((τ : ℂ) * Complex.I)).re = 0 := by
    rw [stripS0Tilde_imag, Complex.I_mul_re, ← Complex.ofReal_re (∫ u in (0 : ℝ)..τ, _)]
    simp
  have hpx_pos : 0 < Real.pi ^ 2 * ξ := by positivity
  have hlog_px : Complex.log (Real.pi ^ 2 * ξ : ℂ) = ((Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) := by
    rw [show (Real.pi ^ 2 * ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hpx_pos.le]
  have hPhi_re : (mellinPhi ((τ : ℂ) * Complex.I) ξ).re = 0 := by
    simp [mellinPhi, hS0_re, hlog_px]
  have hnorm_exp_Phi : ‖Complex.exp ((c : ℂ) * mellinPhi ((τ : ℂ) * Complex.I) ξ)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [hPhi_re]
  have hnorm_pow : ‖(1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ = (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
    have hre_exp : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hre_exp, Complex.norm_cpow_real]
    have hnorm_base : ‖(1 : ℂ) - (τ : ℂ) * Complex.I‖ = (1 + τ ^ 2) ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_rpow]
      congr 1
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, Complex.sub_im,
        Complex.one_im, Complex.mul_im, mul_one]
      ring
    rw [hnorm_base, ← Real.rpow_mul (by positivity)]
    norm_num
  have hnorm_eq : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ =
      (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) *
        Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re := by
    rw [mellinK0, norm_mul, norm_mul, hnorm_pow, hnorm_exp_Phi, mul_one, Complex.norm_exp]
  refine ⟨hnorm_eq, ?_⟩
  have hvert := FormalResearch.Asymptotics.binetDiff_re_vertical_le hc (by norm_num : (0 : ℝ) < 1) τ
  simp only [Complex.ofReal_zero, zero_add] at hvert
  have hdiff0 : FormalResearch.Asymptotics.binetDiff c (0 : ℂ) = 0 := by
    simp [FormalResearch.Asymptotics.binetDiff]
  rw [hdiff0, Complex.zero_re] at hvert
  have hexp_le : Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hvert
  rw [hnorm_eq]
  calc (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) *
        Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re
      ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hexp_le (Real.rpow_nonneg (by positivity) _)
    _ = (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := mul_one _

/-- Fifth-order edge remainder `R̃₅(i τ) = S̃₀(i τ) - (π² / 36) (i τ)³` (`mat:T4`(b)). -/
noncomputable def edgeR5 (τ : ℝ) : ℂ :=
  stripS0Tilde ((τ : ℂ) * Complex.I) - (Real.pi ^ 2 / 36 : ℂ) * ((τ : ℂ) * Complex.I) ^ 3

/-- Purely imaginary integral representation `R̃₅(i τ) = i ∫₀^τ h_th(π u / 2) du` (`(e34)`). -/
theorem edgeR5_eq_imag_integral (τ : ℝ) :
    edgeR5 τ = Complex.I * ∫ u in (0 : ℝ)..τ, ceHth (Real.pi * u / 2) := by
  have hint1 : IntervalIntegrable
      (fun u : ℝ => Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2))) volume 0 τ :=
    continuous_log_tanh_div.intervalIntegrable 0 τ
  have hint2 : IntervalIntegrable (fun u : ℝ => (Real.pi * u / 2) ^ 2 / 3) volume 0 τ :=
    (by fun_prop : Continuous (fun u : ℝ => (Real.pi * u / 2) ^ 2 / 3)).intervalIntegrable 0 τ
  have hint_sq : ∫ u in (0 : ℝ)..τ, (Real.pi * u / 2) ^ 2 / 3 = Real.pi ^ 2 / 36 * τ ^ 3 := by
    have h1 : ∀ u : ℝ, (Real.pi * u / 2) ^ 2 / 3 = (Real.pi ^ 2 / 12) * u ^ 2 := fun u => by ring
    simp_rw [h1, intervalIntegral.integral_const_mul, integral_pow]
    ring
  have hce : ∫ u in (0 : ℝ)..τ, ceHth (Real.pi * u / 2) =
      (∫ u in (0 : ℝ)..τ, Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2))) +
        Real.pi ^ 2 / 36 * τ ^ 3 := by
    simp_rw [ceHth]
    rw [intervalIntegral.integral_add hint1 hint2, hint_sq]
  have hI3 : ((τ : ℂ) * Complex.I) ^ 3 = -(τ ^ 3 : ℂ) * Complex.I := by
    calc ((τ : ℂ) * Complex.I) ^ 3 = (τ : ℂ) ^ 3 * Complex.I ^ 2 * Complex.I := by ring
      _ = (τ : ℂ) ^ 3 * (-1) * Complex.I := by rw [Complex.I_sq]
      _ = -(τ ^ 3 : ℂ) * Complex.I := by ring
  rw [edgeR5, stripS0Tilde_imag, hce, hI3]
  push_cast
  ring

private lemma ceHth_even (x : ℝ) : ceHth (-x) = ceHth x := by
  unfold ceHth
  rw [Real.tanh_neg, neg_div_neg_eq, neg_sq]

private lemma ceHth_nonneg (x : ℝ) : 0 ≤ ceHth x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [← ceHth_even x]
    exact (ceHth_pos (neg_pos.mpr hx)).le
  · simp [ceHth]
  · exact (ceHth_pos hx).le

private lemma ceHth_le_third_pow_four (x : ℝ) : ceHth x ≤ x ^ 4 / 3 := by
  wlog hx : 0 ≤ x generalizing x
  · have h := this (-x) (by linarith)
    have h4 : (-x) ^ 4 = x ^ 4 := by ring
    rwa [ceHth_even, h4] at h
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [ceHth]
  · rcases le_or_gt x 1 with hx1 | hx1
    · exact (ceHth_le_of_le_one hx_pos hx1).trans (by nlinarith [pow_nonneg hx 4])
    · exact (ceHth_lt_of_ge_one hx1.le).le

private lemma ceHth_continuous : Continuous (fun u : ℝ => ceHth (Real.pi * u / 2)) := by
  have heq : (fun u : ℝ => ceHth (Real.pi * u / 2)) =
      fun u : ℝ => Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2)) +
        (Real.pi * u / 2) ^ 2 / 3 := rfl
  rw [heq]
  exact continuous_log_tanh_div.add (by fun_prop)

/-- **Lemma T.4(b) (`(e34)`):** `‖R̃₅(i τ)‖ ≤ (π⁴ / 240) |τ|⁵` and `‖R̃₅(i τ)‖ ≤ 2 |τ|⁵`. -/
theorem norm_edgeR5_le (τ : ℝ) :
    ‖edgeR5 τ‖ ≤ (Real.pi ^ 4 / 240) * |τ| ^ 5 ∧ ‖edgeR5 τ‖ ≤ 2 * |τ| ^ 5 := by
  have hnorm : ‖edgeR5 τ‖ = |∫ u in (0 : ℝ)..τ, ceHth (Real.pi * u / 2)| := by
    rw [edgeR5_eq_imag_integral, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have hint_ce : IntervalIntegrable (fun u : ℝ => ceHth (Real.pi * u / 2)) volume 0 τ :=
    ceHth_continuous.intervalIntegrable 0 τ
  have hint_bd : IntervalIntegrable (fun u : ℝ => (Real.pi * u / 2) ^ 4 / 3) volume 0 τ :=
    (by fun_prop : Continuous (fun u : ℝ => (Real.pi * u / 2) ^ 4 / 3)).intervalIntegrable 0 τ
  have h1 : ‖edgeR5 τ‖ ≤ (Real.pi ^ 4 / 240) * |τ| ^ 5 := by
    rw [hnorm]
    rcases le_or_gt 0 τ with hτ | hτ
    · have hnn : 0 ≤ ∫ u in (0 : ℝ)..τ, ceHth (Real.pi * u / 2) :=
        intervalIntegral.integral_nonneg hτ fun u _ => ceHth_nonneg _
      have hmono : ∫ u in (0 : ℝ)..τ, ceHth (Real.pi * u / 2) ≤
          ∫ u in (0 : ℝ)..τ, (Real.pi * u / 2) ^ 4 / 3 :=
        intervalIntegral.integral_mono_on hτ hint_ce hint_bd fun u _ =>
          ceHth_le_third_pow_four _
      have hbd_eval : ∫ u in (0 : ℝ)..τ, (Real.pi * u / 2) ^ 4 / 3 =
          (Real.pi ^ 4 / 240) * τ ^ 5 := by
        have hf : ∀ u : ℝ, (Real.pi * u / 2) ^ 4 / 3 = (Real.pi ^ 4 / 48) * u ^ 4 := fun u => by ring
        simp_rw [hf, intervalIntegral.integral_const_mul, integral_pow]
        ring
      rw [abs_of_nonneg hnn, abs_of_nonneg hτ, ← hbd_eval]
      exact hmono
    · rw [intervalIntegral.integral_symm, abs_neg]
      have hnn : 0 ≤ ∫ u in τ..0, ceHth (Real.pi * u / 2) :=
        intervalIntegral.integral_nonneg hτ.le fun u _ => ceHth_nonneg _
      have hmono : ∫ u in τ..0, ceHth (Real.pi * u / 2) ≤
          ∫ u in τ..0, (Real.pi * u / 2) ^ 4 / 3 :=
        intervalIntegral.integral_mono_on hτ.le hint_ce.symm hint_bd.symm fun u _ =>
          ceHth_le_third_pow_four _
      have hneg_bd : ∫ u in τ..0, (Real.pi * u / 2) ^ 4 / 3 =
          (Real.pi ^ 4 / 240) * (-τ) ^ 5 := by
        have hf : ∀ u : ℝ, (Real.pi * u / 2) ^ 4 / 3 = (Real.pi ^ 4 / 48) * u ^ 4 := fun u => by ring
        simp_rw [hf, intervalIntegral.integral_const_mul, integral_pow]
        ring
      rw [abs_of_nonneg hnn, abs_of_neg hτ]
      linarith
  have hpi4 : Real.pi ^ 4 / 240 ≤ 2 := by
    have h4 : Real.pi < 4 := Real.pi_lt_four
    have hp4 : Real.pi ^ 4 < 4 ^ 4 := pow_lt_pow_left₀ h4 Real.pi_pos.le (by decide)
    linarith [show (4 : ℝ) ^ 4 = 256 by norm_num]
  have h2 : ‖edgeR5 τ‖ ≤ 2 * |τ| ^ 5 :=
    h1.trans (mul_le_mul_of_nonneg_right hpi4 (pow_nonneg (abs_nonneg τ) 5))
  exact ⟨h1, h2⟩

/-- Exponential remainder bound `‖exp(c R̃₅(i τ)) - 1‖ ≤ 2 c |τ|⁵` for `c ≥ 0` (`(e34)`). -/
theorem norm_exp_edgeR5_sub_one_le {c : ℝ} (hc : 0 ≤ c) (τ : ℝ) :
    ‖Complex.exp ((c : ℂ) * edgeR5 τ) - 1‖ ≤ 2 * c * |τ| ^ 5 := by
  set θ : ℝ := ∫ u in (0 : ℝ)..τ, ceHth (Real.pi * u / 2)
  have hedge : (c : ℂ) * edgeR5 τ = ((c * θ : ℝ) : ℂ) * Complex.I := by
    rw [edgeR5_eq_imag_integral]
    push_cast
    ring
  have hexp_bound : ∀ α : ℝ, ‖Complex.exp ((α : ℂ) * Complex.I) - 1‖ ≤ |α| := by
    intro α
    have hftc : Complex.exp ((α : ℂ) * Complex.I) - 1 =
        ∫ t in (0 : ℝ)..α, Complex.I * Complex.exp ((t : ℂ) * Complex.I) := by
      have hderiv : ∀ t ∈ uIcc (0 : ℝ) α,
          HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
            (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) t := by
        intro t _
        have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
        exact (hlin.cexp).congr_deriv (by ring)
      have hint : IntervalIntegrable
          (fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) volume 0 α :=
        (by fun_prop : Continuous (fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I))).intervalIntegrable 0 α
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      simpa using h.symm
    rw [hftc]
    have hnorm_le := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := α) (C := (1 : ℝ))
      (f := fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) fun t _ => by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
    simpa [Real.dist_eq] using hnorm_le
  have hθ_norm : |θ| = ‖edgeR5 τ‖ := by
    rw [edgeR5_eq_imag_integral, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  calc ‖Complex.exp ((c : ℂ) * edgeR5 τ) - 1‖
      = ‖Complex.exp (((c * θ : ℝ) : ℂ) * Complex.I) - 1‖ := by rw [hedge]
    _ ≤ |c * θ| := hexp_bound (c * θ)
    _ = c * ‖edgeR5 τ‖ := by rw [abs_mul, abs_of_nonneg hc, hθ_norm]
    _ ≤ c * (2 * |τ| ^ 5) := mul_le_mul_of_nonneg_left (norm_edgeR5_le τ).2 hc
    _ = 2 * c * |τ| ^ 5 := by ring

/-- Quadratic Taylor bound for `(1 - i x)^{-1/2}` (`mat:T4`(b)):
`‖(1 - i x)^{-1/2} - (1 + i x / 2)‖ ≤ (3 / 8) x²` for all `x : ℝ`. -/
theorem one_sub_imag_rpow_neg_half_approx (x : ℝ) :
    ‖(1 - (x : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) - (1 + (1 / 2 : ℂ) * (x : ℂ) * Complex.I)‖ ≤
      (3 / 8 : ℝ) * x ^ 2 := by
  let φ : ℝ → ℂ := fun t => (1 - (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
  let φ' : ℝ → ℂ := fun t => (1 / 2 : ℂ) * Complex.I * (1 - (t : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ))
  let φ'' : ℝ → ℂ := fun t => -(3 / 4 : ℂ) * (1 - (t : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ))
  have hslit : ∀ t : ℝ, 1 - (t : ℂ) * Complex.I ∈ Complex.slitPlane := fun t => by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp
  have hinner : ∀ t : ℝ, HasDerivAt (fun s : ℝ => 1 - (s : ℂ) * Complex.I) (-Complex.I) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
    exact ((hasDerivAt_const t (1 : ℂ)).sub h1).congr_deriv (by simp)
  have hd1 : ∀ t : ℝ, HasDerivAt φ (φ' t) t := fun t => by
    have h : HasDerivAt ((fun z : ℂ => z ^ (-(1 / 2 : ℂ))) ∘ fun s : ℝ => 1 - (s : ℂ) * Complex.I)
        ((-(1 / 2 : ℂ)) * (1 - (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ) - 1) * (-Complex.I)) t :=
      (Complex.hasStrictDerivAt_cpow_const (hslit t)).hasDerivAt.comp t (hinner t)
    refine h.congr_deriv ?_
    dsimp [φ']
    have hpow : -(1 / 2 : ℂ) - 1 = -(3 / 2 : ℂ) := by norm_num
    rw [hpow]
    ring
  have hd2 : ∀ t : ℝ, HasDerivAt φ' (φ'' t) t := fun t => by
    have h0 : HasDerivAt ((fun z : ℂ => z ^ (-(3 / 2 : ℂ))) ∘ fun s : ℝ => 1 - (s : ℂ) * Complex.I)
        ((-(3 / 2 : ℂ)) * (1 - (t : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ) - 1) * (-Complex.I)) t :=
      (Complex.hasStrictDerivAt_cpow_const (hslit t)).hasDerivAt.comp t (hinner t)
    have h := h0.const_mul ((1 / 2 : ℂ) * Complex.I)
    refine h.congr_deriv ?_
    dsimp [φ'']
    have hpow : -(3 / 2 : ℂ) - 1 = -(5 / 2 : ℂ) := by norm_num
    rw [hpow]
    calc (1 / 2 : ℂ) * Complex.I * ((-(3 / 2 : ℂ)) * (1 - (t : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) *
          (-Complex.I))
        = (3 / 4 : ℂ) * (Complex.I * Complex.I) * (1 - (t : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by ring
      _ = (3 / 4 : ℂ) * (-1) * (1 - (t : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by
          rw [← sq, Complex.I_sq]
      _ = -(3 / 4 : ℂ) * (1 - (t : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by ring
  have hφ''_cont : Continuous φ'' := by
    refine continuous_const.mul ?_
    refine Continuous.cpow (by fun_prop) continuous_const fun t => hslit t
  have hφ''_norm : ∀ u : ℝ, ‖φ'' u‖ ≤ (3 / 4 : ℝ) := fun u => by
    dsimp [φ'']
    have hpow : (-(5 / 2 : ℂ)) = ((-(5 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, norm_neg, show ‖(3 / 4 : ℂ)‖ = (3 / 4 : ℝ) by norm_num, hpow, Complex.norm_cpow_real]
    have hbase : 1 ≤ ‖(1 : ℂ) - (u : ℂ) * Complex.I‖ := by
      have hsq : 1 ≤ ‖(1 : ℂ) - (u : ℂ) * Complex.I‖ ^ 2 := by
        rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, Complex.sub_im,
          Complex.one_im, Complex.mul_im, mul_one, add_zero, zero_sub]
        nlinarith [sq_nonneg u]
      nlinarith [norm_nonneg ((1 : ℂ) - (u : ℂ) * Complex.I)]
    have hle1 : ‖(1 : ℂ) - (u : ℂ) * Complex.I‖ ^ (-(5 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)
    linarith
  have hφ'_cont : Continuous φ' := continuous_iff_continuousAt.mpr fun t => (hd2 t).continuousAt
  have hφ'_bound : ∀ t : ℝ, ‖φ' t - φ' 0‖ ≤ (3 / 4 : ℝ) * |t| := fun t => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hd2 u) (hφ''_cont.intervalIntegrable 0 t)
    rw [← hftc]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
      (C := (3 / 4 : ℝ)) (f := φ'') fun u _ => hφ''_norm u
    simpa [Real.dist_eq] using hnorm
  let G : ℝ → ℂ := fun t => φ t - (1 + (1 / 2 : ℂ) * (t : ℂ) * Complex.I)
  have hG0 : G 0 = 0 := by simp [G, φ]
  have hG_deriv : ∀ t : ℝ, HasDerivAt G (φ' t - φ' 0) t := fun t => by
    have hlin : HasDerivAt (fun s : ℝ => 1 + (1 / 2 : ℂ) * (s : ℂ) * Complex.I)
        ((1 / 2 : ℂ) * Complex.I) t := by
      have h1 : HasDerivAt (fun s : ℝ => (1 / 2 : ℂ) * (s : ℂ) * Complex.I)
          ((1 / 2 : ℂ) * Complex.I) t := by
        simpa [mul_assoc] using (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
          (1 / 2 : ℂ)).mul_const Complex.I).congr_deriv (by simp)
      exact h1.const_add (1 : ℂ)
    have hφ0 : φ' 0 = (1 / 2 : ℂ) * Complex.I := by simp [φ']
    rw [hφ0]
    exact ((hd1 t).sub hlin).congr_deriv (by simp)
  have hG_ftc : G x = ∫ t in (0 : ℝ)..x, (φ' t - φ' 0) := by
    have hint : IntervalIntegrable (fun t : ℝ => φ' t - φ' 0) volume 0 x :=
      (hφ'_cont.sub continuous_const).intervalIntegrable 0 x
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG_deriv t) hint
    rw [hG0, sub_zero] at h
    exact h.symm
  change ‖G x‖ ≤ (3 / 8 : ℝ) * x ^ 2
  rw [hG_ftc]
  have hint_g : IntervalIntegrable (fun t : ℝ => φ' t - φ' 0) volume 0 x :=
    (hφ'_cont.sub continuous_const).intervalIntegrable 0 x
  have hint_bd : IntervalIntegrable (fun t : ℝ => (3 / 4 : ℝ) * |t|) volume 0 x :=
    (by fun_prop : Continuous (fun t : ℝ => (3 / 4 : ℝ) * |t|)).intervalIntegrable 0 x
  rcases le_or_gt 0 x with hx | hx
  · calc ‖∫ t in (0 : ℝ)..x, (φ' t - φ' 0)‖
        ≤ ∫ t in (0 : ℝ)..x, ‖φ' t - φ' 0‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx
      _ ≤ ∫ t in (0 : ℝ)..x, (3 / 4 : ℝ) * |t| :=
          intervalIntegral.integral_mono_on hx hint_g.norm hint_bd fun t _ => hφ'_bound t
      _ = ∫ t in (0 : ℝ)..x, (3 / 4 : ℝ) * t :=
          intervalIntegral.integral_congr fun t ht => by
            rw [uIcc_of_le hx] at ht
            rw [abs_of_nonneg ht.1]
      _ = (3 / 8 : ℝ) * x ^ 2 := by
          rw [intervalIntegral.integral_const_mul, integral_id]
          ring
  · rw [intervalIntegral.integral_symm, norm_neg]
    calc ‖∫ t in x..0, (φ' t - φ' 0)‖
        ≤ ∫ t in x..0, ‖φ' t - φ' 0‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx.le
      _ ≤ ∫ t in x..0, (3 / 4 : ℝ) * |t| :=
          intervalIntegral.integral_mono_on hx.le hint_g.symm.norm hint_bd.symm fun t _ =>
            hφ'_bound t
      _ = ∫ t in x..0, (3 / 4 : ℝ) * (-t) :=
          intervalIntegral.integral_congr fun t ht => by
            rw [uIcc_of_le hx.le] at ht
            rw [abs_of_nonpos ht.2]
      _ = (3 / 8 : ℝ) * x ^ 2 := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, integral_id]
          ring

/-! ### Wave 3 `(P2)` / `(P4)` corollaries -/

/-- **Lemma T.4(e) `(P2)` uniform phase floor:** for `L > 0`, `τ₀ > 0` with
`ceEll (π τ₀ / 2) = L`,
- `Φ'(τ; L) ≥ log(3 / 2) min(L / 4, 0.149)` for `|τ| ≤ τ₀ / 2`, and
- `-Φ'(τ; L) ≥ log(3 / 2) min(L / 4, 0.149)` for `|τ| ≥ 3 τ₀ / 2`. -/
theorem edgePhiDeriv_phase_floor_P2 {L τ₀ : ℝ} (hL : 0 < L) (hτ₀ : 0 < τ₀)
    (hτ₀_eq : ceEll (Real.pi * τ₀ / 2) = L) :
    (∀ τ : ℝ, |τ| ≤ τ₀ / 2 →
      Real.log (3 / 2) * min (L / 4) (149 / 1000 : ℝ) ≤ edgePhiDeriv L τ) ∧
    (∀ τ : ℝ, 3 * τ₀ / 2 ≤ |τ| →
      Real.log (3 / 2) * min (L / 4) (149 / 1000 : ℝ) ≤ -edgePhiDeriv L τ) := by
  set a : ℝ := Real.pi * τ₀ / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have htau := tau0_gt_sqrt hL hτ₀ hτ₀_eq
  have ha_gt : Real.sqrt 3 / 2 * Real.sqrt L < a := by
    have h1 := mul_lt_mul_of_pos_left htau (by positivity : 0 < Real.pi / 4)
    have hlhs : Real.pi / 4 * (2 * Real.sqrt 3 / Real.pi * Real.sqrt L) =
        Real.sqrt 3 / 2 * Real.sqrt L := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      norm_num
    have hrhs : Real.pi / 4 * τ₀ = a := by dsimp [a]; ring
    linarith
  have ha_sq : L / 4 < a ^ 2 / 3 := by
    have hsq : (Real.sqrt 3 / 2 * Real.sqrt L) ^ 2 < a ^ 2 :=
      pow_lt_pow_left₀ ha_gt (by positivity) (by decide)
    have hlhs : (Real.sqrt 3 / 2 * Real.sqrt L) ^ 2 = 3 / 4 * L := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hL.le]
      ring
    linarith
  have hmin_le_a : min (L / 4) (149 / 1000 : ℝ) ≤ ceGamma a :=
    (min_le_min ha_sq.le le_rfl).trans (ceGamma_ge_min ha)
  have hgam_mono : ceGamma a ≤ ceGamma (Real.pi * τ₀ / 2) :=
    ceGamma_strictMonoOn.monotoneOn (mem_Ioi.mpr ha) (mem_Ioi.mpr (by positivity))
      (by dsimp [a]; nlinarith [Real.pi_pos])
  have hmin_nn : 0 ≤ min (L / 4) (149 / 1000 : ℝ) := le_min (by positivity) (by norm_num)
  have hlog32_pos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hlog32_le : Real.log (3 / 2) ≤ Real.log 2 :=
    Real.log_le_log (by norm_num) (by norm_num)
  constructor
  · intro τ hτ
    calc Real.log (3 / 2) * min (L / 4) (149 / 1000 : ℝ)
        ≤ Real.log 2 * ceGamma a :=
          mul_le_mul hlog32_le hmin_le_a hmin_nn (Real.log_nonneg (by norm_num))
      _ = ceGamma a * Real.log 2 := mul_comm _ _
      _ ≤ edgePhiDeriv L τ := edgePhiDeriv_ge_half_tau0 hL hτ₀ hτ₀_eq hτ
  · intro τ hτ
    calc Real.log (3 / 2) * min (L / 4) (149 / 1000 : ℝ)
        ≤ Real.log (3 / 2) * ceGamma (Real.pi * τ₀ / 2) :=
          mul_le_mul_of_nonneg_left (hmin_le_a.trans hgam_mono) hlog32_pos.le
      _ = ceGamma (Real.pi * τ₀ / 2) * Real.log (3 / 2) := mul_comm _ _
      _ ≤ -edgePhiDeriv L τ := neg_edgePhiDeriv_ge_three_halves_tau0 hL hτ₀ hτ₀_eq hτ

/-- **Lemma T.4(e) `(P4)` integrated curvature bound:** for `L > 0`, `τ₀ > 0` with
`ceEll (π τ₀ / 2) = L`,
`∫ τ in 0..(τ₀ / 2), |Φ''(τ)| = Φ'(0; L) - Φ'(τ₀ / 2; L) ≤ L`. -/
theorem integral_abs_edgePhiDeriv2_le {L τ₀ : ℝ} (_hL : 0 < L) (hτ₀ : 0 < τ₀)
    (hτ₀_eq : ceEll (Real.pi * τ₀ / 2) = L) :
    (∫ τ in (0 : ℝ)..(τ₀ / 2), |edgePhiDeriv2 τ| =
        edgePhiDeriv L 0 - edgePhiDeriv L (τ₀ / 2)) ∧
      ∫ τ in (0 : ℝ)..(τ₀ / 2), |edgePhiDeriv2 τ| ≤ L := by
  set b : ℝ := τ₀ / 2
  have hb : 0 < b := by dsimp [b]; positivity
  let F : ℝ → ℝ := fun τ => ceEll (Real.pi * τ / 2)
  have hF_deriv : ∀ τ ∈ Ioo (0 : ℝ) b, HasDerivAt F (-edgePhiDeriv2 τ) τ := fun τ hτ =>
    (m2_bounds hτ.1).1
  have hF_lim0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hmul : Tendsto (fun s : ℝ => Real.pi * s / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun s : ℝ => Real.pi * s / 2) := by fun_prop
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact div_pos (mul_pos Real.pi_pos hs) two_pos
    exact ceEll_tendsto_zero.comp hmul
  have hF_limb : Tendsto F (𝓝[<] b) (𝓝 (F b)) :=
    (m2_bounds hb).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hderiv2_cont : Continuous edgePhiDeriv2 := by
    rw [continuous_iff_continuousAt]
    intro τ
    by_cases hτ : τ = 0
    · subst hτ
      have h0 : edgePhiDeriv2 0 = 0 := by simp [edgePhiDeriv2]
      rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
      have hlim : Tendsto (fun t : ℝ => (Real.pi ^ 2 / 6) * |t|) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ => (Real.pi ^ 2 / 6) * |t|) := by fun_prop
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
      refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hlim
      by_cases ht : t = 0
      · subst ht; simp [edgePhiDeriv2]
      · exact (edgePhiDeriv2_abs_le ht).trans (min_le_left _ _)
    · have hsh : Real.sinh (Real.pi * τ) ≠ 0 := by
        rcases lt_or_gt_of_ne hτ with hlt | hgt
        · have hneg : 0 < -(Real.pi * τ) := by nlinarith [Real.pi_pos]
          have hpos : 0 < Real.sinh (-(Real.pi * τ)) := (sinh_gt_id hneg).trans' hneg
          rw [Real.sinh_neg] at hpos
          linarith
        · have hpos : 0 < Real.pi * τ := mul_pos Real.pi_pos hgt
          exact ((sinh_gt_id hpos).trans' hpos).ne'
      have hden : Real.pi * τ * Real.sinh (Real.pi * τ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero Real.pi_ne_zero hτ) hsh
      unfold edgePhiDeriv2
      exact ((continuousAt_const.mul ((Real.continuous_sinh.continuousAt.comp
        (continuousAt_const.mul continuousAt_id)).sub (continuousAt_const.mul continuousAt_id))).div
        ((continuousAt_const.mul continuousAt_id).mul (Real.continuous_sinh.continuousAt.comp
          (continuousAt_const.mul continuousAt_id))) hden)
  have hint_neg : IntervalIntegrable (fun τ : ℝ => -edgePhiDeriv2 τ) volume 0 b :=
    hderiv2_cont.neg.intervalIntegrable 0 b
  have hftc : ∫ τ in (0 : ℝ)..b, (-edgePhiDeriv2 τ) = F b - 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hb hF_deriv hint_neg hF_lim0 hF_limb
  have habs_eq : ∫ τ in (0 : ℝ)..b, |edgePhiDeriv2 τ| =
      ∫ τ in (0 : ℝ)..b, (-edgePhiDeriv2 τ) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le hb.le] at hτ
    rcases eq_or_lt_of_le hτ.1 with rfl | hpos
    · simp [edgePhiDeriv2]
    · have hnn : 0 ≤ -edgePhiDeriv2 τ := by
        have hm := (m2_bounds hpos).2.1
        have hτ2 : 0 ≤ τ / (1 + τ ^ 2) := by positivity
        linarith
      rw [← abs_neg (edgePhiDeriv2 τ), abs_of_nonneg hnn]
  have hphi_diff : edgePhiDeriv L 0 - edgePhiDeriv L b = F b := by
    have hb0 : b ≠ 0 := hb.ne'
    have hlog : Real.log (Real.tanh (Real.pi * |b| / 2) / (Real.pi * |b| / 2)) = -F b := by
      rw [abs_of_pos hb]
      dsimp [F]
      unfold ceEll
      rw [← Real.log_inv, inv_div]
    simp only [edgePhiDeriv, ↓reduceIte, hb0, add_zero, hlog]
    ring
  have h_eq : ∫ τ in (0 : ℝ)..b, |edgePhiDeriv2 τ| = edgePhiDeriv L 0 - edgePhiDeriv L b := by
    rw [habs_eq, hftc, sub_zero, hphi_diff]
  refine ⟨h_eq, ?_⟩
  rw [h_eq, hphi_diff]
  have hmono : ceEll (Real.pi * b / 2) ≤ ceEll (Real.pi * τ₀ / 2) :=
    ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
      (by dsimp [b]; nlinarith [Real.pi_pos])
  simpa [F, hτ₀_eq] using hmono

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.binetRem_eq_binetB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.binetRem_eq_binetB

/-- info: 'FormalResearch.CohnElkies.binetLogGamma_eq_stirling_add_binetRem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.binetLogGamma_eq_stirling_add_binetRem

/-- info: 'FormalResearch.CohnElkies.exp_stirling_add_binetRem_eq_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.exp_stirling_add_binetRem_eq_gamma

/-- info: 'FormalResearch.CohnElkies.stripH_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.stripH_eq

/-- info: 'FormalResearch.CohnElkies.mellin_strip_kernel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.mellin_strip_kernel_eq

/-- info: 'FormalResearch.CohnElkies.stripS0Tilde_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.stripS0Tilde_imag

/-- info: 'FormalResearch.CohnElkies.norm_mellinK0_imag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_mellinK0_imag_le

/-- info: 'FormalResearch.CohnElkies.edgeR5_eq_imag_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.edgeR5_eq_imag_integral

/-- info: 'FormalResearch.CohnElkies.norm_edgeR5_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_edgeR5_le

/-- info: 'FormalResearch.CohnElkies.norm_exp_edgeR5_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_exp_edgeR5_sub_one_le

/-- info: 'FormalResearch.CohnElkies.one_sub_imag_rpow_neg_half_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.one_sub_imag_rpow_neg_half_approx

/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv_phase_floor_P2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.edgePhiDeriv_phase_floor_P2

/-- info: 'FormalResearch.CohnElkies.integral_abs_edgePhiDeriv2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.integral_abs_edgePhiDeriv2_le

end FormalResearch.CohnElkies
