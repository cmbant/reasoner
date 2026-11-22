module

public import FormalResearch.ModularBootstrap.SlitStrip.PoissonJensenInput
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Harmonic majorant identification `h = U` (`HarmonicMajorantIdentification`)

Proves `HarmonicMajorantIdentification` (`SlitStrip/PoissonJensenInput.lean`, paper:
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G, `vlo:Gap`, "The harmonic majorant
and the deficit"):

For every `x ∈ [0, ξ_*)` with upper-half-plane preimage `z_x = xUHP(ξ_* - x) + i yUHP(ξ_* - x)`,
`majorantReal x = -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel xUHP yUHP σ`.

## Proof strategy
1. **Holomorphic completion of `U` on `slitStrip`:**
   `majorantHolomorphic b := i U₀ + (4π/3) ∫₀¹ pMap(t b) b dt` has complex derivative
   `(4π/3) pMap b` on `slitStrip`, so `majorant2D b := (majorantHolomorphic b).im` is harmonic on
   `slitStrip`, agrees with `majorantReal` on `(-ξ_*, ξ_*)`, has linear growth `O(1 + |Re b|)`,
   and approaches `0` on `|Im b| = 1/2` and `-slitL(x)` on the slits `Im b = 0, |x| > ξ_*`.
2. **Schwarz integral of `-slitL ∘ slitBoundaryMap` on the upper half-plane:**
   `schwarzSlit z := -π⁻¹ ∫_{σ ∈ slitPreimage} slitL(slitBoundaryMap σ) * ((1 + σ z)/((σ - z)(1 + σ²))) dσ`
   is holomorphic on `{0 < z.im}`, has imaginary part equal to
   `-∫_{σ ∈ slitPreimage} slitL(slitBoundaryMap σ) * poissonKernel z.re z.im σ`, approaches the
   boundary data at every `σ ∈ ℝ \ {-1, 0, 1}`, and has logarithmic growth at `{-1, 0, 1, ∞}`.
3. **Phragmén--Lindelöf uniqueness:**
   On the shifted upper half-plane `z ↦ z + i η` (`η > 0`), the difference
   `Δ(z) = majorantHolomorphic (confB z) - schwarzSlit z` is compared against `ε cosh((π/2) confB z)`
   via `g_{ε,η}(z) = exp(± i Δ(z + i η) - ε cosh((π/2) confB (z + i η)))` and
   `PhragmenLindelof.right_half_plane_of_bounded_on_real`. Letting `η ↓ 0` and `ε ↓ 0` yields
   `majorant2D (confB z) = (schwarzSlit z).im` on `{0 < z.im}`, and specializing to `z_x` gives
   `HarmonicMajorantIdentification`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real Classical Interval

namespace FormalResearch.ModularBootstrap.PoissonJensen

/-! ### 1. Domain and holomorphy of `complexArsinh` and `pMap` -/

/-- Domain where `w^2 + 1 ∉ (-∞, 0]`, i.e., `ℂ \ {± i t | t ≥ 1}`. -/
def arsinhDomain : Set ℂ := {w : ℂ | w ^ 2 + 1 ∈ slitPlane}

lemma isOpen_arsinhDomain : IsOpen arsinhDomain :=
  isOpen_slitPlane.preimage (by fun_prop)

private lemma arg_lt_pi_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) : z.arg < π :=
  Complex.arg_lt_pi_iff.mpr (hz.imp le_of_lt id)

lemma cpow_half_re_pos {z : ℂ} (hz : z ∈ slitPlane) :
    0 < (z ^ (1 / 2 : ℂ)).re := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  rw [Complex.cpow_def_of_ne_zero hz0, Complex.exp_re]
  have him : (Complex.log z * (1 / 2 : ℂ)).im = Complex.arg z / 2 := by
    simp [Complex.mul_im, Complex.log_im]; ring
  rw [him]
  have hlt : z.arg < π := arg_lt_pi_of_mem_slitPlane hz
  have hgt : -π < z.arg := Complex.neg_pi_lt_arg z
  have hcos : 0 < Real.cos (Complex.arg z / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  exact mul_pos (Real.exp_pos _) hcos

private lemma cpow_half_sq' {z : ℂ} (hz : z ≠ 0) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [Complex.cpow_def_of_ne_zero hz, sq, ← Complex.exp_add]
  have h : Complex.log z * (1 / 2 : ℂ) + Complex.log z * (1 / 2 : ℂ) = Complex.log z := by ring
  rw [h, Complex.exp_log hz]

lemma arsinhDomain_add_sqrt_mem_slitPlane {w : ℂ} (hw : w ∈ arsinhDomain) :
    w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ slitPlane := by
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hs_re : 0 < s.re := cpow_half_re_pos hw
  have hs_sq : s ^ 2 = w ^ 2 + 1 := cpow_half_sq' (slitPlane_ne_zero hw)
  have hprod : (w + s) * (s - w) = 1 := by linear_combination hs_sq
  have hne : w + s ≠ 0 := by intro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  rw [mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  have him : (w + s).im = 0 := hnot.2
  have hre : (w + s).re ≤ 0 := hnot.1
  have hreal : ∃ r : ℝ, r < 0 ∧ w + s = (r : ℂ) := by
    refine ⟨(w + s).re, lt_of_le_of_ne hre ?_, Complex.ext rfl (by simpa using him)⟩
    intro h0; apply hne; exact Complex.ext h0 him
  obtain ⟨r, hr, hrs⟩ := hreal
  have hsw : s - w = ((r⁻¹ : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hne
    rw [hprod, hrs]
    push_cast
    rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne)]
  have h2s : 2 * s = ((r + r⁻¹ : ℝ) : ℂ) := by
    have : 2 * s = (w + s) + (s - w) := by ring
    rw [this, hrs, hsw]; push_cast; ring
  have h2s_re := congrArg Complex.re h2s
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Complex.ofReal_re] at h2s_re
  have hr_inv : r⁻¹ < 0 := inv_lt_zero.mpr hr
  linarith

lemma hasDerivAt_complexArsinh {w : ℂ} (hw : w ∈ arsinhDomain) :
    HasDerivAt complexArsinh ((w ^ 2 + 1) ^ (-(1 / 2 : ℂ))) w := by
  unfold complexArsinh
  have hw0 : w ^ 2 + 1 ≠ 0 := slitPlane_ne_zero hw
  have hd_sq : HasDerivAt (fun z : ℂ => z ^ 2 + 1) (2 * w) w := by
    simpa using ((hasDerivAt_id w).pow 2).add_const 1
  have hd_cpow : HasDerivAt (fun z : ℂ => (z ^ 2 + 1) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (w ^ 2 + 1) ^ ((1 / 2 : ℂ) - 1) * (2 * w)) w :=
    hd_sq.cpow_const hw
  have hd_sum : HasDerivAt (fun z : ℂ => z + (z ^ 2 + 1) ^ (1 / 2 : ℂ))
      (1 + (1 / 2 : ℂ) * (w ^ 2 + 1) ^ ((1 / 2 : ℂ) - 1) * (2 * w)) w :=
    (hasDerivAt_id w).add hd_cpow
  have hd_log := hd_sum.clog (arsinhDomain_add_sqrt_mem_slitPlane hw)
  refine hd_log.congr_deriv ?_
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hs_ne : s ≠ 0 := by
    intro h
    have hsq := cpow_half_sq' hw0
    change s ^ 2 = w ^ 2 + 1 at hsq
    rw [h, zero_pow two_ne_zero] at hsq
    exact hw0 hsq.symm
  have hs_sq : s ^ 2 = w ^ 2 + 1 := cpow_half_sq' hw0
  have hneg : (w ^ 2 + 1) ^ (-(1 / 2 : ℂ)) = s⁻¹ := by
    rw [Complex.cpow_neg]
  have hexp : (w ^ 2 + 1) ^ ((1 / 2 : ℂ) - 1) = s / (w ^ 2 + 1) := by
    rw [Complex.cpow_sub _ _ hw0, Complex.cpow_one]
  rw [hneg, hexp]
  have hadd_ne : w + s ≠ 0 := slitPlane_ne_zero (arsinhDomain_add_sqrt_mem_slitPlane hw)
  have hderiv_simp : 1 + (1 / 2 : ℂ) * (s / (w ^ 2 + 1)) * (2 * w) = (w + s) * s / (w ^ 2 + 1) := by
    field_simp [hw0]
    linear_combination -hs_sq
  rw [hderiv_simp]
  field_simp [hw0, hadd_ne, hs_ne]
  exact hs_sq

lemma neg_I_mul_sinh_pi_re_im (b : ℂ) :
    (-Complex.I * Complex.sinh ((π : ℂ) * b)).re = Real.cosh (π * b.re) * Real.sin (π * b.im) ∧
      (-Complex.I * Complex.sinh ((π : ℂ) * b)).im = -(Real.sinh (π * b.re) * Real.cos (π * b.im)) := by
  have hpb : (π : ℂ) * b = ((π * b.re : ℝ) : ℂ) + ((π * b.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hpb, Complex.sinh_add]
  have hs1 : Complex.sinh ((π * b.re : ℝ) : ℂ) = ((Real.sinh (π * b.re) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sinh]
  have hc1 : Complex.cosh ((π * b.re : ℝ) : ℂ) = ((Real.cosh (π * b.re) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cosh]
  have hs2 : Complex.sinh (((π * b.im : ℝ) : ℂ) * Complex.I) = ((Real.sin (π * b.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin]
  have hc2 : Complex.cosh (((π * b.im : ℝ) : ℂ) * Complex.I) = ((Real.cos (π * b.im) : ℝ) : ℂ) := by
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos]
  rw [hs1, hc1, hs2, hc2]
  have heq : -Complex.I * (((Real.sinh (π * b.re) : ℝ) : ℂ) * ((Real.cos (π * b.im) : ℝ) : ℂ) +
      ((Real.cosh (π * b.re) : ℝ) : ℂ) * (((Real.sin (π * b.im) : ℝ) : ℂ) * Complex.I)) =
      ((Real.cosh (π * b.re) * Real.sin (π * b.im) : ℝ) : ℂ) +
        ((-(Real.sinh (π * b.re) * Real.cos (π * b.im)) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.add_re]; ring
    · simp [Complex.mul_im, Complex.add_im]; ring
  rw [heq]
  constructor
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]; ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]; ring

lemma mem_arsinhDomain_of_slitStrip {b : ℂ} (hb : b ∈ slitStrip) :
    -Complex.I * Complex.sinh ((π : ℂ) * b) ∈ arsinhDomain := by
  set w : ℂ := -Complex.I * Complex.sinh ((π : ℂ) * b)
  change w ^ 2 + 1 ∈ slitPlane
  rw [mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  have hw2_im : (w ^ 2).im = 0 := by simpa using hnot.2
  have hw2_re : (w ^ 2).re ≤ -1 := by
    have h1 : (w ^ 2 + 1).re ≤ 0 := hnot.1
    have h2 : (w ^ 2 + 1).re = (w ^ 2).re + 1 := by simp
    linarith
  have him_eq : (w ^ 2).im = 2 * w.re * w.im := by simp [pow_two]; ring
  have hre_eq : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two]
  rw [him_eq] at hw2_im
  rw [hre_eq] at hw2_re
  have hw_im_ne : w.im ≠ 0 := by
    intro h0; rw [h0] at hw2_re; nlinarith [sq_nonneg w.re]
  have hw_re : w.re = 0 := by
    rcases mul_eq_zero.mp hw2_im with h | h
    · nlinarith
    · exact absurd h hw_im_ne
  rw [hw_re] at hw2_re
  have him_ge : 1 ≤ |w.im| := by
    have hsq : 1 ≤ w.im ^ 2 := by linarith
    exact (one_le_sq_iff_one_le_abs w.im).mp hsq
  obtain ⟨hre_f, him_f⟩ := neg_I_mul_sinh_pi_re_im b
  have hsin : Real.sin (π * b.im) = 0 := by
    have : Real.cosh (π * b.re) * Real.sin (π * b.im) = 0 := by rw [← hre_f]; exact hw_re
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (Real.cosh_pos _).ne'
    · exact h
  have hbim_lt : |b.im| < 1 / 2 := hb.1
  have hpi := Real.pi_pos
  have hpb_abs : |π * b.im| < π / 2 := by
    rw [abs_mul, abs_of_pos hpi]; nlinarith
  have hbim0 : b.im = 0 := by
    have h1 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [(abs_lt.mp hpb_abs).1])
      (by linarith [(abs_lt.mp hpb_abs).2])).mp hsin
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hpi.ne'
    · exact h
  have him_abs : |w.im| = |Real.sinh (π * b.re)| := by
    rw [him_f, hbim0, mul_zero, Real.cos_zero, mul_one, abs_neg]
  rw [him_abs] at him_ge
  have hxi_ge : xiStar ≤ |b.re| := by
    have hsinh_eq : Real.sinh (π * xiStar) = 1 := sinh_pi_mul_xiStar
    have hsinh_le : Real.sinh (π * xiStar) ≤ Real.sinh (π * |b.re|) := by
      rw [hsinh_eq]
      have habs_sinh : |Real.sinh (π * b.re)| = Real.sinh (π * |b.re|) := by
        rcases le_or_gt 0 b.re with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le h))]
        · have hm : π * b.re < 0 := mul_neg_of_pos_of_neg hpi h
          rw [abs_of_neg h, abs_of_neg (Real.sinh_neg_iff.mpr hm), mul_neg, Real.sinh_neg]
      rwa [← habs_sinh]
    have hpi_le : π * xiStar ≤ π * |b.re| := Real.sinh_le_sinh.mp hsinh_le
    exact le_of_mul_le_mul_left hpi_le hpi
  exact hb.2 ⟨hbim0, hxi_ge⟩

lemma differentiableOn_pMap_slitStrip : DifferentiableOn ℂ pMap slitStrip := by
  intro b hb
  unfold pMap
  have hd_sinh : HasDerivAt (fun z : ℂ => -Complex.I * Complex.sinh ((π : ℂ) * z))
      (-Complex.I * (Complex.cosh ((π : ℂ) * b) * π)) b := by
    have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) * z) (π : ℂ) b := by
      simpa using (hasDerivAt_id b).const_mul (π : ℂ)
    exact ((Complex.hasDerivAt_sinh _).comp b h1).const_mul (-Complex.I)
  have hd_ar := hasDerivAt_complexArsinh (mem_arsinhDomain_of_slitStrip hb)
  exact ((hd_ar.comp b hd_sinh).const_mul (π : ℂ)⁻¹).differentiableAt.differentiableWithinAt

lemma isOpen_slitStrip : IsOpen slitStrip := by
  unfold slitStrip
  have h1 : IsOpen {b : ℂ | |b.im| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have h2 : IsClosed {b : ℂ | b.im = 0 ∧ xiStar ≤ |b.re|} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_re))
  exact h1.sdiff h2

lemma pMap_conj (b : ℂ) (hb : b ∈ slitStrip) :
    pMap (starRingEnd ℂ b) = -starRingEnd ℂ (pMap b) := by
  have hw : -Complex.I * Complex.sinh ((π : ℂ) * b) ∈ arsinhDomain := mem_arsinhDomain_of_slitStrip hb
  set w : ℂ := -Complex.I * Complex.sinh ((π : ℂ) * b)
  have hw_conj : -Complex.I * Complex.sinh ((π : ℂ) * starRingEnd ℂ b) = -starRingEnd ℂ w := by
    dsimp [w]
    rw [map_mul, map_neg, Complex.conj_I, neg_neg, ← Complex.sinh_conj, map_mul,
      Complex.conj_ofReal]
    ring
  have har : complexArsinh (-starRingEnd ℂ w) = -starRingEnd ℂ (complexArsinh w) := by
    unfold complexArsinh
    have hw2_conj : ((-starRingEnd ℂ w) ^ 2 + 1) = starRingEnd ℂ (w ^ 2 + 1) := by
      simp [pow_two]
    have harg_ne_pi : (w ^ 2 + 1).arg ≠ π := (arg_lt_pi_of_mem_slitPlane hw).ne
    have hcpow_conj : ((-starRingEnd ℂ w) ^ 2 + 1) ^ (1 / 2 : ℂ) =
        starRingEnd ℂ ((w ^ 2 + 1) ^ (1 / 2 : ℂ)) := by
      have hh : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
        simp only [map_div₀, map_one, map_ofNat]
      have hconj_slit : starRingEnd ℂ (w ^ 2 + 1) ∈ slitPlane := by
        change w ^ 2 + 1 ∈ slitPlane at hw
        rw [mem_slitPlane_iff] at hw ⊢
        rcases hw with hre | him
        · left; simpa only [Complex.conj_re] using hre
        · right; simpa only [Complex.conj_im, neg_ne_zero] using him
      have harg_conj : (starRingEnd ℂ (w ^ 2 + 1)).arg ≠ π :=
        (arg_lt_pi_of_mem_slitPlane hconj_slit).ne
      rw [hw2_conj]
      conv_lhs => rw [← hh]
      simpa [RingHomCompTriple.comp_apply, Complex.conj_conj] using
        Complex.cpow_conj (starRingEnd ℂ (w ^ 2 + 1)) (1 / 2 : ℂ) harg_conj
    have hz_slit : w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ slitPlane :=
      arsinhDomain_add_sqrt_mem_slitPlane hw
    have hz_conj_slit : starRingEnd ℂ (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)) ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hz_slit ⊢
      rcases hz_slit with hre | him
      · left; simpa using hre
      · right; simp only [Complex.conj_im, neg_ne_zero]; exact him
    have hprod : (-starRingEnd ℂ w + starRingEnd ℂ ((w ^ 2 + 1) ^ (1 / 2 : ℂ))) *
        starRingEnd ℂ (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)) = 1 := by
      have hs2 : ((w ^ 2 + 1) ^ (1 / 2 : ℂ)) ^ 2 = w ^ 2 + 1 :=
        cpow_half_sq' (slitPlane_ne_zero hw)
      have h1 : ((w ^ 2 + 1) ^ (1 / 2 : ℂ) - w) * (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)) = 1 := by
        linear_combination hs2
      have h2 := congrArg (starRingEnd ℂ) h1
      simpa [sub_eq_add_neg, add_comm] using h2
    have hinv : -starRingEnd ℂ w + ((-starRingEnd ℂ w) ^ 2 + 1) ^ (1 / 2 : ℂ) =
        (starRingEnd ℂ (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)))⁻¹ := by
      rw [hcpow_conj]
      exact eq_inv_of_mul_eq_one_left hprod
    have harg_conj : (starRingEnd ℂ (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ))).arg ≠ π :=
      (arg_lt_pi_of_mem_slitPlane hz_conj_slit).ne
    have harg_orig : (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)).arg ≠ π :=
      (arg_lt_pi_of_mem_slitPlane hz_slit).ne
    rw [hinv, Complex.log_inv _ harg_conj, Complex.log_conj _ harg_orig]
  unfold pMap
  rw [hw_conj, har, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

lemma pMap_im_abs_le_half {b : ℂ} (hb : b ∈ slitStrip) : |(pMap b).im| ≤ 1 / 2 := by
  have hpi := Real.pi_pos
  have him_pos : ∀ {z : ℂ}, z ∈ slitStrip → 0 < z.im → |(pMap z).im| ≤ 1 / 2 := by
    intro z hz hzim
    set w : ℂ := -Complex.I * Complex.sinh ((π : ℂ) * z)
    have hw_dom : w ∈ arsinhDomain := mem_arsinhDomain_of_slitStrip hz
    have hw_re : 0 < w.re := by
      have h1 := (neg_I_mul_sinh_pi_re_im z).1
      have hzim_abs : |z.im| < 1 / 2 := hz.1
      have hsin : 0 < Real.sin (π * z.im) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hzim) (by
          have := (abs_lt.mp hzim_abs).2; nlinarith)
      rw [show w = -Complex.I * Complex.sinh ((π : ℂ) * z) from rfl, h1]
      exact mul_pos (Real.cosh_pos _) hsin
    have hs_re : 0 < ((w ^ 2 + 1) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hw_dom
    have hsum_re : 0 < (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)).re := by
      simp only [Complex.add_re]; linarith
    have harg : |Complex.arg (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ))| ≤ π / 2 := by
      have h1 := Complex.abs_arg_le_pi_div_two_iff.mpr hsum_re.le
      exact h1
    have hp_im : (pMap z).im = Complex.arg (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)) / π := by
      unfold pMap complexArsinh
      have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hpi_inv, Complex.im_ofReal_mul, Complex.log_im]
      change π⁻¹ * (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)).arg = _
      ring
    rw [hp_im, abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    linarith
  rcases lt_trichotomy b.im 0 with hneg | hzero | hpos
  · have hconj : starRingEnd ℂ b ∈ slitStrip := by
      refine ⟨by simpa using hb.1, ?_⟩
      rintro ⟨him, hre⟩
      simp only [Complex.conj_im, neg_eq_zero, Complex.conj_re] at him hre
      exact hb.2 ⟨him, hre⟩
    have h1 := him_pos hconj (by simpa using hneg)
    have h2 : (pMap b).im = (pMap (starRingEnd ℂ b)).im := by
      have hc := congrArg Complex.im (pMap_conj b hb)
      simp only [Complex.neg_im, Complex.conj_im, neg_neg] at hc
      exact hc.symm
    rwa [h2]
  · have hbre : |b.re| ≤ xiStar := by
      by_contra hlt
      push Not at hlt
      exact hb.2 ⟨hzero, hlt.le⟩
    have hb_eq : b = (b.re : ℂ) := Complex.ext rfl hzero
    rw [hb_eq, pMap_ofReal hbre]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, abs_div, abs_neg, abs_of_pos hpi, div_le_iff₀ hpi]
    unfold arcsinSinh
    have harc_le : |Real.arcsin (Real.sinh (π * b.re))| ≤ π / 2 :=
      abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
    linarith
  · exact him_pos hb hpos

lemma pMap_re_abs_le {b : ℂ} (hb : b ∈ slitStrip) : |(pMap b).re| ≤ |b.re| + 1 := by
  have hpi := Real.pi_pos
  set w : ℂ := -Complex.I * Complex.sinh ((π : ℂ) * b)
  have hw_dom : w ∈ arsinhDomain := mem_arsinhDomain_of_slitStrip hb
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hs_sq : s ^ 2 = w ^ 2 + 1 := cpow_half_sq' (slitPlane_ne_zero hw_dom)
  have hprod : (w + s) * (s - w) = 1 := by linear_combination hs_sq
  have hsum_ne : w + s ≠ 0 := by intro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  have hs_norm : ‖s‖ ≤ ‖w‖ + 1 := by
    have h1 : ‖s‖ ^ 2 = ‖w ^ 2 + 1‖ := by
      rw [← Complex.norm_pow, hs_sq]
    have h2 : ‖w ^ 2 + 1‖ ≤ (‖w‖ + 1) ^ 2 := by
      calc ‖w ^ 2 + 1‖ ≤ ‖w ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖w‖ ^ 2 + 1 := by simp [norm_pow]
        _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ + 1 := by linarith [norm_nonneg w]
        _ = (‖w‖ + 1) ^ 2 := by ring
    nlinarith [norm_nonneg s, norm_nonneg w]
  have hsum_ub : ‖w + s‖ ≤ 2 * ‖w‖ + 1 := by
    calc ‖w + s‖ ≤ ‖w‖ + ‖s‖ := norm_add_le _ _
      _ ≤ ‖w‖ + (‖w‖ + 1) := by linarith
      _ = 2 * ‖w‖ + 1 := by ring
  have hinv_ub : ‖w + s‖⁻¹ ≤ 2 * ‖w‖ + 1 := by
    have hnorm_inv : ‖w + s‖⁻¹ = ‖s - w‖ := by
      have : (w + s)⁻¹ = s - w := inv_eq_of_mul_eq_one_right hprod
      rw [← this, norm_inv]
    rw [hnorm_inv]
    calc ‖s - w‖ ≤ ‖s‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ (‖w‖ + 1) + ‖w‖ := by linarith
      _ = 2 * ‖w‖ + 1 := by ring
  have hlog_bd : |Real.log ‖w + s‖| ≤ Real.log (2 * ‖w‖ + 1) := by
    have hpos : 0 < ‖w + s‖ := norm_pos_iff.mpr hsum_ne
    rw [abs_le]
    constructor
    · have hle : Real.log (‖w + s‖⁻¹) ≤ Real.log (2 * ‖w‖ + 1) :=
        Real.log_le_log (inv_pos.mpr hpos) hinv_ub
      rw [Real.log_inv] at hle
      linarith
    · exact Real.log_le_log hpos hsum_ub
  have hw_bd : ‖w‖ ≤ Real.exp (π * |b.re|) := by
    have hw_norm : ‖w‖ = ‖Complex.sinh ((π : ℂ) * b)‖ := by
      dsimp [w]; rw [norm_mul, norm_neg, norm_I, one_mul]
    have hsinh_sq : ‖Complex.sinh ((π : ℂ) * b)‖ ^ 2 =
        Real.sinh (π * b.re) ^ 2 + Real.sin (π * b.im) ^ 2 := by
      have hre_im := neg_I_mul_sinh_pi_re_im b
      have heq : ‖Complex.sinh ((π : ℂ) * b)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
        rw [← hw_norm, Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq]
      rw [heq, hre_im.1, hre_im.2]
      have hcosh : Real.cosh (π * b.re) ^ 2 = Real.sinh (π * b.re) ^ 2 + 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
      have hsin : Real.sin (π * b.im) ^ 2 + Real.cos (π * b.im) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq _
      calc (Real.cosh (π * b.re) * Real.sin (π * b.im)) ^ 2 +
            (-(Real.sinh (π * b.re) * Real.cos (π * b.im))) ^ 2
          = (Real.sinh (π * b.re) ^ 2 + 1) * Real.sin (π * b.im) ^ 2 +
              Real.sinh (π * b.re) ^ 2 * Real.cos (π * b.im) ^ 2 := by rw [← hcosh]; ring
        _ = Real.sinh (π * b.re) ^ 2 * (Real.sin (π * b.im) ^ 2 + Real.cos (π * b.im) ^ 2) +
              Real.sin (π * b.im) ^ 2 := by ring
        _ = Real.sinh (π * b.re) ^ 2 + Real.sin (π * b.im) ^ 2 := by rw [hsin, mul_one]
    have hle_cosh : ‖w‖ ≤ Real.cosh (π * b.re) := by
      have h1 : Real.sinh (π * b.re) ^ 2 + Real.sin (π * b.im) ^ 2 ≤ Real.cosh (π * b.re) ^ 2 := by
        have hsin1 : Real.sin (π * b.im) ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_le_one (π * b.im)]
        linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
      have hsq : ‖w‖ ^ 2 ≤ Real.cosh (π * b.re) ^ 2 := by rwa [hw_norm, hsinh_sq]
      nlinarith [norm_nonneg w, Real.cosh_pos (π * b.re)]
    have hcosh_exp : Real.cosh (π * b.re) ≤ Real.exp (π * |b.re|) := by
      rw [Real.cosh_eq]
      have h1 : Real.exp (π * b.re) ≤ Real.exp (π * |b.re|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) hpi.le)
      have h2 : Real.exp (-(π * b.re)) ≤ Real.exp (π * |b.re|) :=
        Real.exp_le_exp.mpr (by rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) hpi.le)
      linarith
    exact hle_cosh.trans hcosh_exp
  have h2w1 : 2 * ‖w‖ + 1 ≤ Real.exp (π * |b.re| + π) := by
    have he : (3 : ℝ) ≤ Real.exp π := by
      have h0 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
      have hsq : (4 : ℝ) ≤ Real.exp (1 + 1) := by rw [Real.exp_add]; nlinarith
      have h2pi : (1 + 1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
      linarith [Real.exp_le_exp.mpr h2pi]
    calc 2 * ‖w‖ + 1 ≤ 2 * Real.exp (π * |b.re|) + 1 := by linarith
      _ ≤ 2 * Real.exp (π * |b.re|) + Real.exp (π * |b.re|) := by
          gcongr; exact Real.one_le_exp (by positivity)
      _ = 3 * Real.exp (π * |b.re|) := by ring
      _ ≤ Real.exp π * Real.exp (π * |b.re|) := by gcongr
      _ = Real.exp (π * |b.re| + π) := by rw [← Real.exp_add]; ring_nf
  have hp_re : (pMap b).re = Real.log ‖w + s‖ / π := by
    unfold pMap complexArsinh
    have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hpi_inv, Complex.re_ofReal_mul, Complex.log_re]
    change π⁻¹ * Real.log ‖w + s‖ = _
    ring
  rw [hp_re, abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
  have hlog_le : Real.log (2 * ‖w‖ + 1) ≤ π * |b.re| + π :=
    (Real.log_le_log (by positivity) h2w1).trans (by rw [Real.log_exp])
  linarith [hlog_bd]

/-! ### 2. Holomorphic completion `majorantHolomorphic` and `majorant2D` -/

/-- Holomorphic completion of `U` on `slitStrip`:
`Φ_U(b) = i U₀ + (4π/3) ∫₀¹ p(t b) b dt`. -/
noncomputable def majorantHolomorphic (b : ℂ) : ℂ :=
  Complex.I * (majorantU0 : ℂ) + ((4 * π / 3 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b

/-- Harmonic majorant `U(b) = Im Φ_U(b)` on `slitStrip`. -/
noncomputable def majorant2D (b : ℂ) : ℝ := (majorantHolomorphic b).im

lemma smul_mem_slitStrip {b : ℂ} (hb : b ∈ slitStrip) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) * b ∈ slitStrip := by
  have hre : ((t : ℂ) * b).re = t * b.re := by simp
  have him : ((t : ℂ) * b).im = t * b.im := by simp
  refine ⟨?_, ?_⟩
  · change |((t : ℂ) * b).im| < 1 / 2
    rw [him, abs_mul, abs_of_nonneg ht0]
    have hbim : |b.im| < 1 / 2 := hb.1
    nlinarith [abs_nonneg b.im]
  · rintro ⟨htim, htre⟩
    rw [him] at htim
    rw [hre, abs_mul, abs_of_nonneg ht0] at htre
    rcases mul_eq_zero.mp htim with rfl | hbim0
    · simp only [zero_mul] at htre
      linarith [xiStar_pos]
    · have hle : t * |b.re| ≤ |b.re| := mul_le_of_le_one_left (abs_nonneg b.re) ht1
      exact hb.2 ⟨hbim0, htre.trans hle⟩

lemma hasDerivAt_majorantHolomorphic {b₀ : ℂ} (hb₀ : b₀ ∈ slitStrip) :
    HasDerivAt majorantHolomorphic (((4 * π / 3 : ℝ) : ℂ) * pMap b₀) b₀ := by
  have hcompact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have hcont_mul : Continuous fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 :=
    Complex.continuous_ofReal.comp continuous_fst |>.mul continuous_snd
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * b₀ ∈ slitStrip := fun t ht =>
    smul_mem_slitStrip hb₀ ht.1 ht.2
  have hopen_pre : IsOpen {p : ℝ × ℂ | (p.1 : ℂ) * p.2 ∈ slitStrip} :=
    isOpen_slitStrip.preimage hcont_mul
  have hsub : Icc (0 : ℝ) 1 ×ˢ ({b₀} : Set ℂ) ⊆ {p : ℝ × ℂ | (p.1 : ℂ) * p.2 ∈ slitStrip} := by
    rintro ⟨t, b⟩ ⟨ht, hb⟩
    rw [mem_singleton_iff] at hb; subst hb
    exact hmem t ht
  obtain ⟨U, V, hU_open, hV_open, hIU, hbV, hUV⟩ :=
    generalized_tube_lemma hcompact isCompact_singleton hopen_pre hsub
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hV_open b₀ (hbV (mem_singleton b₀))
  have htube : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b ∈ Metric.ball b₀ δ, (t : ℂ) * b ∈ slitStrip :=
    fun t ht b hb => show (t, b) ∈ {p : ℝ × ℂ | (p.1 : ℂ) * p.2 ∈ slitStrip} from
      hUV ⟨hIU ht, hball hb⟩
  -- Derivative of `pMap` on `slitStrip`
  have hp_an : AnalyticOnNhd ℂ pMap slitStrip :=
    differentiableOn_pMap_slitStrip.analyticOnNhd isOpen_slitStrip
  obtain ⟨pDeriv, hp_diff, hpDeriv_cont⟩ :
      ∃ pDeriv : ℂ → ℂ, (∀ w ∈ slitStrip, HasDerivAt pMap (pDeriv w) w) ∧
        ContinuousOn pDeriv slitStrip :=
    ⟨deriv pMap, fun w hw =>
      (differentiableOn_pMap_slitStrip w hw).differentiableAt
        (isOpen_slitStrip.mem_nhds hw) |>.hasDerivAt,
      hp_an.deriv.continuousOn⟩
  have hp_cont : ContinuousOn pMap slitStrip := differentiableOn_pMap_slitStrip.continuousOn
  -- Bound on `closedBall b₀ (δ / 2)`
  have hcb_sub : Metric.closedBall b₀ (δ / 2) ⊆ Metric.ball b₀ δ :=
    Metric.closedBall_subset_ball (by linarith)
  have hK_compact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall b₀ (δ / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall b₀ (δ / 2))
  let F : ℂ → ℝ → ℂ := fun b t => pMap ((t : ℂ) * b) * b
  obtain ⟨F', hF'_def⟩ : ∃ F' : ℂ → ℝ → ℂ,
      F' = fun (b : ℂ) (t : ℝ) => pMap ((t : ℂ) * b) + (t : ℂ) * b * pDeriv ((t : ℂ) * b) := ⟨_, rfl⟩
  have hF'_app : ∀ b t, F' b t = pMap ((t : ℂ) * b) + (t : ℂ) * b * pDeriv ((t : ℂ) * b) := fun b t => by
    rw [hF'_def]
  have hF'_cont : ContinuousOn (fun p : ℝ × ℂ => F' p.2 p.1) (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall b₀ (δ / 2)) := by
    rw [hF'_def]
    have hm : MapsTo (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall b₀ (δ / 2)) slitStrip :=
      fun p hp => htube p.1 hp.1 p.2 (hcb_sub hp.2)
    have h1 : ContinuousOn (fun p : ℝ × ℂ => pMap ((p.1 : ℂ) * p.2)) (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall b₀ (δ / 2)) :=
      hp_cont.comp hcont_mul.continuousOn hm
    have h2 : ContinuousOn (fun p : ℝ × ℂ => pDeriv ((p.1 : ℂ) * p.2)) (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall b₀ (δ / 2)) :=
      hpDeriv_cont.comp hcont_mul.continuousOn hm
    exact h1.add (hcont_mul.continuousOn.mul h2)
  have hK_ne : (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall b₀ (δ / 2)).Nonempty :=
    ⟨(0, b₀), ⟨le_rfl, zero_le_one⟩, Metric.mem_closedBall_self (by linarith)⟩
  obtain ⟨p_max, _, hp_max⟩ := hK_compact.exists_isMaxOn hK_ne hF'_cont.norm
  obtain ⟨M_bd, hM_bd⟩ : ∃ M_bd : ℝ, M_bd = ‖F' p_max.2 p_max.1‖ := ⟨_, rfl⟩
  have hF_meas : ∀ b ∈ Metric.ball b₀ (δ / 2),
      AEStronglyMeasurable (F b) (volume.restrict (Ι 0 1)) := fun b hb => by
    have hm : MapsTo (fun t : ℝ => (t : ℂ) * b) (Icc 0 1) slitStrip :=
      fun t ht => htube t ht b (hcb_sub (Metric.ball_subset_closedBall hb))
    have hcont : ContinuousOn (F b) (Icc 0 1) :=
      (hp_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn hm).mul
        continuousOn_const
    rw [Set.uIoc_of_le zero_le_one]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : IntervalIntegrable (F b₀) volume 0 1 := by
    have hm : MapsTo (fun t : ℝ => (t : ℂ) * b₀) (Icc 0 1) slitStrip :=
      fun t ht => hmem t ht
    have hcont : ContinuousOn (F b₀) (Icc 0 1) :=
      (hp_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn hm).mul
        continuousOn_const
    exact hcont.intervalIntegrable_of_Icc zero_le_one
  have hF'_meas : AEStronglyMeasurable (F' b₀) (volume.restrict (Ι 0 1)) := by
    rw [Set.uIoc_of_le zero_le_one, hF'_def]
    have hm : MapsTo (fun t : ℝ => (t : ℂ) * b₀) (Icc 0 1) slitStrip := fun t ht => hmem t ht
    have hmul_cont : Continuous fun t : ℝ => (t : ℂ) * b₀ :=
      Complex.continuous_ofReal.mul continuous_const
    have hcont : ContinuousOn (fun t : ℝ => pMap ((t : ℂ) * b₀) + (t : ℂ) * b₀ * pDeriv ((t : ℂ) * b₀)) (Icc 0 1) :=
      (hp_cont.comp hmul_cont.continuousOn hm).add
        (hmul_cont.continuousOn.mul (hpDeriv_cont.comp hmul_cont.continuousOn hm))
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ b ∈ Metric.ball b₀ (δ / 2), ‖F' b t‖ ≤ M_bd := by
    refine Eventually.of_forall fun t ht b hb => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [hM_bd]
    exact @hp_max (t, b) ⟨Ioc_subset_Icc_self ht, Metric.ball_subset_closedBall hb⟩
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ b ∈ Metric.ball b₀ (δ / 2),
      HasDerivAt (fun z => F z t) (F' b t) b := by
    refine Eventually.of_forall fun t ht b hb => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hmem_tb : (t : ℂ) * b ∈ slitStrip :=
      htube t (Ioc_subset_Icc_self ht) b (hcb_sub (Metric.ball_subset_closedBall hb))
    have hd_lin : HasDerivAt (fun z : ℂ => (t : ℂ) * z) (t : ℂ) b := by
      simpa using (hasDerivAt_id b).const_mul (t : ℂ)
    have hd_p : HasDerivAt (fun z : ℂ => pMap ((t : ℂ) * z)) (pDeriv ((t : ℂ) * b) * (t : ℂ)) b :=
      (hp_diff _ hmem_tb).comp b hd_lin
    have hd_mul := hd_p.mul (hasDerivAt_id b)
    refine hd_mul.congr_deriv ?_
    rw [hF'_app]
    dsimp only [id_eq]
    ring
  have hF_meas_nhds : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable (F b) (volume.restrict (Ι 0 1)) := by
    filter_upwards [Metric.ball_mem_nhds b₀ (half_pos hδ_pos)] with b hb
    exact hF_meas b hb
  have hderiv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds b₀ (half_pos hδ_pos))
    hF_meas_nhds hF_int hF'_meas h_bound intervalIntegrable_const h_diff).2
  -- Now evaluate `∫ t in 0..1, F' b₀ t = pMap b₀` via FTC on `t ↦ (t : ℂ) * pMap ((t : ℂ) * b₀)`
  have hftc : ∫ t in (0 : ℝ)..1, F' b₀ t = pMap b₀ := by
    have hG_deriv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => (s : ℂ) * pMap ((s : ℂ) * b₀)) (F' b₀ t) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hlin_R : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
        simpa using (hasDerivAt_id t).ofReal_comp
      have hlin_b : HasDerivAt (fun s : ℝ => (s : ℂ) * b₀) b₀ t := by
        simpa using (hlin_R.mul_const b₀)
      have hp_t := (hp_diff _ (hmem t ht)).comp t hlin_b
      have hmul := hlin_R.mul hp_t
      refine hmul.congr_deriv ?_
      dsimp only [Function.comp_apply]
      rw [hF'_app]; ring
    have hF'_int : IntervalIntegrable (F' b₀) volume 0 1 :=
      (hF'_cont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht, Metric.mem_closedBall_self (by linarith)⟩)).intervalIntegrable_of_Icc zero_le_one
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hG_deriv hF'_int
    simpa using heq
  rw [hftc] at hderiv
  exact (hderiv.const_mul ((4 * π / 3 : ℝ) : ℂ)).const_add (Complex.I * (majorantU0 : ℂ))

lemma differentiableOn_majorantHolomorphic : DifferentiableOn ℂ majorantHolomorphic slitStrip :=
  fun _ hb => (hasDerivAt_majorantHolomorphic hb).differentiableAt.differentiableWithinAt

lemma complexArsinh_neg {w : ℂ} (hw : w ∈ arsinhDomain) :
    complexArsinh (-w) = -complexArsinh w := by
  unfold complexArsinh
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hsq : (-w) ^ 2 + 1 = w ^ 2 + 1 := by ring
  rw [hsq]
  have hs_sq : s ^ 2 = w ^ 2 + 1 := cpow_half_sq' (slitPlane_ne_zero hw)
  have hprod : (-w + s) * (w + s) = 1 := by linear_combination hs_sq
  have hinv : -w + s = (w + s)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hz_slit : w + s ∈ slitPlane := arsinhDomain_add_sqrt_mem_slitPlane hw
  have harg : (w + s).arg ≠ π := (arg_lt_pi_of_mem_slitPlane hz_slit).ne
  rw [hinv, Complex.log_inv _ harg]

lemma pMap_neg {b : ℂ} (hb : b ∈ slitStrip) : pMap (-b) = -pMap b := by
  unfold pMap
  have h1 : -Complex.I * Complex.sinh ((π : ℂ) * -b) = -(-Complex.I * Complex.sinh ((π : ℂ) * b)) := by
    rw [mul_neg, Complex.sinh_neg]; ring
  rw [h1, complexArsinh_neg (mem_arsinhDomain_of_slitStrip hb)]
  ring

lemma neg_mem_slitStrip {b : ℂ} (hb : b ∈ slitStrip) : -b ∈ slitStrip := by
  refine ⟨?_, ?_⟩
  · simpa [abs_neg] using hb.1
  · rintro ⟨him, hre⟩
    simp only [Complex.neg_im, neg_eq_zero, Complex.neg_re, abs_neg] at him hre
    exact hb.2 ⟨him, hre⟩

lemma majorant2D_neg {b : ℂ} (hb : b ∈ slitStrip) : majorant2D (-b) = majorant2D b := by
  unfold majorant2D majorantHolomorphic
  have heq : ∀ t ∈ uIcc (0 : ℝ) 1, pMap ((t : ℂ) * (-b)) * (-b) = pMap ((t : ℂ) * b) * b := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have htb : (t : ℂ) * b ∈ slitStrip := smul_mem_slitStrip hb ht.1 ht.2
    rw [show (t : ℂ) * (-b) = -((t : ℂ) * b) by ring, pMap_neg htb]
    ring
  rw [intervalIntegral.integral_congr heq]

lemma majorant2D_conj {b : ℂ} (hb : b ∈ slitStrip) :
    majorant2D (starRingEnd ℂ b) = majorant2D b := by
  have hconj_mem : starRingEnd ℂ b ∈ slitStrip := by
    refine ⟨by simpa using hb.1, ?_⟩
    rintro ⟨him, hre⟩
    simp only [Complex.conj_im, neg_eq_zero, Complex.conj_re] at him hre
    exact hb.2 ⟨him, hre⟩
  have hint_cont : ContinuousOn (fun t : ℝ => pMap ((t : ℂ) * b) * b) (Icc 0 1) :=
    (differentiableOn_pMap_slitStrip.continuousOn.comp
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
      (fun t ht => smul_mem_slitStrip hb ht.1 ht.2)).mul continuousOn_const
  have hint_eq : ∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * starRingEnd ℂ b) * starRingEnd ℂ b =
      -starRingEnd ℂ (∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b) := by
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
        pMap ((t : ℂ) * starRingEnd ℂ b) * starRingEnd ℂ b =
          -starRingEnd ℂ (pMap ((t : ℂ) * b) * b) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have htb : (t : ℂ) * b ∈ slitStrip := smul_mem_slitStrip hb ht.1 ht.2
      have harg : (t : ℂ) * starRingEnd ℂ b = starRingEnd ℂ ((t : ℂ) * b) := by
        rw [map_mul, Complex.conj_ofReal]
      rw [harg, pMap_conj _ htb, map_mul]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg]
    have hcomm : (∫ t in (0 : ℝ)..1, Complex.conjCLE.toContinuousLinearMap (pMap ((t : ℂ) * b) * b)) =
        Complex.conjCLE.toContinuousLinearMap (∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b) :=
      Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
        (hint_cont.intervalIntegrable_of_Icc zero_le_one)
    exact congrArg Neg.neg hcomm
  unfold majorant2D majorantHolomorphic
  rw [hint_eq]
  have hconst : ((4 * π / 3 : ℝ) : ℂ) * (-starRingEnd ℂ (∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b)) =
      -starRingEnd ℂ (((4 * π / 3 : ℝ) : ℂ) * (∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b)) := by
    rw [map_mul, Complex.conj_ofReal]; ring
  rw [hconst]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_im, Complex.neg_im]
  ring

lemma majorant2D_ofReal_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ xiStar) :
    majorant2D (x : ℂ) = majorantReal x := by
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · have h0 : majorant2D (0 : ℂ) = majorantU0 := by
      unfold majorant2D majorantHolomorphic
      simp
    have hr0 : majorantReal 0 = majorantU0 := by
      rw [majorantReal_of_abs_le (by simp [xiStar_pos.le])]
      simp
    simpa using h0.trans hr0.symm
  · rw [majorantReal_eq_path ⟨hx0, hx1⟩]
    unfold majorant2D majorantHolomorphic
    have hsub : ∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * (x : ℂ)) * (x : ℂ) =
        ∫ s in (0 : ℝ)..x, pMap (s : ℂ) := by
      have h1 : ∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * (x : ℂ)) * (x : ℂ) =
          (∫ t in (0 : ℝ)..1, pMap (((t * x : ℝ) : ℂ))) * (x : ℂ) := by
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_congr fun t _ => ?_
        push_cast; rfl
      rw [h1, intervalIntegral.integral_comp_mul_right (fun s : ℝ => pMap (s : ℂ)) hxpos.ne']
      simp only [zero_mul, one_mul, Complex.real_smul]
      have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
      push_cast
      field_simp [hxC]
    rw [hsub]
    simp [Complex.add_im, Complex.mul_im]

lemma arcsinSinh_neg (x : ℝ) : arcsinSinh (-x) = -arcsinSinh x := by
  unfold arcsinSinh
  rw [mul_neg, Real.sinh_neg, Real.arcsin_neg]

lemma majorant2D_ofReal {x : ℝ} (hx : |x| ≤ xiStar) :
    majorant2D (x : ℂ) = majorantReal x := by
  rw [majorantReal_of_abs_le hx]
  unfold majorant2D majorantHolomorphic
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
      pMap ((t : ℂ) * (x : ℂ)) * (x : ℂ) =
        ((-arcsinSinh (t * x) / π : ℝ) : ℂ) * Complex.I * (x : ℂ) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have htx : |t * x| ≤ xiStar := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg x) ht.2).trans hx
    rw [show (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) by push_cast; rfl, pMap_ofReal htx]
  rw [intervalIntegral.integral_congr hcongr]
  have him_int : (∫ t in (0 : ℝ)..1,
      ((-arcsinSinh (t * x) / π : ℝ) : ℂ) * Complex.I * (x : ℂ)).im =
      ∫ t in (0 : ℝ)..1, (-arcsinSinh (t * x) / π) * x := by
    have heq2 : ∀ t : ℝ,
        ((-arcsinSinh (t * x) / π : ℝ) : ℂ) * Complex.I * (x : ℂ) =
          ((((-arcsinSinh (t * x) / π) * x : ℝ) : ℂ)) * Complex.I := by
      intro t; push_cast; ring
    simp_rw [heq2, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    simp
  have hre : (Complex.I * (majorantU0 : ℂ) +
      ((4 * π / 3 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
        ((-arcsinSinh (t * x) / π : ℝ) : ℂ) * Complex.I * (x : ℂ)).im =
      majorantU0 + (4 * π / 3) * (∫ t in (0 : ℝ)..1, (-arcsinSinh (t * x) / π) * x) := by
    rw [Complex.add_im]
    have h1 : (Complex.I * (majorantU0 : ℂ)).im = majorantU0 := by simp
    rw [h1, Complex.im_ofReal_mul, him_int]
  rw [hre]
  rcases eq_or_lt_of_le (abs_nonneg x) with habs0 | _
  · have hx0 : x = 0 := abs_eq_zero.mp habs0.symm
    subst hx0; simp
  · have hx_ne : x ≠ 0 := fun h => by subst h; simp at *
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    have hsub : ∫ t in (0 : ℝ)..1, (-arcsinSinh (t * x) / π) * x =
        -(∫ u in (0 : ℝ)..x, arcsinSinh u) / π := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_comp_mul_right (fun u : ℝ => -arcsinSinh u / π) hx_ne]
      simp only [zero_mul, one_mul, smul_eq_mul]
      have h1 : x⁻¹ * (∫ u in (0 : ℝ)..x, -arcsinSinh u / π) * x =
          -(∫ u in (0 : ℝ)..x, arcsinSinh u) / π := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
        field_simp [hx_ne]
      exact h1
    rw [hsub]
    have habs_int : ∫ u in (0 : ℝ)..x, arcsinSinh u = ∫ s in (0 : ℝ)..|x|, arcsinSinh s := by
      rcases le_or_gt 0 x with hx0 | hxneg
      · rw [abs_of_nonneg hx0]
      · rw [abs_of_neg hxneg]
        have hcomp := intervalIntegral.integral_comp_neg arcsinSinh (a := (0 : ℝ)) (b := -x)
        simp only [neg_zero, neg_neg] at hcomp
        have heq : (fun s : ℝ => arcsinSinh (-s)) = (fun s : ℝ => -arcsinSinh s) := by
          ext s; exact arcsinSinh_neg s
        rw [heq, intervalIntegral.integral_neg] at hcomp
        rw [intervalIntegral.integral_symm (a := 0) (b := x)] at hcomp
        linarith [hcomp]
    rw [habs_int]
    field_simp [hpi]
    ring

lemma majorant2D_abs_le {b : ℂ} (hb : b ∈ slitStrip) :
    |majorant2D b| ≤ |majorantU0| + (4 * π / 3) * (|b.re| + 2) ^ 2 := by
  have hpi := Real.pi_pos
  have him_le : |majorant2D b| ≤ ‖majorantHolomorphic b‖ := Complex.abs_im_le_norm _
  have hnorm_U : ‖Complex.I * (majorantU0 : ℂ)‖ = |majorantU0| := by
    rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm_c : ‖((4 * π / 3 : ℝ) : ℂ)‖ = 4 * π / 3 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖pMap ((t : ℂ) * b) * b‖ ≤ (|b.re| + 2) ^ 2 := by
    intro t ht
    have htb : (t : ℂ) * b ∈ slitStrip := smul_mem_slitStrip hb ht.1 ht.2
    have hp_re : |(pMap ((t : ℂ) * b)).re| ≤ |b.re| + 1 := by
      have h1 := pMap_re_abs_le htb
      have h2 : |((t : ℂ) * b).re| ≤ |b.re| := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          abs_mul, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (abs_nonneg b.re) ht.2
      linarith
    have hp_im : |(pMap ((t : ℂ) * b)).im| ≤ 1 / 2 := pMap_im_abs_le_half htb
    have hp_norm : ‖pMap ((t : ℂ) * b)‖ ≤ |b.re| + 2 := by
      have := Complex.norm_le_abs_re_add_abs_im (pMap ((t : ℂ) * b))
      linarith
    have hb_norm : ‖b‖ ≤ |b.re| + 2 := by
      have hle := Complex.norm_le_abs_re_add_abs_im b
      have hbim : |b.im| < 1 / 2 := hb.1
      linarith
    rw [norm_mul]
    nlinarith [norm_nonneg (pMap ((t : ℂ) * b)), norm_nonneg b, abs_nonneg b.re]
  have hint_norm : ‖∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b‖ ≤ (|b.re| + 2) ^ 2 := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := (|b.re| + 2) ^ 2) (fun t ht => by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact hbd t (Ioc_subset_Icc_self ht))
    simpa using h1
  calc |majorant2D b| ≤ ‖majorantHolomorphic b‖ := him_le
    _ ≤ ‖Complex.I * (majorantU0 : ℂ)‖ +
        ‖((4 * π / 3 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b‖ := norm_add_le _ _
    _ = |majorantU0| + (4 * π / 3) * ‖∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b‖ := by
        rw [hnorm_U, norm_mul, hnorm_c]
    _ ≤ |majorantU0| + (4 * π / 3) * (|b.re| + 2) ^ 2 := by
        gcongr

/-! ### 3. Boundary limits of `majorant2D` on edges and slits -/

lemma majorant2D_sub_horizontal {y : ℝ} (hy_abs : |y| < 1 / 2) (hy_ne : y ≠ 0) (x₁ x₂ : ℝ) :
    majorant2D ((x₂ : ℂ) + (y : ℂ) * Complex.I) -
        majorant2D ((x₁ : ℂ) + (y : ℂ) * Complex.I) =
      (4 * π / 3) * ∫ t in x₁..x₂, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im := by
  have hmem : ∀ t : ℝ, (t : ℂ) + (y : ℂ) * Complex.I ∈ slitStrip := by
    intro t
    refine ⟨?_, ?_⟩
    · simpa using hy_abs
    · rintro ⟨him, _⟩
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one] at him
      exact hy_ne (by linarith)
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => majorant2D ((s : ℂ) + (y : ℂ) * Complex.I))
        ((4 * π / 3) * (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) t := by
    intro t
    have hd_line : HasDerivAt (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) 1 t := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t) |>.add_const ((y : ℂ) * Complex.I)
    have hd_hol := (hasDerivAt_majorantHolomorphic (hmem t)).scomp t hd_line
    have hd_im := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd_hol
    refine hd_im.congr_deriv ?_
    change ((1 : ℂ) • (((4 * π / 3 : ℝ) : ℂ) * pMap ((t : ℂ) + (y : ℂ) * Complex.I))).im = _
    rw [one_smul, Complex.im_ofReal_mul]
  have hcont : Continuous (fun t : ℝ => (4 * π / 3) * (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) := by
    have hmap : Continuous (fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    have hp : Continuous (fun t : ℝ => pMap ((t : ℂ) + (y : ℂ) * Complex.I)) :=
      differentiableOn_pMap_slitStrip.continuousOn.comp_continuous hmap hmem
    exact continuous_const.mul (Complex.continuous_im.comp hp)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x₁) (b := x₂)
    (fun t _ => hderiv t) (hcont.intervalIntegrable x₁ x₂)
  rw [intervalIntegral.integral_const_mul] at hftc
  exact hftc.symm

lemma majorant2D_lipschitz_re {y : ℝ} (hy_abs : |y| < 1 / 2) (hy_ne : y ≠ 0) (x₁ x₂ : ℝ) :
    |majorant2D ((x₁ : ℂ) + (y : ℂ) * Complex.I) -
        majorant2D ((x₂ : ℂ) + (y : ℂ) * Complex.I)| ≤
      (2 * π / 3) * |x₁ - x₂| := by
  have hpi := Real.pi_pos
  have hsub := majorant2D_sub_horizontal hy_abs hy_ne x₂ x₁
  rw [hsub]
  have hbd : ∀ t ∈ uIoc x₂ x₁, ‖(pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im‖ ≤ 1 / 2 := by
    intro t _
    rw [Real.norm_eq_abs]
    exact pMap_im_abs_le_half ⟨by simpa using hy_abs, fun ⟨him, _⟩ => by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one] at him
      exact hy_ne (by linarith)⟩
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs] at hint
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π / 3)]
  have hle : (4 * π / 3) * |∫ t in x₂..x₁, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im| ≤
      (4 * π / 3) * ((1 / 2) * |x₁ - x₂|) := by
    gcongr
  linarith

lemma majorant2D_I_mul {y : ℝ} (hy : |y| < 1 / 2) :
    majorant2D ((y : ℂ) * Complex.I) = majorantImag y := by
  rw [majorantImag_eq]
  unfold majorant2D majorantHolomorphic
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
      pMap ((t : ℂ) * ((y : ℂ) * Complex.I)) * ((y : ℂ) * Complex.I) =
        (((Real.arsinh (Real.sin (π * (t * y))) / π) * y : ℝ) : ℂ) * Complex.I := by
    intro t _
    have h1 : (t : ℂ) * ((y : ℂ) * Complex.I) = ((t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1, pMap_mul_I]
    push_cast; ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal]
  have him : (Complex.I * (majorantU0 : ℂ) +
      ((4 * π / 3 : ℝ) : ℂ) * (((∫ t in (0 : ℝ)..1,
        Real.arsinh (Real.sin (π * (t * y))) / π * y : ℝ) : ℂ) * Complex.I)).im =
      majorantU0 + (4 * π / 3) * ∫ t in (0 : ℝ)..1,
        Real.arsinh (Real.sin (π * (t * y))) / π * y := by
    simp [Complex.add_im, Complex.mul_im]
  rw [him]
  rcases eq_or_ne y 0 with rfl | hy_ne
  · simp
  · have hpi := Real.pi_pos.ne'
    have hsub : ∫ t in (0 : ℝ)..1, Real.arsinh (Real.sin (π * (t * y))) / π * y =
        (∫ u in (0 : ℝ)..y, Real.arsinh (Real.sin (π * u))) / π := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_comp_mul_right (fun u => Real.arsinh (Real.sin (π * u)) / π) hy_ne]
      simp only [zero_mul, one_mul, smul_eq_mul]
      rw [intervalIntegral.integral_div]
      field_simp [hy_ne]
    rw [hsub]
    field_simp [hpi]

lemma tendsto_pMap_edge_top_im (t : ℝ) :
    Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) (𝓝[<] (1 / 2)) (𝓝 0) := by
  have hpi := Real.pi_pos
  have hlim_z : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[<] (1 / 2))
      (𝓝 ((t : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)) := by
    refine tendsto_const_nhds.add ?_
    exact (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      tendsto_const_nhds
  let w : ℂ → ℂ := fun z => -Complex.I * Complex.sinh ((π : ℂ) * z)
  have hw_cont : Continuous w :=
    continuous_const.mul (Complex.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hw_val : w ((t : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) =
      ((Real.cosh (π * t) : ℝ) : ℂ) := by
    dsimp [w]
    have hre_im := neg_I_mul_sinh_pi_re_im ((t : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)
    have hre0 : ((t : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I).re = t := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    have him0 : ((t : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I).im = 1 / 2 := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
    rw [hre0, him0, show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two,
      Real.cos_pi_div_two, mul_one, mul_zero, neg_zero] at hre_im
    exact Complex.ext hre_im.1 hre_im.2
  have hw_tend : Tendsto (fun y : ℝ => w ((t : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] (1 / 2))
      (𝓝 ((Real.cosh (π * t) : ℝ) : ℂ)) := by
    rw [← hw_val]
    exact hw_cont.continuousAt.tendsto.comp hlim_z
  have hc_pos : 0 < Real.cosh (π * t) ^ 2 + 1 := by positivity
  have hsq_slit : ((Real.cosh (π * t) ^ 2 + 1 : ℝ) : ℂ) ∈ slitPlane := by
    rw [Complex.ofReal_mem_slitPlane]; exact hc_pos
  have hcpow_cont : ContinuousAt (fun u : ℂ => u ^ (1 / 2 : ℂ))
      ((Real.cosh (π * t) ^ 2 + 1 : ℝ) : ℂ) :=
    continuousAt_cpow_const hsq_slit
  have hz_tend : Tendsto (fun y : ℝ => (w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) (𝓝[<] (1 / 2))
      (𝓝 ((Real.cosh (π * t) ^ 2 + 1 : ℝ) : ℂ)) := by
    have h1 := (hw_tend.pow 2).add (tendsto_const_nhds (x := (1 : ℂ)))
    convert h1 using 2; push_cast; ring
  have hs_tend : Tendsto (fun y : ℝ => ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[<] (1 / 2)) (𝓝 (((Real.cosh (π * t) ^ 2 + 1 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) :=
    hcpow_cont.tendsto.comp hz_tend
  have hs_val : (((Real.cosh (π * t) ^ 2 + 1 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      ((Real.sqrt (Real.cosh (π * t) ^ 2 + 1) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hc_pos.le (1 / 2)]
    congr 1
    rw [Real.sqrt_eq_rpow]
  rw [hs_val] at hs_tend
  have hsum_lim : 0 < Real.cosh (π * t) + Real.sqrt (Real.cosh (π * t) ^ 2 + 1) := by positivity
  have hsum_slit : ((Real.cosh (π * t) + Real.sqrt (Real.cosh (π * t) ^ 2 + 1) : ℝ) : ℂ) ∈ slitPlane := by
    rw [Complex.ofReal_mem_slitPlane]; exact hsum_lim
  have hsum_tend : Tendsto (fun y : ℝ =>
      w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[<] (1 / 2))
      (𝓝 ((Real.cosh (π * t) + Real.sqrt (Real.cosh (π * t) ^ 2 + 1) : ℝ) : ℂ)) := by
    convert hw_tend.add hs_tend using 2; push_cast; ring
  have harg_tend : Tendsto (fun y : ℝ =>
      Complex.arg (w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)))
      (𝓝[<] (1 / 2)) (𝓝 0) := by
    have h0 : Complex.arg ((Real.cosh (π * t) + Real.sqrt (Real.cosh (π * t) ^ 2 + 1) : ℝ) : ℂ) = 0 :=
      Complex.arg_ofReal_of_nonneg hsum_lim.le
    rw [← h0]
    exact (Complex.continuousAt_arg hsum_slit).tendsto.comp hsum_tend
  have him_eq : ∀ y : ℝ, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im =
      Complex.arg (w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)) / π := by
    intro y
    unfold pMap complexArsinh
    have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hpi_inv, Complex.im_ofReal_mul, Complex.log_im]
    change π⁻¹ * _ = _
    ring
  simp_rw [him_eq]
  simpa using harg_tend.div_const π

lemma tendsto_majorant2D_edge_top (u : ℝ) :
    Tendsto majorant2D (𝓝[slitStrip] ((u : ℂ) + (1 / 2 : ℝ) * Complex.I)) (𝓝 0) := by
  have hpi := Real.pi_pos
  have hvert : Tendsto (fun y : ℝ => majorant2D ((u : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have himag : Tendsto majorantImag (𝓝[<] (1 / 2)) (𝓝 0) := by
      rw [← majorantImag_half]
      have hcont : Continuous majorantImag := by
        have heq : majorantImag = fun y : ℝ =>
            majorantU0 + (4 / 3) * ∫ t in (0 : ℝ)..y, Real.arsinh (Real.sin (π * t)) :=
          funext majorantImag_eq
        rw [heq]
        have harsinh_cont : Continuous Real.arsinh := by
          change Continuous (fun x : ℝ => Real.log (x + Real.sqrt (1 + x ^ 2)))
          refine Continuous.log (by fun_prop) fun x => ?_
          have hsq : |x| < Real.sqrt (1 + x ^ 2) := by
            rw [← Real.sqrt_sq_eq_abs]
            exact Real.sqrt_lt_sqrt (sq_nonneg x) (by linarith)
          linarith [neg_abs_le x, hsq]
        have hf : Continuous fun t : ℝ => Real.arsinh (Real.sin (π * t)) :=
          harsinh_cont.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
        have hint : ∀ a b : ℝ,
            IntervalIntegrable (fun t : ℝ => Real.arsinh (Real.sin (π * t))) volume a b :=
          fun a b => hf.intervalIntegrable a b
        have hprim : Continuous fun y : ℝ => ∫ t in (0 : ℝ)..y, Real.arsinh (Real.sin (π * t)) :=
          intervalIntegral.continuous_primitive hint 0
        exact continuous_const.add (continuous_const.mul hprim)
      exact hcont.continuousWithinAt.tendsto
    have himag_vert : Tendsto (fun y : ℝ => majorant2D ((y : ℂ) * Complex.I)) (𝓝[<] (1 / 2)) (𝓝 0) := by
      refine himag.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (-(1 / 2) : ℝ) < 1 / 2 by norm_num)] with y hy
      rw [majorant2D_I_mul (abs_lt.mpr hy)]
    have hint_tend : Tendsto (fun y : ℝ =>
        ∫ t in (0 : ℝ)..u, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) (𝓝[<] (1 / 2)) (𝓝 0) := by
      have h0 : ∫ _t in (0 : ℝ)..u, (0 : ℝ) = 0 := by simp
      conv_rhs => rw [← h0]
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (F := fun y t => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) (f := fun _ => (0 : ℝ))
          (a := 0) (b := u) (l := (𝓝[<] (1 / 2 : ℝ))) (bound := fun _ => (1 / 2 : ℝ)) ?_ ?_
          intervalIntegrable_const ?_
      · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
        have hcont : Continuous (fun t : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) :=
          Complex.continuous_im.comp (differentiableOn_pMap_slitStrip.continuousOn.comp_continuous
            (Complex.continuous_ofReal.add continuous_const) (fun t =>
              ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by
                simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one] at him
                exact hy.1.ne' (by linarith)⟩))
        exact hcont.aestronglyMeasurable
      · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
        filter_upwards with t _
        rw [Real.norm_eq_abs]
        exact pMap_im_abs_le_half ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one] at him
          exact hy.1.ne' (by linarith)⟩
      · filter_upwards with t _
        exact tendsto_pMap_edge_top_im t
    have hsum : Tendsto (fun y : ℝ =>
        majorant2D ((y : ℂ) * Complex.I) +
          (4 * π / 3) * ∫ t in (0 : ℝ)..u, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im)
        (𝓝[<] (1 / 2)) (𝓝 (0 + (4 * π / 3) * 0)) :=
      himag_vert.add (tendsto_const_nhds.mul hint_tend)
    rw [show (0 : ℝ) + (4 * π / 3) * 0 = 0 by ring] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
    have hsub := majorant2D_sub_horizontal (by rw [abs_of_pos hy.1]; exact hy.2) hy.1.ne' 0 u
    simp only [Complex.ofReal_zero, zero_add] at hsub
    linarith
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hvert' := Metric.tendsto_nhdsWithin_nhds.mp hvert (ε / 2) (half_pos hε)
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hvert'
  refine ⟨min (min δ₁ (1 / 4)) (ε / (2 * (2 * π / 3 + 1))), by positivity, fun b hb hdist => ?_⟩
  rw [Complex.dist_eq] at hdist
  have hbim_lt : b.im < 1 / 2 := (abs_lt.mp hb.1).2
  have hdist_im : |b.im - 1 / 2| < δ₁ := by
    have := Complex.abs_im_le_norm (b - ((u : ℂ) + (1 / 2 : ℝ) * Complex.I))
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at this
    calc |b.im - 1 / 2| ≤ ‖b - ((u : ℂ) + (1 / 2 : ℝ) * Complex.I)‖ := this
      _ < min (min δ₁ (1 / 4)) (ε / (2 * (2 * π / 3 + 1))) := hdist
      _ ≤ min δ₁ (1 / 4) := min_le_left _ _
      _ ≤ δ₁ := min_le_left _ _
  have hbim_pos : 0 < b.im := by
    have : |b.im - 1 / 2| < 1 / 4 := by
      have := Complex.abs_im_le_norm (b - ((u : ℂ) + (1 / 2 : ℝ) * Complex.I))
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at this
      calc |b.im - 1 / 2| ≤ ‖b - ((u : ℂ) + (1 / 2 : ℝ) * Complex.I)‖ := this
        _ < _ := hdist
        _ ≤ min δ₁ (1 / 4) := min_le_left _ _
        _ ≤ 1 / 4 := min_le_right _ _
    linarith [(abs_lt.mp this).1]
  have h_mid : |majorant2D ((u : ℂ) + (b.im : ℂ) * Complex.I)| < ε / 2 := by
    simpa [Real.dist_eq, sub_zero] using hδ₁ hbim_lt (by simpa [Real.dist_eq] using hdist_im)
  have h_lip : |majorant2D b - majorant2D ((u : ℂ) + (b.im : ℂ) * Complex.I)| ≤
      (2 * π / 3) * |b.re - u| := by
    have hb_eq : b = (b.re : ℂ) + (b.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h := majorant2D_lipschitz_re hb.1 hbim_pos.ne' b.re u
    rwa [← hb_eq] at h
  have hre_dist : |b.re - u| < ε / (2 * (2 * π / 3 + 1)) := by
    have := Complex.abs_re_le_norm (b - ((u : ℂ) + (1 / 2 : ℝ) * Complex.I))
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, Complex.ofReal_im, sub_zero, add_zero] at this
    calc |b.re - u| ≤ ‖b - ((u : ℂ) + (1 / 2 : ℝ) * Complex.I)‖ := this
      _ < _ := hdist
      _ ≤ ε / (2 * (2 * π / 3 + 1)) := min_le_right _ _
  have h_lip2 : (2 * π / 3) * |b.re - u| < ε / 2 := by
    have hpos : 0 < 2 * π / 3 + 1 := by positivity
    calc (2 * π / 3) * |b.re - u|
        < (2 * π / 3) * (ε / (2 * (2 * π / 3 + 1))) := by gcongr
      _ ≤ (2 * π / 3 + 1) * (ε / (2 * (2 * π / 3 + 1))) := by gcongr; linarith
      _ = ε / 2 := by field_simp [hpos.ne']
  rw [Real.dist_eq, sub_zero]
  calc |majorant2D b|
      ≤ |majorant2D b - majorant2D ((u : ℂ) + (b.im : ℂ) * Complex.I)| +
          |majorant2D ((u : ℂ) + (b.im : ℂ) * Complex.I)| := by
        simpa using abs_add_le (majorant2D b - majorant2D ((u : ℂ) + (b.im : ℂ) * Complex.I))
          (majorant2D ((u : ℂ) + (b.im : ℂ) * Complex.I))
    _ < (2 * π / 3) * |b.re - u| + ε / 2 := by linarith
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := add_halves ε

lemma tendsto_majorant2D_edge_bot (u : ℝ) :
    Tendsto majorant2D (𝓝[slitStrip] ((u : ℂ) - (1 / 2 : ℝ) * Complex.I)) (𝓝 0) := by
  have hconj_tend : Tendsto (starRingEnd ℂ)
      (𝓝[slitStrip] ((u : ℂ) - (1 / 2 : ℝ) * Complex.I))
      (𝓝[slitStrip] ((u : ℂ) + (1 / 2 : ℝ) * Complex.I)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hlim : starRingEnd ℂ ((u : ℂ) - (1 / 2 : ℝ) * Complex.I) =
          (u : ℂ) + (1 / 2 : ℝ) * Complex.I := by
        rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
      rw [← hlim]
      exact Complex.continuous_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with b hb
      refine ⟨by simpa using hb.1, ?_⟩
      rintro ⟨him, hre⟩
      simp only [Complex.conj_im, neg_eq_zero, Complex.conj_re] at him hre
      exact hb.2 ⟨him, hre⟩
  have hcomp := (tendsto_majorant2D_edge_top u).comp hconj_tend
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact majorant2D_conj hb

private lemma cpow_half_of_im_neg {z : ℂ} (hz : z.im < 0) :
    z ^ (1 / 2 : ℂ) = ((Real.sqrt ‖z‖ : ℝ) : ℂ) *
      (((Real.sin ((-z).arg / 2) : ℝ) : ℂ) - Complex.I * ((Real.cos ((-z).arg / 2) : ℝ) : ℂ)) := by
  have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_im] at hz; exact hz.false
  have harg_add : (-z).arg = z.arg + π := Complex.arg_neg_eq_arg_add_pi_of_im_neg hz
  have harg_eq : z.arg / 2 = (-z).arg / 2 - π / 2 := by linarith
  have hcos : Real.cos (z.arg / 2) = Real.sin ((-z).arg / 2) := by
    rw [harg_eq, Real.cos_sub_pi_div_two]
  have hsin : Real.sin (z.arg / 2) = -Real.cos ((-z).arg / 2) := by
    rw [harg_eq, Real.sin_sub_pi_div_two]
  rw [Complex.cpow_def_of_ne_zero hz0]
  have h12 : Complex.log z * (1 / 2 : ℂ) =
      ((Real.log ‖z‖ / 2 : ℝ) : ℂ) + ((z.arg / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]; ring
    · simp [Complex.log_im]; ring
  rw [h12, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, hcos, hsin]
  have hsqrt : Real.exp (Real.log ‖z‖ / 2) = Real.sqrt ‖z‖ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hz0)]
    congr 1; ring
  rw [hsqrt]
  push_cast; ring

lemma tendsto_pMap_slit_right {t : ℝ} (ht : xiStar < t) :
    Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) (𝓝[>] 0) (𝓝 (-(1 / 2))) := by
  have hpi := Real.pi_pos
  have hlim_z : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
    have h0 : (t : ℂ) = (t : ℂ) + (0 : ℂ) * Complex.I := by simp
    conv_rhs => rw [h0]
    exact tendsto_const_nhds.add
      ((Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        tendsto_const_nhds)
  let w : ℂ → ℂ := fun z => -Complex.I * Complex.sinh ((π : ℂ) * z)
  have hw_cont : Continuous w :=
    continuous_const.mul (Complex.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hw_val : w (t : ℂ) = -Complex.I * ((Real.sinh (π * t) : ℝ) : ℂ) := by
    dsimp [w]
    rw [show (π : ℂ) * (t : ℂ) = ((π * t : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sinh]
  have hw_tend : Tendsto (fun y : ℝ => w ((t : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (-Complex.I * ((Real.sinh (π * t) : ℝ) : ℂ))) := by
    rw [← hw_val]
    exact hw_cont.continuousAt.tendsto.comp hlim_z
  have hsinh_gt : 1 < Real.sinh (π * t) := by
    rw [← sinh_pi_mul_xiStar]
    exact Real.sinh_lt_sinh.mpr (mul_lt_mul_of_pos_left ht hpi)
  have hsq_pos : 0 < Real.sinh (π * t) ^ 2 - 1 := by nlinarith
  have hnz_tend : Tendsto (fun y : ℝ => -((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1))
      (𝓝[>] 0) (𝓝 ((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ)) := by
    have h1 := ((hw_tend.pow 2).add (tendsto_const_nhds (x := (1 : ℂ)))).neg
    convert h1 using 2
    rw [mul_pow, neg_sq, Complex.I_sq]; push_cast; ring
  have harg_nz : Tendsto (fun y : ℝ =>
      Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1))) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Complex.arg ((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ) = 0 :=
      Complex.arg_ofReal_of_nonneg hsq_pos.le
    have hcmp := (Complex.continuousAt_arg (Complex.ofReal_mem_slitPlane.mpr hsq_pos)).tendsto.comp
      hnz_tend
    rw [h0] at hcmp
    exact hcmp
  have hnorm_tend : Tendsto (fun y : ℝ =>
      ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖) (𝓝[>] 0)
      (𝓝 (Real.sinh (π * t) ^ 2 - 1)) := by
    have h1 := (continuous_norm.tendsto _).comp hnz_tend
    have hnl : ‖((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ)‖ = Real.sinh (π * t) ^ 2 - 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hsq_pos.le]
    rw [hnl] at h1
    convert h1 using 1
    ext y
    exact (norm_neg _).symm
  have him_neg_ev : ∀ᶠ y : ℝ in 𝓝[>] 0,
      ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1).im < 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
    have hri := neg_I_mul_sinh_pi_re_im ((t : ℂ) + (y : ℂ) * Complex.I)
    have hre0 : ((t : ℂ) + (y : ℂ) * Complex.I).re = t := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    have him0 : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
    rw [hre0, him0] at hri
    have hw_re_pos : 0 < (w ((t : ℂ) + (y : ℂ) * Complex.I)).re := by
      dsimp [w]; rw [hri.1]
      exact mul_pos (Real.cosh_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hy.1)
        (by nlinarith [hy.2]))
    have hw_im_neg : (w ((t : ℂ) + (y : ℂ) * Complex.I)).im < 0 := by
      dsimp [w]; rw [hri.2]
      have hsinh_pos : 0 < Real.sinh (π * t) := by linarith
      have hcos_pos : 0 < Real.cos (π * y) :=
        Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
      nlinarith
    have him_sq : ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1).im =
        2 * (w ((t : ℂ) + (y : ℂ) * Complex.I)).re *
          (w ((t : ℂ) + (y : ℂ) * Complex.I)).im := by
      simp [pow_two]; ring
    rw [him_sq]
    nlinarith
  have hs_tend : Tendsto (fun y : ℝ =>
      ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (-Complex.I * ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ))) := by
    have hsqrt_tend : Tendsto (fun y : ℝ =>
        Real.sqrt ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖) (𝓝[>] 0)
        (𝓝 (Real.sqrt (Real.sinh (π * t) ^ 2 - 1))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hnorm_tend
    have hsin_tend : Tendsto (fun y : ℝ =>
        Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 0) := by
      have h1 := (Real.continuous_sin.continuousAt.tendsto.comp (harg_nz.div_const 2))
      change Tendsto (fun y : ℝ =>
        Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 (Real.sin (0 / 2))) at h1
      simpa [Real.sin_zero] using h1
    have hcos_tend : Tendsto (fun y : ℝ =>
        Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 1) := by
      have h1 := (Real.continuous_cos.continuousAt.tendsto.comp (harg_nz.div_const 2))
      change Tendsto (fun y : ℝ =>
        Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 (Real.cos (0 / 2))) at h1
      simpa [Real.cos_zero] using h1
    have hcomb : Tendsto (fun y : ℝ =>
        ((Real.sqrt ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖ : ℝ) : ℂ) *
          (((Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2) : ℝ) : ℂ) -
            Complex.I * ((Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2) : ℝ) : ℂ)))
        (𝓝[>] 0)
        (𝓝 (((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) *
          (((0 : ℝ) : ℂ) - Complex.I * ((1 : ℝ) : ℂ)))) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hsqrt_tend).mul
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp hsin_tend).sub
          (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hcos_tend)))
    have hlim_eq : ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) *
        (((0 : ℝ) : ℂ) - Complex.I * ((1 : ℝ) : ℂ)) =
        -Complex.I * ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hlim_eq] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [him_neg_ev] with y hy
    exact (cpow_half_of_im_neg hy).symm
  let r : ℝ := Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1)
  have hr_pos : 0 < r := by positivity
  have hsum_tend : Tendsto (fun y : ℝ =>
      w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (((-r : ℝ) : ℂ) * Complex.I)) := by
    have h1 := hw_tend.add hs_tend
    convert h1 using 2
    push_cast [r]; ring
  have hlim_slit : (((-r : ℝ) : ℂ) * Complex.I) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    right
    simpa using hr_pos.ne'
  have harg_lim : Complex.arg (((-r : ℝ) : ℂ) * Complex.I) = -(π / 2) := by
    rw [show ((-r : ℝ) : ℂ) * Complex.I = (r : ℂ) * (-Complex.I) by push_cast; ring,
      Complex.arg_real_mul (-Complex.I) hr_pos, Complex.arg_neg_I]
  have harg_tend : Tendsto (fun y : ℝ =>
      Complex.arg (w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)))
      (𝓝[>] 0) (𝓝 (-(π / 2))) := by
    rw [← harg_lim]
    exact (Complex.continuousAt_arg hlim_slit).tendsto.comp hsum_tend
  have him_eq : ∀ y : ℝ, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im =
      Complex.arg (w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)) / π := by
    intro y
    unfold pMap complexArsinh
    have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hpi_inv, Complex.im_ofReal_mul, Complex.log_im]
    change π⁻¹ * _ = _
    ring
  simp_rw [him_eq]
  have hres := harg_tend.div_const π
  have hdiv : -(π / 2) / π = -(1 / 2) := by field_simp [hpi.ne']
  rwa [hdiv] at hres

lemma tendsto_majorant2D_slit_nonneg {x₀ : ℝ} (hx₀ : xiStar ≤ x₀) :
    Tendsto majorant2D (𝓝[slitStrip] (x₀ : ℂ)) (𝓝 (-slitL x₀)) := by
  have hpi := Real.pi_pos
  have hx₀_pos : 0 < x₀ := xiStar_pos.trans_le hx₀
  have hvert : Tendsto (fun y : ℝ => majorant2D ((x₀ : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (-slitL x₀)) := by
    have himag : Tendsto (fun y : ℝ => majorant2D ((y : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 majorantU0) := by
      have h0 : majorantImag 0 = majorantU0 := by rw [majorantImag_eq]; simp
      have hcont : Continuous majorantImag := by
        have heq : majorantImag = fun y : ℝ =>
            majorantU0 + (4 / 3) * ∫ t in (0 : ℝ)..y, Real.arsinh (Real.sin (π * t)) :=
          funext majorantImag_eq
        rw [heq]
        have harsinh_cont : Continuous Real.arsinh := by
          change Continuous (fun x : ℝ => Real.log (x + Real.sqrt (1 + x ^ 2)))
          refine Continuous.log (by fun_prop) fun x => ?_
          have hsq : |x| < Real.sqrt (1 + x ^ 2) := by
            rw [← Real.sqrt_sq_eq_abs]
            exact Real.sqrt_lt_sqrt (sq_nonneg x) (by linarith)
          linarith [neg_abs_le x, hsq]
        have hf : Continuous fun t : ℝ => Real.arsinh (Real.sin (π * t)) :=
          harsinh_cont.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
        have hint : ∀ a b : ℝ,
            IntervalIntegrable (fun t : ℝ => Real.arsinh (Real.sin (π * t))) volume a b :=
          fun a b => hf.intervalIntegrable a b
        have hprim : Continuous fun y : ℝ => ∫ t in (0 : ℝ)..y, Real.arsinh (Real.sin (π * t)) :=
          intervalIntegral.continuous_primitive hint 0
        exact continuous_const.add (continuous_const.mul hprim)
      refine (h0 ▸ hcont.continuousWithinAt.tendsto).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
      rw [majorant2D_I_mul (abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩)]
    let f_lim : ℝ → ℝ := fun t => if t ≤ xiStar then -arcsinSinh t / π else -(1 / 2)
    have hf_lim_int : IntervalIntegrable f_lim volume 0 x₀ := by
      refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hx₀_pos.le]
      have hmeas : AEStronglyMeasurable f_lim (volume.restrict (Icc 0 x₀)) := by
        refine Measurable.aestronglyMeasurable ?_
        refine Measurable.ite (measurableSet_Iic) ?_ measurable_const
        have harc : Continuous arcsinSinh := by
          unfold arcsinSinh; fun_prop
        exact (harc.measurable.neg.div_const π)
      have hbd : ∀ t ∈ Icc (0 : ℝ) x₀, ‖f_lim t‖ ≤ 1 := by
        intro t _
        rw [Real.norm_eq_abs]
        dsimp [f_lim]
        split_ifs with hle
        · rw [abs_div, abs_neg, abs_of_pos hpi, div_le_one hpi]
          unfold arcsinSinh
          have harc := abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin (Real.sinh (π * t)),
            Real.arcsin_le_pi_div_two (Real.sinh (π * t))⟩
          linarith
        · norm_num
      exact MeasureTheory.IntegrableOn.of_bound (measure_Icc_lt_top) hmeas 1
        ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hbd t ht)
    have hint_lim : majorantU0 + (4 * π / 3) * ∫ t in (0 : ℝ)..x₀, f_lim t = -slitL x₀ := by
      have hxi_mem : xiStar ∈ uIcc (0 : ℝ) x₀ :=
        Set.mem_uIcc.mpr (Or.inl ⟨xiStar_pos.le, hx₀⟩)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hf_lim_int.mono_set (Set.uIcc_subset_uIcc_left hxi_mem))
        (hf_lim_int.mono_set (Set.uIcc_subset_uIcc_right hxi_mem))
      have h_left : ∫ t in (0 : ℝ)..xiStar, f_lim t = -(∫ t in (0 : ℝ)..xiStar, arcsinSinh t) / π := by
        have hcongr : EqOn f_lim (fun t => -arcsinSinh t / π) (uIoc 0 xiStar) := by
          intro t ht
          rw [Set.uIoc_of_le xiStar_pos.le] at ht
          dsimp [f_lim]; rw [if_pos ht.2]
        rw [intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => hcongr ht)]
        rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
      have h_right : ∫ t in xiStar..x₀, f_lim t = -(1 / 2) * (x₀ - xiStar) := by
        have hcongr : ∀ t ∈ Ioc xiStar x₀, f_lim t = -(1 / 2) := by
          intro t ht; dsimp [f_lim]; rw [if_neg (not_le.mpr ht.1)]
        rw [intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht =>
          hcongr t (Set.uIoc_of_le hx₀ ▸ ht))]
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      rw [← hsplit, h_left, h_right]
      unfold majorantU0 slitL
      rw [abs_of_pos xiStar_pos, abs_of_pos hx₀_pos]
      field_simp [hpi.ne']
      ring
    have hint_tend : Tendsto (fun y : ℝ =>
        ∫ t in (0 : ℝ)..x₀, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im)
        (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..x₀, f_lim t)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (F := fun y t => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im)
        (f := f_lim) (a := 0) (b := x₀) (l := (𝓝[>] (0 : ℝ))) (bound := fun _ => (1 / 2 : ℝ)) ?_ ?_
        intervalIntegrable_const ?_
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
        have hcont : Continuous (fun t : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im) :=
          Complex.continuous_im.comp (differentiableOn_pMap_slitStrip.continuousOn.comp_continuous
            (Complex.continuous_ofReal.add continuous_const) (fun t =>
              ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by
                simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one] at him
                exact hy.1.ne' (by linarith)⟩))
        exact hcont.aestronglyMeasurable
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
        filter_upwards with t _
        rw [Real.norm_eq_abs]
        exact pMap_im_abs_le_half ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one] at him
          exact hy.1.ne' (by linarith)⟩
      · have hne_xi : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) x₀ → t ≠ xiStar := by
          have hsingle : ({xiStar} : Set ℝ)ᶜ ∈ ae volume :=
            compl_mem_ae_iff.mpr Real.volume_singleton
          filter_upwards [hsingle] with t ht _
          exact ht
        filter_upwards [hne_xi] with t ht htu
        have ht_ne := ht htu
        rw [Set.uIoc_of_le hx₀_pos.le] at htu
        rcases lt_or_gt_of_ne ht_ne with hlt | hgt
        · dsimp [f_lim]; rw [if_pos hlt.le]
          have hmem_t : (t : ℂ) ∈ slitStrip := by
            refine ⟨by simp, ?_⟩
            rintro ⟨_, hre⟩
            have habs : |t| < xiStar := by rw [abs_of_pos htu.1]; exact hlt
            rw [Complex.ofReal_re] at hre
            linarith [habs, hre]
          have hp_cont : ContinuousAt pMap (t : ℂ) :=
            (differentiableOn_pMap_slitStrip.continuousOn.continuousAt
              (isOpen_slitStrip.mem_nhds hmem_t))
          have hz_tend : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
            have h0 : (t : ℂ) = (t : ℂ) + (0 : ℂ) * Complex.I := by simp
            conv_rhs => rw [h0]
            exact tendsto_const_nhds.add
              ((Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
                tendsto_const_nhds)
          have him_tend := (Complex.continuous_im.continuousAt.comp hp_cont).tendsto.comp hz_tend
          have hp_val : (pMap (t : ℂ)).im = -arcsinSinh t / π := by
            rw [pMap_ofReal (by rw [abs_of_pos htu.1]; exact hlt.le)]
            simp
          change Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im)
            (𝓝[>] 0) (𝓝 (pMap (t : ℂ)).im) at him_tend
          rwa [hp_val] at him_tend
        · dsimp [f_lim]; rw [if_neg (not_le.mpr hgt)]
          exact tendsto_pMap_slit_right hgt
    have hsum : Tendsto (fun y : ℝ =>
        majorant2D ((y : ℂ) * Complex.I) +
          (4 * π / 3) * ∫ t in (0 : ℝ)..x₀, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im)
        (𝓝[>] 0) (𝓝 (majorantU0 + (4 * π / 3) * ∫ t in (0 : ℝ)..x₀, f_lim t)) :=
      himag.add (tendsto_const_nhds.mul hint_tend)
    rw [hint_lim] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
    have hsub := majorant2D_sub_horizontal (by rw [abs_of_pos hy.1]; exact hy.2) hy.1.ne' 0 x₀
    simp only [Complex.ofReal_zero, zero_add] at hsub
    linarith
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hvert' := Metric.tendsto_nhdsWithin_nhds.mp hvert (ε / 2) (half_pos hε)
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hvert'
  have hreal_cont : ∃ δ₂ > 0, ∀ r : ℝ, |r| < xiStar → |r - x₀| < δ₂ →
      |majorantReal r - (-slitL x₀)| < ε := by
    rcases eq_or_lt_of_le hx₀ with rfl | hgt
    · have hcont_mr : ContinuousOn majorantReal (Icc (-xiStar) xiStar) := by
        have heq : EqOn majorantReal (fun r : ℝ =>
            majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..|r|, arcsinSinh s) (Icc (-xiStar) xiStar) :=
          fun r hr => majorantReal_of_abs_le (abs_le.mpr hr)
        refine ContinuousOn.congr ?_ heq
        refine continuousOn_const.sub (continuousOn_const.mul ?_)
        have hprim : Continuous fun u : ℝ => ∫ s in (0 : ℝ)..u, arcsinSinh s :=
          intervalIntegral.continuous_primitive intervalIntegrable_arcsinSinh 0
        exact (hprim.comp continuous_abs).continuousOn
      have hcont_at := (hcont_mr xiStar ⟨by linarith [xiStar_pos], le_rfl⟩)
      rw [Metric.continuousWithinAt_iff, majorantReal_xiStar] at hcont_at
      obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hcont_at ε hε
      refine ⟨δ₂, hδ₂_pos, fun r hr hdist => ?_⟩
      exact hδ₂ (abs_le.mp hr.le) hdist
    · refine ⟨x₀ - xiStar, sub_pos.mpr hgt, fun r hr hdist => ?_⟩
      exfalso
      have : r < xiStar := (abs_lt.mp hr).2
      linarith [(abs_lt.mp hdist).1]
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hreal_cont
  refine ⟨min (min δ₁ δ₂) (ε / (2 * (2 * π / 3 + 1))), by positivity, fun b hb hdist => ?_⟩
  rw [Complex.dist_eq] at hdist
  rw [Real.dist_eq]
  rcases eq_or_ne b.im 0 with hbim0 | hbim_ne
  · have hbre_lt : |b.re| < xiStar := by
      by_contra hnot
      push Not at hnot
      exact hb.2 ⟨hbim0, hnot⟩
    have hb_eq : b = (b.re : ℂ) := Complex.ext rfl hbim0
    rw [hb_eq, majorant2D_ofReal hbre_lt.le]
    have hre_dist : |b.re - x₀| < δ₂ := by
      have := Complex.abs_re_le_norm (b - (x₀ : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      calc |b.re - x₀| ≤ ‖b - (x₀ : ℂ)‖ := this
        _ < _ := hdist
        _ ≤ min δ₁ δ₂ := min_le_left _ _
        _ ≤ δ₂ := min_le_right _ _
    exact hδ₂ b.re hbre_lt hre_dist
  · let b' : ℂ := if 0 < b.im then b else starRingEnd ℂ b
    have hb'_mem : b' ∈ slitStrip := by
      dsimp [b']
      split_ifs
      · exact hb
      · refine ⟨by simpa using hb.1, ?_⟩
        rintro ⟨him, hre⟩
        simp only [Complex.conj_im, neg_eq_zero, Complex.conj_re] at him hre
        exact hb.2 ⟨him, hre⟩
    have hb'_im_pos : 0 < b'.im := by
      dsimp [b']
      split_ifs with hp
      · exact hp
      · have hlt := lt_of_le_of_ne (not_lt.mp hp) hbim_ne
        simpa using hlt
    have hb'_re : b'.re = b.re := by dsimp [b']; split_ifs <;> simp
    have hm2_eq : majorant2D b' = majorant2D b := by
      dsimp [b']; split_ifs
      · rfl
      · exact majorant2D_conj hb
    have hb'_dist : ‖b' - (x₀ : ℂ)‖ = ‖b - (x₀ : ℂ)‖ := by
      dsimp [b']; split_ifs
      · rfl
      · conv_lhs => rw [← Complex.conj_ofReal x₀, ← map_sub, Complex.norm_conj]
    rw [← hm2_eq]
    have hdist_im : b'.im < δ₁ := by
      have := Complex.abs_im_le_norm (b' - (x₀ : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      calc b'.im = |b'.im| := (abs_of_pos hb'_im_pos).symm
        _ ≤ ‖b' - (x₀ : ℂ)‖ := this
        _ = ‖b - (x₀ : ℂ)‖ := hb'_dist
        _ < _ := hdist
        _ ≤ min δ₁ δ₂ := min_le_left _ _
        _ ≤ δ₁ := min_le_left _ _
    have h_mid : |majorant2D ((x₀ : ℂ) + (b'.im : ℂ) * Complex.I) - (-slitL x₀)| < ε / 2 := by
      simpa [Real.dist_eq] using hδ₁ hb'_im_pos (by simpa [Real.dist_eq, abs_of_pos hb'_im_pos] using hdist_im)
    have h_lip : |majorant2D b' - majorant2D ((x₀ : ℂ) + (b'.im : ℂ) * Complex.I)| ≤
        (2 * π / 3) * |b'.re - x₀| := by
      have hb'_eq : b' = (b'.re : ℂ) + (b'.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
      have h := majorant2D_lipschitz_re hb'_mem.1 hb'_im_pos.ne' b'.re x₀
      rwa [← hb'_eq] at h
    have hre_dist : |b'.re - x₀| < ε / (2 * (2 * π / 3 + 1)) := by
      have := Complex.abs_re_le_norm (b' - (x₀ : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      calc |b'.re - x₀| ≤ ‖b' - (x₀ : ℂ)‖ := this
        _ = ‖b - (x₀ : ℂ)‖ := hb'_dist
        _ < _ := hdist
        _ ≤ ε / (2 * (2 * π / 3 + 1)) := min_le_right _ _
    have h_lip2 : (2 * π / 3) * |b'.re - x₀| < ε / 2 := by
      have hpos : 0 < 2 * π / 3 + 1 := by positivity
      calc (2 * π / 3) * |b'.re - x₀|
          < (2 * π / 3) * (ε / (2 * (2 * π / 3 + 1))) := by gcongr
        _ ≤ (2 * π / 3 + 1) * (ε / (2 * (2 * π / 3 + 1))) := by gcongr; linarith
        _ = ε / 2 := by field_simp [hpos.ne']
    calc |majorant2D b' - (-slitL x₀)|
        ≤ |majorant2D b' - majorant2D ((x₀ : ℂ) + (b'.im : ℂ) * Complex.I)| +
            |majorant2D ((x₀ : ℂ) + (b'.im : ℂ) * Complex.I) - (-slitL x₀)| := by
          simpa [sub_eq_add_neg, add_assoc] using abs_add_le
            (majorant2D b' - majorant2D ((x₀ : ℂ) + (b'.im : ℂ) * Complex.I))
            (majorant2D ((x₀ : ℂ) + (b'.im : ℂ) * Complex.I) - (-slitL x₀))
      _ < (2 * π / 3) * |b'.re - x₀| + ε / 2 := by linarith
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := add_halves ε

lemma tendsto_majorant2D_slit {x₀ : ℝ} (hx₀ : xiStar ≤ |x₀|) :
    Tendsto majorant2D (𝓝[slitStrip] (x₀ : ℂ)) (𝓝 (-slitL x₀)) := by
  rcases le_or_gt 0 x₀ with hx0 | hxneg
  · exact tendsto_majorant2D_slit_nonneg (by rwa [abs_of_nonneg hx0] at hx₀)
  · have hneg_mem : Tendsto Neg.neg (𝓝[slitStrip] (x₀ : ℂ)) (𝓝[slitStrip] ((-x₀ : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with b hb
        exact neg_mem_slitStrip hb
    have hcomp := (tendsto_majorant2D_slit_nonneg (x₀ := -x₀) (by rwa [← abs_of_neg hxneg])).comp hneg_mem
    have hL : slitL (-x₀) = slitL x₀ := by unfold slitL; rw [abs_neg]
    rw [hL] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact majorant2D_neg hb

lemma confB_mem_slitStrip {z : ℂ} (hz : 0 < z.im) : confB z ∈ slitStrip :=
  confB_bijOn.mapsTo hz

lemma tendsto_majorant2D_confB {σ : ℝ} (h0 : σ ≠ 0) (h1 : σ ≠ 1) (hm1 : σ ≠ -1) :
    Tendsto (fun z : ℂ => majorant2D (confB z)) (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ))
      (𝓝 (if σ ∈ slitPreimage then -slitL (slitBoundaryMap σ) else 0)) := by
  have hconfB_tend : Tendsto confB (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝[slitStrip] (confB (σ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (confB_continuousWithinAt_real h0 h1 hm1).tendsto.mono_left
        (nhdsWithin_mono _ fun z (hz : 0 < z.im) => le_of_lt hz)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact confB_mem_slitStrip hz
  have hre : (confB (σ : ℂ)).re = slitBoundaryMap σ := confB_real_re h0 h1 hm1
  rcases lt_trichotomy σ (-1) with hm | rfl | hm1_gt
  · have hnot : σ ∉ slitPreimage := by
      rintro (⟨h, _⟩ | (h : 1 < σ)) <;> linarith
    rw [if_neg hnot]
    have him := confB_real_im_of_lt_neg_one hm
    have hcb : confB (σ : ℂ) = ((confB (σ : ℂ)).re : ℂ) - (1 / 2 : ℝ) * Complex.I := by
      apply Complex.ext <;> simp [him]
    rw [hcb] at hconfB_tend
    exact (tendsto_majorant2D_edge_bot _).comp hconfB_tend
  · exact absurd rfl hm1
  · rcases lt_trichotomy σ 0 with h0_lt | rfl | h0_gt
    · have hin : σ ∈ slitPreimage := Or.inl ⟨hm1_gt, h0_lt⟩
      rw [if_pos hin]
      have him := confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1_gt, h0_lt⟩
      have hcb : confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := Complex.ext hre him
      rw [hcb] at hconfB_tend
      have hge := xiStar_le_slitBoundaryMap ⟨hm1_gt, h0_lt⟩
      have habs : xiStar ≤ |slitBoundaryMap σ| := hge.trans (le_abs_self _)
      exact (tendsto_majorant2D_slit habs).comp hconfB_tend
    · exact absurd rfl h0
    · rcases lt_trichotomy σ 1 with h1_lt | rfl | h1_gt
      · have hnot : σ ∉ slitPreimage := by
          rintro (⟨h, _⟩ | (h : 1 < σ)) <;> linarith
        rw [if_neg hnot]
        have him := confB_real_im_of_mem_Ioo_zero_one ⟨h0_gt, h1_lt⟩
        have hcb : confB (σ : ℂ) = ((confB (σ : ℂ)).re : ℂ) + (1 / 2 : ℝ) * Complex.I := by
          apply Complex.ext <;> simp [him]
        rw [hcb] at hconfB_tend
        exact (tendsto_majorant2D_edge_top _).comp hconfB_tend
      · exact absurd rfl h1
      · have hin : σ ∈ slitPreimage := Or.inr h1_gt
        rw [if_pos hin]
        have him := confB_real_im_of_one_lt h1_gt
        have hcb : confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := Complex.ext hre him
        rw [hcb] at hconfB_tend
        have hle := slitBoundaryMap_le_neg_xiStar h1_gt
        have habs : xiStar ≤ |slitBoundaryMap σ| := by
          have : slitBoundaryMap σ ≤ -xiStar := hle
          linarith [neg_abs_le (slitBoundaryMap σ)]
        exact (tendsto_majorant2D_slit habs).comp hconfB_tend

/-! ### 4. Schwarz integral `schwarzSlit` on the upper half-plane -/

noncomputable def schwarzKernel (z : ℂ) (σ : ℝ) : ℂ :=
  (1 + (σ : ℂ) * z) / (((σ : ℂ) - z) * ((1 + σ ^ 2 : ℝ) : ℂ))

noncomputable def schwarzSlit (z : ℂ) : ℂ :=
  -((π : ℂ)⁻¹) * ∫ σ in slitPreimage, (slitL (slitBoundaryMap σ) : ℂ) * schwarzKernel z σ

private lemma one_add_sq_le (x₀ σ : ℝ) :
    1 + σ ^ 2 ≤ 2 * (x₀ ^ 2 + 1) * ((σ - x₀) ^ 2 + 1) := by
  have h1 : σ ^ 2 ≤ 2 * (σ - x₀) ^ 2 + 2 * x₀ ^ 2 := by nlinarith [sq_nonneg (σ - 2 * x₀)]
  nlinarith [sq_nonneg x₀, sq_nonneg (σ - x₀)]

private lemma sub_sq_add_one_le (x₀ σ : ℝ) :
    (σ - x₀) ^ 2 + 1 ≤ 2 * (x₀ ^ 2 + 1) * (1 + σ ^ 2) := by
  have h1 : (σ - x₀) ^ 2 ≤ 2 * σ ^ 2 + 2 * x₀ ^ 2 := by nlinarith [sq_nonneg (σ + x₀)]
  nlinarith [sq_nonneg x₀, sq_nonneg σ]

private lemma norm_sub_ofReal_sq_ge {z₀ : ℂ} (hz₀ : 0 < z₀.im) {z : ℂ}
    (hz : z ∈ Metric.ball z₀ (z₀.im / 2)) (σ : ℝ) :
    (min (1 / 4 : ℝ) ((z₀.im / 2) ^ 2 / (4 * (z₀.im / 2) ^ 2 + 1))) * ((σ - z₀.re) ^ 2 + 1) ≤
      ‖(σ : ℂ) - z‖ ^ 2 := by
  set δ := z₀.im / 2
  have hδ : 0 < δ := half_pos hz₀
  have hz_dist : ‖z - z₀‖ < δ := Complex.dist_eq z z₀ ▸ Metric.mem_ball.mp hz
  have hre : |z.re - z₀.re| ≤ δ := (Complex.abs_re_le_norm (z - z₀)).trans hz_dist.le
  have him : δ ≤ z.im := by
    have h1 := (Complex.abs_im_le_norm (z - z₀)).trans hz_dist.le
    rw [Complex.sub_im] at h1
    linarith [(abs_le.mp h1).1, show z₀.im = 2 * δ by dsimp [δ]; ring]
  have hnorm_sq : ‖(σ : ℂ) - z‖ ^ 2 = (σ - z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
      mul_neg, neg_mul, neg_neg]
    ring
  rw [hnorm_sq]
  by_cases hcase : |σ - z₀.re| ≤ 2 * δ
  · have h1 : (σ - z₀.re) ^ 2 + 1 ≤ 4 * δ ^ 2 + 1 := by
      have : (σ - z₀.re) ^ 2 ≤ (2 * δ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hcase 2
      linarith
    have h2 : δ ^ 2 / (4 * δ ^ 2 + 1) * ((σ - z₀.re) ^ 2 + 1) ≤ δ ^ 2 := by
      calc δ ^ 2 / (4 * δ ^ 2 + 1) * ((σ - z₀.re) ^ 2 + 1)
          ≤ δ ^ 2 / (4 * δ ^ 2 + 1) * (4 * δ ^ 2 + 1) := by gcongr
        _ = δ ^ 2 := div_mul_cancel₀ _ (by positivity)
    calc min (1 / 4 : ℝ) (δ ^ 2 / (4 * δ ^ 2 + 1)) * ((σ - z₀.re) ^ 2 + 1)
        ≤ (δ ^ 2 / (4 * δ ^ 2 + 1)) * ((σ - z₀.re) ^ 2 + 1) := by
          gcongr; exact min_le_right _ _
      _ ≤ δ ^ 2 := h2
      _ ≤ z.im ^ 2 := by nlinarith
      _ ≤ (σ - z.re) ^ 2 + z.im ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
  · push Not at hcase
    have hsub : |σ - z₀.re| / 2 ≤ |σ - z.re| := by
      have htri : |σ - z₀.re| ≤ |σ - z.re| + |z.re - z₀.re| := by
        simpa [sub_add_sub_cancel] using abs_add_le (σ - z.re) (z.re - z₀.re)
      linarith
    have hsq1 : (σ - z₀.re) ^ 2 / 4 ≤ (σ - z.re) ^ 2 := by
      have : (|σ - z₀.re| / 2) ^ 2 ≤ |σ - z.re| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsub 2
      rw [div_pow, sq_abs, sq_abs] at this
      linarith
    have hmin_le : min (1 / 4 : ℝ) (δ ^ 2 / (4 * δ ^ 2 + 1)) ≤ δ ^ 2 / (4 * δ ^ 2 + 1) :=
      min_le_right _ _
    have hc1 : min (1 / 4 : ℝ) (δ ^ 2 / (4 * δ ^ 2 + 1)) * (σ - z₀.re) ^ 2 ≤ (σ - z.re) ^ 2 := by
      calc min (1 / 4 : ℝ) (δ ^ 2 / (4 * δ ^ 2 + 1)) * (σ - z₀.re) ^ 2
          ≤ (1 / 4) * (σ - z₀.re) ^ 2 := by gcongr; exact min_le_left _ _
        _ ≤ (σ - z.re) ^ 2 := by linarith
    have hc2 : min (1 / 4 : ℝ) (δ ^ 2 / (4 * δ ^ 2 + 1)) * 1 ≤ z.im ^ 2 := by
      have hfrac : δ ^ 2 / (4 * δ ^ 2 + 1) ≤ δ ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg δ]
      calc min (1 / 4 : ℝ) (δ ^ 2 / (4 * δ ^ 2 + 1)) * 1
          ≤ δ ^ 2 / (4 * δ ^ 2 + 1) := by rw [mul_one]; exact hmin_le
        _ ≤ δ ^ 2 := hfrac
        _ ≤ z.im ^ 2 := by nlinarith
    linarith

private lemma continuousOn_slitBoundaryMap_slitPreimage :
    ContinuousOn slitBoundaryMap slitPreimage := by
  unfold slitBoundaryMap
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.log ?_ ?_)
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun σ hσ => ?_)
    have h0 : σ ≠ 0 := by rcases hσ with ⟨_, h⟩ | (h : 1 < σ) <;> linarith
    have hm1 : σ ≠ -1 := by rcases hσ with ⟨h, _⟩ | (h : 1 < σ) <;> linarith
    exact mul_ne_zero (neg_ne_zero.mpr h0) (fun h => hm1 (by linarith))
  · intro σ hσ
    rcases hσ with ⟨hm1, h0⟩ | (h1 : 1 < σ)
    · exact div_ne_zero (by linarith) (mul_ne_zero (by linarith) (by linarith))
    · exact div_ne_zero (by linarith) (mul_ne_zero (by linarith) (by linarith))

private lemma schwarzKernel_aestronglyMeasurable {z : ℂ} (hz : 0 < z.im) :
    AEStronglyMeasurable (fun σ : ℝ => (slitL (slitBoundaryMap σ) : ℂ) * schwarzKernel z σ)
      (volume.restrict slitPreimage) := by
  have hslit_open : IsOpen slitPreimage := isOpen_Ioo.union isOpen_Ioi
  have hcont : ContinuousOn (fun σ : ℝ => (slitL (slitBoundaryMap σ) : ℂ) * schwarzKernel z σ)
      slitPreimage := by
    have hslitL : ContinuousOn (fun σ => (slitL (slitBoundaryMap σ) : ℂ)) slitPreimage := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold slitL
      exact (continuousOn_const.mul continuousOn_slitBoundaryMap_slitPreimage.abs).div_const 3
    refine hslitL.mul ?_
    unfold schwarzKernel
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun σ _ => ?_)
    refine mul_ne_zero ?_ (Complex.ofReal_ne_zero.mpr (by positivity))
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
    linarith
  exact hcont.aestronglyMeasurable hslit_open.measurableSet

private lemma schwarzKernel_norm_le {z₀ : ℂ} (hz₀ : 0 < z₀.im) {z : ℂ}
    (hz : z ∈ Metric.ball z₀ (z₀.im / 2)) (σ : ℝ) :
    ‖schwarzKernel z σ‖ ≤
      ((1 + ‖z₀‖ + z₀.im / 2) /
        Real.sqrt (min (1 / 4 : ℝ) ((z₀.im / 2) ^ 2 / (4 * (z₀.im / 2) ^ 2 + 1))) *
        Real.sqrt (2 * (z₀.re ^ 2 + 1)) * (2 * (z₀.re ^ 2 + 1)) * π) *
        poissonKernel z₀.re 1 σ := by
  set c₀ := min (1 / 4 : ℝ) ((z₀.im / 2) ^ 2 / (4 * (z₀.im / 2) ^ 2 + 1))
  have hc₀ : 0 < c₀ := lt_min (by norm_num) (div_pos (sq_pos_of_pos (half_pos hz₀)) (by positivity))
  have hz_dist : ‖z - z₀‖ < z₀.im / 2 := Complex.dist_eq z z₀ ▸ Metric.mem_ball.mp hz
  have hz_norm : ‖z‖ ≤ ‖z₀‖ + z₀.im / 2 := by
    calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by congr 1; ring
      _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + z₀.im / 2 := by linarith
  have hnum : ‖1 + (σ : ℂ) * z‖ ≤ (1 + ‖z₀‖ + z₀.im / 2) * Real.sqrt (1 + σ ^ 2) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (1 + σ ^ 2) := by
      conv_lhs => rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith [sq_nonneg σ])
    have h2 : |σ| ≤ Real.sqrt (1 + σ ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    calc ‖1 + (σ : ℂ) * z‖ ≤ ‖(1 : ℂ)‖ + ‖(σ : ℂ) * z‖ := norm_add_le _ _
      _ = 1 + |σ| * ‖z‖ := by simp [Complex.norm_real]
      _ ≤ Real.sqrt (1 + σ ^ 2) + Real.sqrt (1 + σ ^ 2) * (‖z₀‖ + z₀.im / 2) := by
          gcongr
      _ = (1 + ‖z₀‖ + z₀.im / 2) * Real.sqrt (1 + σ ^ 2) := by ring
  have hden1 : Real.sqrt c₀ * Real.sqrt ((σ - z₀.re) ^ 2 + 1) ≤ ‖(σ : ℂ) - z‖ := by
    have hsq := norm_sub_ofReal_sq_ge hz₀ hz σ
    rw [← Real.sqrt_mul hc₀.le]
    exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hsq⟩
  have hden_pos : 0 < Real.sqrt c₀ * Real.sqrt ((σ - z₀.re) ^ 2 + 1) := by positivity
  have hinv_le : (‖(σ : ℂ) - z‖ * (1 + σ ^ 2))⁻¹ ≤
      (Real.sqrt c₀ * Real.sqrt ((σ - z₀.re) ^ 2 + 1) * (1 + σ ^ 2))⁻¹ := by
    gcongr
  have hkern_eq : ‖schwarzKernel z σ‖ = ‖1 + (σ : ℂ) * z‖ / (‖(σ : ℂ) - z‖ * (1 + σ ^ 2)) := by
    unfold schwarzKernel
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsqrt_rat : Real.sqrt (1 + σ ^ 2) / Real.sqrt ((σ - z₀.re) ^ 2 + 1) ≤
      Real.sqrt (2 * (z₀.re ^ 2 + 1)) := by
    have hle := one_add_sq_le z₀.re σ
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity)), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hinv_sq : (1 + σ ^ 2)⁻¹ ≤ 2 * (z₀.re ^ 2 + 1) * ((σ - z₀.re) ^ 2 + 1)⁻¹ := by
    have hle := sub_sq_add_one_le z₀.re σ
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    calc (1 : ℝ) ≤ ((σ - z₀.re) ^ 2 + 1)⁻¹ * (2 * (z₀.re ^ 2 + 1) * (1 + σ ^ 2)) := by
          rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]; linarith
      _ = 2 * (z₀.re ^ 2 + 1) * ((σ - z₀.re) ^ 2 + 1)⁻¹ * (1 + σ ^ 2) := by ring
  have hpk : ((σ - z₀.re) ^ 2 + 1)⁻¹ = π * poissonKernel z₀.re 1 σ := by
    unfold poissonKernel
    have hpi := Real.pi_pos.ne'
    field_simp [hpi]
  rw [hkern_eq, div_eq_mul_inv]
  calc ‖1 + (σ : ℂ) * z‖ * (‖(σ : ℂ) - z‖ * (1 + σ ^ 2))⁻¹
      ≤ (1 + ‖z₀‖ + z₀.im / 2) * Real.sqrt (1 + σ ^ 2) *
          (Real.sqrt c₀ * Real.sqrt ((σ - z₀.re) ^ 2 + 1) * (1 + σ ^ 2))⁻¹ := by
        gcongr
    _ = (1 + ‖z₀‖ + z₀.im / 2) / Real.sqrt c₀ *
          (Real.sqrt (1 + σ ^ 2) / Real.sqrt ((σ - z₀.re) ^ 2 + 1)) * (1 + σ ^ 2)⁻¹ := by
        rw [mul_inv, mul_inv]; ring
    _ ≤ (1 + ‖z₀‖ + z₀.im / 2) / Real.sqrt c₀ * Real.sqrt (2 * (z₀.re ^ 2 + 1)) *
          (2 * (z₀.re ^ 2 + 1) * ((σ - z₀.re) ^ 2 + 1)⁻¹) := by
        gcongr
    _ = ((1 + ‖z₀‖ + z₀.im / 2) / Real.sqrt c₀ * Real.sqrt (2 * (z₀.re ^ 2 + 1)) *
          (2 * (z₀.re ^ 2 + 1)) * π) * poissonKernel z₀.re 1 σ := by
        rw [hpk]; ring

lemma schwarzSlit_integrable {z : ℂ} (hz : 0 < z.im) :
    IntegrableOn (fun σ : ℝ => (slitL (slitBoundaryMap σ) : ℂ) * schwarzKernel z σ) slitPreimage := by
  set c₀ := min (1 / 4 : ℝ) ((z.im / 2) ^ 2 / (4 * (z.im / 2) ^ 2 + 1))
  let C_k : ℝ := (1 + ‖z‖ + z.im / 2) / Real.sqrt c₀ *
    Real.sqrt (2 * (z.re ^ 2 + 1)) * (2 * (z.re ^ 2 + 1)) * π
  have hdom : IntegrableOn (fun σ : ℝ => C_k * (slitL (slitBoundaryMap σ) * poissonKernel z.re 1 σ))
      slitPreimage :=
    (identification_integrand_integrable z.re one_pos).const_mul C_k
  refine hdom.mono' (schwarzKernel_aestronglyMeasurable hz) (ae_of_all _ fun σ => ?_)
  have hslit_nonneg : 0 ≤ slitL (slitBoundaryMap σ) := by unfold slitL; positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hslit_nonneg]
  have hle := schwarzKernel_norm_le hz (Metric.mem_ball_self (half_pos hz)) σ
  calc slitL (slitBoundaryMap σ) * ‖schwarzKernel z σ‖
      ≤ slitL (slitBoundaryMap σ) * (C_k * poissonKernel z.re 1 σ) := by gcongr
    _ = C_k * (slitL (slitBoundaryMap σ) * poissonKernel z.re 1 σ) := by ring

lemma differentiableOn_schwarzSlit : DifferentiableOn ℂ schwarzSlit {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  change 0 < z₀.im at hz₀
  set c₀ := min (1 / 4 : ℝ) ((z₀.im / 2) ^ 2 / (4 * (z₀.im / 2) ^ 2 + 1))
  have hc₀ : 0 < c₀ := lt_min (by norm_num) (div_pos (sq_pos_of_pos (half_pos hz₀)) (by positivity))
  let F : ℂ → ℝ → ℂ := fun z σ => (slitL (slitBoundaryMap σ) : ℂ) * schwarzKernel z σ
  let F' : ℂ → ℝ → ℂ := fun z σ => (slitL (slitBoundaryMap σ) : ℂ) / ((σ : ℂ) - z) ^ 2
  let bound : ℝ → ℝ := fun σ =>
    (π * (2 * (z₀.re ^ 2 + 1)) * c₀⁻¹) * (slitL (slitBoundaryMap σ) * poissonKernel z₀.re 1 σ)
  have hbound_int : IntegrableOn bound slitPreimage :=
    (identification_integrand_integrable z₀.re one_pos).const_mul _
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (F z) (volume.restrict slitPreimage) := by
    filter_upwards [Metric.ball_mem_nhds z₀ (half_pos hz₀)] with z hz
    have hz_dist : ‖z - z₀‖ < z₀.im / 2 := Complex.dist_eq z z₀ ▸ Metric.mem_ball.mp hz
    have hzim : 0 < z.im := by
      have h1 := (Complex.abs_im_le_norm (z - z₀)).trans hz_dist.le
      rw [Complex.sub_im] at h1
      linarith [(abs_le.mp h1).1]
    exact schwarzKernel_aestronglyMeasurable hzim
  have hF_int : Integrable (F z₀) (volume.restrict slitPreimage) := schwarzSlit_integrable hz₀
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict slitPreimage) := by
    have hslit_open : IsOpen slitPreimage := isOpen_Ioo.union isOpen_Ioi
    have hcont : ContinuousOn (F' z₀) slitPreimage := by
      have hslitL : ContinuousOn (fun σ => (slitL (slitBoundaryMap σ) : ℂ)) slitPreimage := by
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        unfold slitL
        exact (continuousOn_const.mul continuousOn_slitBoundaryMap_slitPreimage.abs).div_const 3
      refine hslitL.div (by fun_prop) (fun σ _ => ?_)
      apply pow_ne_zero 2
      intro h0
      have := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
      linarith
    exact hcont.aestronglyMeasurable hslit_open.measurableSet
  have h_bound : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      ∀ z ∈ Metric.ball z₀ (z₀.im / 2), ‖F' z σ‖ ≤ bound σ := by
    refine ae_of_all _ fun σ z hz => ?_
    dsimp [F', bound]
    have hslit_nonneg : 0 ≤ slitL (slitBoundaryMap σ) := by unfold slitL; positivity
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hslit_nonneg, norm_pow]
    have hsq := norm_sub_ofReal_sq_ge hz₀ hz σ
    have hpos : 0 < c₀ * ((σ - z₀.re) ^ 2 + 1) := by positivity
    have hpk : ((σ - z₀.re) ^ 2 + 1)⁻¹ = π * poissonKernel z₀.re 1 σ := by
      unfold poissonKernel; field_simp [Real.pi_pos.ne']
    have hinv : (‖(σ : ℂ) - z‖ ^ 2)⁻¹ ≤ (c₀ * ((σ - z₀.re) ^ 2 + 1))⁻¹ := by gcongr
    have h1 : slitL (slitBoundaryMap σ) / ‖(σ : ℂ) - z‖ ^ 2 ≤
        (π * c₀⁻¹) * (slitL (slitBoundaryMap σ) * poissonKernel z₀.re 1 σ) := by
      rw [div_eq_mul_inv]
      calc slitL (slitBoundaryMap σ) * (‖(σ : ℂ) - z‖ ^ 2)⁻¹
          ≤ slitL (slitBoundaryMap σ) * (c₀ * ((σ - z₀.re) ^ 2 + 1))⁻¹ := by gcongr
        _ = (π * c₀⁻¹) * (slitL (slitBoundaryMap σ) * poissonKernel z₀.re 1 σ) := by
            rw [mul_inv, hpk]; ring
    have h2 : 1 ≤ 2 * (z₀.re ^ 2 + 1) := by nlinarith [sq_nonneg z₀.re]
    have hpk_nonneg : 0 ≤ poissonKernel z₀.re 1 σ := by unfold poissonKernel; positivity
    calc slitL (slitBoundaryMap σ) / ‖(σ : ℂ) - z‖ ^ 2
        ≤ (π * c₀⁻¹) * (slitL (slitBoundaryMap σ) * poissonKernel z₀.re 1 σ) := h1
      _ ≤ (π * (2 * (z₀.re ^ 2 + 1)) * c₀⁻¹) * (slitL (slitBoundaryMap σ) * poissonKernel z₀.re 1 σ) := by
          have : 0 ≤ π * c₀⁻¹ * (slitL (slitBoundaryMap σ) * poissonKernel z₀.re 1 σ) := by
            positivity
          nlinarith
  have h_diff : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      ∀ z ∈ Metric.ball z₀ (z₀.im / 2), HasDerivAt (F · σ) (F' z σ) z := by
    refine ae_of_all _ fun σ z hz => ?_
    have hz_dist : ‖z - z₀‖ < z₀.im / 2 := Complex.dist_eq z z₀ ▸ Metric.mem_ball.mp hz
    have hzim : 0 < z.im := by
      have h1 := (Complex.abs_im_le_norm (z - z₀)).trans hz_dist.le
      rw [Complex.sub_im] at h1
      linarith [(abs_le.mp h1).1]
    have hne : (σ : ℂ) - z ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
      linarith
    have h1p : (1 + σ ^ 2 : ℝ) ≠ 0 := by positivity
    have hkern_eq : ∀ w ∈ Metric.ball z₀ (z₀.im / 2),
        schwarzKernel w σ = ((σ : ℂ) - w)⁻¹ - ((σ / (1 + σ ^ 2) : ℝ) : ℂ) := by
      intro w hw
      have hw_dist : ‖w - z₀‖ < z₀.im / 2 := Complex.dist_eq w z₀ ▸ Metric.mem_ball.mp hw
      have hwim : 0 < w.im := by
        have h1 := (Complex.abs_im_le_norm (w - z₀)).trans hw_dist.le
        rw [Complex.sub_im] at h1
        linarith [(abs_le.mp h1).1]
      have hwne : (σ : ℂ) - w ≠ 0 := by
        intro h0; have := congrArg Complex.im h0
        simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
        linarith
      have h1pC : (1 : ℂ) + (σ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h1p
      unfold schwarzKernel
      rw [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
      push_cast
      field_simp [hwne, h1pC]
      ring
    have hsub : HasDerivAt (fun w : ℂ => (σ : ℂ) - w) (-1 : ℂ) z := by
      simpa using (hasDerivAt_id z).const_sub (σ : ℂ)
    have hinv := (hsub.inv hne).sub_const (((σ / (1 + σ ^ 2) : ℝ) : ℂ))
    have hev_ball : (fun w : ℂ => schwarzKernel w σ) =ᶠ[𝓝 z]
        (fun w : ℂ => ((σ : ℂ) - w)⁻¹ - ((σ / (1 + σ ^ 2) : ℝ) : ℂ)) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) hkern_eq
    have hinv_congr : HasDerivAt (fun w : ℂ => schwarzKernel w σ) (1 / ((σ : ℂ) - z) ^ 2) z := by
      refine (hinv.congr_of_eventuallyEq hev_ball).congr_deriv ?_
      ring
    exact (hinv_congr.const_mul _).congr_deriv (by dsimp [F']; ring)
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ (half_pos hz₀)) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hfun : schwarzSlit = fun z => -((π : ℂ)⁻¹) * ∫ σ in slitPreimage, F z σ := rfl
  rw [hfun]
  exact (hderiv.const_mul (-((π : ℂ)⁻¹))).differentiableAt.differentiableWithinAt

lemma schwarzSlit_im {z : ℂ} (hz : 0 < z.im) :
    (schwarzSlit z).im = -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel z.re z.im σ := by
  have hint := schwarzSlit_integrable hz
  have hcomm := Complex.imCLM.integral_comp_comm hint
  have him_kern : ∀ σ : ℝ, (schwarzKernel z σ).im = π * poissonKernel z.re z.im σ := by
    intro σ
    have hne : (σ : ℂ) - z ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
      linarith
    have h1p : (1 + σ ^ 2 : ℝ) ≠ 0 := by positivity
    have h1pC : (1 : ℂ) + (σ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h1p
    have hkern_eq : schwarzKernel z σ = ((σ : ℂ) - z)⁻¹ - ((σ / (1 + σ ^ 2) : ℝ) : ℂ) := by
      unfold schwarzKernel
      rw [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
      push_cast
      field_simp [hne, h1pC]
      ring
    rw [hkern_eq, Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.inv_im]
    have hconj : ((σ : ℂ) - z).im = -z.im := by simp
    have hnsq : Complex.normSq ((σ : ℂ) - z) = (σ - z.re) ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    rw [hconj, hnsq]
    unfold poissonKernel
    have hpi := Real.pi_pos.ne'
    field_simp [hpi]
  unfold schwarzSlit
  have hpi_inv : -((π : ℂ)⁻¹) = ((-π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hpi_inv, Complex.im_ofReal_mul]
  change (-π⁻¹) * Complex.imCLM (∫ σ in slitPreimage, _) = _
  rw [← hcomm]
  have hcongr : (fun σ : ℝ => Complex.imCLM ((slitL (slitBoundaryMap σ) : ℂ) * schwarzKernel z σ)) =
      (fun σ : ℝ => slitL (slitBoundaryMap σ) * (π * poissonKernel z.re z.im σ)) := by
    ext σ
    change ((slitL (slitBoundaryMap σ) : ℂ) * schwarzKernel z σ).im = _
    rw [Complex.im_ofReal_mul, him_kern]
  rw [hcongr, show (fun σ : ℝ => slitL (slitBoundaryMap σ) * (π * poissonKernel z.re z.im σ)) =
      (fun σ : ℝ => π * (slitL (slitBoundaryMap σ) * poissonKernel z.re z.im σ)) by ext σ; ring,
    integral_const_mul]
  have hpi := Real.pi_pos.ne'
  field_simp [hpi]

lemma tendsto_schwarzSlit_im {σ₀ : ℝ} (h0 : σ₀ ≠ 0) (h1 : σ₀ ≠ 1) (hm1 : σ₀ ≠ -1) :
    Tendsto (fun z : ℂ => (schwarzSlit z).im) (𝓝[{z : ℂ | 0 < z.im}] (σ₀ : ℂ))
      (𝓝 (if σ₀ ∈ slitPreimage then -slitL (slitBoundaryMap σ₀) else 0)) := by
  let g : ℝ → ℝ := fun σ => if σ ∈ slitPreimage then -slitL (slitBoundaryMap σ) else 0
  have hg_cont : ContinuousAt g σ₀ := by
    have hslit_open : IsOpen slitPreimage := isOpen_Ioo.union isOpen_Ioi
    have hcompl_open : IsOpen ((Iio (-1 : ℝ)) ∪ Ioo 0 1) := isOpen_Iio.union isOpen_Ioo
    by_cases hmem : σ₀ ∈ slitPreimage
    · have hev : g =ᶠ[𝓝 σ₀] fun σ => -slitL (slitBoundaryMap σ) := by
        filter_upwards [hslit_open.mem_nhds hmem] with σ hσ
        dsimp [g]; simp [hσ]
      refine ContinuousAt.congr ?_ hev.symm
      have hc := (continuousOn_slitBoundaryMap_slitPreimage.continuousAt
        (hslit_open.mem_nhds hmem))
      unfold slitL
      exact ((hc.abs.const_mul (2 * π)).div_const 3).neg
    · have hmem' : σ₀ ∈ (Iio (-1 : ℝ)) ∪ Ioo 0 1 := by
        rcases lt_trichotomy σ₀ (-1) with h | rfl | h
        · exact Or.inl h
        · exact absurd rfl hm1
        · rcases lt_trichotomy σ₀ 0 with h0' | rfl | h0'
          · exact absurd (Or.inl ⟨h, h0'⟩) hmem
          · exact absurd rfl h0
          · rcases lt_trichotomy σ₀ 1 with h1' | rfl | h1'
            · exact Or.inr ⟨h0', h1'⟩
            · exact absurd rfl h1
            · exact absurd (Or.inr h1') hmem
      have hev : g =ᶠ[𝓝 σ₀] fun _ => (0 : ℝ) := by
        filter_upwards [hcompl_open.mem_nhds hmem'] with σ hσ
        have hnot : σ ∉ slitPreimage := by
          rcases hσ with (h : σ < -1) | ⟨ha, hb⟩ <;>
            rintro (⟨h1', h2'⟩ | (h3' : 1 < σ)) <;> linarith
        dsimp [g]; simp [hnot]
      exact continuousAt_const.congr hev.symm
  have hg_int : ∀ x : ℝ, ∀ {y : ℝ}, 0 < y → Integrable (fun σ : ℝ => g σ * poissonKernel x y σ) := by
    intro x y hy
    have hi := (identification_integrand_integrable x hy).neg
    have hslit_meas : MeasurableSet slitPreimage := (isOpen_Ioo.union isOpen_Ioi).measurableSet
    refine ((integrable_indicator_iff hslit_meas).mpr hi).congr (ae_of_all _ fun σ => ?_)
    dsimp [g, Set.indicator]
    split_ifs <;> ring
  have him_eq : ∀ z : ℂ, 0 < z.im →
      (schwarzSlit z).im = ∫ σ : ℝ, g σ * poissonKernel z.re z.im σ := by
    intro z hz
    rw [schwarzSlit_im hz, ← integral_neg]
    have hslit_meas : MeasurableSet slitPreimage := (isOpen_Ioo.union isOpen_Ioi).measurableSet
    have heq_univ : (fun σ : ℝ => g σ * poissonKernel z.re z.im σ) =
        slitPreimage.indicator (fun σ => -(slitL (slitBoundaryMap σ) * poissonKernel z.re z.im σ)) := by
      ext σ
      dsimp [g, Set.indicator]
      split_ifs <;> ring
    rw [heq_univ, integral_indicator hslit_meas]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hg_cont (ε / 2) (half_pos hε)
  let C_δ : ℝ := 4 * (δ ^ 2 + 1) / δ ^ 2
  have hCδ_pos : 0 < C_δ := by positivity
  let I_tail : ℝ := ∫ σ : ℝ, (|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ
  have hItail_int : Integrable (fun σ : ℝ => (|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) := by
    have h1 : Integrable (fun σ : ℝ => |g σ| * poissonKernel σ₀ 1 σ) := by
      refine (hg_int σ₀ one_pos).norm.congr (ae_of_all _ fun σ => ?_)
      have hpk : 0 ≤ poissonKernel σ₀ 1 σ := by unfold poissonKernel; positivity
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpk]
    have h2 : Integrable (fun σ : ℝ => |g σ₀| * poissonKernel σ₀ 1 σ) :=
      (integrable_poissonKernel σ₀ one_pos).const_mul _
    exact (h1.add h2).congr (ae_of_all _ fun σ => (add_mul _ _ _).symm)
  have hItail_nonneg : 0 ≤ I_tail := by
    refine integral_nonneg fun σ => ?_
    have hpk : 0 ≤ poissonKernel σ₀ 1 σ := by unfold poissonKernel; positivity
    positivity
  let η₁ := min (δ / 2) (ε / (2 * (C_δ * I_tail + 1)))
  refine ⟨η₁, by positivity, fun z hz hdist => ?_⟩
  rw [Complex.dist_eq] at hdist
  change 0 < z.im at hz
  rw [Real.dist_eq, him_eq z hz]
  have hpk_int := integrable_poissonKernel z.re hz
  have hpk_one := integral_poissonKernel z.re hz
  have hdiff_eq : (∫ σ : ℝ, g σ * poissonKernel z.re z.im σ) - g σ₀ =
      ∫ σ : ℝ, (g σ - g σ₀) * poissonKernel z.re z.im σ := by
    have hsub : (fun σ : ℝ => (g σ - g σ₀) * poissonKernel z.re z.im σ) =
        (fun σ : ℝ => g σ * poissonKernel z.re z.im σ - g σ₀ * poissonKernel z.re z.im σ) := by
      ext σ; ring
    rw [hsub, integral_sub (hg_int z.re hz) (hpk_int.const_mul (g σ₀)), integral_const_mul,
      hpk_one, mul_one]
  rw [hdiff_eq]
  have hzre : |z.re - σ₀| < δ / 2 := by
    have := Complex.abs_re_le_norm (z - (σ₀ : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    calc |z.re - σ₀| ≤ ‖z - (σ₀ : ℂ)‖ := this
      _ < η₁ := hdist
      _ ≤ δ / 2 := min_le_left _ _
  have hzim_lt : z.im < ε / (2 * (C_δ * I_tail + 1)) := by
    have h1 := Complex.abs_im_le_norm (z - (σ₀ : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_of_pos hz] at h1
    calc z.im ≤ ‖z - (σ₀ : ℂ)‖ := h1
      _ < η₁ := hdist
      _ ≤ ε / (2 * (C_δ * I_tail + 1)) := min_le_right _ _
  have hpt : ∀ σ : ℝ, |(g σ - g σ₀) * poissonKernel z.re z.im σ| ≤
      (ε / 2) * poissonKernel z.re z.im σ +
        (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) := by
    intro σ
    have hpk_pos : 0 ≤ poissonKernel z.re z.im σ := by unfold poissonKernel; positivity
    rw [abs_mul, abs_of_nonneg hpk_pos]
    by_cases hnear : |σ - σ₀| < δ
    · have hsmall : |g σ - g σ₀| < ε / 2 := by simpa [Real.dist_eq] using hδ hnear
      have hnonneg : 0 ≤ (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) := by
        have : 0 ≤ poissonKernel σ₀ 1 σ := by unfold poissonKernel; positivity
        positivity
      nlinarith
    · push Not at hnear
      have hge_half : |σ - σ₀| / 2 ≤ |σ - z.re| := by
        have := abs_add_le (σ - z.re) (z.re - σ₀)
        rw [sub_add_sub_cancel] at this
        linarith
      have hsq_ge : (σ - z.re) ^ 2 + z.im ^ 2 ≥ (δ ^ 2 / (4 * (δ ^ 2 + 1))) * ((σ - σ₀) ^ 2 + 1) := by
        have h1 : (σ - σ₀) ^ 2 / 4 ≤ (σ - z.re) ^ 2 := by
          have : (|σ - σ₀| / 2) ^ 2 ≤ |σ - z.re| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hge_half 2
          rw [div_pow, sq_abs, sq_abs] at this
          linarith
        have h2 : δ ^ 2 / (δ ^ 2 + 1) * ((σ - σ₀) ^ 2 + 1) ≤ (σ - σ₀) ^ 2 := by
          have h3 : δ ^ 2 ≤ (σ - σ₀) ^ 2 := by
            have hpow := pow_le_pow_left₀ hδ_pos.le hnear 2
            rwa [sq_abs (σ - σ₀)] at hpow
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg δ]
        have h2' : (δ ^ 2 / (4 * (δ ^ 2 + 1))) * ((σ - σ₀) ^ 2 + 1) ≤ (σ - σ₀) ^ 2 / 4 := by
          have hsc : δ ^ 2 / (4 * (δ ^ 2 + 1)) * ((σ - σ₀) ^ 2 + 1) =
              (1 / 4 : ℝ) * (δ ^ 2 / (δ ^ 2 + 1) * ((σ - σ₀) ^ 2 + 1)) := by
            have h1d : δ ^ 2 + 1 ≠ 0 := by positivity
            field_simp [h1d]
          rw [hsc]
          linarith [h2]
        have h3 : 0 ≤ z.im ^ 2 := sq_nonneg _
        linarith [h1, h2', h3]
      have hpk_tail : poissonKernel z.re z.im σ ≤ z.im * C_δ * poissonKernel σ₀ 1 σ := by
        unfold poissonKernel
        have hden_pos : 0 < (δ ^ 2 / (4 * (δ ^ 2 + 1))) * ((σ - σ₀) ^ 2 + 1) := by positivity
        have hinv : (π * ((σ - z.re) ^ 2 + z.im ^ 2))⁻¹ ≤
            (π * ((δ ^ 2 / (4 * (δ ^ 2 + 1))) * ((σ - σ₀) ^ 2 + 1)))⁻¹ := by gcongr
        calc z.im / (π * ((σ - z.re) ^ 2 + z.im ^ 2))
            = z.im * (π * ((σ - z.re) ^ 2 + z.im ^ 2))⁻¹ := div_eq_mul_inv _ _
          _ ≤ z.im * (π * ((δ ^ 2 / (4 * (δ ^ 2 + 1))) * ((σ - σ₀) ^ 2 + 1)))⁻¹ := by gcongr
          _ = z.im * C_δ * (1 / (π * ((σ - σ₀) ^ 2 + 1 ^ 2))) := by
              have h1d : (1 + δ ^ 2 : ℝ) ≠ 0 := by positivity
              have h4d : (4 + δ ^ 2 * 4 : ℝ) ≠ 0 := by positivity
              dsimp [C_δ]; field_simp [Real.pi_pos.ne', hδ_pos.ne', h1d, h4d]
      have htri : |g σ - g σ₀| ≤ |g σ| + |g σ₀| := by
        simpa [sub_eq_add_neg] using abs_add_le (g σ) (-g σ₀)
      have hnonneg : 0 ≤ (ε / 2) * poissonKernel z.re z.im σ := by positivity
      calc |g σ - g σ₀| * poissonKernel z.re z.im σ
          ≤ (|g σ| + |g σ₀|) * (z.im * C_δ * poissonKernel σ₀ 1 σ) := by
            gcongr
        _ = (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) := by ring
        _ ≤ (ε / 2) * poissonKernel z.re z.im σ +
              (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) := by linarith
  have hdom_int : Integrable (fun σ : ℝ => (ε / 2) * poissonKernel z.re z.im σ +
      (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ)) :=
    (hpk_int.const_mul _).add (hItail_int.const_mul _)
  have hint_norm : |∫ σ : ℝ, (g σ - g σ₀) * poissonKernel z.re z.im σ| ≤
      ∫ σ : ℝ, (ε / 2) * poissonKernel z.re z.im σ +
        (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) := by
    calc |∫ σ : ℝ, (g σ - g σ₀) * poissonKernel z.re z.im σ|
        ≤ ∫ σ : ℝ, |(g σ - g σ₀) * poissonKernel z.re z.im σ| := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun σ : ℝ => (g σ - g σ₀) * poissonKernel z.re z.im σ)
      _ ≤ ∫ σ : ℝ, (ε / 2) * poissonKernel z.re z.im σ +
            (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun σ => abs_nonneg _) hdom_int
            (ae_of_all _ hpt)
  have hint_eval : ∫ σ : ℝ, (ε / 2) * poissonKernel z.re z.im σ +
        (z.im * C_δ) * ((|g σ| + |g σ₀|) * poissonKernel σ₀ 1 σ) =
      ε / 2 + z.im * (C_δ * I_tail) := by
    rw [integral_add (hpk_int.const_mul _) (hItail_int.const_mul _),
      integral_const_mul, hpk_one, mul_one, integral_const_mul]
    dsimp [I_tail]; ring
  rw [hint_eval] at hint_norm
  have htail_lt : z.im * (C_δ * I_tail) < ε / 2 := by
    calc z.im * (C_δ * I_tail)
        ≤ z.im * (C_δ * I_tail + 1) := by gcongr; linarith
      _ < (ε / (2 * (C_δ * I_tail + 1))) * (C_δ * I_tail + 1) := by gcongr
      _ = ε / 2 := by
          have : C_δ * I_tail + 1 ≠ 0 := by positivity
          field_simp [this]
  linarith

private lemma real_log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 := Real.log_le_sub_one_of_pos hsqrt
  have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht.le]; ring
  linarith

private lemma integral_abs_log_mul_poissonKernel :
    ∃ C_log : ℝ, 0 < C_log ∧ ∀ (u₀ : ℝ) {y : ℝ}, 0 < y →
      Integrable (fun u : ℝ => |Real.log (|u|)| * poissonKernel u₀ y u) ∧
        ∫ u : ℝ, |Real.log (|u|)| * poissonKernel u₀ y u ≤
          C_log * (1 + |Real.log ‖(u₀ : ℂ) + (y : ℂ) * Complex.I‖|) := by
  have hint_unit : IntegrableOn (fun s : ℝ => |Real.log (|s|)|) (Icc (-1) 1) := by
    have hlog : IntervalIntegrable (fun u : ℝ => |Real.log (|u|)|) volume (-1) 1 := by
      have h0 := (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).abs
      have e : (fun u : ℝ => |Real.log (|u|)|) = fun u => |Real.log u| := by
        funext u; rw [Real.log_abs]
      rw [e]; exact h0
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hlog
  let K₀ : ℝ := ∫ s in Icc (-1 : ℝ) 1, |Real.log (|s|)|
  have hK₀ : 0 ≤ K₀ := setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _
  let C_log : ℝ := (4 / π + 1) + ((2 / π) * K₀ + (4 / π + 1) * Real.log 2 + 16 * Real.sqrt 2 / π)
  refine ⟨C_log, by positivity, fun u₀ y hy => ?_⟩
  set w₀ : ℂ := (u₀ : ℂ) + (y : ℂ) * Complex.I
  set r : ℝ := ‖w₀‖
  have hr_pos : 0 < r := norm_pos_iff.mpr (by
    intro h0; have := congrArg Complex.im h0; simp [w₀] at this; linarith)
  have hy_le_r : y ≤ r := by
    have h := Complex.abs_im_le_norm w₀
    have him : w₀.im = y := by simp [w₀]
    rwa [him, abs_of_pos hy] at h
  let t1 : ℝ → ℝ := Set.indicator (Icc (-(r / 2)) (r / 2))
    (fun u => (4 / (π * r)) * |Real.log (|u|)|)
  let t2 : ℝ → ℝ := fun u => (|Real.log r| + Real.log 2) * poissonKernel u₀ y u
  let t3 : ℝ → ℝ := Set.indicator {u : ℝ | 2 * r ≤ |u|}
    (fun u => (8 / π) * Real.sqrt r * |u| ^ (-(3 / 2 : ℝ)))
  have ht1_int : Integrable t1 := by
    rw [integrable_indicator_iff measurableSet_Icc]
    have hcomp : IntegrableOn (fun u : ℝ => |Real.log (|u|)|) (Icc (-(r / 2)) (r / 2)) := by
      have hlog : IntervalIntegrable (fun u : ℝ => |Real.log (|u|)|) volume (-(r / 2)) (r / 2) := by
        have h0 := (intervalIntegral.intervalIntegrable_log' (a := -(r / 2)) (b := r / 2)).abs
        have e : (fun u : ℝ => |Real.log (|u|)|) = fun u => |Real.log u| := by
          funext u; rw [Real.log_abs]
        rw [e]; exact h0
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hr_pos])).mp hlog
    exact hcomp.const_mul _
  have ht2_int : Integrable t2 := (integrable_poissonKernel u₀ hy).const_mul _
  have ht3_int : Integrable t3 := by
    have hset : {u : ℝ | 2 * r ≤ |u|} = Iic (-(2 * r)) ∪ Ici (2 * r) := by
      ext u; simp [le_abs']
    rw [integrable_indicator_iff (isClosed_le continuous_const continuous_abs).measurableSet, hset]
    have hrpow_pos : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ioi (2 * r)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)
    have hIci : IntegrableOn (fun u : ℝ => |u| ^ (-(3 / 2 : ℝ))) (Ici (2 * r)) := by
      refine (MeasureTheory.IntegrableOn.congr_set_ae hrpow_pos Ioi_ae_eq_Ici.symm).congr_fun (fun u hu => ?_)
        measurableSet_Ici
      rw [abs_of_pos (by linarith [show 2 * r ≤ u from hu])]
    have hIic : IntegrableOn (fun u : ℝ => |u| ^ (-(3 / 2 : ℝ))) (Iic (-(2 * r))) := by
      have hneg := ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
        (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr hIci
      have himg : Neg.neg ⁻¹' Ici (2 * r) = Iic (-(2 * r)) := by
        ext u; simp [le_neg]
      change IntegrableOn (fun u : ℝ => |(-u)| ^ (-(3 / 2 : ℝ))) (Neg.neg ⁻¹' Ici (2 * r)) volume at hneg
      rw [himg] at hneg
      exact hneg.congr_fun (fun u _ => by dsimp only; rw [abs_neg]) measurableSet_Iic
    exact (integrableOn_union.mpr ⟨hIic, hIci⟩).const_mul _
  have hdom : ∀ u : ℝ, |Real.log (|u|)| * poissonKernel u₀ y u ≤ t1 u + t2 u + t3 u := by
    intro u
    have hpk_nonneg : 0 ≤ poissonKernel u₀ y u := by unfold poissonKernel; positivity
    have ht1_nonneg : 0 ≤ t1 u := indicator_nonneg (fun _ _ => by positivity) u
    have ht2_nonneg : 0 ≤ t2 u := by dsimp [t2]; positivity
    have ht3_nonneg : 0 ≤ t3 u := indicator_nonneg (fun _ _ => by positivity) u
    by_cases h1 : |u| ≤ r / 2
    · have hdist : r / 2 ≤ ‖(u : ℂ) - w₀‖ := by
        have htri := norm_sub_norm_le w₀ (u : ℂ)
        rw [norm_sub_rev] at htri
        have hu_norm : ‖(u : ℂ)‖ = |u| := by simp [Complex.norm_real]
        linarith [htri, hu_norm, h1]
      have hsq_ge : (r / 2) ^ 2 ≤ (u - u₀) ^ 2 + y ^ 2 := by
        have hnorm_sq : ‖(u : ℂ) - w₀‖ ^ 2 = (u - u₀) ^ 2 + y ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; simp [w₀]; ring
        rw [← hnorm_sq]
        exact pow_le_pow_left₀ (by positivity) hdist 2
      have hpk_le : poissonKernel u₀ y u ≤ 4 / (π * r) := by
        unfold poissonKernel
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1' : y * r ≤ r ^ 2 := by nlinarith [hy_le_r, hr_pos]
        have h2' : r ^ 2 ≤ 4 * ((u - u₀) ^ 2 + y ^ 2) := by linarith [hsq_ge]
        have hpi := Real.pi_pos
        calc y * (π * r) = π * (y * r) := by ring
          _ ≤ π * (4 * ((u - u₀) ^ 2 + y ^ 2)) := mul_le_mul_of_nonneg_left (h1'.trans h2') hpi.le
          _ = 4 * (π * ((u - u₀) ^ 2 + y ^ 2)) := by ring
      have ht1_eq : t1 u = (4 / (π * r)) * |Real.log (|u|)| :=
        indicator_of_mem (mem_Icc.mpr (abs_le.mp h1)) _
      have hmul : |Real.log (|u|)| * poissonKernel u₀ y u ≤ t1 u := by
        rw [ht1_eq, mul_comm (4 / (π * r))]
        exact mul_le_mul_of_nonneg_left hpk_le (abs_nonneg _)
      linarith [hmul, ht2_nonneg, ht3_nonneg]
    · push Not at h1
      by_cases h2 : |u| < 2 * r
      · have hu_pos : 0 < |u| := by linarith [hr_pos, h1]
        have hlog_tri : |Real.log (|u|)| ≤ |Real.log r| + Real.log 2 := by
          have heq : Real.log (|u|) = Real.log r + Real.log (|u| / r) := by
            rw [← Real.log_mul hr_pos.ne' (div_ne_zero hu_pos.ne' hr_pos.ne')]
            congr 1; field_simp [hr_pos.ne']
          have hlog_rat : |Real.log (|u| / r)| ≤ Real.log 2 := by
            rw [abs_le]; constructor
            · rw [← Real.log_inv]
              exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ (by positivity)]; linarith [h1])
            · exact Real.log_le_log (div_pos hu_pos hr_pos) (by rw [div_le_iff₀ hr_pos]; linarith [h2])
          calc |Real.log (|u|)| = |Real.log r + Real.log (|u| / r)| := by rw [heq]
            _ ≤ |Real.log r| + |Real.log (|u| / r)| := abs_add_le _ _
            _ ≤ |Real.log r| + Real.log 2 := by linarith [hlog_rat]
        have hmul : |Real.log (|u|)| * poissonKernel u₀ y u ≤ t2 u := by
          dsimp [t2]; exact mul_le_mul_of_nonneg_right hlog_tri hpk_nonneg
        linarith [hmul, ht1_nonneg, ht3_nonneg]
      · push Not at h2
        have hu_pos : 0 < |u| := by linarith [hr_pos, h2]
        have hlog_tri : |Real.log (|u|)| ≤ |Real.log r| + Real.log (|u| / r) := by
          have heq : Real.log (|u|) = Real.log r + Real.log (|u| / r) := by
            rw [← Real.log_mul hr_pos.ne' (div_ne_zero hu_pos.ne' hr_pos.ne')]
            congr 1; field_simp [hr_pos.ne']
          have hlog_nn : 0 ≤ Real.log (|u| / r) :=
            Real.log_nonneg (by rw [le_div_iff₀ hr_pos]; linarith [h2])
          calc |Real.log (|u|)| = |Real.log r + Real.log (|u| / r)| := by rw [heq]
            _ ≤ |Real.log r| + |Real.log (|u| / r)| := abs_add_le _ _
            _ = |Real.log r| + Real.log (|u| / r) := by rw [abs_of_nonneg hlog_nn]
        have hsqrt : Real.log (|u| / r) ≤ 2 * Real.sqrt (|u| / r) :=
          real_log_le_two_sqrt (div_pos hu_pos hr_pos)
        have hdist : |u| / 2 ≤ ‖(u : ℂ) - w₀‖ := by
          have htri := norm_sub_norm_le (u : ℂ) w₀
          have hu_norm : ‖(u : ℂ)‖ = |u| := by simp [Complex.norm_real]
          linarith [htri, hu_norm, h2]
        have hsq_ge : (|u| / 2) ^ 2 ≤ (u - u₀) ^ 2 + y ^ 2 := by
          have hnorm_sq : ‖(u : ℂ) - w₀‖ ^ 2 = (u - u₀) ^ 2 + y ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; simp [w₀]; ring
          rw [← hnorm_sq]
          exact pow_le_pow_left₀ (by positivity) hdist 2
        have hpk_le : poissonKernel u₀ y u ≤ 4 * r / (π * |u| ^ 2) := by
          unfold poissonKernel
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1' : y * |u| ^ 2 ≤ r * |u| ^ 2 := mul_le_mul_of_nonneg_right hy_le_r (sq_nonneg _)
          have h2' : r * |u| ^ 2 ≤ 4 * r * ((u - u₀) ^ 2 + y ^ 2) := by
            have hle : |u| ^ 2 ≤ 4 * ((u - u₀) ^ 2 + y ^ 2) := by
              have h4 : (|u| / 2) ^ 2 = |u| ^ 2 / 4 := by ring
              linarith [hsq_ge, h4]
            calc r * |u| ^ 2 ≤ r * (4 * ((u - u₀) ^ 2 + y ^ 2)) :=
                  mul_le_mul_of_nonneg_left hle hr_pos.le
              _ = 4 * r * ((u - u₀) ^ 2 + y ^ 2) := by ring
          have hpi := Real.pi_pos
          calc y * (π * |u| ^ 2) = π * (y * |u| ^ 2) := by ring
            _ ≤ π * (4 * r * ((u - u₀) ^ 2 + y ^ 2)) := mul_le_mul_of_nonneg_left (h1'.trans h2') hpi.le
            _ = 4 * r * (π * ((u - u₀) ^ 2 + y ^ 2)) := by ring
        have hterm3 : Real.log (|u| / r) * poissonKernel u₀ y u ≤
            (8 / π) * Real.sqrt r * |u| ^ (-(3 / 2 : ℝ)) := by
          have hlog_nn : 0 ≤ Real.log (|u| / r) :=
            Real.log_nonneg (by rw [le_div_iff₀ hr_pos]; linarith [h2])
          calc Real.log (|u| / r) * poissonKernel u₀ y u
              ≤ (2 * Real.sqrt (|u| / r)) * (4 * r / (π * |u| ^ 2)) :=
                mul_le_mul hsqrt hpk_le hpk_nonneg (by positivity)
            _ = (8 / π) * Real.sqrt r * (Real.sqrt |u| / |u| ^ 2) := by
                rw [Real.sqrt_div hu_pos.le]
                have hsr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
                field_simp [hsr, Real.pi_pos.ne', hu_pos.ne']
                rw [Real.sq_sqrt hr_pos.le]; ring
            _ = (8 / π) * Real.sqrt r * |u| ^ (-(3 / 2 : ℝ)) := by
                congr 1
                rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_natCast |u| 2,
                  ← Real.rpow_neg hu_pos.le, ← Real.rpow_add hu_pos]
                norm_num
        have ht3_eq : t3 u = (8 / π) * Real.sqrt r * |u| ^ (-(3 / 2 : ℝ)) :=
          indicator_of_mem (show u ∈ {x : ℝ | 2 * r ≤ |x|} from h2) _
        have hmul : |Real.log (|u|)| * poissonKernel u₀ y u ≤ t2 u + t3 u := by
          have h0 : |Real.log (|u|)| * poissonKernel u₀ y u ≤
              |Real.log r| * poissonKernel u₀ y u + Real.log (|u| / r) * poissonKernel u₀ y u := by
            have := mul_le_mul_of_nonneg_right hlog_tri hpk_nonneg
            linarith [this]
          have ht2_ge : |Real.log r| * poissonKernel u₀ y u ≤ t2 u := by
            dsimp [t2]; nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2), hpk_nonneg]
          linarith [h0, ht2_ge, hterm3, ht3_eq]
        linarith [hmul, ht1_nonneg]
  have hf_meas : AEStronglyMeasurable (fun u : ℝ => |Real.log (|u|)| * poissonKernel u₀ y u) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((continuous_abs.measurable.comp (measurable_id' (α := ℝ))).log.abs).mul ?_
    unfold poissonKernel; fun_prop
  have hf_int : Integrable (fun u : ℝ => |Real.log (|u|)| * poissonKernel u₀ y u) :=
    ((ht1_int.add ht2_int).add ht3_int).mono' hf_meas (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (poissonKernel_nonneg hy.le u))]
      exact hdom u)
  refine ⟨hf_int, ?_⟩
  have hint_le : ∫ u : ℝ, |Real.log (|u|)| * poissonKernel u₀ y u ≤
      (∫ u : ℝ, t1 u) + (∫ u : ℝ, t2 u) + (∫ u : ℝ, t3 u) := by
    have h1 := integral_mono hf_int ((ht1_int.add ht2_int).add ht3_int) hdom
    have hA := integral_add (ht1_int.add ht2_int) ht3_int
    have hB := integral_add ht1_int ht2_int
    have hAB : ∫ u : ℝ, t1 u + t2 u + t3 u = (∫ u : ℝ, t1 u) + (∫ u : ℝ, t2 u) + (∫ u : ℝ, t3 u) := by
      simpa only [Pi.add_apply] using hA.trans (by simpa only [Pi.add_apply] using congrArg (· + _) hB)
    exact h1.trans_eq hAB
  -- Bound each of `∫ t1`, `∫ t2`, `∫ t3`:
  have ht1_bd : ∫ u : ℝ, t1 u ≤ (4 / π) * |Real.log r| + (4 / π) * Real.log 2 + (2 / π) * K₀ := by
    rw [integral_indicator measurableSet_Icc, integral_const_mul]
    have hscale : ∫ u in Icc (-(r / 2)) (r / 2), |Real.log (|u|)| =
        (r / 2) * ∫ s in Icc (-1 : ℝ) 1, |Real.log (|(r / 2) * s|)| := by
      rw [setIntegral_congr_set (Ioc_ae_eq_Icc (a := -(r / 2)) (b := r / 2)).symm,
        setIntegral_congr_set (Ioc_ae_eq_Icc (a := (-1 : ℝ)) (b := 1)).symm]
      have h1 := intervalIntegral.integral_comp_mul_left (fun u : ℝ => |Real.log (|u|)|)
        (show r / 2 ≠ 0 by positivity) (a := -1) (b := 1)
      simp only [mul_neg, mul_one, smul_eq_mul] at h1
      rw [intervalIntegral.integral_of_le (by linarith : -(r / 2) ≤ r / 2),
        intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at h1
      rw [h1, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    have hsub_le : ∫ s in Icc (-1 : ℝ) 1, |Real.log (|(r / 2) * s|)| ≤
        2 * |Real.log (r / 2)| + K₀ := by
      have hint1 : IntegrableOn (fun _ : ℝ => |Real.log (r / 2)|) (Icc (-1) 1) :=
        integrableOn_const (hs := measure_Icc_lt_top.ne)
      have hle : ∫ s in Icc (-1 : ℝ) 1, |Real.log (|(r / 2) * s|)| ≤
          ∫ s in Icc (-1 : ℝ) 1, (|Real.log (r / 2)| + |Real.log (|s|)|) := by
        refine integral_mono_ae ?_ (hint1.add hint_unit) ?_
        · have hm : Measurable fun s : ℝ => (r / 2) * s := measurable_const.mul measurable_id
          exact ((hint1.add hint_unit).mono'
            (((hm.abs).log.abs).aestronglyMeasurable)
            ((ae_restrict_mem measurableSet_Icc).mono fun s _ => by
              rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
              rcases eq_or_ne s 0 with rfl | hs0
              · simp
              · rw [abs_mul, abs_of_pos (half_pos hr_pos), Real.log_mul (half_pos hr_pos).ne' (abs_ne_zero.mpr hs0)]
                exact abs_add_le _ _))
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with s _
          rcases eq_or_ne s 0 with rfl | hs0
          · simp
          · rw [abs_mul, abs_of_pos (half_pos hr_pos), Real.log_mul (half_pos hr_pos).ne' (abs_ne_zero.mpr hs0)]
            exact abs_add_le _ _
      rw [integral_add hint1 hint_unit] at hle
      have hvol : ∫ _ in Icc (-1 : ℝ) 1, |Real.log (r / 2)| = 2 * |Real.log (r / 2)| := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        norm_num
      rw [hvol] at hle
      exact hle
    have hlog_half : |Real.log (r / 2)| ≤ |Real.log r| + Real.log 2 := by
      rw [Real.log_div hr_pos.ne' two_ne_zero]
      have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      calc |Real.log r - Real.log 2| ≤ |Real.log r| + |Real.log 2| := abs_sub _ _
        _ = |Real.log r| + Real.log 2 := by rw [abs_of_nonneg h2]
    rw [hscale]
    calc 4 / (π * r) * (r / 2 * ∫ s in Icc (-1 : ℝ) 1, |Real.log (|(r / 2) * s|)|)
        = (2 / π) * ∫ s in Icc (-1 : ℝ) 1, |Real.log (|(r / 2) * s|)| := by
          field_simp [Real.pi_pos.ne', hr_pos.ne']; ring
      _ ≤ (2 / π) * (2 * |Real.log (r / 2)| + K₀) := by gcongr
      _ ≤ (2 / π) * (2 * (|Real.log r| + Real.log 2) + K₀) := by gcongr
      _ = (4 / π) * |Real.log r| + (4 / π) * Real.log 2 + (2 / π) * K₀ := by ring
  have ht2_bd : ∫ u : ℝ, t2 u = |Real.log r| + Real.log 2 := by
    dsimp [t2]
    rw [integral_const_mul, integral_poissonKernel u₀ hy, mul_one]
  have ht3_bd : ∫ u : ℝ, t3 u ≤ 16 * Real.sqrt 2 / π := by
    have hset : {u : ℝ | 2 * r ≤ |u|} = Iic (-(2 * r)) ∪ Ici (2 * r) := by
      ext u; simp [le_abs']
    rw [integral_indicator (isClosed_le continuous_const continuous_abs).measurableSet,
      integral_const_mul, hset]
    have hrpow_pos : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ioi (2 * r)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)
    have hIci_int : IntegrableOn (fun u : ℝ => |u| ^ (-(3 / 2 : ℝ))) (Ici (2 * r)) := by
      refine (MeasureTheory.IntegrableOn.congr_set_ae hrpow_pos Ioi_ae_eq_Ici.symm).congr_fun (fun u hu => ?_)
        measurableSet_Ici
      rw [abs_of_pos (by linarith [show 2 * r ≤ u from hu])]
    have hIic_int : IntegrableOn (fun u : ℝ => |u| ^ (-(3 / 2 : ℝ))) (Iic (-(2 * r))) := by
      have hneg := ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
        (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr hIci_int
      have himg : Neg.neg ⁻¹' Ici (2 * r) = Iic (-(2 * r)) := by
        ext u; simp [le_neg]
      change IntegrableOn (fun u : ℝ => |(-u)| ^ (-(3 / 2 : ℝ))) (Neg.neg ⁻¹' Ici (2 * r)) volume at hneg
      rw [himg] at hneg
      exact hneg.congr_fun (fun u _ => by dsimp only; rw [abs_neg]) measurableSet_Iic
    have hdisj : Disjoint (Iic (-(2 * r))) (Ici (2 * r)) :=
      Set.disjoint_left.mpr fun u h1 h2 => by linarith [mem_Iic.mp h1, mem_Ici.mp h2, hr_pos]
    have hunion : ∫ u in Iic (-(2 * r)) ∪ Ici (2 * r), |u| ^ (-(3 / 2 : ℝ)) =
        (∫ u in Iic (-(2 * r)), |u| ^ (-(3 / 2 : ℝ))) + (∫ u in Ici (2 * r), |u| ^ (-(3 / 2 : ℝ))) :=
      setIntegral_union hdisj measurableSet_Ici hIic_int hIci_int
    have hIci_val : ∫ u in Ici (2 * r), |u| ^ (-(3 / 2 : ℝ)) = 2 * (2 * r) ^ (-(1 / 2 : ℝ)) := by
      rw [setIntegral_congr_set Ioi_ae_eq_Ici.symm]
      have hcongr : EqOn (fun u : ℝ => |u| ^ (-(3 / 2 : ℝ))) (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ioi (2 * r)) := by
        intro u hu; dsimp only; rw [abs_of_pos (by linarith [show 2 * r < u from hu, hr_pos])]
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
      rw [integral_Ioi_rpow_of_lt (by norm_num) (by linarith)]
      rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num]
      ring
    have hIic_val : ∫ u in Iic (-(2 * r)), |u| ^ (-(3 / 2 : ℝ)) = 2 * (2 * r) ^ (-(1 / 2 : ℝ)) := by
      have hneg : ∫ u in Iic (-(2 * r)), |u| ^ (-(3 / 2 : ℝ)) =
          ∫ u in Ici (2 * r), |u| ^ (-(3 / 2 : ℝ)) := by
        have h1 := (Measure.measurePreserving_neg volume).setIntegral_preimage_emb
          (MeasurableEquiv.neg ℝ).measurableEmbedding (fun u : ℝ => |u| ^ (-(3 / 2 : ℝ))) (Ici (2 * r))
        have himg : Neg.neg ⁻¹' Ici (2 * r) = Iic (-(2 * r)) := by
          ext u; simp [le_neg]
        change ∫ x in Neg.neg ⁻¹' Ici (2 * r), |(-x)| ^ (-(3 / 2 : ℝ)) =
          ∫ y in Ici (2 * r), |y| ^ (-(3 / 2 : ℝ)) at h1
        rw [himg] at h1
        simpa [abs_neg] using h1
      rw [hneg, hIci_val]
    have hcomb : (8 / π) * Real.sqrt r * (4 * (2 * r) ^ (-(1 / 2 : ℝ))) = 16 * Real.sqrt 2 / π := by
      have hsqrt_inv : (2 * r) ^ (-(1 / 2 : ℝ)) = 1 / (Real.sqrt 2 * Real.sqrt r) := by
        rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul zero_le_two, one_div]
      rw [hsqrt_inv]
      have hsr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
      have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
      field_simp [hsr, hs2, Real.pi_pos.ne']
      nlinarith [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hunion, hIic_val, hIci_val]
    calc (8 / π) * Real.sqrt r * (2 * (2 * r) ^ (-(1 / 2 : ℝ)) + 2 * (2 * r) ^ (-(1 / 2 : ℝ)))
        = (8 / π) * Real.sqrt r * (4 * (2 * r) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 16 * Real.sqrt 2 / π := le_of_eq hcomb
  calc ∫ u : ℝ, |Real.log (|u|)| * poissonKernel u₀ y u
      ≤ (∫ u : ℝ, t1 u) + (∫ u : ℝ, t2 u) + (∫ u : ℝ, t3 u) := hint_le
    _ ≤ ((4 / π) * |Real.log r| + (4 / π) * Real.log 2 + (2 / π) * K₀) +
          (|Real.log r| + Real.log 2) + (16 * Real.sqrt 2 / π) := by linarith
    _ = (4 / π + 1) * |Real.log r| +
          ((2 / π) * K₀ + (4 / π + 1) * Real.log 2 + 16 * Real.sqrt 2 / π) := by ring
    _ ≤ C_log * (1 + |Real.log r|) := by
          dsimp [C_log]
          have h1 : 0 ≤ (4 / π + 1) := by positivity
          have h2 : 0 ≤ (2 / π) * K₀ + (4 / π + 1) * Real.log 2 + 16 * Real.sqrt 2 / π := by
            have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
            positivity
          nlinarith [abs_nonneg (Real.log r)]

lemma schwarzSlit_im_growth :
    ∃ C_S : ℝ, 0 < C_S ∧ ∀ z : ℂ, 0 < z.im →
      |(schwarzSlit z).im| ≤
        C_S * (1 + |Real.log ‖z - 1‖| + |Real.log ‖z‖| + |Real.log ‖z + 1‖|) := by
  obtain ⟨C_log, hC_pos, hlog⟩ := integral_abs_log_mul_poissonKernel
  refine ⟨C_log, hC_pos, fun z hz => ?_⟩
  rw [schwarzSlit_im hz, abs_neg]
  have hL_le : ∀ σ ∈ slitPreimage,
      |slitL (slitBoundaryMap σ)| ≤ (1 / 3 : ℝ) * (|Real.log (|σ - 1|)| + |Real.log (|σ|)| + |Real.log (|σ + 1|)|) := by
    intro σ hσ
    have hslit_nonneg : 0 ≤ slitL (slitBoundaryMap σ) := by unfold slitL; positivity
    rw [abs_of_nonneg hslit_nonneg]
    have h0 : σ ≠ 0 := by rcases hσ with ⟨_, h⟩ | (h : 1 < σ) <;> linarith
    have h1 : σ ≠ 1 := by rcases hσ with ⟨_, h⟩ | (h : 1 < σ) <;> linarith
    have hm1 : σ ≠ -1 := by rcases hσ with ⟨h, _⟩ | (h : 1 < σ) <;> linarith
    have hsbm : slitBoundaryMap σ =
        (2 * π)⁻¹ * (Real.log (|σ - 1|) - Real.log (|σ|) - Real.log (|σ + 1|)) := by
      rcases hσ with ⟨hm1', h0'⟩ | (h1' : 1 < σ)
      · unfold slitBoundaryMap
        have ha : (1 - σ) / ((-σ) * (1 + σ)) = |σ - 1| / (|σ| * |σ + 1|) := by
          rw [abs_of_neg (by linarith), abs_of_neg h0', abs_of_pos (by linarith)]
          ring
        rw [ha, Real.log_div (abs_ne_zero.mpr (sub_ne_zero.mpr h1))
            (mul_ne_zero (abs_ne_zero.mpr h0) (abs_ne_zero.mpr (by linarith))),
          Real.log_mul (abs_ne_zero.mpr h0) (abs_ne_zero.mpr (by linarith))]
        ring
      · rw [slitBoundaryMap_eq_leftBranch]
        have ha : (σ - 1) / (σ * (σ + 1)) = |σ - 1| / (|σ| * |σ + 1|) := by
          rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]
        rw [ha, Real.log_div (abs_ne_zero.mpr (sub_ne_zero.mpr h1))
            (mul_ne_zero (abs_ne_zero.mpr h0) (abs_ne_zero.mpr (by linarith))),
          Real.log_mul (abs_ne_zero.mpr h0) (abs_ne_zero.mpr (by linarith))]
        ring
    unfold slitL
    rw [hsbm]
    have habs : |(2 * π)⁻¹ * (Real.log (|σ - 1|) - Real.log (|σ|) - Real.log (|σ + 1|))| ≤
        (2 * π)⁻¹ * (|Real.log (|σ - 1|)| + |Real.log (|σ|)| + |Real.log (|σ + 1|)|) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      gcongr
      calc |Real.log (|σ - 1|) - Real.log (|σ|) - Real.log (|σ + 1|)|
          ≤ |Real.log (|σ - 1|) - Real.log (|σ|)| + |Real.log (|σ + 1|)| := abs_sub _ _
        _ ≤ (|Real.log (|σ - 1|)| + |Real.log (|σ|)|) + |Real.log (|σ + 1|)| := by
            gcongr; exact abs_sub _ _
    have hpi := Real.pi_pos
    calc 2 * π * |(2 * π)⁻¹ * (Real.log (|σ - 1|) - Real.log (|σ|) - Real.log (|σ + 1|))| / 3
        ≤ 2 * π * ((2 * π)⁻¹ * (|Real.log (|σ - 1|)| + |Real.log (|σ|)| + |Real.log (|σ + 1|)|)) / 3 := by
          gcongr
      _ = (1 / 3 : ℝ) * (|Real.log (|σ - 1|)| + |Real.log (|σ|)| + |Real.log (|σ + 1|)|) := by
          field_simp [hpi.ne']
  have hint_pos : ∀ a : ℝ, Integrable (fun σ : ℝ => |Real.log (|σ - a|)| * poissonKernel z.re z.im σ) ∧
      ∫ σ : ℝ, |Real.log (|σ - a|)| * poissonKernel z.re z.im σ ≤
        C_log * (1 + |Real.log ‖z - (a : ℂ)‖|) := by
    intro a
    obtain ⟨hi, hbd⟩ := hlog (z.re - a) hz
    have heq_f : (fun σ : ℝ => |Real.log (|σ - a|)| * poissonKernel z.re z.im σ) =
        (fun σ : ℝ => |Real.log (|σ - a|)| * poissonKernel (z.re - a) z.im (σ - a)) := by
      ext σ; unfold poissonKernel; ring_nf
    have hcomp_int : Integrable (fun σ : ℝ => |Real.log (|σ - a|)| * poissonKernel (z.re - a) z.im (σ - a)) :=
      hi.comp_sub_right a
    have hcomp_val : ∫ σ : ℝ, |Real.log (|σ - a|)| * poissonKernel (z.re - a) z.im (σ - a) =
        ∫ u : ℝ, |Real.log (|u|)| * poissonKernel (z.re - a) z.im u :=
      integral_sub_right_eq_self (fun u => |Real.log (|u|)| * poissonKernel (z.re - a) z.im u) a
    have hz_eq : ((z.re - a : ℝ) : ℂ) + (z.im : ℂ) * Complex.I = z - (a : ℂ) := by
      apply Complex.ext <;> simp
    rw [hz_eq] at hbd
    rw [heq_f, hcomp_val]
    exact ⟨hcomp_int, hbd⟩
  have h1 := hint_pos 1
  have h0 := hint_pos 0
  have hm1 := hint_pos (-1)
  have hdom : Integrable (fun σ : ℝ => (1 / 3 : ℝ) *
      (|Real.log (|σ - 1|)| * poissonKernel z.re z.im σ +
       |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ +
       |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ)) :=
    ((h1.1.add h0.1).add hm1.1).const_mul (1 / 3 : ℝ)
  have hslit_int := identification_integrand_integrable z.re hz
  have hslit_nonneg : 0 ≤ ∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel z.re z.im σ := by
    refine setIntegral_nonneg (isOpen_Ioo.union isOpen_Ioi).measurableSet fun σ _ => ?_
    have hL : 0 ≤ slitL (slitBoundaryMap σ) := by unfold slitL; positivity
    have hP : 0 ≤ poissonKernel z.re z.im σ := by unfold poissonKernel; positivity
    exact mul_nonneg hL hP
  rw [abs_of_nonneg hslit_nonneg]
  have hmono_slit : ∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel z.re z.im σ ≤
      ∫ σ in slitPreimage, (1 / 3 : ℝ) *
        (|Real.log (|σ - 1|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ) := by
    refine setIntegral_mono_on hslit_int hdom.integrableOn (isOpen_Ioo.union isOpen_Ioi).measurableSet ?_
    intro σ hσ
    have hL := hL_le σ hσ
    have hLn : 0 ≤ slitL (slitBoundaryMap σ) := by unfold slitL; positivity
    rw [abs_of_nonneg hLn] at hL
    have hP : 0 ≤ poissonKernel z.re z.im σ := by unfold poissonKernel; positivity
    calc slitL (slitBoundaryMap σ) * poissonKernel z.re z.im σ
        ≤ ((1 / 3 : ℝ) * (|Real.log (|σ - 1|)| + |Real.log (|σ|)| + |Real.log (|σ + 1|)|)) *
            poissonKernel z.re z.im σ := by gcongr
      _ = (1 / 3 : ℝ) * (|Real.log (|σ - 1|)| * poissonKernel z.re z.im σ +
            |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ +
            |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ) := by
          simp only [sub_zero, sub_neg_eq_add]; ring
  have hmono_univ : ∫ σ in slitPreimage, (1 / 3 : ℝ) *
        (|Real.log (|σ - 1|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ) ≤
      ∫ σ : ℝ, (1 / 3 : ℝ) *
        (|Real.log (|σ - 1|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ) := by
    refine setIntegral_le_integral hdom (ae_of_all _ fun σ => ?_)
    have hP : 0 ≤ poissonKernel z.re z.im σ := by unfold poissonKernel; positivity
    positivity
  have heval : ∫ σ : ℝ, (1 / 3 : ℝ) *
        (|Real.log (|σ - 1|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ +
         |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ) ≤
      C_log * (1 + |Real.log ‖z - 1‖| + |Real.log ‖z‖| + |Real.log ‖z + 1‖|) := by
    have h123 : ∫ σ : ℝ, |Real.log (|σ - 1|)| * poissonKernel z.re z.im σ +
        |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ +
        |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ =
        ((∫ σ : ℝ, |Real.log (|σ - 1|)| * poissonKernel z.re z.im σ) +
          (∫ σ : ℝ, |Real.log (|σ - 0|)| * poissonKernel z.re z.im σ)) +
          (∫ σ : ℝ, |Real.log (|σ - (-1)|)| * poissonKernel z.re z.im σ) := by
      have hA := integral_add (h1.1.add h0.1) hm1.1
      have hB := integral_add h1.1 h0.1
      simpa only [Pi.add_apply] using hA.trans (by simpa only [Pi.add_apply] using congrArg (· + _) hB)
    rw [integral_const_mul, h123]
    have h1' := h1.2; have h0' := h0.2; have hm1' := hm1.2
    simp only [Complex.ofReal_one, Complex.ofReal_zero, sub_zero, Complex.ofReal_neg,
      sub_neg_eq_add] at h1' h0' hm1'
    simp only [sub_zero, sub_neg_eq_add]
    have hsum : (∫ σ : ℝ, |Real.log (|σ - 1|)| * poissonKernel z.re z.im σ) +
        (∫ σ : ℝ, |Real.log (|σ|)| * poissonKernel z.re z.im σ) +
        (∫ σ : ℝ, |Real.log (|σ + 1|)| * poissonKernel z.re z.im σ) ≤
        C_log * (1 + |Real.log ‖z - 1‖|) + C_log * (1 + |Real.log ‖z‖|) +
          C_log * (1 + |Real.log ‖z + 1‖|) := by
      linarith [h1', h0', hm1']
    have hnonneg : 0 ≤ C_log * (|Real.log ‖z - 1‖| + |Real.log ‖z‖| + |Real.log ‖z + 1‖|) := by
      positivity
    linarith
  exact (hmono_slit.trans hmono_univ).trans heval

/-! ### 5. Phragmén–Lindelöf uniqueness and `HarmonicMajorantIdentification` -/

noncomputable def barrierW (z : ℂ) : ℂ := Complex.cosh (((π / 2 : ℝ) : ℂ) * confB z)

lemma differentiableOn_barrierW : DifferentiableOn ℂ barrierW {z : ℂ | 0 < z.im} := by
  intro z hz
  have hd_confB : HasDerivAt confB (confBDeriv z) z := hasDerivAt_confB hz
  have hd_mul := hd_confB.const_mul ((π / 2 : ℝ) : ℂ)
  have hd_cosh := (Complex.hasDerivAt_cosh _).comp z hd_mul
  exact hd_cosh.differentiableAt.differentiableWithinAt

lemma re_barrierW_ge {z : ℂ} (hz : 0 < z.im) :
    (Real.sqrt 2 / 4) * Real.exp ((1 / 4 : ℝ) * |Real.log ‖confE z‖|) ≤ (barrierW z).re := by
  set b := confB z
  have hb_im := confB_im_bounds hz
  have hpi := Real.pi_pos
  have hpb : ((π / 2 : ℝ) : ℂ) * b =
      ((π / 2 * b.re : ℝ) : ℂ) + ((π / 2 * b.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hre : (barrierW z).re = Real.cosh (π / 2 * b.re) * Real.cos (π / 2 * b.im) := by
    unfold barrierW
    rw [hpb, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hcos_ge : Real.sqrt 2 / 2 ≤ Real.cos (π / 2 * b.im) := by
    rw [← Real.cos_pi_div_four, ← Real.cos_abs (π / 2 * b.im)]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    have hpi2 : (0 : ℝ) < π / 2 := by positivity
    have hb_abs : |b.im| < 1 / 2 := abs_lt.mpr hb_im
    rw [abs_mul, abs_of_pos hpi2]
    nlinarith [hb_abs, Real.pi_pos]
  have hcosh_ge : (1 / 2 : ℝ) * Real.exp ((π / 2) * |b.re|) ≤ Real.cosh (π / 2 * b.re) := by
    rw [Real.cosh_eq]
    rcases le_or_gt 0 b.re with hnn | hneg
    · rw [abs_of_nonneg hnn]
      linarith [Real.exp_pos (-(π / 2 * b.re))]
    · rw [abs_of_neg hneg]
      have : Real.exp (π / 2 * -b.re) = Real.exp (-(π / 2 * b.re)) := by ring_nf
      linarith [Real.exp_pos (π / 2 * b.re)]
  have hexp_eq : Real.exp (2 * π * b.re) = ‖confE z‖ := by
    have he := exp_two_pi_mul_confB hz
    rw [← he, Complex.norm_exp]
    congr 1
    have h2pi : ((2 * π : ℝ) : ℂ) = 2 * (π : ℂ) := by push_cast; rfl
    have hmul_re : (2 * (π : ℂ) * b).re = 2 * π * b.re := by
      rw [← h2pi, Complex.re_ofReal_mul]
    exact (hmul_re.symm : 2 * π * b.re = (2 * (π : ℂ) * b).re)
  have hbre_eq : |b.re| = (2 * π)⁻¹ * |Real.log ‖confE z‖| := by
    have hlog : 2 * π * b.re = Real.log ‖confE z‖ := by
      rw [← hexp_eq, Real.log_exp]
    have hpi2 : (0 : ℝ) < (2 * π)⁻¹ := by positivity
    have hbre : b.re = (2 * π)⁻¹ * (2 * π * b.re) := by field_simp [hpi.ne']
    rw [hbre, hlog, abs_mul, abs_of_pos hpi2]
  have hscale : (π / 2) * ((2 * π)⁻¹ * |Real.log ‖confE z‖|) = (1 / 4 : ℝ) * |Real.log ‖confE z‖| := by
    field_simp [hpi.ne']; ring
  rw [hbre_eq, hscale] at hcosh_ge
  have hcosh_pos : 0 < Real.cosh (π / 2 * b.re) := Real.cosh_pos _
  have hcos_pos : 0 < Real.sqrt 2 / 2 := by positivity
  rw [hre]
  calc (Real.sqrt 2 / 4) * Real.exp ((1 / 4 : ℝ) * |Real.log ‖confE z‖|)
      = ((1 / 2 : ℝ) * Real.exp ((1 / 4 : ℝ) * |Real.log ‖confE z‖|)) * (Real.sqrt 2 / 2) := by ring
    _ ≤ Real.cosh (π / 2 * b.re) * Real.cos (π / 2 * b.im) := by gcongr

lemma re_barrierW_nonneg {z : ℂ} (hz : 0 < z.im) : 0 ≤ (barrierW z).re :=
  le_trans (by positivity) (re_barrierW_ge hz)

private lemma log_sq_le_rpow {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ^ 2 ≤ 256 * t ^ (1 / 8 : ℝ) := by
  have ht_pos : 0 < t := by linarith
  have h1 : Real.log t = 16 * Real.log (t ^ (1 / 16 : ℝ)) := by
    rw [Real.log_rpow ht_pos]; ring
  have hpow_pos : 0 < t ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos ht_pos _
  have hpow_ge : 1 ≤ t ^ (1 / 16 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have h2 : Real.log (t ^ (1 / 16 : ℝ)) ≤ t ^ (1 / 16 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hpow_pos]
  have hnn : 0 ≤ Real.log t := Real.log_nonneg ht
  have hle : Real.log t ≤ 16 * t ^ (1 / 16 : ℝ) := by linarith
  calc Real.log t ^ 2 ≤ (16 * t ^ (1 / 16 : ℝ)) ^ 2 := by
        exact pow_le_pow_left₀ hnn hle 2
    _ = 256 * (t ^ (1 / 16 : ℝ)) ^ 2 := by ring
    _ = 256 * t ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht_pos.le]; norm_num

private lemma im_diff_le_poly_log :
    ∃ C_Δ : ℝ, 0 < C_Δ ∧ ∀ z : ℂ, 0 < z.im →
      |majorant2D (confB z) - (schwarzSlit z).im| ≤
        C_Δ * (1 + |Real.log ‖z - 1‖| + |Real.log ‖z‖| + |Real.log ‖z + 1‖|) ^ 2 := by
  obtain ⟨C_S, hC_S, hS⟩ := schwarzSlit_im_growth
  have hpi := Real.pi_pos
  let C_Δ : ℝ := |majorantU0| + (4 * π / 3) * (1 + (2 * π)⁻¹ + 2) ^ 2 + C_S
  refine ⟨C_Δ, by positivity, fun z hz => ?_⟩
  have hM := majorant2D_abs_le (confB_mem_slitStrip hz)
  have hS_z := hS z hz
  have hconfE_ne : confE z ≠ 0 := by
    rw [← exp_two_pi_mul_confB hz]; exact Complex.exp_ne_zero _
  have hre_eq : (confB z).re = (2 * π)⁻¹ * Real.log ‖confE z‖ := by
    have he : Real.exp (2 * π * (confB z).re) = ‖confE z‖ := by
      rw [← exp_two_pi_mul_confB hz, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    have hlog : 2 * π * (confB z).re = Real.log ‖confE z‖ := by rw [← he, Real.log_exp]
    field_simp [hpi.ne'] at hlog ⊢
    linarith [hlog]
  have hconfE_norm : ‖confE z‖ = ‖z - 1‖ / (‖z‖ * ‖z + 1‖) := by
    unfold confE; rw [norm_div, norm_mul]
  have hz_ne : z ≠ 0 := by intro h; rw [h, Complex.zero_im] at hz; exact hz.false
  have hz1_ne : z - 1 ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; linarith
  have hzp1_ne : z + 1 ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; linarith
  have hlogE : |Real.log ‖confE z‖| ≤ |Real.log ‖z - 1‖| + |Real.log ‖z‖| + |Real.log ‖z + 1‖| := by
    rw [hconfE_norm, Real.log_div (norm_ne_zero_iff.mpr hz1_ne)
        (mul_ne_zero (norm_ne_zero_iff.mpr hz_ne) (norm_ne_zero_iff.mpr hzp1_ne)),
      Real.log_mul (norm_ne_zero_iff.mpr hz_ne) (norm_ne_zero_iff.mpr hzp1_ne)]
    calc |Real.log ‖z - 1‖ - (Real.log ‖z‖ + Real.log ‖z + 1‖)|
        ≤ |Real.log ‖z - 1‖| + |Real.log ‖z‖ + Real.log ‖z + 1‖| := abs_sub _ _
      _ ≤ |Real.log ‖z - 1‖| + (|Real.log ‖z‖| + |Real.log ‖z + 1‖|) := by gcongr; exact abs_add_le _ _
      _ = _ := by ring
  set Q := 1 + |Real.log ‖z - 1‖| + |Real.log ‖z‖| + |Real.log ‖z + 1‖|
  have hQ_ge : 1 ≤ Q := by
    dsimp [Q]; linarith [abs_nonneg (Real.log ‖z - 1‖), abs_nonneg (Real.log ‖z‖),
      abs_nonneg (Real.log ‖z + 1‖)]
  have hre_bd : |(confB z).re| + 2 ≤ ((2 * π)⁻¹ + 2) * Q := by
    rw [hre_eq, abs_mul, abs_of_pos (by positivity)]
    have h1 : |Real.log ‖confE z‖| ≤ Q := by dsimp [Q]; linarith
    have h2 : (2 : ℝ) ≤ 2 * Q := by linarith
    calc (2 * π)⁻¹ * |Real.log ‖confE z‖| + 2 ≤ (2 * π)⁻¹ * Q + 2 * Q := by gcongr
      _ = ((2 * π)⁻¹ + 2) * Q := by ring
  have hM_bd : |majorant2D (confB z)| ≤
      (|majorantU0| + (4 * π / 3) * (1 + (2 * π)⁻¹ + 2) ^ 2) * Q ^ 2 := by
    have hQ2 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ_ge
    have hsq : (|(confB z).re| + 2) ^ 2 ≤ (1 + (2 * π)⁻¹ + 2) ^ 2 * Q ^ 2 := by
      have : |(confB z).re| + 2 ≤ (1 + (2 * π)⁻¹ + 2) * Q := by linarith [hQ_ge]
      calc (|(confB z).re| + 2) ^ 2 ≤ ((1 + (2 * π)⁻¹ + 2) * Q) ^ 2 := by
            exact pow_le_pow_left₀ (by positivity) this 2
        _ = (1 + (2 * π)⁻¹ + 2) ^ 2 * Q ^ 2 := by ring
    calc |majorant2D (confB z)| ≤ |majorantU0| + (4 * π / 3) * (|(confB z).re| + 2) ^ 2 := hM
      _ ≤ |majorantU0| * Q ^ 2 + (4 * π / 3) * ((1 + (2 * π)⁻¹ + 2) ^ 2 * Q ^ 2) := by
          gcongr; nlinarith [abs_nonneg majorantU0]
      _ = (|majorantU0| + (4 * π / 3) * (1 + (2 * π)⁻¹ + 2) ^ 2) * Q ^ 2 := by ring
  have hS_bd : |(schwarzSlit z).im| ≤ C_S * Q ^ 2 := by
    have : Q ≤ Q ^ 2 := by nlinarith
    calc |(schwarzSlit z).im| ≤ C_S * Q := hS_z
      _ ≤ C_S * Q ^ 2 := by gcongr
  calc |majorant2D (confB z) - (schwarzSlit z).im|
      ≤ |majorant2D (confB z)| + |(schwarzSlit z).im| := abs_sub _ _
    _ ≤ C_Δ * Q ^ 2 := by dsimp [C_Δ]; linarith

private lemma near_one_qLog_confE {w : ℂ} (hw : 0 < w.im) (h_one : ‖w - 1‖ ≤ 1 / 4) :
    (1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| ≤
      1 + 2 * Real.log 4 + Real.log (‖w - 1‖⁻¹)) ∧
    (‖w - 1‖⁻¹ / 3 ≤ max ‖confE w‖ ‖confE w‖⁻¹) := by
  have ht_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (fun h => by
    have := congrArg Complex.im h; simp at this; linarith)
  have hw_lo : 3 / 4 ≤ ‖w‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (1 - w)
    rw [sub_sub_cancel, norm_one, norm_sub_rev (1 : ℂ) w] at htri
    linarith [htri, h_one]
  have hw_hi : ‖w‖ ≤ 5 / 4 := by
    have htri := norm_add_le (w - 1) 1
    simp only [sub_add_cancel, norm_one] at htri
    linarith [htri, h_one]
  have hwp1_lo : 7 / 4 ≤ ‖w + 1‖ := by
    have h1 : (2 : ℂ) + (w - 1) = w + 1 := by ring
    have htri := norm_sub_norm_le (2 : ℂ) (-(w - 1))
    simp only [sub_neg_eq_add, norm_neg] at htri
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h1, h2] at htri
    linarith [htri, h_one]
  have hwp1_hi : ‖w + 1‖ ≤ 9 / 4 := by
    have h1 : (w - 1) + (2 : ℂ) = w + 1 := by ring
    have htri := norm_add_le (w - 1) 2
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h1, h2] at htri
    linarith [htri, h_one]
  have hl0 : |Real.log ‖w‖| ≤ Real.log 4 := by
    have hw_pos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw_lo
    rw [abs_le]; constructor
    · rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by linarith [hw_lo])
    · exact Real.log_le_log hw_pos (by linarith [hw_hi])
  have hlp1 : |Real.log ‖w + 1‖| ≤ Real.log 4 := by
    have hp_pos : 0 < ‖w + 1‖ := lt_of_lt_of_le (by norm_num) hwp1_lo
    rw [abs_le]; constructor
    · rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by linarith [hwp1_lo])
    · exact Real.log_le_log hp_pos (by linarith [hwp1_hi])
  have hlm1 : |Real.log ‖w - 1‖| = Real.log (‖w - 1‖⁻¹) := by
    rw [Real.log_inv, abs_of_neg (Real.log_neg ht_pos (by linarith [h_one]))]
  have hE_inv : ‖w - 1‖⁻¹ / 3 ≤ ‖confE w‖⁻¹ := by
    unfold confE; rw [norm_div, norm_mul, inv_div]
    have hprod : ‖w‖ * ‖w + 1‖ ≥ 1 / 3 := by nlinarith [hw_lo, hwp1_lo]
    rw [div_le_div_iff₀ (by positivity) ht_pos]
    calc ‖w - 1‖⁻¹ * ‖w - 1‖ = 1 := inv_mul_cancel₀ ht_pos.ne'
      _ ≤ ‖w‖ * ‖w + 1‖ * 3 := by linarith [hprod]
  exact ⟨by linarith [hl0, hlp1, hlm1], hE_inv.trans (le_max_right _ _)⟩

private lemma near_zero_qLog_confE {w : ℂ} (hw : 0 < w.im) (h_zero : ‖w‖ ≤ 1 / 4) :
    (1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| ≤
      1 + 2 * Real.log 4 + Real.log (‖w‖⁻¹)) ∧
    (‖w‖⁻¹ / 3 ≤ max ‖confE w‖ ‖confE w‖⁻¹) := by
  have ht_pos : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by
    have := congrArg Complex.im h; simp at this; linarith)
  have hm1_lo : 3 / 4 ≤ ‖w - 1‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one, norm_sub_rev] at htri
    linarith [htri, h_zero]
  have hm1_hi : ‖w - 1‖ ≤ 5 / 4 := by
    have htri := norm_sub_le w (1 : ℂ)
    rw [norm_one] at htri
    linarith [htri, h_zero]
  have hp1_lo : 3 / 4 ≤ ‖w + 1‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (-w)
    rw [norm_one, norm_neg, sub_neg_eq_add, add_comm] at htri
    linarith [htri, h_zero]
  have hp1_hi : ‖w + 1‖ ≤ 5 / 4 := by
    have htri := norm_add_le w (1 : ℂ)
    rw [norm_one] at htri
    linarith [htri, h_zero]
  have hlm1 : |Real.log ‖w - 1‖| ≤ Real.log 4 := by
    have hm1_pos : 0 < ‖w - 1‖ := lt_of_lt_of_le (by norm_num) hm1_lo
    rw [abs_le]; constructor
    · rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by linarith [hm1_lo])
    · exact Real.log_le_log hm1_pos (by linarith [hm1_hi])
  have hlp1 : |Real.log ‖w + 1‖| ≤ Real.log 4 := by
    have hp1_pos : 0 < ‖w + 1‖ := lt_of_lt_of_le (by norm_num) hp1_lo
    rw [abs_le]; constructor
    · rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by linarith [hp1_lo])
    · exact Real.log_le_log hp1_pos (by linarith [hp1_hi])
  have hl0 : |Real.log ‖w‖| = Real.log (‖w‖⁻¹) := by
    rw [Real.log_inv, abs_of_neg (Real.log_neg ht_pos (by linarith [h_zero]))]
  have hE_ge : ‖w‖⁻¹ / 3 ≤ ‖confE w‖ := by
    unfold confE; rw [norm_div, norm_mul]
    have hden_pos : 0 < ‖w‖ * ‖w + 1‖ := mul_pos ht_pos (lt_of_lt_of_le (by norm_num) hp1_lo)
    rw [div_le_div_iff₀ (by positivity) hden_pos]
    calc ‖w‖⁻¹ * (‖w‖ * ‖w + 1‖) = ‖w‖⁻¹ * ‖w‖ * ‖w + 1‖ := by ring
      _ = ‖w + 1‖ := by rw [inv_mul_cancel₀ ht_pos.ne', one_mul]
      _ ≤ 5 / 4 := hp1_hi
      _ ≤ ‖w - 1‖ * 3 := by linarith [hm1_lo]
  exact ⟨by linarith [hlm1, hlp1, hl0], hE_ge.trans (le_max_left _ _)⟩

private lemma near_neg_one_qLog_confE {w : ℂ} (hw : 0 < w.im) (h_negone : ‖w + 1‖ ≤ 1 / 4) :
    (1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| ≤
      1 + 2 * Real.log 4 + Real.log (‖w + 1‖⁻¹)) ∧
    (‖w + 1‖⁻¹ / 3 ≤ max ‖confE w‖ ‖confE w‖⁻¹) := by
  have ht_pos : 0 < ‖w + 1‖ := norm_pos_iff.mpr (fun h => by
    have := congrArg Complex.im h; simp at this; linarith)
  have hw_lo : 3 / 4 ≤ ‖w‖ := by
    have htri := norm_sub_norm_le (-1 : ℂ) w
    simp only [norm_neg, norm_one] at htri
    rw [show (-1 : ℂ) - w = -(w + 1) by ring, norm_neg] at htri
    linarith [htri, h_negone]
  have hw_hi : ‖w‖ ≤ 5 / 4 := by
    have htri := norm_sub_le (w + 1) 1
    rw [add_sub_cancel_right, norm_one] at htri
    linarith [htri, h_negone]
  have hm1_lo : 7 / 4 ≤ ‖w - 1‖ := by
    have htri2 := norm_sub_norm_le (2 : ℂ) (w + 1)
    rw [show (2 : ℂ) - (w + 1) = -(w - 1) by ring, norm_neg, show ‖(2 : ℂ)‖ = 2 by norm_num] at htri2
    linarith [htri2, h_negone]
  have hm1_hi : ‖w - 1‖ ≤ 9 / 4 := by
    have h1 : (w + 1) - (2 : ℂ) = w - 1 := by ring
    have htri := norm_sub_le (w + 1) 2
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h1, h2] at htri
    linarith [htri, h_negone]
  have hl0 : |Real.log ‖w‖| ≤ Real.log 4 := by
    have hw_pos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw_lo
    rw [abs_le]; constructor
    · rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by linarith [hw_lo])
    · exact Real.log_le_log hw_pos (by linarith [hw_hi])
  have hlm1 : |Real.log ‖w - 1‖| ≤ Real.log 4 := by
    have hm1_pos : 0 < ‖w - 1‖ := lt_of_lt_of_le (by norm_num) hm1_lo
    rw [abs_le]; constructor
    · rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by linarith [hm1_lo])
    · exact Real.log_le_log hm1_pos (by linarith [hm1_hi])
  have hlp1 : |Real.log ‖w + 1‖| = Real.log (‖w + 1‖⁻¹) := by
    rw [Real.log_inv, abs_of_neg (Real.log_neg ht_pos (by linarith [h_negone]))]
  have hE_ge : ‖w + 1‖⁻¹ / 3 ≤ ‖confE w‖ := by
    unfold confE; rw [norm_div, norm_mul]
    have hden_pos : 0 < ‖w‖ * ‖w + 1‖ := mul_pos (lt_of_lt_of_le (by norm_num) hw_lo) ht_pos
    rw [div_le_div_iff₀ (by positivity) hden_pos]
    calc ‖w + 1‖⁻¹ * (‖w‖ * ‖w + 1‖) = ‖w‖ * (‖w + 1‖⁻¹ * ‖w + 1‖) := by ring
      _ = ‖w‖ := by rw [inv_mul_cancel₀ ht_pos.ne', mul_one]
      _ ≤ 5 / 4 := hw_hi
      _ ≤ ‖w - 1‖ * 3 := by linarith [hm1_lo]
  exact ⟨by linarith [hl0, hlm1, hlp1], hE_ge.trans (le_max_left _ _)⟩

private lemma growth_domination_by_barrier {ε : ℝ} (hε : 0 < ε) :
    (∃ R : ℝ, 3 ≤ R ∧ ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      ∀ w : ℂ, 0 < w.im →
        (R ≤ ‖w‖ ∨ ‖w - 1‖ ≤ r ∨ ‖w‖ ≤ r ∨ ‖w + 1‖ ≤ r) →
          |majorant2D (confB w) - (schwarzSlit w).im| ≤ ε * (barrierW w).re) ∧
    (∃ M_ε : ℝ, 0 ≤ M_ε ∧ ∀ w : ℂ, 0 < w.im →
      |majorant2D (confB w) - (schwarzSlit w).im| - ε * (barrierW w).re ≤ M_ε) := by
  obtain ⟨C_Δ, hC_pos, hΔ⟩ := im_diff_le_poly_log
  have hcs_pos : 0 < ε * (Real.sqrt 2 / 4) := by positivity
  -- Use `|Real.log t| ≤ 16 * max(t, t⁻¹)^(1/16)`? Wait: `log_sq_le_rpow` gives `(log u)^2 ≤ 256 * u^(1/8)` for `u ≥ 1`,
  -- and `u^(1/8) = u^(-1/8) * u^(1/4)` -> `C * u^(1/8) ≤ c * u^(1/4)` once `u^(1/8) ≥ C / c`!
  let c0 : ℝ := ε * (Real.sqrt 2 / 4)
  -- Pick threshold `T ≥ 16` so for `u ≥ T`: `16 * C_Δ * (1 + 3 * Real.log (2 * u))^2 ≤ c0 * (u / 4)^(1/4)`.
  have hex_R : ∃ R : ℝ, 3 ≤ R ∧ ∀ w : ℂ, 0 < w.im → R ≤ ‖w‖ →
      |majorant2D (confB w) - (schwarzSlit w).im| ≤ ε * (barrierW w).re := by
    have htend : Tendsto (fun u : ℝ =>
        C_Δ * (1 + 3 * Real.log (2 * u)) ^ 2 - c0 * (u / 2) ^ (1 / 4 : ℝ)) atTop atBot := by
      -- Since `(1 + 3 log(2u))^2 ≤ (1 + 3 log 2 + 3 log u)^2 ≤ C' * (log u)^2 ≤ C'' * u^(1/8)` while `(u/2)^(1/4) = 2^(-1/4) u^(1/4)`
      -- proves directly by algebra on `u^(1/8)`!
      refine tendsto_atTop_atBot.mpr fun B => ?_
      let K : ℝ := C_Δ * (2 * (1 + 3 * Real.log 2) ^ 2 + 18 * 256)
      have hK_nn : 0 ≤ K := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        positivity
      let C1 : ℝ := c0 * (2 : ℝ) ^ (-(1 / 4 : ℝ))
      have hC1 : 0 < C1 := by positivity
      let M0 : ℝ := max 4 (((max 0 (-B) + K) / C1 + 1) ^ 8)
      refine ⟨M0, fun u hu => ?_⟩
      have hu4 : 4 ≤ u := (le_max_left _ _).trans hu
      have hu_pos : 0 < u := by linarith
      have hu1 : 1 ≤ u := by linarith
      have hlog_u : 0 ≤ Real.log u := Real.log_nonneg hu1
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hsq_exp : (1 + 3 * Real.log (2 * u)) ^ 2 ≤
          2 * (1 + 3 * Real.log 2) ^ 2 + 18 * Real.log u ^ 2 := by
        rw [Real.log_mul two_ne_zero hu_pos.ne']
        nlinarith [sq_nonneg ((1 + 3 * Real.log 2) - 3 * Real.log u)]
      have hl1 : C_Δ * (1 + 3 * Real.log (2 * u)) ^ 2 ≤ K * u ^ (1 / 8 : ℝ) := by
        have h1 : Real.log u ^ 2 ≤ 256 * u ^ (1 / 8 : ℝ) := log_sq_le_rpow hu1
        have hu8 : 1 ≤ u ^ (1 / 8 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
        have hsq_nn : 0 ≤ 2 * (1 + 3 * Real.log 2) ^ 2 := by positivity
        have hterm : 2 * (1 + 3 * Real.log 2) ^ 2 ≤ 2 * (1 + 3 * Real.log 2) ^ 2 * u ^ (1 / 8 : ℝ) := by
          nlinarith [hu8, hsq_nn]
        calc C_Δ * (1 + 3 * Real.log (2 * u)) ^ 2
            ≤ C_Δ * (2 * (1 + 3 * Real.log 2) ^ 2 + 18 * Real.log u ^ 2) := by
              exact mul_le_mul_of_nonneg_left hsq_exp hC_pos.le
          _ ≤ C_Δ * (2 * (1 + 3 * Real.log 2) ^ 2 + 18 * (256 * u ^ (1 / 8 : ℝ))) := by gcongr
          _ ≤ C_Δ * (2 * (1 + 3 * Real.log 2) ^ 2 * u ^ (1 / 8 : ℝ) +
                18 * 256 * u ^ (1 / 8 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left (add_le_add hterm (le_of_eq (by ring))) hC_pos.le
          _ = K * u ^ (1 / 8 : ℝ) := by dsimp [K]; ring
      have hpow_mul : u ^ (1 / 4 : ℝ) = u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_add hu_pos]; norm_num
      have hdiv_pow : (u / 2) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (-(1 / 4 : ℝ)) * u ^ (1 / 4 : ℝ) := by
        rw [div_eq_mul_inv, Real.mul_rpow hu_pos.le (by norm_num), Real.inv_rpow (by norm_num),
          ← Real.rpow_neg (by norm_num)]
        ring
      have hu8_ge : (max 0 (-B) + K) / C1 + 1 ≤ u ^ (1 / 8 : ℝ) := by
        have h_base : ((max 0 (-B) + K) / C1 + 1) ^ 8 ≤ u := (le_max_right _ _).trans hu
        have h_nn : 0 ≤ (max 0 (-B) + K) / C1 + 1 := by positivity
        have hpow := Real.rpow_le_rpow (by positivity) h_base (by norm_num : (0 : ℝ) ≤ 1 / 8)
        rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul h_nn,
          show ((8 : ℕ) : ℝ) * (1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one] at hpow
        exact hpow
      have hu8_pos : 1 ≤ u ^ (1 / 8 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
      have hrhs_eq : c0 * (u / 2) ^ (1 / 4 : ℝ) = C1 * (u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ)) := by
        rw [hdiv_pow, hpow_mul]; dsimp [C1]; ring
      calc C_Δ * (1 + 3 * Real.log (2 * u)) ^ 2 - c0 * (u / 2) ^ (1 / 4 : ℝ)
          ≤ K * u ^ (1 / 8 : ℝ) - C1 * (u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ)) := by
            linarith [hl1, hrhs_eq]
        _ = u ^ (1 / 8 : ℝ) * (K - C1 * u ^ (1 / 8 : ℝ)) := by ring
        _ ≤ u ^ (1 / 8 : ℝ) * (K - C1 * ((max 0 (-B) + K) / C1 + 1)) := by gcongr
        _ = u ^ (1 / 8 : ℝ) * (-max 0 (-B) - C1) := by
            have hC1_eq : C1 * ((max 0 (-B) + K) / C1 + 1) = max 0 (-B) + K + C1 := by
              field_simp [hC1.ne']
            rw [hC1_eq]; ring
        _ ≤ 1 * (-max 0 (-B)) := by
            have h1 : -max 0 (-B) - C1 ≤ -max 0 (-B) := by linarith [hC1]
            have h2 : -max 0 (-B) ≤ 0 := by linarith [le_max_left (0 : ℝ) (-B)]
            nlinarith [hu8_pos, h1, h2]
        _ ≤ B := by linarith [le_max_right (0 : ℝ) (-B)]
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (htend.eventually_le_atBot 0)
    refine ⟨max 4 R₀, by linarith [le_max_left (4 : ℝ) R₀], fun w hw hRw => ?_⟩
    have hw4 : 4 ≤ ‖w‖ := (le_max_left _ _).trans hRw
    have hR0w : R₀ ≤ ‖w‖ := (le_max_right _ _).trans hRw
    have hQ : 1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| ≤ 1 + 3 * Real.log (2 * ‖w‖) := by
      have hm1 : 1 ≤ ‖w - 1‖ := by
        have htri := norm_sub_norm_le w (1 : ℂ)
        rw [norm_one] at htri
        linarith [htri, hw4]
      have hm2 : ‖w - 1‖ ≤ 2 * ‖w‖ := by
        calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = ‖w‖ + 1 := by simp
          _ ≤ 2 * ‖w‖ := by linarith [hw4]
      have hp1 : 1 ≤ ‖w + 1‖ := by
        have htri := norm_sub_norm_le w (-1 : ℂ)
        rw [sub_neg_eq_add, norm_neg, norm_one] at htri
        linarith [htri, hw4]
      have hp2 : ‖w + 1‖ ≤ 2 * ‖w‖ := by
        calc ‖w + 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = ‖w‖ + 1 := by simp
          _ ≤ 2 * ‖w‖ := by linarith [hw4]
      have hw1 : 1 ≤ ‖w‖ := by linarith [hw4]
      have hw2 : ‖w‖ ≤ 2 * ‖w‖ := by linarith [hw4]
      have l1 : |Real.log ‖w - 1‖| ≤ Real.log (2 * ‖w‖) := by
        rw [abs_of_nonneg (Real.log_nonneg hm1)]
        exact Real.log_le_log (by linarith [hm1]) hm2
      have l2 : |Real.log ‖w‖| ≤ Real.log (2 * ‖w‖) := by
        rw [abs_of_nonneg (Real.log_nonneg hw1)]
        exact Real.log_le_log (by linarith [hw1]) hw2
      have l3 : |Real.log ‖w + 1‖| ≤ Real.log (2 * ‖w‖) := by
        rw [abs_of_nonneg (Real.log_nonneg hp1)]
        exact Real.log_le_log (by linarith [hp1]) hp2
      linarith [l1, l2, l3]
    have hpoly : C_Δ * (1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖|) ^ 2 ≤
        C_Δ * (1 + 3 * Real.log (2 * ‖w‖)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hQ 2) hC_pos.le
    have hE : ‖confE w‖ ≤ 2 / ‖w‖ := by
      unfold confE
      rw [norm_div, norm_mul]
      have hnum : ‖w - 1‖ ≤ 3 / 2 * ‖w‖ := by
        calc ‖w - 1‖ ≤ ‖w‖ + 1 := by simpa using norm_sub_le w 1
          _ ≤ 3 / 2 * ‖w‖ := by linarith [hw4]
      have hden : 3 / 4 * ‖w‖ * ‖w‖ ≤ ‖w‖ * ‖w + 1‖ := by
        have hp : 3 / 4 * ‖w‖ ≤ ‖w + 1‖ := by
          have htri := norm_sub_norm_le w (-1 : ℂ)
          rw [sub_neg_eq_add, norm_neg, norm_one] at htri
          linarith [htri, hw4]
        nlinarith [norm_nonneg w]
      have hw_pos : 0 < ‖w‖ := by linarith [hw4]
      have hden_pos : 0 < ‖w‖ * ‖w + 1‖ := by nlinarith [hden, hw_pos]
      rw [div_le_div_iff₀ hden_pos hw_pos]
      nlinarith [hnum, hden, hw_pos]
    have hE_pos : 0 < ‖confE w‖ := by
      rw [← exp_two_pi_mul_confB hw]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
    have hW_ge : c0 * (‖w‖ / 2) ^ (1 / 4 : ℝ) ≤ ε * (barrierW w).re := by
      have hlogE : Real.log (‖w‖ / 2) ≤ |Real.log ‖confE w‖| := by
        have hw_ne : ‖w‖ ≠ 0 := by linarith [hw4]
        have hinv : ‖w‖ / 2 ≤ ‖confE w‖⁻¹ := by
          rw [← one_div, le_div_iff₀ hE_pos]
          have h1 : ‖w‖ / 2 * ‖confE w‖ ≤ ‖w‖ / 2 * (2 / ‖w‖) := by gcongr
          have h2 : ‖w‖ / 2 * (2 / ‖w‖) = 1 := by field_simp [hw_ne]
          linarith [h1, h2]
        calc Real.log (‖w‖ / 2) ≤ Real.log (‖confE w‖⁻¹) := Real.log_le_log (by linarith [hw4]) hinv
          _ = -Real.log ‖confE w‖ := Real.log_inv _
          _ ≤ |Real.log ‖confE w‖| := neg_le_abs _
      have hexp : (‖w‖ / 2) ^ (1 / 4 : ℝ) ≤ Real.exp ((1 / 4 : ℝ) * |Real.log ‖confE w‖|) := by
        rw [Real.rpow_def_of_pos (by linarith [hw4])]
        have harg_le : Real.log (‖w‖ / 2) * (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) * |Real.log ‖confE w‖| := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hlogE (by norm_num)
        exact Real.exp_le_exp.mpr harg_le
      have h1 := re_barrierW_ge hw
      dsimp [c0]
      calc ε * (Real.sqrt 2 / 4) * (‖w‖ / 2) ^ (1 / 4 : ℝ)
          = ε * ((Real.sqrt 2 / 4) * (‖w‖ / 2) ^ (1 / 4 : ℝ)) := by ring
        _ ≤ ε * ((Real.sqrt 2 / 4) * Real.exp ((1 / 4 : ℝ) * |Real.log ‖confE w‖|)) := by gcongr
        _ ≤ ε * (barrierW w).re := by gcongr
    have hdiff := hΔ w hw
    have hR0' := hR₀ ‖w‖ hR0w
    linarith [hdiff, hpoly, hR0', hW_ge]
  -- Near `-1, 0, 1` (`‖w - a‖ ≤ r`), deduce cleanly from `(Real.log t⁻¹)^2 ≤ 256 * t^(-1/8)` for `t ∈ (0, 1]`.
  have hex_small : ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      ∀ w : ℂ, 0 < w.im → (‖w - 1‖ ≤ r ∨ ‖w‖ ≤ r ∨ ‖w + 1‖ ≤ r) →
        |majorant2D (confB w) - (schwarzSlit w).im| ≤ ε * (barrierW w).re := by
    have htend : Tendsto (fun t : ℝ =>
        C_Δ * (1 + 2 * Real.log 4 + Real.log (t⁻¹)) ^ 2 - c0 * (t⁻¹ / 3) ^ (1 / 4 : ℝ))
        (𝓝[>] 0) atBot := by
      -- Substitute `u = t⁻¹ → atTop`!
      have htend_inv : Tendsto (fun u : ℝ =>
          C_Δ * (1 + 2 * Real.log 4 + Real.log u) ^ 2 - c0 * (u / 3) ^ (1 / 4 : ℝ)) atTop atBot := by
        refine tendsto_atTop_atBot.mpr fun B => ?_
        let K : ℝ := C_Δ * (2 * (1 + 2 * Real.log 4) ^ 2 + 2 * 256)
        have hK_nn : 0 ≤ K := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
        let C1 : ℝ := c0 * (3 : ℝ) ^ (-(1 / 4 : ℝ))
        have hC1 : 0 < C1 := by positivity
        let M0 : ℝ := max 1 (((max 0 (-B) + K) / C1 + 1) ^ 8)
        refine ⟨M0, fun u hu => ?_⟩
        have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
        have hu_pos : 0 < u := by linarith
        have hu8 : 1 ≤ u ^ (1 / 8 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
        have hl1 : C_Δ * (1 + 2 * Real.log 4 + Real.log u) ^ 2 ≤ K * u ^ (1 / 8 : ℝ) := by
          have h1 : Real.log u ^ 2 ≤ 256 * u ^ (1 / 8 : ℝ) := log_sq_le_rpow hu1
          have hsq : (1 + 2 * Real.log 4 + Real.log u) ^ 2 ≤
              2 * (1 + 2 * Real.log 4) ^ 2 + 2 * Real.log u ^ 2 := by
            nlinarith [sq_nonneg ((1 + 2 * Real.log 4) - Real.log u)]
          have hsq_nn : 0 ≤ 2 * (1 + 2 * Real.log 4) ^ 2 := by positivity
          have hterm : 2 * (1 + 2 * Real.log 4) ^ 2 ≤ 2 * (1 + 2 * Real.log 4) ^ 2 * u ^ (1 / 8 : ℝ) := by
            nlinarith [hu8, hsq_nn]
          calc C_Δ * (1 + 2 * Real.log 4 + Real.log u) ^ 2
              ≤ C_Δ * (2 * (1 + 2 * Real.log 4) ^ 2 + 2 * Real.log u ^ 2) :=
                mul_le_mul_of_nonneg_left hsq hC_pos.le
            _ ≤ C_Δ * (2 * (1 + 2 * Real.log 4) ^ 2 + 2 * (256 * u ^ (1 / 8 : ℝ))) := by gcongr
            _ ≤ C_Δ * (2 * (1 + 2 * Real.log 4) ^ 2 * u ^ (1 / 8 : ℝ) +
                  2 * 256 * u ^ (1 / 8 : ℝ)) := by
                exact mul_le_mul_of_nonneg_left (add_le_add hterm (le_of_eq (by ring))) hC_pos.le
            _ = K * u ^ (1 / 8 : ℝ) := by dsimp [K]; ring
        have hdiv_pow : (u / 3) ^ (1 / 4 : ℝ) = (3 : ℝ) ^ (-(1 / 4 : ℝ)) * u ^ (1 / 4 : ℝ) := by
          rw [div_eq_mul_inv, Real.mul_rpow hu_pos.le (by norm_num), Real.inv_rpow (by norm_num),
            ← Real.rpow_neg (by norm_num)]
          ring
        have hpow_mul : u ^ (1 / 4 : ℝ) = u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ) := by
          rw [← Real.rpow_add hu_pos]; norm_num
        have hu8_ge : (max 0 (-B) + K) / C1 + 1 ≤ u ^ (1 / 8 : ℝ) := by
          have h_base : ((max 0 (-B) + K) / C1 + 1) ^ 8 ≤ u := (le_max_right _ _).trans hu
          have h_nn : 0 ≤ (max 0 (-B) + K) / C1 + 1 := by positivity
          have hpow := Real.rpow_le_rpow (by positivity) h_base (by norm_num : (0 : ℝ) ≤ 1 / 8)
          rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul h_nn,
            show ((8 : ℕ) : ℝ) * (1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one] at hpow
          exact hpow
        have hrhs_eq : c0 * (u / 3) ^ (1 / 4 : ℝ) = C1 * (u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ)) := by
          rw [hdiv_pow, hpow_mul]; dsimp [C1]; ring
        calc C_Δ * (1 + 2 * Real.log 4 + Real.log u) ^ 2 - c0 * (u / 3) ^ (1 / 4 : ℝ)
            ≤ K * u ^ (1 / 8 : ℝ) - C1 * (u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ)) := by
              linarith [hl1, hrhs_eq]
          _ = u ^ (1 / 8 : ℝ) * (K - C1 * u ^ (1 / 8 : ℝ)) := by ring
          _ ≤ u ^ (1 / 8 : ℝ) * (K - C1 * ((max 0 (-B) + K) / C1 + 1)) := by gcongr
          _ = u ^ (1 / 8 : ℝ) * (-max 0 (-B) - C1) := by
              have hC1_eq : C1 * ((max 0 (-B) + K) / C1 + 1) = max 0 (-B) + K + C1 := by
                field_simp [hC1.ne']
              rw [hC1_eq]; ring
          _ ≤ 1 * (-max 0 (-B)) := by
              have h1 : -max 0 (-B) ≤ 0 := by linarith [le_max_left (0 : ℝ) (-B)]
              nlinarith [hu8, hC1, h1]
          _ ≤ B := by linarith [le_max_right (0 : ℝ) (-B)]
      exact htend_inv.comp tendsto_inv_nhdsGT_zero
    have hev : ∀ᶠ t : ℝ in 𝓝[>] 0,
        C_Δ * (1 + 2 * Real.log 4 + Real.log (t⁻¹)) ^ 2 - c0 * (t⁻¹ / 3) ^ (1 / 4 : ℝ) ≤ 0 :=
      htend.eventually_le_atBot 0
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨r₀, hr₀_pos, hr₀⟩ := hev
    refine ⟨min (1 / 4) (r₀ / 2), by positivity, by linarith [min_le_left (1 / 4 : ℝ) (r₀ / 2)], ?_⟩
    intro w hw hcase
    have hE_pos : 0 < ‖confE w‖ := by
      rw [← exp_two_pi_mul_confB hw]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
    have hdiff := hΔ w hw
    have hr_le : ∀ t : ℝ, 0 < t → t ≤ min (1 / 4) (r₀ / 2) →
        C_Δ * (1 + 2 * Real.log 4 + Real.log (t⁻¹)) ^ 2 ≤ c0 * (t⁻¹ / 3) ^ (1 / 4 : ℝ) := by
      intro t ht htr
      have ht_ball : t ∈ Metric.ball (0 : ℝ) r₀ := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
        linarith [htr.trans (min_le_right _ _)]
      linarith [hr₀ ht_ball ht]
    have hbound_of : ∀ (t : ℝ), 0 < t → t ≤ min (1 / 4) (r₀ / 2) →
        1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| ≤
          1 + 2 * Real.log 4 + Real.log (t⁻¹) →
        t⁻¹ / 3 ≤ max ‖confE w‖ (‖confE w‖⁻¹) →
        |majorant2D (confB w) - (schwarzSlit w).im| ≤ ε * (barrierW w).re := by
      intro t ht htr hQ hE_max
      have hQ_nn : 0 ≤ 1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| := by
        linarith [abs_nonneg (Real.log ‖w - 1‖), abs_nonneg (Real.log ‖w‖), abs_nonneg (Real.log ‖w + 1‖)]
      have hpoly : C_Δ * (1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖|) ^ 2 ≤
          C_Δ * (1 + 2 * Real.log 4 + Real.log (t⁻¹)) ^ 2 := by gcongr
      have hlogE : Real.log (t⁻¹ / 3) ≤ |Real.log ‖confE w‖| := by
        rcases le_max_iff.mp hE_max with h1 | h2
        · calc Real.log (t⁻¹ / 3) ≤ Real.log ‖confE w‖ := Real.log_le_log (by positivity) h1
            _ ≤ |Real.log ‖confE w‖| := le_abs_self _
        · calc Real.log (t⁻¹ / 3) ≤ Real.log (‖confE w‖⁻¹) := Real.log_le_log (by positivity) h2
            _ = -Real.log ‖confE w‖ := Real.log_inv _
            _ ≤ |Real.log ‖confE w‖| := neg_le_abs _
      have hexp : (t⁻¹ / 3) ^ (1 / 4 : ℝ) ≤ Real.exp ((1 / 4 : ℝ) * |Real.log ‖confE w‖|) := by
        rw [Real.rpow_def_of_pos (by positivity)]
        exact Real.exp_le_exp.mpr (by linarith)
      have hW_ge := re_barrierW_ge hw
      have h1 := hr_le t ht htr
      have hW' : c0 * (t⁻¹ / 3) ^ (1 / 4 : ℝ) ≤ ε * (barrierW w).re := by
        dsimp [c0]
        calc ε * (Real.sqrt 2 / 4) * (t⁻¹ / 3) ^ (1 / 4 : ℝ)
            = ε * ((Real.sqrt 2 / 4) * (t⁻¹ / 3) ^ (1 / 4 : ℝ)) := by ring
          _ ≤ ε * ((Real.sqrt 2 / 4) * Real.exp ((1 / 4 : ℝ) * |Real.log ‖confE w‖|)) := by gcongr
          _ ≤ ε * (barrierW w).re := by gcongr
      linarith
    rcases hcase with h_one | h_zero | h_negone
    · have h1 := near_one_qLog_confE hw (h_one.trans (min_le_left _ _))
      have ht_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (fun h => by
        have := congrArg Complex.im h; simp at this; linarith)
      exact hbound_of ‖w - 1‖ ht_pos h_one h1.1 h1.2
    · have h1 := near_zero_qLog_confE hw (h_zero.trans (min_le_left _ _))
      have ht_pos : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by
        have := congrArg Complex.im h; simp at this; linarith)
      exact hbound_of ‖w‖ ht_pos h_zero h1.1 h1.2
    · have h1 := near_neg_one_qLog_confE hw (h_negone.trans (min_le_left _ _))
      have ht_pos : 0 < ‖w + 1‖ := norm_pos_iff.mpr (fun h => by
        have := congrArg Complex.im h; simp at this; linarith)
      exact hbound_of ‖w + 1‖ ht_pos h_negone h1.1 h1.2
  obtain ⟨R, hR, hR_bd⟩ := hex_R
  obtain ⟨r, hr_pos, hr_half, hr_bd⟩ := hex_small
  refine ⟨⟨R, hR, r, hr_pos, hr_half, fun w hw hcase => ?_⟩, ?_⟩
  · rcases hcase with h1 | h2 | h3 | h4
    · exact hR_bd w hw h1
    · exact hr_bd w hw (Or.inl h2)
    · exact hr_bd w hw (Or.inr (Or.inl h3))
    · exact hr_bd w hw (Or.inr (Or.inr h4))
  · -- Remaining compact-like region: `‖w‖ ≤ R`, `r ≤ ‖w - 1‖`, `r ≤ ‖w‖`, `r ≤ ‖w + 1‖`!
    let Qmax : ℝ := 1 + max (|Real.log r|) (|Real.log (R + 1)|) * 3
    let M_ε : ℝ := C_Δ * Qmax ^ 2
    refine ⟨M_ε, by positivity, fun w hw => ?_⟩
    by_cases hcase : R ≤ ‖w‖ ∨ ‖w - 1‖ ≤ r ∨ ‖w‖ ≤ r ∨ ‖w + 1‖ ≤ r
    · have h1 := hcase.elim (hR_bd w hw) (hr_bd w hw)
      have : |majorant2D (confB w) - (schwarzSlit w).im| - ε * (barrierW w).re ≤ 0 := by linarith
      exact this.trans (by positivity)
    · push Not at hcase
      have hlog_bd : ∀ u : ℝ, r ≤ u → u ≤ R + 1 → |Real.log u| ≤ max |Real.log r| |Real.log (R + 1)| := by
        intro u hur huR
        have hu_pos : 0 < u := lt_of_lt_of_le hr_pos hur
        have h1 := Real.log_le_log hr_pos hur
        have h2 := Real.log_le_log hu_pos huR
        rw [abs_le]; constructor
        · have : -max |Real.log r| |Real.log (R + 1)| ≤ -|Real.log r| := neg_le_neg (le_max_left _ _)
          linarith [neg_abs_le (Real.log r)]
        · have : |Real.log (R + 1)| ≤ max |Real.log r| |Real.log (R + 1)| := le_max_right _ _
          linarith [le_abs_self (Real.log (R + 1))]
      have hm1_u : ‖w - 1‖ ≤ R + 1 := by
        calc ‖w - 1‖ ≤ ‖w‖ + 1 := by simpa using norm_sub_le w 1
          _ ≤ R + 1 := by linarith [hcase.1]
      have hw_u : ‖w‖ ≤ R + 1 := by linarith [hcase.1]
      have hp1_u : ‖w + 1‖ ≤ R + 1 := by
        calc ‖w + 1‖ ≤ ‖w‖ + 1 := by simpa using norm_add_le w 1
          _ ≤ R + 1 := by linarith [hcase.1]
      have hQ_le : 1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| ≤ Qmax := by
        have l1 := hlog_bd ‖w - 1‖ hcase.2.1.le hm1_u
        have l2 := hlog_bd ‖w‖ hcase.2.2.1.le hw_u
        have l3 := hlog_bd ‖w + 1‖ hcase.2.2.2.le hp1_u
        dsimp [Qmax]; linarith
      have hQ_nn : 0 ≤ 1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖| := by
        linarith [abs_nonneg (Real.log ‖w - 1‖), abs_nonneg (Real.log ‖w‖), abs_nonneg (Real.log ‖w + 1‖)]
      have hdiff := hΔ w hw
      have hW_nn : 0 ≤ ε * (barrierW w).re := mul_nonneg hε.le (re_barrierW_nonneg hw)
      have hsq : C_Δ * (1 + |Real.log ‖w - 1‖| + |Real.log ‖w‖| + |Real.log ‖w + 1‖|) ^ 2 ≤ M_ε := by
        dsimp [M_ε]; gcongr
      linarith

/-- Complex-`b` harmonic majorant identification (`h = U` at every `z₀` in the upper half-plane,
`vlo:Gap` / `vlo:PJ`). -/
theorem majorant2D_confB_eq_schwarzSlit_im (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    majorant2D (confB z₀) = (schwarzSlit z₀).im := by
    let Δ : ℂ → ℂ := fun z => majorantHolomorphic (confB z) - schwarzSlit z
    have hΔ_diff : DifferentiableOn ℂ Δ {z : ℂ | 0 < z.im} := by
      intro z hz
      have hd_confB : DifferentiableWithinAt ℂ confB {z : ℂ | 0 < z.im} z :=
        (hasDerivAt_confB hz).differentiableAt.differentiableWithinAt
      have hd_maj : DifferentiableAt ℂ majorantHolomorphic (confB z) :=
        (hasDerivAt_majorantHolomorphic (confB_mem_slitStrip hz)).differentiableAt
      have h1 : DifferentiableWithinAt ℂ (fun w => majorantHolomorphic (confB w))
          {z : ℂ | 0 < z.im} z :=
        DifferentiableAt.comp_differentiableWithinAt (g := majorantHolomorphic) (f := confB)
          z hd_maj hd_confB
      exact h1.sub (differentiableOn_schwarzSlit z hz)
    have hΔ_im : ∀ z : ℂ, (Δ z).im = majorant2D (confB z) - (schwarzSlit z).im := by
      intro z; rfl
    have hstep_eps : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ s : ℝ, |s| = 1 →
        -s * (Δ z₀).im - ε * (barrierW z₀).re ≤ δ := by
      intro ε hε δ hδ s hs_abs
      obtain ⟨⟨R, hR, r, hr_pos, hr_half, h_out⟩, ⟨M_ε, hM_nn, h_all⟩⟩ :=
        growth_domination_by_barrier hε
      -- Compact set `S = [-R, R] \ (B(-1, r/2) ∪ B(0, r/2) ∪ B(1, r/2))`
      let S : Set ℝ := Icc (-R) R ∩
        ({x : ℝ | r / 2 ≤ |x + 1|} ∩ {x : ℝ | r / 2 ≤ |x|} ∩ {x : ℝ | r / 2 ≤ |x - 1|})
      have hS_compact : IsCompact S := by
        refine isCompact_Icc.inter_right ?_
        exact ((isClosed_le continuous_const (continuous_abs.comp (continuous_id.add continuous_const))).inter
          (isClosed_le continuous_const continuous_abs)).inter
          (isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const)))
      have hS_small : ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ r / 2 ∧
          ∀ σ ∈ S, ∀ z : ℂ, 0 < z.im → ‖z - (σ : ℂ)‖ < η₀ →
            |majorant2D (confB z) - (schwarzSlit z).im| < δ := by
        have hcover : ∀ σ : ℝ, σ ∈ S → ∃ ρ > 0, ∀ z : ℂ, 0 < z.im → ‖z - (σ : ℂ)‖ < ρ →
            |majorant2D (confB z) - (schwarzSlit z).im| < δ := by
          intro σ hσ
          have hm1 : σ ≠ -1 := by
            intro h; have := hσ.2.1.1; rw [h] at this; norm_num at this; linarith
          have h0 : σ ≠ 0 := by
            intro h; have := hσ.2.1.2; rw [h] at this; norm_num at this; linarith
          have h1 : σ ≠ 1 := by
            intro h; have := hσ.2.2; rw [h] at this; norm_num at this; linarith
          have ht_M := tendsto_majorant2D_confB h0 h1 hm1
          have ht_S := tendsto_schwarzSlit_im h0 h1 hm1
          have ht_diff := ht_M.sub ht_S
          rw [sub_self, Metric.tendsto_nhdsWithin_nhds] at ht_diff
          obtain ⟨ρ, hρ_pos, hρ⟩ := ht_diff δ hδ
          refine ⟨ρ, hρ_pos, fun z hz hdist => ?_⟩
          simpa [Real.dist_eq, sub_zero] using hρ hz (Complex.dist_eq z (σ : ℂ) ▸ hdist)
        choose ρ hρ_pos hρ_bd using hcover
        have hfinite := hS_compact.elim_nhds_subcover
          (fun σ => if h : σ ∈ S then Metric.ball σ (ρ σ h / 2) else ∅)
          (fun σ hσ => by
            rw [dif_pos hσ]
            exact Metric.ball_mem_nhds σ (half_pos (hρ_pos σ hσ)))
        rcases hfinite with ⟨t, ht_sub, ht_cover⟩
        by_cases ht_empty : t.Nonempty
        · let η₀ : ℝ := min (r / 2) (t.inf' ht_empty fun σ =>
            if h : σ ∈ S then ρ σ h / 2 else 1)
          have hη₀_pos : 0 < η₀ := by
            refine lt_min (half_pos hr_pos) ?_
            rw [Finset.lt_inf'_iff]
            intro σ hσt
            split_ifs with hσS
            · exact half_pos (hρ_pos σ hσS)
            · exact one_pos
          refine ⟨η₀, hη₀_pos, min_le_left _ _, fun σ hσ z hz hdist => ?_⟩
          have hmem := ht_cover hσ
          simp only [Set.mem_iUnion, exists_prop] at hmem
          obtain ⟨σ₀, hσ₀t, hσ₀_ball⟩ := hmem
          have hσ₀S : σ₀ ∈ S := ht_sub σ₀ hσ₀t
          rw [dif_pos hσ₀S] at hσ₀_ball
          have hdist1 : |σ - σ₀| < ρ σ₀ hσ₀S / 2 := by simpa [Real.dist_eq] using hσ₀_ball
          have hdist2 : ‖(σ : ℂ) - (σ₀ : ℂ)‖ < ρ σ₀ hσ₀S / 2 := by
            simpa [← Complex.ofReal_sub, Complex.norm_real] using hdist1
          have hη_le : η₀ ≤ ρ σ₀ hσ₀S / 2 := by
            calc η₀ ≤ t.inf' ht_empty (fun u => if h : u ∈ S then ρ u h / 2 else 1) := min_le_right _ _
              _ ≤ if h : σ₀ ∈ S then ρ σ₀ h / 2 else 1 := Finset.inf'_le _ hσ₀t
              _ = ρ σ₀ hσ₀S / 2 := dif_pos hσ₀S
          have hdist_tot : ‖z - (σ₀ : ℂ)‖ < ρ σ₀ hσ₀S := by
            have hsum : (z - (σ : ℂ)) + ((σ : ℂ) - (σ₀ : ℂ)) = z - (σ₀ : ℂ) := by ring
            calc ‖z - (σ₀ : ℂ)‖ = ‖(z - (σ : ℂ)) + ((σ : ℂ) - (σ₀ : ℂ))‖ := by rw [hsum]
              _ ≤ ‖z - (σ : ℂ)‖ + ‖(σ : ℂ) - (σ₀ : ℂ)‖ := norm_add_le _ _
              _ < η₀ + ρ σ₀ hσ₀S / 2 := by linarith [hdist, hdist2]
              _ ≤ ρ σ₀ hσ₀S := by linarith [hη_le]
          exact hρ_bd σ₀ hσ₀S z hz hdist_tot
        · rw [Finset.not_nonempty_iff_eq_empty] at ht_empty
          refine ⟨r / 2, half_pos hr_pos, le_rfl, fun σ hσ => ?_⟩
          exfalso
          have hmem := ht_cover hσ
          simp [ht_empty] at hmem
      obtain ⟨η₀, hη₀_pos, hη₀_le, hS_bd⟩ := hS_small
      -- For every `η ∈ (0, η₀)`, apply `PhragmenLindelof.right_half_plane_of_bounded_on_real` to `f_η`
      have h_shifted : ∀ η : ℝ, 0 < η → η < η₀ →
          ‖Complex.exp (((s : ℂ) * Complex.I) * Δ (z₀ + (η : ℂ) * Complex.I) -
            (ε : ℂ) * barrierW (z₀ + (η : ℂ) * Complex.I))‖ ≤ Real.exp δ := by
        intro η hη hη_lt
        let f : ℂ → ℂ := fun w =>
          Complex.exp (((s : ℂ) * Complex.I) * Δ (Complex.I * w + (η : ℂ) * Complex.I) -
            (ε : ℂ) * barrierW (Complex.I * w + (η : ℂ) * Complex.I))
        have hmap_im : ∀ w : ℂ, -η < w.re → 0 < (Complex.I * w + (η : ℂ) * Complex.I).im := by
          intro w hw
          simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
            zero_add, Complex.ofReal_im, Complex.ofReal_re]
          linarith [hw]
        have hf_diff : DiffContOnCl ℂ f {w : ℂ | 0 < w.re} := by
          have hU_open : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
          have hd_open : DifferentiableOn ℂ f {w : ℂ | -η < w.re} := by
            intro w hw
            have him := hmap_im w hw
            have hlin : HasDerivAt (fun u : ℂ => Complex.I * u + (η : ℂ) * Complex.I) Complex.I w := by
              simpa using ((hasDerivAt_id w).const_mul Complex.I).add_const ((η : ℂ) * Complex.I)
            have hd_Δ := (hΔ_diff _ him).differentiableAt (hU_open.mem_nhds him)
            have hd_W := (differentiableOn_barrierW _ him).differentiableAt (hU_open.mem_nhds him)
            have hc1 := (hd_Δ.comp w hlin.differentiableAt).const_mul ((s : ℂ) * Complex.I)
            have hc2 := (hd_W.comp w hlin.differentiableAt).const_mul (ε : ℂ)
            exact ((hc1.sub hc2).cexp).differentiableWithinAt
          have hsub : closure {w : ℂ | 0 < w.re} ⊆ {w : ℂ | -η < w.re} := by
            intro w hw
            have hcl : w.re ≥ 0 := by
              rw [Metric.mem_closure_iff] at hw
              by_contra hlt; push Not at hlt
              obtain ⟨u, hu, hdist⟩ := hw (-w.re) (by linarith [hlt])
              have hle := Complex.abs_re_le_norm (u - w)
              have hlt' := (abs_lt.mp (hle.trans_lt (Complex.dist_eq u w ▸ (dist_comm w u ▸ hdist)))).2
              change 0 < u.re at hu
              simp only [Complex.sub_re] at hlt'; linarith [hlt']
            change -η < w.re; linarith [hcl, hη]
          exact ⟨hd_open.mono (fun w hw => by change 0 < w.re at hw; change -η < w.re; linarith [hw, hη]),
            hd_open.continuousOn.mono hsub⟩
        have hf_bd : ∀ w : ℂ, 0 ≤ w.re → ‖f w‖ ≤ Real.exp M_ε := by
          intro w hw
          have him : 0 < (Complex.I * w + (η : ℂ) * Complex.I).im := hmap_im w (by linarith [hw, hη])
          dsimp [f]
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have hre_exp : (((s : ℂ) * Complex.I) * Δ (Complex.I * w + (η : ℂ) * Complex.I) -
              (ε : ℂ) * barrierW (Complex.I * w + (η : ℂ) * Complex.I)).re =
              -s * (Δ (Complex.I * w + (η : ℂ) * Complex.I)).im -
                ε * (barrierW (Complex.I * w + (η : ℂ) * Complex.I)).re := by
            simp [Complex.sub_re, Complex.mul_re]
          rw [hre_exp]
          have hs_bd : -s * (Δ (Complex.I * w + (η : ℂ) * Complex.I)).im ≤
              |majorant2D (confB (Complex.I * w + (η : ℂ) * Complex.I)) -
                (schwarzSlit (Complex.I * w + (η : ℂ) * Complex.I)).im| := by
            rw [← hΔ_im]
            have h1 := le_abs_self (-s * (Δ (Complex.I * w + (η : ℂ) * Complex.I)).im)
            rwa [abs_mul, abs_neg, hs_abs, one_mul] at h1
          linarith [h_all _ him, hs_bd]
        have hf_exp : ∃ c < (2 : ℝ), ∃ B,
            f =O[Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}] fun w => Real.exp (B * ‖w‖ ^ c) := by
          refine ⟨0, by norm_num, 0, Asymptotics.isBigO_iff.mpr ⟨Real.exp M_ε, ?_⟩⟩
          rw [Filter.eventually_inf_principal]
          filter_upwards with w hw
          have hnorm : ‖Real.exp ((0 : ℝ) * ‖w‖ ^ (0 : ℝ))‖ = 1 := by simp
          rw [hnorm, mul_one]
          exact hf_bd w hw.le
        have hf_re : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖ :=
          ⟨Real.exp M_ε, eventually_atTop.mpr ⟨0, fun x hx => hf_bd (x : ℂ) (by simpa using hx)⟩⟩
        have hf_im : ∀ x : ℝ, ‖f (x * Complex.I)‖ ≤ Real.exp δ := by
          intro x
          have harg : Complex.I * ((x : ℂ) * Complex.I) + (η : ℂ) * Complex.I =
              ((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I := by
            rw [← mul_assoc, mul_comm Complex.I (x : ℂ), mul_assoc, Complex.I_mul_I]
            push_cast; ring
          have him : 0 < (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
          dsimp [f]
          rw [harg, Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have hre_exp : (((s : ℂ) * Complex.I) * Δ (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I) -
              (ε : ℂ) * barrierW (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).re =
              -s * (Δ (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im -
                ε * (barrierW (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).re := by
            simp [Complex.sub_re, Complex.mul_re]
          rw [hre_exp]
          have hs_bd : -s * (Δ (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im ≤
              |majorant2D (confB (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)) -
                (schwarzSlit (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im| := by
            rw [← hΔ_im]
            have h1 := le_abs_self (-s * (Δ (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im)
            rwa [abs_mul, abs_neg, hs_abs, one_mul] at h1
          let w := ((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I
          have hW_nn : 0 ≤ ε * (barrierW w).re := mul_nonneg hε.le (re_barrierW_nonneg him)
          by_cases hinS : -x ∈ S
          · have hdist : ‖w - ((-x : ℝ) : ℂ)‖ < η₀ := by
              have : w - ((-x : ℝ) : ℂ) = (η : ℂ) * Complex.I := by dsimp [w]; ring
              rw [this, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_of_nonneg hη.le]
              exact hη_lt
            have h1 := hS_bd (-x) hinS w him hdist
            linarith [hs_bd, h1, hW_nn]
          · have hcase_out : R ≤ ‖w‖ ∨ ‖w - 1‖ ≤ r ∨ ‖w‖ ≤ r ∨ ‖w + 1‖ ≤ r := by
              dsimp [S] at hinS
              rw [Set.mem_inter_iff, not_and] at hinS
              by_cases hIcc : -x ∈ Icc (-R) R
              · have h_not := hinS hIcc
                simp only [Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_le] at h_not
                have hη_r2 : η < r / 2 := hη_lt.trans_le hη₀_le
                by_cases ha1 : |-x + 1| < r / 2
                · right; right; right
                  have heq : w + 1 = (((-x + 1 : ℝ) : ℂ) + (η : ℂ) * Complex.I) := by
                    dsimp [w]; push_cast; ring
                  calc ‖w + 1‖ ≤ ‖((-x + 1 : ℝ) : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := by
                        rw [heq]; exact norm_add_le _ _
                    _ = |-x + 1| + η := by
                        rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_I, mul_one,
                          Real.norm_eq_abs, Real.norm_of_nonneg hη.le]
                    _ ≤ r / 2 + r / 2 := by linarith [ha1, hη_r2]
                    _ = r := add_halves r
                · push Not at ha1
                  by_cases ha0 : |-x| < r / 2
                  · right; right; left
                    calc ‖w‖ ≤ ‖((-x : ℝ) : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
                      _ = |-x| + η := by
                          rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_I, mul_one,
                            Real.norm_eq_abs, Real.norm_of_nonneg hη.le]
                      _ ≤ r / 2 + r / 2 := by linarith [ha0, hη_r2]
                      _ = r := add_halves r
                  · push Not at ha0
                    have ham1 : |-x - 1| < r / 2 := h_not ⟨ha1, ha0⟩
                    right; left
                    have heq : w - 1 = (((-x - 1 : ℝ) : ℂ) + (η : ℂ) * Complex.I) := by
                      dsimp [w]; push_cast; ring
                    calc ‖w - 1‖ ≤ ‖((-x - 1 : ℝ) : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := by
                          rw [heq]; exact norm_add_le _ _
                      _ = |-x - 1| + η := by
                          rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_I, mul_one,
                            Real.norm_eq_abs, Real.norm_of_nonneg hη.le]
                      _ ≤ r / 2 + r / 2 := by linarith [ham1, hη_r2]
                      _ = r := add_halves r
              · left
                have hR_le : R < |-x| := by
                  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hIcc
                  rcases hIcc with h | h
                  · exact lt_of_lt_of_le (by linarith [h]) (neg_le_abs (-x))
                  · exact lt_of_lt_of_le h (le_abs_self (-x))
                have hw_ge : |-x| ≤ ‖w‖ := by
                  have hre_w : w.re = -x := by simp [w]
                  simpa [hre_w] using Complex.abs_re_le_norm w
                linarith [hR_le, hw_ge]
            have h1 := h_out w him hcase_out
            linarith [hs_bd, h1]
        have hw0 : 0 ≤ (-Complex.I * z₀).re := by simp [hz₀.le]
        have hphl := PhragmenLindelof.right_half_plane_of_bounded_on_real hf_diff hf_exp hf_re hf_im hw0
        have harg : Complex.I * (-Complex.I * z₀) + (η : ℂ) * Complex.I = z₀ + (η : ℂ) * Complex.I := by
          rw [← mul_assoc, mul_neg, Complex.I_mul_I]; ring
        dsimp [f] at hphl
        rwa [harg] at hphl
      -- Let `η ↓ 0`: `tendsto` of `z₀ + η * I` to `z₀` where `Δ` and `barrierW` are continuous!
      have ht_lim : Tendsto (fun η : ℝ =>
          ‖Complex.exp (((s : ℂ) * Complex.I) * Δ (z₀ + (η : ℂ) * Complex.I) -
            (ε : ℂ) * barrierW (z₀ + (η : ℂ) * Complex.I))‖)
          (𝓝[>] 0)
          (𝓝 ‖Complex.exp (((s : ℂ) * Complex.I) * Δ z₀ - (ε : ℂ) * barrierW z₀)‖) := by
        have hz_tend : Tendsto (fun η : ℝ => z₀ + (η : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 z₀) := by
          have : z₀ = z₀ + (0 : ℂ) * Complex.I := by simp
          conv_rhs => rw [this]
          exact tendsto_const_nhds.add
            ((Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
              tendsto_const_nhds)
        have hΔ_cont : ContinuousAt Δ z₀ :=
          hΔ_diff.continuousOn.continuousAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz₀)
        have hW_cont : ContinuousAt barrierW z₀ :=
          differentiableOn_barrierW.continuousOn.continuousAt
            (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz₀)
        refine continuous_norm.continuousAt.tendsto.comp (Complex.continuous_exp.continuousAt.tendsto.comp ?_)
        exact (tendsto_const_nhds.mul (hΔ_cont.tendsto.comp hz_tend)).sub
          (tendsto_const_nhds.mul (hW_cont.tendsto.comp hz_tend))
      have h_le : ‖Complex.exp (((s : ℂ) * Complex.I) * Δ z₀ - (ε : ℂ) * barrierW z₀)‖ ≤ Real.exp δ := by
        refine le_of_tendsto ht_lim ?_
        filter_upwards [Ioo_mem_nhdsGT hη₀_pos] with η hy
        exact h_shifted η hy.1 hy.2
      rw [Complex.norm_exp, Real.exp_le_exp] at h_le
      have hre_exp : (((s : ℂ) * Complex.I) * Δ z₀ - (ε : ℂ) * barrierW z₀).re =
          -s * (Δ z₀).im - ε * (barrierW z₀).re := by
        simp [Complex.sub_re, Complex.mul_re]
      rwa [hre_exp] at h_le
    -- Let `δ ↓ 0` then `ε ↓ 0` for `s = 1` and `s = -1`:
    have h_both : ∀ s : ℝ, |s| = 1 → -s * (Δ z₀).im ≤ 0 := by
      intro s hs_abs
      have h_eps : ∀ ε > 0, -s * (Δ z₀).im - ε * (barrierW z₀).re ≤ 0 := by
        intro ε hε
        by_contra hlt; push Not at hlt
        linarith [hstep_eps ε hε ((-s * (Δ z₀).im - ε * (barrierW z₀).re) / 2) (by linarith) s hs_abs]
      by_contra hgt; push Not at hgt
      let ε := (-s * (Δ z₀).im) / (2 * ((barrierW z₀).re + 1))
      have hε_pos : 0 < ε := div_pos hgt (by have := re_barrierW_nonneg hz₀; positivity)
      have h1 := h_eps ε hε_pos
      have hW_lt : ε * (barrierW z₀).re < (-s * (Δ z₀).im) / 2 := by
        have hnn := re_barrierW_nonneg hz₀
        calc ε * (barrierW z₀).re < ε * ((barrierW z₀).re + 1) := by gcongr; linarith
          _ = (-s * (Δ z₀).im) / 2 := by
              have hne : (barrierW z₀).re + 1 ≠ 0 := by linarith
              dsimp [ε]; field_simp [hne]
      linarith
    have h1 := h_both 1 (by simp)
    have h2 := h_both (-1) (by simp)
    have him0 : (Δ z₀).im = 0 := by linarith [h1, h2]
    have hdz := hΔ_im z₀
    linarith [hdz, him0]

/-- Complex-`b` harmonic majorant identification written as a Poisson integral over
`slitPreimage` for any `z₀ ∈ ℍ` (`U(𝓑(z₀)) = -∫_{slitPreimage} L(𝓑_∂(σ)) P(z₀, σ) dσ`). -/
theorem harmonicMajorantIdentification_complex {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    majorant2D (confB z₀) =
      -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel z₀.re z₀.im σ := by
  rw [majorant2D_confB_eq_schwarzSlit_im z₀ hz₀, schwarzSlit_im hz₀]

/--
info: 'FormalResearch.ModularBootstrap.PoissonJensen.harmonicMajorantIdentification_complex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms harmonicMajorantIdentification_complex

/-- Identification `h = U` (`HarmonicMajorantIdentification`, Lemma G, `vlo:Gap`). -/
theorem harmonicMajorantIdentification : HarmonicMajorantIdentification := by
  -- Specialize to `z₀ = realSliceData.xUHP (xiStar - x) + I * realSliceData.yUHP (xiStar - x)`
  intro x hx
  have hx_mem : xiStar - x ∈ Ioc 0 xiStar := ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
  have hy_pos : 0 < realSliceData.yUHP (xiStar - x) :=
    lt_of_lt_of_le (mul_pos realSliceData.hc_y (Real.sqrt_pos.mpr hx_mem.1))
      (realSliceData.im_lower (xiStar - x) hx_mem)
  set z₀ : ℂ := (realSliceData.xUHP (xiStar - x) : ℂ) +
    (realSliceData.yUHP (xiStar - x) : ℂ) * Complex.I
  have hz₀_im : 0 < z₀.im := by simpa [z₀] using hy_pos
  have hcb : confB z₀ = (x : ℂ) := by
    have hp := realSliceData_preimage hx_mem
    simpa [z₀, sub_sub_cancel] using hp.2
  have hpt := majorant2D_confB_eq_schwarzSlit_im z₀ hz₀_im
  rw [hcb, majorant2D_ofReal (by rw [abs_of_nonneg hx.1]; exact hx.2.le),
    schwarzSlit_im hz₀_im] at hpt
  simpa [z₀] using hpt

/--
info: 'FormalResearch.ModularBootstrap.PoissonJensen.harmonicMajorantIdentification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms harmonicMajorantIdentification

end FormalResearch.ModularBootstrap.PoissonJensen

