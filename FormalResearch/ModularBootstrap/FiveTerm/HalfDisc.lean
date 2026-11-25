module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The half-disc `Ω`, the map `ζ`, and the involution `σ` (`cts:involution`, preface; `cts:sigma`)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, §`cts:s3` (eq. `cts:sigma`) and the
opening paragraph of Lemma C3 (`cts:involution`).

With `Ω = {|z| < 1, Re z > 0}` the right half-disc, `ℍ` the upper half-plane,
`ζ(z) = ((i - z)/(i + z))²` and `σ(z) = (1 - z)/(1 + z)`:

* `zetaHD_bijOn`: `ζ` maps `Ω` bijectively onto `ℍ`;
* `zetaHD_zero`, `zetaHD_one`, `sigmaHD_fixed`: `ζ(0) = 1`, `ζ(1) = -1`, `σ(√2 - 1) = √2 - 1`;
* `zetaHD_conj`: `ζ(z̄) = 1/conj ζ(z)`; `zetaHD_sigma`: `ζ(σ z) = -1/ζ(z)`;
  `sigmaHD_sigmaHD`, `sigmaHD_mem`: `σ` is an involution of `Ω`;
* `sigmaHD_imag`: `σ(iy) = e^{-2i arctan y}` (so `σ(iy) = e^{-iψ}` with `ψ = 2 arctan y`);
  `zetaHD_imag`: `ζ(iy) = ((1-y)/(1+y))²`; `arctan_two_mul_div`: `arctan(2y/(1-y²)) = 2 arctan y`.

These are the exact conformal-geometry preliminaries of Lemma C3. The outer function `G_outer` on `Ω`
itself (existence, the functional identity `cts:R-id`, the coupling `cts:coupling`) is not here.
All results are proved unconditionally.
-/

@[expose] public section

open Complex
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The right half-disc `Ω = {|z| < 1, Re z > 0}`. -/
def halfDisc : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ 0 < z.re}

/-- The upper half-plane `ℍ = {Im ζ > 0}`. -/
def upperPlane : Set ℂ := {w : ℂ | 0 < w.im}

/-- `u(z) = (i - z)/(i + z)`; maps `Ω` onto the open first quadrant. -/
noncomputable def uHD (z : ℂ) : ℂ := (Complex.I - z) / (Complex.I + z)

/-- `ζ(z) = ((i - z)/(i + z))²`. -/
noncomputable def zetaHD (z : ℂ) : ℂ := uHD z ^ 2

/-- `σ(z) = (1 - z)/(1 + z)`. -/
noncomputable def sigmaHD (z : ℂ) : ℂ := (1 - z) / (1 + z)

lemma I_add_ne_zero {z : ℂ} (hz : 0 < z.re) : Complex.I + z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma one_add_ne_zero {z : ℂ} (hz : 0 < z.re) : 1 + z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma normSq_I_add {z : ℂ} : Complex.normSq (Complex.I + z) = z.re ^ 2 + (1 + z.im) ^ 2 := by
  rw [Complex.normSq_apply]; simp; ring

lemma uHD_re {z : ℂ} (hz : 0 < z.re) :
    (uHD z).re = (1 - z.re ^ 2 - z.im ^ 2) / (z.re ^ 2 + (1 + z.im) ^ 2) := by
  have hD : 0 < z.re ^ 2 + (1 + z.im) ^ 2 := by positivity
  unfold uHD
  rw [Complex.div_re, normSq_I_add]
  simp
  field_simp
  ring

lemma uHD_im {z : ℂ} (hz : 0 < z.re) :
    (uHD z).im = 2 * z.re / (z.re ^ 2 + (1 + z.im) ^ 2) := by
  have hD : 0 < z.re ^ 2 + (1 + z.im) ^ 2 := by positivity
  unfold uHD
  rw [Complex.div_im, normSq_I_add]
  simp
  field_simp
  ring

lemma sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `u` maps `Ω` into the open first quadrant. -/
lemma uHD_mem {z : ℂ} (hz : z ∈ halfDisc) : 0 < (uHD z).re ∧ 0 < (uHD z).im := by
  obtain ⟨h1, h2⟩ := hz
  have hD : 0 < z.re ^ 2 + (1 + z.im) ^ 2 := by positivity
  have hn : z.re ^ 2 + z.im ^ 2 < 1 := by
    rw [← sq_norm_eq]; nlinarith only [h1, norm_nonneg z]
  rw [uHD_re h2, uHD_im h2]
  exact ⟨div_pos (by linarith) hD, div_pos (by positivity) hD⟩

lemma zetaHD_mem {z : ℂ} (hz : z ∈ halfDisc) : zetaHD z ∈ upperPlane := by
  obtain ⟨h1, h2⟩ := uHD_mem hz
  show 0 < (uHD z ^ 2).im
  rw [sq, Complex.mul_im]
  nlinarith only [mul_pos h1 h2]

lemma zetaHD_zero : zetaHD 0 = 1 := by
  simp [zetaHD, uHD, Complex.I_ne_zero]

lemma zetaHD_one : zetaHD 1 = -1 := by
  have h : Complex.I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  unfold zetaHD uHD
  rw [div_pow, div_eq_iff (pow_ne_zero 2 h)]
  ring_nf
  simp [Complex.I_sq]
  ring

lemma sub_I_ne_zero' {z : ℂ} (hz : 0 < z.re) : Complex.I - z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma conj_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (starRingEnd ℂ z).re := by simpa using hz

/-- `u(z̄) = 1 / conj u(z)`. -/
lemma uHD_conj {z : ℂ} (hz : 0 < z.re) : uHD (starRingEnd ℂ z) = (starRingEnd ℂ (uHD z))⁻¹ := by
  have h1 := I_add_ne_zero (conj_re_pos hz)
  have h2 : (-Complex.I - starRingEnd ℂ z) ≠ 0 := by
    intro h; apply h1; linear_combination -h
  have h3 : (-Complex.I + starRingEnd ℂ z) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold uHD
  rw [map_div₀, map_sub, map_add, Complex.conj_I, inv_div]
  rw [div_eq_div_iff h1 h2]
  ring_nf

lemma zetaHD_conj {z : ℂ} (hz : 0 < z.re) :
    zetaHD (starRingEnd ℂ z) = (starRingEnd ℂ (zetaHD z))⁻¹ := by
  unfold zetaHD
  rw [uHD_conj hz, inv_pow, map_pow]

/-- `u(σ z) = i / u(z)`. -/
lemma uHD_sigma {z : ℂ} (hz : 0 < z.re) : uHD (sigmaHD z) = Complex.I / uHD z := by
  have h1 := one_add_ne_zero hz
  have h2 := I_add_ne_zero hz
  have h3 := sub_I_ne_zero' hz
  have h4 : Complex.I * (1 + z) + (1 - z) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have h' := congrArg Complex.im h
    simp at this h'
    nlinarith only [this, h', hz]
  unfold uHD sigmaHD
  have e : Complex.I + (1 - z) / (1 + z) = (Complex.I * (1 + z) + (1 - z)) / (1 + z) := by
    field_simp
  have e2 : Complex.I - (1 - z) / (1 + z) = (Complex.I * (1 + z) - (1 - z)) / (1 + z) := by
    field_simp
  rw [e, e2, div_div_div_cancel_right₀ h1]
  rw [div_div_eq_mul_div, div_eq_div_iff h4 h3]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- `ζ(σ z) = -1/ζ(z)`. -/
lemma zetaHD_sigma {z : ℂ} (hz : 0 < z.re) : zetaHD (sigmaHD z) = -(zetaHD z)⁻¹ := by
  unfold zetaHD
  rw [uHD_sigma hz, div_pow, Complex.I_sq, neg_div, one_div]

lemma sigmaHD_sigmaHD {z : ℂ} (hz : 0 < z.re) : sigmaHD (sigmaHD z) = z := by
  have h1 := one_add_ne_zero hz
  unfold sigmaHD
  have h2 : (1 : ℂ) + (1 - z) / (1 + z) = 2 / (1 + z) := by field_simp; ring
  have h3 : (1 : ℂ) - (1 - z) / (1 + z) = 2 * z / (1 + z) := by field_simp; ring
  rw [h2, h3, div_div_div_cancel_right₀ h1]
  have : (2 : ℂ) ≠ 0 := two_ne_zero
  field_simp

lemma sigmaHD_mem {z : ℂ} (hz : z ∈ halfDisc) : sigmaHD z ∈ halfDisc := by
  obtain ⟨h1, h2⟩ := hz
  have hn : z.re ^ 2 + z.im ^ 2 < 1 := by rw [← sq_norm_eq]; nlinarith only [h1, norm_nonneg z]
  have hD : 0 < (1 + z.re) ^ 2 + z.im ^ 2 := by positivity
  have hre : (sigmaHD z).re = (1 - z.re ^ 2 - z.im ^ 2) / ((1 + z.re) ^ 2 + z.im ^ 2) := by
    unfold sigmaHD
    rw [Complex.div_re, Complex.normSq_apply]
    simp
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · have hne : 1 + z ≠ 0 := one_add_ne_zero h2
    unfold sigmaHD
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
    have e1 : ‖1 - z‖ ^ 2 = (1 - z.re) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have e2 : ‖1 + z‖ ^ 2 = (1 + z.re) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [e1, e2]; nlinarith only [h2]
  · rw [hre]; exact div_pos (by linarith) hD

lemma uHD_injOn : Set.InjOn uHD halfDisc := by
  intro z1 hz1 z2 hz2 h
  have a1 := I_add_ne_zero hz1.2
  have a2 := I_add_ne_zero hz2.2
  unfold uHD at h
  rw [div_eq_div_iff a1 a2] at h
  have : (2 * Complex.I) * (z2 - z1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (by simp)
  · exact (sub_eq_zero.mp h0).symm

lemma zetaHD_injOn : Set.InjOn zetaHD halfDisc := by
  intro z1 hz1 z2 hz2 h
  obtain ⟨p1, q1⟩ := uHD_mem hz1
  obtain ⟨p2, q2⟩ := uHD_mem hz2
  unfold zetaHD at h
  have h' : (uHD z1 - uHD z2) * (uHD z1 + uHD z2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact uHD_injOn hz1 hz2 (sub_eq_zero.mp h0)
  · exfalso
    have := congrArg Complex.re h0
    simp at this
    linarith

/-- Every point of the open first quadrant is `u(z)` for a unique `z ∈ Ω`. -/
lemma exists_uHD_eq {u : ℂ} (hre : 0 < u.re) (him : 0 < u.im) :
    ∃ z ∈ halfDisc, uHD z = u := by
  have h1 : (1 + u) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set z : ℂ := Complex.I * (1 - u) / (1 + u) with hz
  have hD : 0 < (1 + u.re) ^ 2 + u.im ^ 2 := by positivity
  have hzre : z.re = 2 * u.im / ((1 + u.re) ^ 2 + u.im ^ 2) := by
    rw [hz, Complex.div_re, Complex.normSq_apply]
    simp
    field_simp
    ring
  have hzpos : 0 < z.re := by rw [hzre]; positivity
  refine ⟨z, ⟨?_, hzpos⟩, ?_⟩
  · rw [hz, norm_div, norm_mul, Complex.norm_I, one_mul, div_lt_one (norm_pos_iff.mpr h1)]
    have e1 : ‖1 - u‖ ^ 2 = (1 - u.re) ^ 2 + u.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have e2 : ‖1 + u‖ ^ 2 = (1 + u.re) ^ 2 + u.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [e1, e2]; nlinarith only [hre]
  · have a1 := I_add_ne_zero hzpos
    have a2 : Complex.I + z = 2 * Complex.I / (1 + u) := by
      rw [hz]; field_simp; ring
    have a3 : Complex.I - z = 2 * Complex.I * u / (1 + u) := by
      rw [hz]; field_simp; ring
    unfold uHD
    rw [a2, a3, div_div_div_cancel_right₀ h1]
    have : (2 * Complex.I : ℂ) ≠ 0 := by simp
    field_simp

lemma zetaHD_surjOn : Set.SurjOn zetaHD halfDisc upperPlane := by
  intro w hw
  have hw' : 0 < w.im := hw
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw'; simp at hw'
  have hρ : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set θ : ℝ := Complex.arg w with hθ
  have hθ0 : 0 < θ := by
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hw'.le) (fun h => ?_)
    have := (Complex.arg_eq_zero_iff.mp h.symm).2
    linarith
  have hθ1 : θ < π := by
    refine lt_of_le_of_ne (Complex.arg_le_pi w) (fun h => ?_)
    have := (Complex.arg_eq_pi_iff.mp h).2
    linarith
  set u : ℂ := ((√‖w‖ : ℝ) : ℂ) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) with hu
  have hsq : u ^ 2 = w := by
    have h1 : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) ^ 2 = Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h2 : ((√‖w‖ : ℝ) : ℂ) ^ 2 = ((‖w‖ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hρ.le]
    rw [hu, mul_pow, h1, h2]
    exact Complex.norm_mul_exp_arg_mul_I w
  have hre : u.re = √‖w‖ * Real.cos (θ / 2) := by
    rw [hu, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : u.im = √‖w‖ * Real.sin (θ / 2) := by
    rw [hu, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hsq0 : 0 < √‖w‖ := Real.sqrt_pos.mpr hρ
  have hc : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  obtain ⟨z, hz, hzu⟩ := exists_uHD_eq (u := u) (by rw [hre]; positivity) (by rw [him]; positivity)
  exact ⟨z, hz, by unfold zetaHD; rw [hzu, hsq]⟩

/-- `ζ` maps `Ω` bijectively onto the upper half-plane (`cts:involution`). -/
theorem zetaHD_bijOn : Set.BijOn zetaHD halfDisc upperPlane :=
  ⟨fun _ hz => zetaHD_mem hz, zetaHD_injOn, zetaHD_surjOn⟩

/-- `σ` fixes `z₀ = √2 - 1`. -/
lemma sigmaHD_fixed : sigmaHD (√2 - 1) = √2 - 1 := by
  have hu : (√2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow]; congr 1; exact Real.sq_sqrt (by norm_num)
  have hne : (1 : ℂ) + (√2 - 1) ≠ 0 := by
    have : (1 : ℂ) + (√2 - 1) = ((√2 : ℝ) : ℂ) := by ring
    rw [this]; exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  unfold sigmaHD
  rw [div_eq_iff hne]
  linear_combination (-1 : ℂ) * hu

/-- `u(iy) = (1 - y)/(1 + y)`, hence `ζ(iy) = ((1-y)/(1+y))²` (`y ≠ -1`). -/
lemma zetaHD_imag {y : ℝ} (hy : y ≠ -1) :
    zetaHD ((y : ℂ) * Complex.I) = (((1 - y) / (1 + y) : ℝ) : ℂ) ^ 2 := by
  have h : (1 : ℝ) + y ≠ 0 := fun h => hy (by linarith)
  have hc : (1 : ℂ) + (y : ℂ) ≠ 0 := by exact_mod_cast h
  unfold zetaHD uHD
  have e1 : Complex.I - (y : ℂ) * Complex.I = Complex.I * (1 - y) := by ring
  have e2 : Complex.I + (y : ℂ) * Complex.I = Complex.I * (1 + y) := by ring
  rw [e1, e2, mul_div_mul_left _ _ Complex.I_ne_zero]
  push_cast
  rfl

/-- `σ(iy) = e^{-2i arctan y}` (`cts:sigma`): the saddle correspondence is the involution of `Ω`. -/
theorem sigmaHD_imag (y : ℝ) :
    sigmaHD ((y : ℂ) * Complex.I) = Complex.exp (-((2 * Real.arctan y : ℝ) : ℂ) * Complex.I) := by
  set s : ℝ := √(1 + y ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hcos : Real.cos (Real.arctan y) = 1 / s := by rw [Real.cos_arctan]
  have hsin : Real.sin (Real.arctan y) = y / s := by rw [Real.sin_arctan]
  have hE : Complex.exp ((Real.arctan y : ℂ) * Complex.I) = (1 + (y : ℂ) * Complex.I) / (s : ℂ) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    push_cast
    field_simp
  have hexp : Complex.exp (-((2 * Real.arctan y : ℝ) : ℂ) * Complex.I) =
      (Complex.exp ((Real.arctan y : ℂ) * Complex.I) * Complex.exp ((Real.arctan y : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_add, ← Complex.exp_neg]
    congr 1; push_cast; ring
  rw [hexp, hE]
  have hsc : (s : ℂ) ^ 2 = 1 + (y : ℂ) ^ 2 := by exact_mod_cast hs2
  have hne : (1 + (y : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hne2 : (1 - (y : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  unfold sigmaHD
  field_simp
  have hI := Complex.I_sq
  linear_combination (-1 : ℂ) * hsc + (-(y : ℂ) ^ 2) * hI

/-- `arctan(2y/(1-y²)) = 2 arctan y` for `0 ≤ y < 1`. -/
lemma arctan_two_mul_div {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Real.arctan (2 * y / (1 - y ^ 2)) = 2 * Real.arctan y := by
  have h : y * y < 1 := by nlinarith only [hy0, hy1]
  have := Real.arctan_add h
  rw [show 2 * y / (1 - y ^ 2) = (y + y) / (1 - y * y) by ring, ← this]
  ring

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaHD_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaHD_bijOn

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaHD_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaHD_sigma

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sigmaHD_sigmaHD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sigmaHD_sigmaHD

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sigmaHD_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sigmaHD_imag

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaHD_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaHD_conj

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sigmaHD_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sigmaHD_fixed
