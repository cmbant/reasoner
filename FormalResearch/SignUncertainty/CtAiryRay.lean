module

public import FormalResearch.SignUncertainty.CtAiryId

/-!
# The ray form of the complex Airy identities

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 1,
`(ct:airy-id1)` and `(ct:airy-id2)`.  **Proved.**

With `w = e^{iπ/6} t` on the ray `e^{iπ/6}ℝ₊` (`dw = e^{iπ/6} dt`) and `κ = 2^{2/3}`, for real `u`:

* `airy_id1`: `-π^{-1/2} Re ∫ e^{iπ/4} w^{1/2} e^{i(κuw + w³/3)} dw = -π (Ai Bi)'(u)`;
* `airy_id2`: `-π^{-1/2} Re ∫ e^{iπ/4} w^{1/2} (w² + κu) e^{i(κuw + w³/3)} dw = 2^{-1/3} π Ai(u) Bi(u)`.

Each is the substitution `w = e^{iπ/6}t` (the integrand becomes `i t^{1/2} e^{αut - t³/3}`, resp.
`i e^{iπ/3} t^{1/2}(t² - αu) e^{αut - t³/3}`) followed by `G_eq_HH`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.Special

namespace FormalResearch.SignUncertainty.CtAiry

/-- The point `w = e^{iπ/6} t` of the ray. -/
noncomputable def rayPt (t : ℝ) : ℂ := Complex.exp (Complex.I * (π / 6 : ℝ)) * (t : ℂ)

lemma exp_pi_six : Complex.exp (Complex.I * (π / 6 : ℝ)) = ⟨√3 / 2, 1 / 2⟩ := by
  apply Complex.ext
  · simp [Complex.exp_re, Real.cos_pi_div_six, Complex.mul_re]
  · simp [Complex.exp_im, Real.sin_pi_div_six, Complex.mul_re]

lemma exp_I_half_pi : Complex.exp (Complex.I * (π / 2 : ℝ)) = Complex.I := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma rayPt_cube (t : ℝ) : rayPt t ^ 3 = Complex.I * (t : ℂ) ^ 3 := by
  unfold rayPt
  rw [mul_pow, ← Complex.exp_nat_mul]
  have : (3 : ℕ) * (Complex.I * (π / 6 : ℝ)) = Complex.I * (π / 2 : ℝ) := by
    push_cast; ring
  rw [this, exp_I_half_pi]

lemma rayPt_sq (t : ℝ) : rayPt t ^ 2 = Complex.exp (Complex.I * (π / 3 : ℝ)) * (t : ℂ) ^ 2 := by
  unfold rayPt
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 2
  push_cast; ring

lemma rayPt_sqrt {t : ℝ} (ht : 0 < t) :
    rayPt t ^ (1 / 2 : ℂ) = Complex.exp (Complex.I * (π / 12 : ℝ)) * ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  unfold rayPt
  have hne : Complex.exp (Complex.I * (π / 6 : ℝ)) ≠ 0 := Complex.exp_ne_zero _
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [mul_comm, Complex.cpow_def_of_ne_zero (mul_ne_zero htc hne),
    Complex.log_ofReal_mul ht hne,
    Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos]),
    Complex.ofReal_cpow ht.le, Complex.cpow_def_of_ne_zero htc, ← Complex.exp_add]
  push_cast
  rw [Complex.ofReal_log ht.le]
  congr 1
  ring

/-- `κ = 2^{2/3}`. -/
noncomputable def kap : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ)

lemma kap_eq : kap = 2 * rr := by
  unfold kap
  have h : (2 : ℝ) ^ (2 / 3 : ℝ) = s2 ^ (2 : ℤ) := two_rpow (by norm_num)
  rw [h, zpow_ofNat, rr_eq]
  have := s2_cube
  have hs := s2_pos
  field_simp
  nlinarith [this]

lemma exp_pi_three : Complex.exp (Complex.I * (π / 3 : ℝ)) = ⟨1 / 2, √3 / 2⟩ := by
  apply Complex.ext
  · simp [Complex.exp_re, Real.cos_pi_div_three, Complex.mul_re]
  · simp [Complex.exp_im, Real.sin_pi_div_three, Complex.mul_re]

lemma K1 : Complex.exp (Complex.I * (π / 4 : ℝ)) * Complex.exp (Complex.I * (π / 12 : ℝ)) *
    Complex.exp (Complex.I * (π / 6 : ℝ)) = Complex.I := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  refine Eq.trans ?_ exp_I_half_pi
  congr 1
  push_cast; ring

lemma K2 : Complex.I * (kap : ℂ) * Complex.exp (Complex.I * (π / 6 : ℝ)) = al := by
  rw [exp_pi_six, kap_eq]
  apply Complex.ext <;> simp [al, Complex.mul_re, Complex.mul_im] <;> ring

lemma K3 : Complex.exp (Complex.I * (π / 3 : ℝ)) * al = -(kap : ℂ) := by
  rw [exp_pi_three, kap_eq]
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [al, Complex.mul_re]; nlinarith [h3, rr_pos]
  · simp [al, Complex.mul_im]; ring

/-- The integrand of `(ct:airy-id1)` along the ray, as a function of `t`. -/
noncomputable def ray1 (u t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (π / 4 : ℝ)) * rayPt t ^ (1 / 2 : ℂ) *
    Complex.exp (Complex.I * ((kap : ℂ) * u * rayPt t + rayPt t ^ 3 / 3)) *
    Complex.exp (Complex.I * (π / 6 : ℝ))

/-- The integrand of `(ct:airy-id2)` along the ray. -/
noncomputable def ray2 (u t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (π / 4 : ℝ)) * rayPt t ^ (1 / 2 : ℂ) * (rayPt t ^ 2 + (kap : ℂ) * u) *
    Complex.exp (Complex.I * ((kap : ℂ) * u * rayPt t + rayPt t ^ 3 / 3)) *
    Complex.exp (Complex.I * (π / 6 : ℝ))

lemma phase_ray (u t : ℝ) :
    Complex.I * ((kap : ℂ) * u * rayPt t + rayPt t ^ 3 / 3) = al * u * t - (t : ℂ) ^ 3 / 3 := by
  rw [rayPt_cube]
  unfold rayPt
  rw [← K2]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((t : ℂ) ^ 3 / 3) * this

lemma ray1_eq {t : ℝ} (ht : 0 < t) (u : ℝ) : ray1 u t = Complex.I * gF (1 / 2) u t := by
  unfold ray1 gF
  rw [rayPt_sqrt ht, phase_ray]
  have := K1
  linear_combination (((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (al * u * t - (t : ℂ) ^ 3 / 3)) * this

lemma ray2_eq {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ray2 u t = Complex.I * Complex.exp (Complex.I * (π / 3 : ℝ)) *
      (gF (5 / 2) u t - al * u * gF (1 / 2) u t) := by
  unfold ray2 gF
  rw [rayPt_sqrt ht, phase_ray, rayPt_sq]
  have h5 : ((t ^ (5 / 2 : ℝ) : ℝ) : ℂ) = ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ 2 := by
    rw [show (5 / 2 : ℝ) = 1 / 2 + (2 : ℕ) by norm_num, Real.rpow_add ht, Real.rpow_natCast]
    push_cast; ring
  rw [h5]
  have k1 := K1
  have k3 := K3
  set E3 := Complex.exp (Complex.I * (π / 3 : ℝ))
  set E := Complex.exp (al * u * t - (t : ℂ) ^ 3 / 3)
  set S := ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  linear_combination (S * E * (E3 * (t : ℂ) ^ 2 + (kap : ℂ) * u)) * k1 +
    (Complex.I * S * E * u) * k3

lemma integral_ray1 (u : ℝ) : ∫ t in Ioi (0 : ℝ), ray1 u t = Complex.I * gI (1 / 2) u := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => ray1_eq ht u), integral_const_mul]
  rfl

lemma integral_ray2 (u : ℝ) :
    ∫ t in Ioi (0 : ℝ), ray2 u t = -(Complex.I * kap / 2) * gI (-1 / 2) u / al := by
  have a1 := gF_integrable (p := 1 / 2) (by norm_num) u
  have a3 := gF_integrable (p := 5 / 2) (by norm_num) u
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => ray2_eq ht u), integral_const_mul,
    integral_sub a3 (a1.const_mul _), integral_const_mul]
  have hi := gI_ibp u
  have h5 : gI (5 / 2) u - al * u * gI (1 / 2) u = (1 / 2 : ℂ) * gI (-1 / 2) u := by
    linear_combination -hi
  have k3 := K3
  change Complex.I * Complex.exp (Complex.I * (π / 3 : ℝ)) *
    (gI (5 / 2) u - al * u * gI (1 / 2) u) = _
  rw [h5]
  field_simp [al_ne]
  rw [show (-(1 / 2) : ℝ) = -1 / 2 by norm_num]
  linear_combination (gI (-1 / 2) u) * k3

/-- **`(ct:airy-id1)`**: `-π^{-1/2} Re ∫_{e^{iπ/6}ℝ₊} e^{iπ/4} w^{1/2} e^{i(κuw + w³/3)} dw
= -π (Ai Bi)'(u)`, `κ = 2^{2/3}`, `u ∈ ℝ`, parametrised by `w = e^{iπ/6} t`, `dw = e^{iπ/6} dt`. -/
theorem airy_id1 (u : ℝ) :
    -(1 / √π) * (∫ t in Ioi (0 : ℝ), ray1 u t).re =
      -π * (airyAi' u * airyBi u + airyAi u * airyBiDeriv u) := by
  rw [integral_ray1]
  have h1 : gI (1 / 2) u = (√π : ℝ) * G1 u := by
    unfold G1
    field_simp [sqrtpi_ne]
  rw [h1, (G_eq_HH u).2.1]
  have hq : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  unfold HH1
  simp [Complex.mul_re, Complex.mul_im]
  field_simp

/-- **`(ct:airy-id2)`**: the same with the extra factor `w² + κu`; the value is
`2^{-1/3} π Ai(u) Bi(u)`. -/
theorem airy_id2 (u : ℝ) :
    -(1 / √π) * (∫ t in Ioi (0 : ℝ), ray2 u t).re =
      (2 : ℝ) ^ (-(1 / 3) : ℝ) * π * (airyAi u * airyBi u) := by
  rw [integral_ray2]
  have h1 : gI (-1 / 2) u = al * (√π : ℝ) * G0 u := by
    unfold G0
    field_simp [sqrtpi_ne, al_ne]
  rw [h1, (G_eq_HH u).1]
  have hq : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  have : -(Complex.I * kap / 2) * (al * (√π : ℝ) * HH0 u) / al =
      -(Complex.I * kap / 2) * (√π : ℝ) * HH0 u := by
    field_simp [al_ne]
  rw [this]
  unfold HH0
  rw [kap_eq]
  show _ = rr * π * _
  simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  field_simp

/-- info: 'FormalResearch.SignUncertainty.CtAiry.airy_id1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_id1

/-- info: 'FormalResearch.SignUncertainty.CtAiry.airy_id2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_id2

end FormalResearch.SignUncertainty.CtAiry
