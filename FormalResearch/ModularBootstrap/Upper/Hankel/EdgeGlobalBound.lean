module

public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeRepresentation
public import FormalResearch.ModularBootstrap.Constants

/-!
# Lemma `SD_G`: global transform bound (order `0`)

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, Lemma `SD_G` (`esd:global`, lines 59--107).

Assume the hypotheses of Lemma `SD_H` (`EdgeHankelHyp`) and
`‖h(v + i/2)‖ ≤ C_E ‖sech²(π(v + i/2)/2)‖` on `E₊`.  With `L(x) = 2π x/3`:

`e^{c' L(x)} ‖ĥ(c' x²/3)‖ ≤ K C_E √(c'/x)`   for every `c' > 0`, `x > 0`   (`edge_global_bound`),
`e^{c' L(x)} ‖ĥ(c' x²/3)‖ ≤ K' C_E √c'`      for every `c' > 0`, `x ≥ ξ_*/2` (`edge_global_bound_xiStar`),

where `K`, `K'` are absolute constants (independent of `h`, `a`, `C`, `C_E`, `c'`, `x`), `ξ_* = xiStar`.
The restriction "all sufficiently large `c'`" and `x ≥ ξ_*/2` of the TeX statement is needed only for the
second form: the uniform bound `‖H₀¹(z)‖ ≤ √(2/π) ‖z‖^{-1/2} e^{-Im z}` holds on the whole open upper
half-plane, so no largeness of `|k b|` is required.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-- `L(x) = 2π x / 3`. -/
noncomputable def edgeL (x : ℝ) : ℝ := 2 * π * x / 3

lemma norm_cosh_sq_ge {b : ℂ} (h0 : 0 ≤ b.im) (h1 : b.im ≤ 1 / 2) :
    (Real.cosh (π * b.re / 2)) ^ 2 / 2 ≤ ‖Complex.cosh (π * b / 2)‖ ^ 2 := by
  have hz : (π : ℂ) * b / 2 = ((π * b.re / 2 : ℝ) : ℂ) + ((π * b.im / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz, cosh_ofReal_add]
  set u : ℝ := π * b.re / 2
  set w : ℝ := π * b.im / 2
  have hw0 : 0 ≤ w := by have := Real.pi_pos; positivity
  have hw1 : w ≤ π / 4 := by have := Real.pi_pos; simp only [w]; nlinarith
  have hcos : 1 / 2 ≤ Real.cos w ^ 2 := by
    have h2 : Real.cos (π / 4) ≤ Real.cos w :=
      Real.cos_le_cos_of_nonneg_of_le_pi hw0 (by linarith [Real.pi_pos]) hw1
    rw [Real.cos_pi_div_four] at h2
    have h3 : 0 ≤ √2 / 2 := by positivity
    have h4 : (√2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, mul_zero, I_im, zero_mul, sub_zero, add_im,
    mul_im, zero_add]
  nlinarith [sq_nonneg (Real.sinh u * Real.sin w), sq_nonneg (Real.cosh u),
    mul_le_mul_of_nonneg_left hcos (sq_nonneg (Real.cosh u)), mul_pow (Real.cosh u) (Real.cos w) 2]

lemma two_div_cosh_sq_le (u : ℝ) : 2 / Real.cosh u ^ 2 ≤ 8 * Real.exp (-2 * |u|) := by
  have hc : Real.exp |u| / 2 ≤ Real.cosh u := by
    rw [Real.cosh_eq]
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]; have := Real.exp_pos (-u); linarith
    · rw [abs_of_nonpos h]; have := Real.exp_pos u; linarith [Real.exp_neg u]
  have hpos : 0 < Real.exp |u| := Real.exp_pos _
  have hcosh2 : Real.exp |u| ^ 2 / 4 ≤ (Real.cosh u) ^ 2 := by nlinarith [hc, hpos]
  have hq : 0 < Real.cosh u ^ 2 := by have := Real.cosh_pos u; positivity
  rw [div_le_iff₀ hq]
  have e1 : Real.exp (-2 * |u|) * Real.exp |u| ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
  have := Real.exp_pos (-2 * |u|)
  nlinarith [hcosh2, e1]

/-- The `sech²` bound on the closed substrip: `1/‖cosh(π b/2)‖² ≤ 8 e^{-π|Re b|}` for `0 ≤ Im b ≤ 1/2`. -/
lemma sech_sq_le_strip {b : ℂ} (h0 : 0 ≤ b.im) (h1 : b.im ≤ 1 / 2) :
    ‖(1 : ℂ) / Complex.cosh (π * b / 2) ^ 2‖ ≤ 8 * Real.exp (-π * |b.re|) := by
  have hge := norm_cosh_sq_ge h0 h1
  have hq : 0 < Real.cosh (π * b.re / 2) ^ 2 / 2 := by have := Real.cosh_pos (π * b.re / 2); positivity
  rw [norm_div, norm_one, norm_pow]
  have h2 := two_div_cosh_sq_le (π * b.re / 2)
  have hu : -2 * |π * b.re / 2| = -π * |b.re| := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]; ring
  rw [hu] at h2
  calc 1 / ‖Complex.cosh (π * b / 2)‖ ^ 2 ≤ 1 / (Real.cosh (π * b.re / 2) ^ 2 / 2) :=
        one_div_le_one_div_of_le hq hge
    _ = 2 / Real.cosh (π * b.re / 2) ^ 2 := by field_simp
    _ ≤ _ := h2

/-- The bound on `‖sech²‖` on `E₊`: `1/‖cosh(π(v + i/2)/2)‖² ≤ 8 e^{-π|v|}`. -/
lemma sech_sq_le (v : ℝ) :
    ‖(1 : ℂ) / Complex.cosh (π * ((v : ℂ) + I / 2) / 2) ^ 2‖ ≤ 8 * Real.exp (-π * |v|) := by
  have := sech_sq_le_strip (b := (v : ℂ) + I / 2) (by simp) (by simp)
  simpa using this

/-- The `sech²` bound on `E₊`: `‖h(v + i/2)‖ ≤ C_E ‖sech²(π(v + i/2)/2)‖`. -/
def EdgeSechBound (h : ℂ → ℂ) (C_E : ℝ) : Prop :=
  ∀ v : ℝ, ‖h ((v : ℂ) + I / 2)‖ ≤ C_E * ‖(1 : ℂ) / Complex.cosh (π * ((v : ℂ) + I / 2) / 2) ^ 2‖

/-- If `h₀ = sech²(π b/2) · B` with `‖B‖ = 1` on `E₊`, the `sech²` bound holds with `C_E = 1`. -/
theorem edgeSechBound_of_unit {B : ℂ → ℂ} (hB : ∀ v : ℝ, ‖B ((v : ℂ) + I / 2)‖ = 1) :
    EdgeSechBound (fun b => (1 : ℂ) / Complex.cosh (π * b / 2) ^ 2 * B b) 1 := by
  intro v
  simp only [norm_mul, hB v, mul_one, one_mul, le_refl]

/-- The absolute constant `∫ 8 e^{-π|v|} (1 + |v|) dv`. -/
noncomputable def sechConst : ℝ := ∫ v : ℝ, 8 * Real.exp (-π * |v|) * (1 + |v|)

lemma integrable_sech_weight : Integrable (fun v : ℝ => 8 * Real.exp (-π * |v|) * (1 + |v|)) := by
  have hint := (integrable_exp_neg_abs (c := π / 2) (by positivity)).const_mul (8 * (1 + 2 / π))
  refine Integrable.mono' hint ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact (by fun_prop : Continuous fun v : ℝ => 8 * Real.exp (-π * |v|) * (1 + |v|)).aestronglyMeasurable
  · have := one_add_mul_exp_le Real.pi_pos |v| (abs_nonneg v)
    rw [Real.norm_of_nonneg (by positivity)]
    calc 8 * Real.exp (-π * |v|) * (1 + |v|) = 8 * (Real.exp (-π * |v|) * (1 + |v|)) := by ring
      _ ≤ 8 * ((1 + 2 / π) * Real.exp (-(π / 2) * |v|)) := by gcongr
      _ = _ := by ring

lemma sechConst_nonneg : 0 ≤ sechConst :=
  integral_nonneg fun v => by positivity

lemma c_mul_rpow_neg_half {c' x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    c' * (4 * π * c' * x / 3) ^ (-(1 / 2 : ℝ)) = √(3 / (4 * π)) * √(c' / x) := by
  have hK : 0 < 4 * π * c' * x / 3 := by positivity
  rw [Real.rpow_neg hK.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
  have e : 3 / (4 * π) * (c' / x) = c' ^ 2 / (4 * π * c' * x / 3) := by
    field_simp
  rw [e, Real.sqrt_div (x := c' ^ 2) (by positivity) (4 * π * c' * x / 3), Real.sqrt_sq hc.le]
  exact (div_eq_mul_inv _ _).symm

/-- **Lemma `SD_G`** (`esd:global`, (SD.G), first inequality): for every `c' > 0`, `x > 0`,
`e^{c' L(x)} ‖ĥ(c' x²/3)‖ ≤ K C_E √(c'/x)` with an absolute constant `K`. -/
theorem edge_global_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℂ → ℂ) (a C C_E : ℝ), 0 < a → EdgeHankelHyp h a C → 0 ≤ C_E →
      EdgeSechBound h C_E → ∀ c' x : ℝ, 0 < c' → 0 < x →
        Real.exp (c' * edgeL x) * ‖edgeHankel c' h (c' * x ^ 2 / 3)‖ ≤ K * C_E * √(c' / x) := by
  refine ⟨(2 * π / 3) * √(2 / π) * √(3 / (4 * π)) * sechConst, by
    have := sechConst_nonneg; positivity, ?_⟩
  intro h a C C_E ha hh hCE hsech c' x hc hx
  set k : ℝ := 4 * π * c' * x / 3 with hkdef
  have hk : 0 < k := by positivity
  have hrep := edge_hankel_representation ha hh hc hx
  -- pointwise bound on the integrand along `E₊`
  have hpt : ∀ v : ℝ, ‖h ((v : ℂ) + I / 2) * hankel0 ((k : ℂ) * ((v : ℂ) + I / 2)) * ((v : ℂ) + I / 2)‖ ≤
      C_E * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) *
        (8 * Real.exp (-π * |v|) * (1 + |v|)) := by
    intro v
    set b : ℂ := (v : ℂ) + I / 2 with hb
    have hbim : b.im = 1 / 2 := by simp [hb]
    have hbre : b.re = v := by simp [hb]
    have hb0 : b ≠ 0 := by intro h0; rw [h0] at hbim; simp at hbim
    have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    have hkb : 0 < ((k : ℂ) * b).im := by
      rw [Complex.im_ofReal_mul, hbim]; positivity
    have hH := norm_hankel0_le hkb
    have hn : ‖(k : ℂ) * b‖ = k * ‖b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le]
    rw [hn, Complex.im_ofReal_mul, hbim] at hH
    have hhb : ‖h b‖ ≤ C_E * (8 * Real.exp (-π * |v|)) :=
      (hsech v).trans (mul_le_mul_of_nonneg_left (sech_sq_le v) hCE)
    have hnb : ‖b‖ ≤ |v| + 1 / 2 := by
      have := Complex.norm_le_abs_re_add_abs_im b
      rw [hbre, hbim, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      exact this
    have hsq : ‖b‖ ^ (1 / 2 : ℝ) ≤ 1 + |v| := by
      refine (Real.rpow_le_rpow hbn.le hnb (by norm_num)).trans ?_
      have := rpow_half_le (y := |v| + 1 / 2) (by positivity)
      linarith [abs_nonneg v]
    have hkb' : (k * ‖b‖) ^ (-(1 / 2 : ℝ)) * ‖b‖ = k ^ (-(1 / 2 : ℝ)) * ‖b‖ ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow hk.le hbn.le]
      have : ‖b‖ ^ (1 / 2 : ℝ) = ‖b‖ ^ (-(1 / 2 : ℝ)) * ‖b‖ := by
        rw [← Real.rpow_add_one hbn.ne']; norm_num
      rw [this]; ring
    have hk12 : 0 < k ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hk _
    have hs2 : 0 ≤ √(2 / π) := Real.sqrt_nonneg _
    rw [norm_mul, norm_mul]
    calc ‖h b‖ * ‖hankel0 ((k : ℂ) * b)‖ * ‖b‖
        ≤ (C_E * (8 * Real.exp (-π * |v|))) * (√(2 / π) * (k * ‖b‖) ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(k * (1 / 2)))) * ‖b‖ := by gcongr
      _ = C_E * √(2 / π) * Real.exp (-(k * (1 / 2))) * (8 * Real.exp (-π * |v|)) *
            ((k * ‖b‖) ^ (-(1 / 2 : ℝ)) * ‖b‖) := by ring
      _ = C_E * √(2 / π) * Real.exp (-(k * (1 / 2))) * (8 * Real.exp (-π * |v|)) *
            (k ^ (-(1 / 2 : ℝ)) * ‖b‖ ^ (1 / 2 : ℝ)) := by rw [hkb']
      _ ≤ C_E * √(2 / π) * Real.exp (-(k * (1 / 2))) * (8 * Real.exp (-π * |v|)) *
            (k ^ (-(1 / 2 : ℝ)) * (1 + |v|)) := by gcongr
      _ = _ := by rw [show -(k * (1 / 2)) = -(k / 2) by ring]; ring
  -- integrate
  have hB : Integrable (fun v : ℝ => C_E * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) *
      (8 * Real.exp (-π * |v|) * (1 + |v|))) := integrable_sech_weight.const_mul _
  have hint : ‖∫ v : ℝ, h ((v : ℂ) + I / 2) * hankel0 ((k : ℂ) * ((v : ℂ) + I / 2)) *
      ((v : ℂ) + I / 2)‖ ≤ C_E * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) * sechConst := by
    calc _ ≤ ∫ v : ℝ, ‖h ((v : ℂ) + I / 2) * hankel0 ((k : ℂ) * ((v : ℂ) + I / 2)) *
          ((v : ℂ) + I / 2)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, C_E * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) *
          (8 * Real.exp (-π * |v|) * (1 + |v|)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) hB
            (Filter.Eventually.of_forall hpt)
      _ = _ := by rw [integral_const_mul]; rfl
  have hnorm : ‖edgeHankel c' h (c' * x ^ 2 / 3)‖ ≤ (2 * π * c' / 3) * (C_E * √(2 / π) *
      k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) * sechConst) := by
    rw [hrep, norm_mul]
    have : ‖(2 * π * c' / 3 : ℂ)‖ = 2 * π * c' / 3 := by
      have : (2 * π * c' / 3 : ℂ) = ((2 * π * c' / 3 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [this]
    exact mul_le_mul_of_nonneg_left hint (by positivity)
  have hLk : c' * edgeL x = k / 2 := by
    unfold edgeL; simp only [hkdef]; ring
  rw [hLk]
  have hexp : Real.exp (k / 2) * Real.exp (-(k / 2)) = 1 := by rw [← Real.exp_add]; simp
  have hck : c' * k ^ (-(1 / 2 : ℝ)) = √(3 / (4 * π)) * √(c' / x) := by
    rw [hkdef]; exact c_mul_rpow_neg_half hc hx
  calc Real.exp (k / 2) * ‖edgeHankel c' h (c' * x ^ 2 / 3)‖
      ≤ Real.exp (k / 2) * ((2 * π * c' / 3) * (C_E * √(2 / π) * k ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(k / 2)) * sechConst)) := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = (2 * π / 3) * √(2 / π) * (c' * k ^ (-(1 / 2 : ℝ))) * sechConst * C_E *
        (Real.exp (k / 2) * Real.exp (-(k / 2))) := by ring
    _ = _ := by rw [hexp, hck]; ring

/-- **Lemma `SD_G`** (`esd:global`, (SD.G), second inequality): for every `c' > 0` and
`x ≥ ξ_*/2` (`ξ_* = xiStar`), `e^{c' L(x)} ‖ĥ(c' x²/3)‖ ≤ K' C_E √c'` with an absolute constant `K'`. -/
theorem edge_global_bound_xiStar :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℂ → ℂ) (a C C_E : ℝ), 0 < a → EdgeHankelHyp h a C → 0 ≤ C_E →
      EdgeSechBound h C_E → ∀ c' x : ℝ, 0 < c' → xiStar / 2 ≤ x →
        Real.exp (c' * edgeL x) * ‖edgeHankel c' h (c' * x ^ 2 / 3)‖ ≤ K * C_E * √c' := by
  obtain ⟨K, hK0, hK⟩ := edge_global_bound
  have hxi := xiStar_pos
  refine ⟨K * √(2 / xiStar), by positivity, ?_⟩
  intro h a C C_E ha hh hCE hsech c' x hc hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  refine (hK h a C C_E ha hh hCE hsech c' x hc hx0).trans ?_
  have h1 : √(c' / x) ≤ √(2 / xiStar) * √c' := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hx0]
    have : 2 / xiStar * c' * x ≥ 2 / xiStar * c' * (xiStar / 2) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    have e : 2 / xiStar * c' * (xiStar / 2) = c' := by field_simp
    linarith
  calc K * C_E * √(c' / x) ≤ K * C_E * (√(2 / xiStar) * √c') :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- `edge_global_bound` and `edge_global_bound_xiStar` with the reference sech² profile: for
`h₀ = sech²(π b/2) B(b)` with `|B| = 1` on `E₊`, one may take `C_E = 1`. -/
theorem edge_global_bound_unit {B : ℂ → ℂ} (hB : ∀ v : ℝ, ‖B ((v : ℂ) + I / 2)‖ = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a C : ℝ), 0 < a →
      EdgeHankelHyp (fun b => (1 : ℂ) / Complex.cosh (π * b / 2) ^ 2 * B b) a C →
      ∀ c' x : ℝ, 0 < c' → 0 < x →
        Real.exp (c' * edgeL x) *
          ‖edgeHankel c' (fun b => (1 : ℂ) / Complex.cosh (π * b / 2) ^ 2 * B b) (c' * x ^ 2 / 3)‖ ≤
            K * √(c' / x) := by
  obtain ⟨K, hK0, hK⟩ := edge_global_bound
  refine ⟨K, hK0, fun a C ha hh c' x hc hx => ?_⟩
  simpa using hK _ a C 1 ha hh zero_le_one (edgeSechBound_of_unit hB) c' x hc hx

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edge_global_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_global_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edge_global_bound_xiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_global_bound_xiStar

end FormalResearch.ModularBootstrap.Upper.Hankel
