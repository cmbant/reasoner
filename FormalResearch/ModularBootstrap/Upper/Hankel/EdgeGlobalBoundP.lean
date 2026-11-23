module

public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeRepresentationP
public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelOrderPAsym
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBound

/-!
# Lemma `FW-SD` (1): global transform bound of order `p`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Lemma `FW-SD` (`fw:SDp`), item (1), `fw:e1.3`,
proved "by the proof of `esd:global` with the uniform large-argument bound
`|H_p¹(k_x b)| ≤ C_p (k_x |b|)^{-1/2} e^{-k_x/2}` and `|b/x|^p ≤ C_p (1 + |v|)^p`".

Assume `EdgeHankelHyp h a C` and `‖h(v + i/2)‖ ≤ C_E ‖sech²(π(v + i/2)/2)‖` on `E₊`, `L(x) = 2π x/3`.  For
every `p` there is an absolute constant `K = K_p` (independent of `h`, `a`, `C`, `C_E`, `c'`, `x`) with

`e^{c' L(x)} ‖(𝓗_{p+1} h)(c' x²/3)‖ ≤ K C_E √(c'/x) x^{-p}`  whenever `4π c' x/3 ≥ 1`   (`edge_global_bound_P`),
`e^{c' L(x)} ‖(𝓗_{p+1} h)(c' x²/3)‖ ≤ K' C_E √c'`  for `x ≥ ξ_*/2` and `c' ≥ 3/(2π ξ_*)`
(`edge_global_bound_P_xiStar`, the form `fw:e1.3` with "for large `c'`").

The condition `4π c' x/3 ≥ 1` (`|k b| ≥ 1/2` on `E₊`) is the range of the order-`p` large-argument bound
`exists_norm_hankelOrd_le`; unlike order `0` the Hankel function is not bounded by `|z|^{-1/2}` near `0`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-- The absolute constant `∫ 8 (1+|v|)^{p+1} e^{-π|v|} dv`. -/
noncomputable def sechConstP (p : ℕ) : ℝ :=
  ∫ v : ℝ, 8 * ((1 + |v|) ^ (p + 1) * Real.exp (-π * |v|))

lemma integrable_sechP_weight (p : ℕ) :
    Integrable (fun v : ℝ => 8 * ((1 + |v|) ^ (p + 1) * Real.exp (-π * |v|))) :=
  (integrable_pow_mul_exp_neg_abs (p + 1) Real.pi_pos).const_mul 8

lemma sechConstP_nonneg (p : ℕ) : 0 ≤ sechConstP p :=
  integral_nonneg fun v => by positivity

lemma norm_edge_point_rpow_le (v : ℝ) : ‖(v : ℂ) + I / 2‖ ^ (1 / 2 : ℝ) ≤ 1 + |v| := by
  have h1 := norm_edge_point_le v
  have h0 : 0 ≤ ‖(v : ℂ) + I / 2‖ := norm_nonneg _
  have h2 : ‖(v : ℂ) + I / 2‖ ^ (1 / 2 : ℝ) ≤ (1 + |v|) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow h0 h1 (by norm_num)
  have h3 : (1 + |v|) ^ (1 / 2 : ℝ) ≤ (1 + |v|) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by norm_num)
  rw [Real.rpow_one] at h3
  exact h2.trans h3

/-- **Lemma `FW-SD` (1)**, `fw:e1.3`: `e^{c' L(x)} ‖𝓗_{p+1}h(c' x²/3)‖ ≤ K_p C_E √(c'/x) x^{-p}` whenever
`k = 4π c' x/3 ≥ 1`, with `K_p` depending only on `p`. -/
theorem edge_global_bound_P (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℂ → ℂ) (a C C_E : ℝ), 0 < a → EdgeHankelHyp h a C → 0 ≤ C_E →
      EdgeSechBound h C_E → ∀ c' x : ℝ, 0 < c' → 0 < x → 1 ≤ 4 * π * c' * x / 3 →
        Real.exp (c' * edgeL x) * ‖edgeHankelP p c' h (c' * x ^ 2 / 3)‖ ≤
          K * C_E * √(c' / x) * (1 / x) ^ p := by
  obtain ⟨Cp, hCp0, hCp⟩ := exists_norm_hankelOrd_le p
  refine ⟨(2 * π / 3) * Cp * √(3 / (4 * π)) * sechConstP p, by
    have := sechConstP_nonneg p; positivity, ?_⟩
  intro h a C C_E ha hh hCE hsech c' x hc hx hk1
  set k : ℝ := 4 * π * c' * x / 3 with hkdef
  have hk : 0 < k := by positivity
  have hrep := edge_hankel_representation_P ha hh p hc hx
  have hpt : ∀ v : ℝ, ‖edgeIntegrandP p c' h x v‖ ≤
      C_E * Cp * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) * (1 / x) ^ p *
        (8 * ((1 + |v|) ^ (p + 1) * Real.exp (-π * |v|))) := by
    intro v
    set b : ℂ := (v : ℂ) + I / 2 with hb
    have hbim : b.im = 1 / 2 := by simp [hb]
    have hbre : b.re = v := by simp [hb]
    have hb0 : b ≠ 0 := by intro h0; rw [h0] at hbim; simp at hbim
    have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    have hbn2 : 1 / 2 ≤ ‖b‖ := by
      have := Complex.abs_im_le_norm b
      rw [hbim, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      exact this
    have hkb : 0 < ((k : ℂ) * b).im := by
      rw [Complex.im_ofReal_mul, hbim]; positivity
    have hkn : ‖(k : ℂ) * b‖ = k * ‖b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le]
    have hkn2 : 1 / 2 ≤ ‖(k : ℂ) * b‖ := by
      rw [hkn]; nlinarith
    have hH := hCp ((k : ℂ) * b) hkb hkn2
    rw [hkn, Complex.im_ofReal_mul, hbim] at hH
    have hhb : ‖h b‖ ≤ C_E * (8 * Real.exp (-π * |v|)) :=
      (hsech v).trans (mul_le_mul_of_nonneg_left (sech_sq_le v) hCE)
    have hpow : ‖(b / (x : ℂ)) ^ p‖ ≤ (1 + |v|) ^ p * (1 / x) ^ p := by
      rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hx.le, ← mul_pow, one_div,
        ← div_eq_mul_inv]
      gcongr
      exact norm_edge_point_le v
    have hsq : ‖b‖ ^ (1 / 2 : ℝ) ≤ 1 + |v| := norm_edge_point_rpow_le v
    have hkb' : (k * ‖b‖) ^ (-(1 / 2 : ℝ)) * ‖b‖ = k ^ (-(1 / 2 : ℝ)) * ‖b‖ ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow hk.le hbn.le]
      have : ‖b‖ ^ (1 / 2 : ℝ) = ‖b‖ ^ (-(1 / 2 : ℝ)) * ‖b‖ := by
        rw [← Real.rpow_add_one hbn.ne']; norm_num
      rw [this]; ring
    have hk12 : 0 < k ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hk _
    unfold edgeIntegrandP
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖h b‖ * ‖(b / (x : ℂ)) ^ p‖ * ‖hankelOrd p ((k : ℂ) * b)‖ * ‖b‖
        ≤ (C_E * (8 * Real.exp (-π * |v|))) * ((1 + |v|) ^ p * (1 / x) ^ p) *
          (Cp * (k * ‖b‖) ^ (-(1 / 2 : ℝ)) * Real.exp (-(k * (1 / 2)))) * ‖b‖ := by gcongr
      _ = C_E * Cp * Real.exp (-(k * (1 / 2))) * (1 / x) ^ p * (8 * Real.exp (-π * |v|)) *
          (1 + |v|) ^ p * ((k * ‖b‖) ^ (-(1 / 2 : ℝ)) * ‖b‖) := by ring
      _ = C_E * Cp * Real.exp (-(k * (1 / 2))) * (1 / x) ^ p * (8 * Real.exp (-π * |v|)) *
          (1 + |v|) ^ p * (k ^ (-(1 / 2 : ℝ)) * ‖b‖ ^ (1 / 2 : ℝ)) := by rw [hkb']
      _ ≤ C_E * Cp * Real.exp (-(k * (1 / 2))) * (1 / x) ^ p * (8 * Real.exp (-π * |v|)) *
          (1 + |v|) ^ p * (k ^ (-(1 / 2 : ℝ)) * (1 + |v|)) := by gcongr
      _ = _ := by rw [show -(k * (1 / 2)) = -(k / 2) by ring, pow_succ]; ring
  have hB : Integrable (fun v : ℝ => C_E * Cp * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) * (1 / x) ^ p *
      (8 * ((1 + |v|) ^ (p + 1) * Real.exp (-π * |v|)))) := (integrable_sechP_weight p).const_mul _
  have hint : ‖edgeIntegralP p c' h x‖ ≤
      C_E * Cp * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) * (1 / x) ^ p * sechConstP p := by
    calc _ ≤ ∫ v : ℝ, ‖edgeIntegrandP p c' h x v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, C_E * Cp * k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) * (1 / x) ^ p *
          (8 * ((1 + |v|) ^ (p + 1) * Real.exp (-π * |v|))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) hB
            (Filter.Eventually.of_forall hpt)
      _ = _ := by rw [integral_const_mul]; rfl
  have hnorm : ‖edgeHankelP p c' h (c' * x ^ 2 / 3)‖ ≤ (2 * π * c' / 3) * (C_E * Cp *
      k ^ (-(1 / 2 : ℝ)) * Real.exp (-(k / 2)) * (1 / x) ^ p * sechConstP p) := by
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
  calc Real.exp (k / 2) * ‖edgeHankelP p c' h (c' * x ^ 2 / 3)‖
      ≤ Real.exp (k / 2) * ((2 * π * c' / 3) * (C_E * Cp * k ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(k / 2)) * (1 / x) ^ p * sechConstP p)) :=
        mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = (2 * π / 3) * Cp * (c' * k ^ (-(1 / 2 : ℝ))) * sechConstP p * C_E * (1 / x) ^ p *
        (Real.exp (k / 2) * Real.exp (-(k / 2))) := by ring
    _ = _ := by rw [hexp, hck]; ring

/-- **Lemma `FW-SD` (1)** in the stated form `fw:e1.3`: for `x ≥ ξ_*/2` and `c' ≥ 3/(2π ξ_*)`,
`e^{c' L(x)} ‖𝓗_{p+1}h(c' x²/3)‖ ≤ K'_p C_E √c'`. -/
theorem edge_global_bound_P_xiStar (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℂ → ℂ) (a C C_E : ℝ), 0 < a → EdgeHankelHyp h a C → 0 ≤ C_E →
      EdgeSechBound h C_E → ∀ c' x : ℝ, 3 / (2 * π * xiStar) ≤ c' → xiStar / 2 ≤ x →
        Real.exp (c' * edgeL x) * ‖edgeHankelP p c' h (c' * x ^ 2 / 3)‖ ≤ K * C_E * √c' := by
  obtain ⟨K, hK0, hK⟩ := edge_global_bound_P p
  have hxi := xiStar_pos
  refine ⟨K * √(2 / xiStar) * (2 / xiStar) ^ p, by positivity, ?_⟩
  intro h a C C_E ha hh hCE hsech c' x hc hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hc0 : 0 < c' := lt_of_lt_of_le (by positivity) hc
  have hk1 : 1 ≤ 4 * π * c' * x / 3 := by
    have h1 : 3 / (2 * π * xiStar) * (2 * π * xiStar) = 3 := by field_simp
    have h2 : 3 ≤ c' * (2 * π * xiStar) := by
      calc 3 = 3 / (2 * π * xiStar) * (2 * π * xiStar) := h1.symm
        _ ≤ c' * (2 * π * xiStar) := by gcongr
    have h3 : c' * (2 * π * xiStar) ≤ c' * (4 * π * x) := by
      have : 2 * π * xiStar ≤ 4 * π * x := by nlinarith [Real.pi_pos]
      exact mul_le_mul_of_nonneg_left this hc0.le
    nlinarith
  refine (hK h a C C_E ha hh hCE hsech c' x hc0 hx0 hk1).trans ?_
  have h1 : √(c' / x) ≤ √(2 / xiStar) * √c' := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hx0]
    have : 2 / xiStar * c' * x ≥ 2 / xiStar * c' * (xiStar / 2) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    have e : 2 / xiStar * c' * (xiStar / 2) = c' := by field_simp
    linarith
  have h2 : (1 / x) ^ p ≤ (2 / xiStar) ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [div_le_div_iff₀ hx0 hxi]; linarith
  calc K * C_E * √(c' / x) * (1 / x) ^ p
      ≤ K * C_E * (√(2 / xiStar) * √c') * (2 / xiStar) ^ p := by gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edge_global_bound_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_global_bound_P

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edge_global_bound_P_xiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_global_bound_P_xiStar

end FormalResearch.ModularBootstrap.Upper.Hankel
