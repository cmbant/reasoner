module

public import FormalResearch.ModularBootstrap.Upper.Design.CombTransform
public import FormalResearch.ModularBootstrap.Upper.Holes.HoleLimit
public import FormalResearch.ModularBootstrap.Upper.Holes.K8

/-!
# Proposition II, step (1): the transform amplitude against the reference level

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition II (`ut:II`), proof step (1).

For `x` to the right of the node `χ_{f+1/2}` of the index-`f` reference comb, the comb-independent
transform amplitude `𝒜_x` of `(SD.4)` (`combAmplitude`, `Upper.Design.CombTransform`) is bounded by
the level `Lev^{(f)}` (`levComb`, `Upper.Holes.HoleLimit`) times the Region-II saddle ratio
`vρ∞(x; n₁)` of Lemma `K8` (`vRhoInfty`), with `n₁ = f - 1/4`:

`𝒜_x ≤ vρ∞(x; n₁) · Lev^{(f)}(x) ≤ (55/100) · Lev^{(f)}(x)`.

* `edgeV_eq_vZeroK8`, `edgeF'_edgeV_eq_edgeDerivK8`: the saddle `v_x` and the edge slope `F'(v_x)` of
  `Upper.Saddle` coincide with the closed forms `v_0`, `F'(v_0)` of `Upper.Holes.K8`.
* `norm_sechSq_bX`: `|sech²(π b_x/2)| = 2 / sinh(π x)` for `b_x = v_x + i/2`.
* `combAmplitude_le_vRhoInfty_mul_levComb`: the displayed bound, with the `(SD.4)` amplitude
  evaluated exactly: `‖1 + ε_H‖ ≤ 1` replaces the paper's `1 + O(1/c')`.
* `combAmplitude_le_levComb_frac`: the rational form `𝒜_x ≤ (55/100) Lev^{(f)}`.

All results are proved unconditionally.
-/

@[expose] public section

open Real
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes

/-! ### 1. The saddle and the edge slope in closed form -/

lemma arccoshR_eq_arcosh {s : ℝ} (hs : 1 ≤ s) : arccoshR s = Real.arcosh s := by
  have h1 : Real.cosh (arccoshR s) = s := cosh_arccoshR hs
  have h2 : Real.cosh (Real.arcosh s) = s := Real.cosh_arcosh hs
  have hn1 : 0 ≤ arccoshR s := arccoshR_nonneg hs
  have hn2 : 0 ≤ Real.arcosh s := Real.arcosh_nonneg hs
  exact Real.cosh_strictMonoOn.injOn hn1 hn2 (h1.trans h2.symm)

lemma edgeV_eq_vZeroK8 {x : ℝ} (hx : xiStar < x) : edgeV x = vZeroK8 x := by
  unfold edgeV vZeroK8
  rw [arccoshR_eq_arcosh (one_lt_sinh_pi_mul hx).le]

lemma cosh_pi_edgeV {x : ℝ} (hx : xiStar < x) : Real.cosh (π * edgeV x) = Real.sinh (π * x) := by
  unfold edgeV
  rw [mul_div_cancel₀ _ Real.pi_pos.ne']
  exact Real.cosh_arcosh (one_lt_sinh_pi_mul hx).le

lemma edgeF'_edgeV_eq_edgeDerivK8 {x : ℝ} (hx : xiStar < x) : edgeF' (edgeV x) = edgeDerivK8 x := by
  have hs1 : 1 < Real.sinh (π * x) := one_lt_sinh_pi_mul hx
  have hv := edgeV_pos hx
  have hch := cosh_pi_edgeV hx
  have hsq : Real.sinh (π * edgeV x) ^ 2 = Real.sinh (π * x) ^ 2 - 1 := by
    have := Real.cosh_sq_sub_sinh_sq (π * edgeV x)
    rw [hch] at this
    linarith
  have hsp : 0 < Real.sinh (π * edgeV x) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hv)
  have hcx : Real.cosh (π * x) ^ 2 = 1 + Real.sinh (π * x) ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq (π * x)
    linarith
  have hnum : Real.sinh (π * edgeV x) = √(Real.sinh (π * x) ^ 2 - 1) := by
    rw [← hsq]; exact (Real.sqrt_sq hsp.le).symm
  unfold edgeF' edgeDerivK8
  rw [hch, hnum]
  have hpos1 : 0 < 1 + Real.sinh (π * x) ^ 2 := by positivity
  have hid : 1 - 2 / Real.cosh (π * x) ^ 2 =
      (Real.sinh (π * x) ^ 2 - 1) / (1 + Real.sinh (π * x) ^ 2) := by
    rw [hcx]; field_simp; ring
  rw [hid, Real.sqrt_div' _ hpos1.le]

/-! ### 2. The modulus of `sech²(π b_x / 2)` -/

lemma norm_cosh_bX_sq (v : ℝ) :
    ‖Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2) / 2)‖ ^ 2 = Real.cosh (π * v) / 2 := by
  have hz : (π : ℂ) * ((v : ℂ) + Complex.I / 2) / 2 =
      ((π * v / 2 : ℝ) : ℂ) + ((π / 4 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp; ring
  rw [hz, cosh_ofReal_add, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    mul_zero, Complex.I_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im, zero_add]
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : Real.cosh (π * v) = Real.cosh (π * v / 2) ^ 2 + Real.sinh (π * v / 2) ^ 2 := by
    rw [← Real.cosh_two_mul]; congr 1; ring
  have h3 : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [h2]
  nlinarith [h3]

lemma norm_sechSq_bX {x : ℝ} (hx : xiStar < x) :
    ‖sechSqProfile (bX x)‖ = 2 / Real.sinh (π * x) := by
  unfold sechSqProfile bX
  rw [norm_div, norm_one, norm_pow, norm_cosh_bX_sq, cosh_pi_edgeV hx]
  have : 0 < Real.sinh (π * x) := by linarith [one_lt_sinh_pi_mul hx]
  field_simp

lemma norm_bX (x : ℝ) : ‖bX x‖ = √(edgeV x ^ 2 + 1 / 4) := by
  have h : bX x = (edgeV x : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I := by
    unfold bX; push_cast; ring
  rw [h, Complex.norm_add_mul_I]
  congr 1; norm_num

/-! ### 3. The amplitude against the level -/

lemma combAmplitude_eq {c' x : ℝ} (hx : xiStar < x) :
    combAmplitude c' x = 2 * Real.exp (-2 * π * c' * x / 3) * (2 / Real.sinh (π * x)) *
      ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ *
      √(√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) := by
  unfold combAmplitude sdvPrefactor
  rw [norm_sechSq_bX hx, norm_bX, edgeF'_edgeV_eq_edgeDerivK8 hx, edgeV_eq_vZeroK8 hx]
  simp

lemma norm_one_add_hankelEps_bX_le {c' x : ℝ} (hc' : 0 < c') (hx : xiStar < x) :
    ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ ≤ 1 := by
  have hx0 : 0 < x := xiStar_pos.trans hx
  have hk : 0 < sdvWave c' x := by unfold sdvWave; positivity
  apply norm_one_add_hankelEps_le
  rw [Complex.im_ofReal_mul]
  have : (bX x).im = 1 / 2 := by simp [bX]
  rw [this]; positivity

/-- The `exp(c' P^{(f)} + J_end^{(f)})` factor of the level dominates `T(x)^{-2 n₁}`. -/
lemma exp_combPf_jEnd_ge {c' x : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f)
    (hx : chiQuantile c' ((f : ℝ) + 1 / 2) < x) :
    1 ≤ tanhTipK8 x ^ (2 * n1Comb f) * Real.exp (c' * combPf c' f x + jEndComb c' x f) := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hχf : chiQuantile c' (f : ℝ) < x :=
    (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))
      (by linarith : (f : ℝ) < (f : ℝ) + 1 / 2)).trans hx
  have hxi : xiStar < x := (xiStar_lt_chiQuantile hc' (by linarith)).trans hχf
  have hx0 : 0 ≤ x := xiStar_pos.le.trans hxi.le
  obtain ⟨hlow, -, -⟩ := combPf_bounds_K4 hc' hf hχf
  obtain ⟨hJ, -⟩ := jEndComb_bounds hc' hf hx
  have h1 : 0 < Real.tanh (π * (x - xiStar) / 2) :=
    tanh_pos_of_pos (by have := Real.pi_pos; nlinarith)
  have h2 : 0 < Real.tanh (π * (x + xiStar) / 2) :=
    tanh_pos_of_pos (by have := Real.pi_pos; have := xiStar_pos; nlinarith)
  have hT : 0 < tanhTipK8 x := mul_pos h1 h2
  have hlogT : realLogT x xiStar = Real.log (tanhTipK8 x) := by
    unfold realLogT tanhTipK8
    rw [norm_blaschkeT_ofReal, abs_of_pos (mul_pos h1 h2), Real.log_mul h1.ne' h2.ne']
  rw [hlogT] at hlow
  rw [Real.rpow_def_of_pos hT, ← Real.exp_add]
  apply Real.one_le_exp
  nlinarith

lemma levComb_pos (c' : ℝ) (f : ℕ) (x : ℝ) : 0 < levComb c' f x := by
  unfold levComb
  exact mul_pos (mul_pos (by norm_num) (div_pos one_pos (sq_pos_of_pos (Real.cosh_pos _))))
    (Real.exp_pos _)

/-- **Proposition II, step (1)**: `𝒜_x ≤ vρ∞(x; n₁) · Lev^{(f)}(x)` with `n₁ = f - 1/4`, for `x` to the
right of the node `χ_{f+1/2}`. -/
theorem combAmplitude_le_vRhoInfty_mul_levComb {c' x : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f)
    (hx : chiQuantile c' ((f : ℝ) + 1 / 2) < x) :
    combAmplitude c' x ≤ vRhoInfty x (n1Comb f) * levComb c' f x := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hχf : chiQuantile c' (f : ℝ) < x :=
    (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))
      (by linarith : (f : ℝ) < (f : ℝ) + 1 / 2)).trans hx
  have hxi : xiStar < x := (xiStar_lt_chiQuantile hc' (by linarith)).trans hχf
  have hx0 : 0 < x := xiStar_pos.trans hxi
  have hS : 0 < Real.sinh (π * x) := by linarith [one_lt_sinh_pi_mul hxi]
  have hexp1 := exp_combPf_jEnd_ge hc' hf hx
  set R : ℝ := √(√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  set E : ℝ := Real.exp (-2 * π * c' * x / 3) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set T : ℝ := tanhTipK8 x with hTdef
  set W : ℝ := Real.exp (c' * combPf c' f x + jEndComb c' x f) with hW
  have hW0 : 0 < W := Real.exp_pos _
  have hcomb : combAmplitude c' x ≤ 2 * E * (2 / Real.sinh (π * x)) * R := by
    rw [combAmplitude_eq hxi]
    have h1 := norm_one_add_hankelEps_bX_le hc' hxi
    have h2 : 0 ≤ 2 * E * (2 / Real.sinh (π * x)) * R := by positivity
    calc 2 * E * (2 / Real.sinh (π * x)) * ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ * R
        ≤ 2 * E * (2 / Real.sinh (π * x)) * 1 * R := by gcongr
      _ = _ := by ring
  have hlev : levComb c' f x = 4 * (1 / Real.cosh (π * x / 2) ^ 2) * (E * W) := by
    unfold levComb
    rw [hE, hW, ← Real.exp_add]
    congr 2
    unfold slitL
    rw [abs_of_pos hx0]
    ring
  have hrho : vRhoInfty x (n1Comb f) =
      (1 / 2 : ℝ) * R * (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * T ^ (2 * n1Comb f) := by
    unfold vRhoInfty
    rw [hR, Real.sqrt_eq_rpow (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x))]
  rw [hlev, hrho]
  have hs2 : Real.sinh (π * x) = 2 * Real.sinh (π * x / 2) * Real.cosh (π * x / 2) := by
    rw [← Real.sinh_two_mul]; congr 1; ring
  have hsy : 0 < Real.sinh (π * x / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hcy : 0 < Real.cosh (π * x / 2) := Real.cosh_pos _
  have hTp : 0 ≤ T ^ (2 * n1Comb f) := by
    have : 0 < T := by
      have h1 : 0 < Real.tanh (π * (x - xiStar) / 2) :=
        tanh_pos_of_pos (by have := Real.pi_pos; nlinarith)
      have h2 : 0 < Real.tanh (π * (x + xiStar) / 2) :=
        tanh_pos_of_pos (by have := Real.pi_pos; have := xiStar_pos; nlinarith)
      exact mul_pos h1 h2
    positivity
  have hkey : (1 / 2 : ℝ) * R * (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) *
        T ^ (2 * n1Comb f) * (4 * (1 / Real.cosh (π * x / 2) ^ 2) * (E * W)) =
      (2 * E * (2 / Real.sinh (π * x)) * R) * (T ^ (2 * n1Comb f) * W) := by
    rw [hs2]
    field_simp
    ring
  calc combAmplitude c' x ≤ 2 * E * (2 / Real.sinh (π * x)) * R := hcomb
    _ = (2 * E * (2 / Real.sinh (π * x)) * R) * 1 := (mul_one _).symm
    _ ≤ (2 * E * (2 / Real.sinh (π * x)) * R) * (T ^ (2 * n1Comb f) * W) := by
        have h0 : 0 ≤ 2 * E * (2 / Real.sinh (π * x)) * R := by positivity
        exact mul_le_mul_of_nonneg_left hexp1 h0
    _ = _ := hkey.symm

/-- **Proposition II, step (1), rational form**: `𝒜_x ≤ (55/100) Lev^{(f)}(x)` for `x > χ_{f+1/2}`
(Lemma `K8`, `vRhoInfty_le`, with `n₁ = f - 1/4 ≥ 3/4`). -/
theorem combAmplitude_le_levComb_frac {c' x : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f)
    (hx : chiQuantile c' ((f : ℝ) + 1 / 2) < x) :
    combAmplitude c' x ≤ (55 / 100 : ℝ) * levComb c' f x := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hχf : chiQuantile c' (f : ℝ) < x :=
    (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))
      (by linarith : (f : ℝ) < (f : ℝ) + 1 / 2)).trans hx
  have hxi : xiStar < x := (xiStar_lt_chiQuantile hc' (by linarith)).trans hχf
  have hn1 : (3 / 4 : ℝ) ≤ n1Comb f := by unfold n1Comb; linarith
  obtain ⟨h1, h2, h3, h4⟩ := vRhoInfty_le hn1 hxi
  have hlev : 0 < levComb c' f x := levComb_pos c' f x
  refine (combAmplitude_le_vRhoInfty_mul_levComb hc' hf hx).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hlev.le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.edgeF'_edgeV_eq_edgeDerivK8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeF'_edgeV_eq_edgeDerivK8

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.norm_sechSq_bX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_sechSq_bX

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.combAmplitude_le_vRhoInfty_mul_levComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combAmplitude_le_vRhoInfty_mul_levComb

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.combAmplitude_le_levComb_frac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combAmplitude_le_levComb_frac

end FormalResearch.ModularBootstrap.Upper.Positivity
