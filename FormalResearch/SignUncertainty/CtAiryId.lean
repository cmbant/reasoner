module

public import FormalResearch.SignUncertainty.CtAiryG0
public import FormalResearch.SignUncertainty.CtAiryOde
public import FormalResearch.Special.AiryValues
public import FormalResearch.Special.AiryBiReal

/-!
# Exact complex Airy identities: `G_0 = -π(Ai² + i Ai Bi)`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 1
(`ct:airy-id1`, `ct:airy-id2`).  **Proved.**

Both `G_0` and `H = -π(Ai² + i AiBi)` solve `y''' = 4uy' + 2y`; their data `(y, y', y'')` at `0`
agree (Gamma-function identities: Legendre duplication at `1/6`, reflection at `1/6` and `1/3`,
`Ai(0), Ai'(0), Bi(0), Bi'(0)` from `FormalResearch.Special.AiryValues`), so they coincide
(`CtAiryOde.ode3_eq_zero`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.Special

namespace FormalResearch.SignUncertainty.CtAiry

/-- `t = 3^{1/6}`. -/
noncomputable def t6 : ℝ := (3 : ℝ) ^ (1 / 6 : ℝ)

lemma t6_pos : 0 < t6 := Real.rpow_pos_of_pos (by norm_num) _

lemma t6_pow6 : t6 ^ 6 = 3 := by
  unfold t6
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma three_rpow {q : ℝ} {k : ℤ} (h : q = k / 6) : (3 : ℝ) ^ q = t6 ^ k := by
  unfold t6
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  rw [h]; ring

/-- `s2 = 2^{1/3}`. -/
noncomputable def s2 : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ)

lemma s2_pos : 0 < s2 := Real.rpow_pos_of_pos (by norm_num) _

lemma s2_cube : s2 ^ 3 = 2 := by
  unfold s2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma two_rpow {q : ℝ} {k : ℤ} (h : q = k / 3) : (2 : ℝ) ^ q = s2 ^ k := by
  unfold s2
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  rw [h]; ring

lemma rr_eq : rr = (s2)⁻¹ := by
  unfold rr
  rw [two_rpow (k := -1) (by norm_num)]
  simp

/-- `gI p 0` is a Gamma value. -/
lemma gI_zero {p : ℝ} (hp : -1 < p) :
    gI p 0 = (((3 : ℝ) ^ ((p + 1) / 3) * (1 / 3) * Real.Gamma ((p + 1) / 3) : ℝ) : ℂ) := by
  have hI := integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := p) (b := 1 / 3) (by norm_num) hp
    (by norm_num)
  unfold gI
  have : ∀ t ∈ Ioi (0 : ℝ), gF p 0 t = ((t ^ p * Real.exp (-(1 / 3) * t ^ (3 : ℝ)) : ℝ) : ℂ) := by
    intro t ht
    have h3 : t ^ (3 : ℝ) = t ^ 3 := by exact_mod_cast Real.rpow_natCast t 3
    unfold gF
    push_cast
    rw [h3]
    congr 1
    simp
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_complex_ofReal, hI]
  congr 2
  have h3 : (1 / 3 : ℝ) ^ (-(p + 1) / 3) = (3 : ℝ) ^ ((p + 1) / 3) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [h3]

lemma al_eq (t : ℝ) (ht : t ^ 3 = √3) :
    al = (rr : ℂ) * (-1 + Complex.I * (t ^ 3 : ℝ)) := by
  apply Complex.ext <;> simp [al, ht]

section values_alg
variable {t s q g h X Y : ℝ}

lemma alg_E1 (ht : 0 < t) (ht6 : t ^ 6 = 3) (hq : 0 < q) (hg : 0 < g) (hh : 0 < h)
    (r1 : g * h * t ^ 3 = 2 * q ^ 2) :
    ((t ^ 3 / 3 * q : ℝ) : ℂ) / (q : ℂ) =
      -(q ^ 2 : ℝ) * (2 * (((t ^ 4 * h)⁻¹ : ℝ) : ℂ) * (-(((t ^ 2 * g)⁻¹ : ℝ) : ℂ)) +
        Complex.I * ((-(((t ^ 2 * g)⁻¹ : ℝ) : ℂ)) * (((t * h)⁻¹ : ℝ) : ℂ) +
          (((t ^ 4 * h)⁻¹ : ℝ) : ℂ) * ((t / g : ℝ) : ℂ))) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have r1c : (g : ℂ) * h * t ^ 3 = 2 * q ^ 2 := by exact_mod_cast r1
  have ht6c : (t : ℂ) ^ 6 = 3 := by exact_mod_cast ht6
  push_cast
  field_simp
  linear_combination ((t : ℂ) ^ 6) * r1c + 2 * (q : ℂ) ^ 2 * ht6c

lemma alg_E0 (ht : 0 < t) (hs : 0 < s) (ht6 : t ^ 6 = 3) (hs3 : s ^ 3 = 2) (hq : 0 < q)
    (hg : 0 < g) (hh : 0 < h) (r1 : g * h * t ^ 3 = 2 * q ^ 2) (r2 : X * h = s ^ 2 * q * g) :
    ((t * X / 3 : ℝ) : ℂ) =
      -(q ^ 2 : ℝ) * ((((t ^ 4 * h)⁻¹ : ℝ) : ℂ) ^ 2 +
        Complex.I * ((((t ^ 4 * h)⁻¹ : ℝ) : ℂ) * (((t * h)⁻¹ : ℝ) : ℂ))) *
      (((s⁻¹ : ℝ) : ℂ) * (-1 + Complex.I * (t ^ 3 : ℝ)) * (q : ℂ)) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have F0 : t ^ 9 * X * s * h ^ 2 = 12 * q ^ 3 := by
    linear_combination (t ^ 9 * s * h) * r2 + (2 * q * t ^ 6) * r1 + 4 * q ^ 3 * ht6 +
      (t ^ 9 * q * g * h) * hs3
  have F0c : (t : ℂ) ^ 9 * X * s * h ^ 2 = 12 * q ^ 3 := by exact_mod_cast F0
  have ht6c : (t : ℂ) ^ 6 = 3 := by exact_mod_cast ht6
  push_cast
  field_simp
  linear_combination F0c - 3 * (q : ℂ) ^ 3 * ht6c + 3 * (q : ℂ) ^ 3 * (t : ℂ) ^ 6 * Complex.I_sq

lemma alg_E2 (ht : 0 < t) (hs : 0 < s) (ht6 : t ^ 6 = 3) (hs3 : s ^ 3 = 2) (hq : 0 < q)
    (hg : 0 < g) (_hh : 0 < h) (r1 : g * h * t ^ 3 = 2 * q ^ 2) (r2 : X * h = s ^ 2 * q * g)
    (r3 : X * Y = 2 * q ^ 2) :
    ((s⁻¹ : ℝ) : ℂ) * (-1 + Complex.I * (t ^ 3 : ℝ)) * ((t ^ 5 / 3 * Y : ℝ) : ℂ) / (q : ℂ) =
      -(q ^ 2 : ℝ) * (2 * (-(((t ^ 2 * g)⁻¹ : ℝ) : ℂ)) ^ 2 +
        Complex.I * (2 * (-(((t ^ 2 * g)⁻¹ : ℝ) : ℂ)) * ((t / g : ℝ) : ℂ))) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hY : Y * s ^ 2 * g = 2 * q * h := by
    have hXpos : X ≠ 0 := by
      intro h0
      rw [h0] at r3
      have : (0 : ℝ) < 2 * q ^ 2 := by positivity
      linarith
    have : q * (Y * s ^ 2 * g) = q * (2 * q * h) := by
      have e : X * (Y * s ^ 2 * g - 2 * q * h) = 0 := by
        linear_combination (s ^ 2 * g) * r3 - (2 * q) * r2
      have := (mul_eq_zero.1 e).resolve_left hXpos
      nlinarith [this]
    exact mul_left_cancel₀ hq.ne' this
  have F2 : t ^ 9 * Y * g ^ 2 = 6 * s * q ^ 3 := by
    have e : s ^ 2 * (t ^ 9 * Y * g ^ 2) = s ^ 2 * (6 * s * q ^ 3) := by
      linear_combination (t ^ 9 * g) * hY + (2 * q * t ^ 6) * r1 + 4 * q ^ 3 * ht6 -
        6 * q ^ 3 * hs3
    exact mul_left_cancel₀ (pow_ne_zero 2 hs.ne') e
  have F2c : (t : ℂ) ^ 9 * Y * g ^ 2 = 6 * s * q ^ 3 := by exact_mod_cast F2
  push_cast
  field_simp
  linear_combination (-1 + Complex.I * (t : ℂ) ^ 3) * F2c
end values_alg

section gamma_facts

lemma t6_cube_sqrt3 : t6 ^ 3 = √3 := by
  have h : (3 : ℝ) ^ (1 / 2 : ℝ) = t6 ^ (3 : ℤ) := three_rpow (k := 3) (by norm_num)
  rw [Real.sqrt_eq_rpow, h]
  simp

lemma sqrtpi_sq : (√π) ^ 2 = π := Real.sq_sqrt Real.pi_pos.le

lemma gam_r1 : Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * t6 ^ 3 = 2 * (√π) ^ 2 := by
  rw [gamma_third_mul_two_thirds, t6_cube_sqrt3, sqrtpi_sq]
  have : (√3 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

lemma gam_r2 : Real.Gamma (1 / 6) * Real.Gamma (2 / 3) =
    s2 ^ 2 * √π * Real.Gamma (1 / 3) := by
  have h := Real.Gamma_mul_Gamma_add_half (1 / 6)
  have e1 : (1 / 6 : ℝ) + 1 / 2 = 2 / 3 := by norm_num
  have e2 : 2 * (1 / 6 : ℝ) = 1 / 3 := by norm_num
  have e3 : (2 : ℝ) ^ (1 - 2 * (1 / 6) : ℝ) = s2 ^ (2 : ℤ) := two_rpow (by norm_num)
  rw [e1, e2] at h
  rw [e2] at e3
  have e5 : s2 ^ (2 : ℤ) = s2 ^ 2 := zpow_ofNat s2 2
  rw [e3, e5] at h
  rw [h]
  ring

lemma gam_r3 : Real.Gamma (1 / 6) * Real.Gamma (5 / 6) = 2 * (√π) ^ 2 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  rw [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num, show π * (1 / 6) = π / 6 by ring,
    Real.sin_pi_div_six] at h
  rw [h, sqrtpi_sq]
  ring

end gamma_facts

section Hside

/-- `H = -π(Ai² + i AiBi)`. -/
noncomputable def HH0 (u : ℝ) : ℂ :=
  -(π : ℂ) * ((airyAi u : ℂ) ^ 2 + Complex.I * (airyAi u : ℂ) * (airyBi u : ℂ))

/-- `H' = -π(2AiAi' + i(Ai'Bi + AiBi'))`. -/
noncomputable def HH1 (u : ℝ) : ℂ :=
  -(π : ℂ) * (2 * (airyAi u : ℂ) * (airyAi' u : ℂ) + Complex.I *
    ((airyAi' u : ℂ) * (airyBi u : ℂ) + (airyAi u : ℂ) * (airyBiDeriv u : ℂ)))

/-- `H'' = -π(2Ai'² + 2uAi² + i(2Ai'Bi' + 2uAiBi))`. -/
noncomputable def HH2 (u : ℝ) : ℂ :=
  -(π : ℂ) * (2 * (airyAi' u : ℂ) ^ 2 + 2 * (u : ℂ) * (airyAi u : ℂ) ^ 2 + Complex.I *
    (2 * (airyAi' u : ℂ) * (airyBiDeriv u : ℂ) + 2 * (u : ℂ) * (airyAi u : ℂ) * (airyBi u : ℂ)))

private lemma dAi (u : ℝ) : HasDerivAt (fun x : ℝ => (airyAi x : ℂ)) (airyAi' u : ℂ) u :=
  (hasDerivAt_airyAi u).ofReal_comp

private lemma dAi' (u : ℝ) : HasDerivAt (fun x : ℝ => (airyAi' x : ℂ)) ((u : ℂ) * airyAi u) u := by
  have := (hasDerivAt_airyAi' u).ofReal_comp
  simpa using this

private lemma dBi (u : ℝ) : HasDerivAt (fun x : ℝ => (airyBi x : ℂ)) (airyBiDeriv u : ℂ) u :=
  (hasDerivAt_airyBi u).ofReal_comp

private lemma dBi' (u : ℝ) : HasDerivAt (fun x : ℝ => (airyBiDeriv x : ℂ)) ((u : ℂ) * airyBi u) u := by
  have := (hasDerivAt_airyBiDeriv u).ofReal_comp
  simpa using this

theorem hasDerivAt_HH0 (u : ℝ) : HasDerivAt HH0 (HH1 u) u := by
  have h := ((((dAi u).pow 2).add (((dAi u).const_mul Complex.I).mul (dBi u)))).const_mul
    (-(π : ℂ))
  refine h.congr_deriv ?_
  unfold HH1
  push_cast
  ring

theorem hasDerivAt_HH1 (u : ℝ) : HasDerivAt HH1 (HH2 u) u := by
  have h1 := ((dAi u).const_mul 2).mul (dAi' u)
  have h2 := ((dAi' u).mul (dBi u)).add ((dAi u).mul (dBi' u))
  have h := (h1.add (h2.const_mul Complex.I)).const_mul (-(π : ℂ))
  refine h.congr_deriv ?_
  unfold HH2
  ring

theorem hasDerivAt_HH2 (u : ℝ) : HasDerivAt HH2 (4 * (u : ℂ) * HH1 u + 2 * HH0 u) u := by
  have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
  have a1 := ((dAi' u).pow 2).const_mul 2
  have a2 := (h0.const_mul 2).mul ((dAi u).pow 2)
  have b1 := ((dAi' u).const_mul 2).mul (dBi' u)
  have b2 := ((h0.const_mul 2).mul (dAi u)).mul (dBi u)
  have h := ((a1.add a2).add ((b1.add b2).const_mul Complex.I)).const_mul (-(π : ℂ))
  refine h.congr_deriv ?_
  unfold HH1 HH0
  simp only [Pi.mul_apply, Pi.pow_apply]
  push_cast
  ring

end Hside

section Values

lemma ai0 : airyAi 0 = (t6 ^ 4 * Real.Gamma (2 / 3))⁻¹ := by
  have h := three_rpow (q := -(2 / 3)) (k := -4) (by norm_num)
  have e : t6 ^ (-4 : ℤ) = (t6 ^ 4)⁻¹ := by simp
  rw [airyAi_zero, h, e, mul_inv, div_eq_mul_inv]

lemma ai'0 : airyAi' 0 = -(t6 ^ 2 * Real.Gamma (1 / 3))⁻¹ := by
  have h := three_rpow (q := -(1 / 3)) (k := -2) (by norm_num)
  have e : t6 ^ (-2 : ℤ) = (t6 ^ 2)⁻¹ := by simp
  rw [airyAi'_zero, h, e, mul_inv, div_eq_mul_inv]

lemma bi0 : airyBi 0 = (t6 * Real.Gamma (2 / 3))⁻¹ := by
  have h := three_rpow (q := -(1 / 6)) (k := -1) (by norm_num)
  have e : t6 ^ (-1 : ℤ) = (t6)⁻¹ := by simp
  rw [airyBi_zero, h, e, mul_inv, div_eq_mul_inv]

lemma bi'0 : airyBiDeriv 0 = t6 / Real.Gamma (1 / 3) := by
  have h := three_rpow (q := 1 / 6) (k := 1) (by norm_num)
  have e := airyBiC'_zero_eq
  have e2 := airyBiC'_ofReal 0
  rw [Complex.ofReal_zero] at e2
  rw [e] at e2
  have e3 : airyBiDeriv 0 = (3 : ℝ) ^ (1 / 6 : ℝ) / Real.Gamma (1 / 3) := by
    exact_mod_cast e2.symm
  rw [e3, h]
  simp

end Values

section ZeroData

lemma g_pos : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
lemma h_pos : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)

lemma gI_zero_a : gI (-1 / 2) 0 = ((t6 * Real.Gamma (1 / 6) / 3 : ℝ) : ℂ) := by
  rw [gI_zero (by norm_num)]
  have e : ((-1 / 2 : ℝ) + 1) / 3 = 1 / 6 := by norm_num
  rw [e]
  congr 1
  show t6 * (1 / 3) * Real.Gamma (1 / 6) = _
  ring

lemma gI_zero_b : gI (1 / 2) 0 = ((t6 ^ 3 / 3 * √π : ℝ) : ℂ) := by
  rw [gI_zero (by norm_num)]
  have e : ((1 / 2 : ℝ) + 1) / 3 = 1 / 2 := by norm_num
  rw [e, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, ← t6_cube_sqrt3]
  congr 1
  ring

lemma gI_zero_c : gI (3 / 2) 0 = ((t6 ^ 5 / 3 * Real.Gamma (5 / 6) : ℝ) : ℂ) := by
  rw [gI_zero (by norm_num)]
  have e : ((3 / 2 : ℝ) + 1) / 3 = 5 / 6 := by norm_num
  rw [e, three_rpow (k := 5) (by norm_num), zpow_ofNat]
  congr 1
  ring

lemma G0_zero : G0 0 = HH0 0 := by
  have hne : al * ((√π : ℝ) : ℂ) ≠ 0 := mul_ne_zero al_ne sqrtpi_ne
  have E := alg_E0 (t := t6) (s := s2) (q := √π) (g := Real.Gamma (1 / 3))
    (h := Real.Gamma (2 / 3)) (X := Real.Gamma (1 / 6)) t6_pos s2_pos t6_pow6 s2_cube
    (Real.sqrt_pos.2 Real.pi_pos) g_pos h_pos gam_r1 gam_r2
  rw [sqrtpi_sq] at E
  unfold G0 HH0
  rw [gI_zero_a, div_eq_iff hne, ai0, bi0, al_eq t6 t6_cube_sqrt3, rr_eq, E]
  push_cast
  ring

lemma G1_zero : G1 0 = HH1 0 := by
  have E := alg_E1 (t := t6) (q := √π) (g := Real.Gamma (1 / 3))
    (h := Real.Gamma (2 / 3)) t6_pos t6_pow6
    (Real.sqrt_pos.2 Real.pi_pos) g_pos h_pos gam_r1
  rw [sqrtpi_sq] at E
  unfold G1 HH1
  rw [gI_zero_b, ai0, ai'0, bi0, bi'0]
  push_cast at E ⊢
  linear_combination E

lemma G2_zero : G2 0 = HH2 0 := by
  have E := alg_E2 (t := t6) (s := s2) (q := √π) (g := Real.Gamma (1 / 3))
    (h := Real.Gamma (2 / 3)) (X := Real.Gamma (1 / 6)) (Y := Real.Gamma (5 / 6)) t6_pos s2_pos
    t6_pow6 s2_cube (Real.sqrt_pos.2 Real.pi_pos) g_pos h_pos gam_r1 gam_r2 gam_r3
  rw [sqrtpi_sq] at E
  unfold G2 HH2
  rw [gI_zero_c, ai'0, bi'0, al_eq t6 t6_cube_sqrt3, rr_eq]
  push_cast at E ⊢
  linear_combination E

end ZeroData

/-- **`G_0 = -π(Ai² + i AiBi)`** on `ℝ`, together with the derivatives `G_0'`, `G_0''`
(Lemma `ct:cfu`, Step 1). -/
theorem G_eq_HH (u : ℝ) : G0 u = HH0 u ∧ G1 u = HH1 u ∧ G2 u = HH2 u := by
  have h0 : ∀ u : ℝ, HasDerivAt (fun x => G0 x - HH0 x) (G1 u - HH1 u) u :=
    fun u => (hasDerivAt_G0 u).sub (hasDerivAt_HH0 u)
  have h1 : ∀ u : ℝ, HasDerivAt (fun x => G1 x - HH1 x) (G2 u - HH2 u) u :=
    fun u => (hasDerivAt_G1 u).sub (hasDerivAt_HH1 u)
  have h2 : ∀ u : ℝ, HasDerivAt (fun x => G2 x - HH2 x)
      (4 * (u : ℂ) * (G1 u - HH1 u) + 2 * (G0 u - HH0 u)) u := by
    intro u
    refine ((hasDerivAt_G2 u).sub (hasDerivAt_HH2 u)).congr_deriv ?_
    ring
  have z := ode3_eq_zero (D0 := fun x => G0 x - HH0 x) (D1 := fun x => G1 x - HH1 x)
    (D2 := fun x => G2 x - HH2 x) h0 h1 h2 (by simp [G0_zero]) (by simp [G1_zero])
    (by simp [G2_zero])
  have e0 : ∀ x, G0 x = HH0 x := fun x => sub_eq_zero.1 (z x)
  have e1 : ∀ x, G1 x = HH1 x := by
    intro x
    have hd : HasDerivAt G0 (HH1 x) x := by
      have : G0 = HH0 := funext e0
      rw [this]; exact hasDerivAt_HH0 x
    exact (hasDerivAt_G0 x).unique hd
  have e2 : ∀ x, G2 x = HH2 x := by
    intro x
    have hd : HasDerivAt G1 (HH2 x) x := by
      have : G1 = HH1 := funext e1
      rw [this]; exact hasDerivAt_HH1 x
    exact (hasDerivAt_G1 x).unique hd
  exact ⟨e0 u, e1 u, e2 u⟩

/-- info: 'FormalResearch.SignUncertainty.CtAiry.G_eq_HH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G_eq_HH

end FormalResearch.SignUncertainty.CtAiry
