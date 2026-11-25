module

public import FormalResearch.SignUncertainty.UctPosFloor
public import FormalResearch.CohnElkies.MellinLiftIntegrals

/-!
# `uct:pos-floor` (3), real transform of `S_pos`: the lower bound `S̃_pos(i c_s x) ≥ c₂ (1+x)^{-5/2}` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:pos-floor` (3), first half of its proof.
Notation: `S_pos = uctSpos = -¼ f₁ + g₁ + g₁'` (`UctPosFloorSeed`), `S̃(i y) = airyTwistedLaplace S y = k e^{-y³/12} ∫ S e^{yu}`.

* `uctSpos_right_tail`: `S_pos(u) ≥ (128π)^{-1} u^{-3/2} e^{-(4/3)u^{3/2}}` for `u ≥ 3` (the paper's `S_pos ≥ c₃ u^{-3/2}e^{-(4/3)u^{3/2}}`
  with explicit `c₃`, from `Ai ≥ (1/(4√π)) u^{-1/4} e^{-(2/3)u^{3/2}}` and `Ai'² ≥ u Ai²`).
* `phi_window_ge`: the window estimate `φ(u) ≥ y³/12 - 16/3` on `|u - y²/4| ≤ y^{1/2}` (`y = r²`, `r ≥ 3`), via the completed cube.
  (The paper's constant `3/2` there is replaced by the cruder `16/3`; only the existence of the bound matters.)
* `airyTwistedLaplace_uctSpos_large`: `S̃(i y) ≥ c₄ y^{-5/2}` for `y ≥ 9`.
* `airyTwistedLaplace_uctSpos_floor` (headline): `∃ c₂ > 0, ∀ x ≥ 0, c₂ (1+x)^{-5/2} ≤ S̃_pos(i c_s x)` (positivity and continuity on the compact range).

Class: proved.  Axiom guards are at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies FormalResearch.Special

namespace FormalResearch.SignUncertainty

/-- **Right tail of `S_pos`** (`β_+ > 0`): `S_pos(u) ≥ (128π)^{-1} u^{-3/2} e^{-(4/3) u^{3/2}}` for `u ≥ 3`. -/
theorem uctSpos_right_tail {u : ℝ} (hu : 3 ≤ u) :
    1 / (128 * Real.pi) * u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) ≤ uctSpos u := by
  have hu0 : 0 < u := by linarith
  have ha1 := airyZero_one
  have hneg := airyDerivFirstZero_lt_zero
  have hgt := airyDerivFirstZero_gt
  rw [uctSpos_eq_ceSb]
  unfold ceSb
  set a := airyZero 1 with ha
  set d := u - a with hd
  have hd0 : 0 < d := by linarith
  have hf : ceF1 u = airyAi u ^ 2 / d := by
    have := ceF1_mul_sub u; field_simp; linarith
  have hg : ceG1 a u = airyAi u ^ 2 / d ^ 2 := by
    have := ceG1_mul_sub_sq u; field_simp; linarith
  set e := u - airyDerivFirstZero with he
  have he0 : 0 < e := by linarith
  have hed : e < d := by rw [he, hd]; linarith
  have hg' : ceG1Deriv airyDerivFirstZero u = airyAi' u ^ 2 / e ^ 2 := by
    have := ceG1Deriv_mul_sq u; field_simp; linarith
  have hAi' := airyAi'_sq_ge u
  have hA : 0 < airyAi u := airyAi_pos_of_gt (by linarith)
  have h1 : u * airyAi u ^ 2 / d ^ 2 ≤ airyAi' u ^ 2 / e ^ 2 := by
    calc u * airyAi u ^ 2 / d ^ 2 ≤ u * airyAi u ^ 2 / e ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
      _ ≤ _ := div_le_div_of_nonneg_right hAi' (by positivity)
  rw [hf, hg, hg']
  -- S ≥ A²/(8u)
  have h2 : airyAi u ^ 2 / (8 * u) ≤ airyAi u ^ 2 / d ^ 2 + airyAi' u ^ 2 / e ^ 2 - 1 / 4 * (airyAi u ^ 2 / d) := by
    have hdu : d ≤ 2 * u := by rw [hd]; linarith [ha1.1]
    have h3 : u * airyAi u ^ 2 / d ^ 2 - 1 / 4 * (airyAi u ^ 2 / d) + airyAi u ^ 2 / d ^ 2 =
        airyAi u ^ 2 * (4 * u - d + 4) / (4 * d ^ 2) := by field_simp
    have h4 : airyAi u ^ 2 / (8 * u) ≤ airyAi u ^ 2 * (4 * u - d + 4) / (4 * d ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h5 : 0 ≤ airyAi u ^ 2 := sq_nonneg _
      have : 8 * u ≤ 4 * (4 * u - d + 4) * 1 := by nlinarith [ha1.1, hdu]
      nlinarith [mul_nonneg h5 (sub_nonneg.mpr (by nlinarith [ha1.1, hdu] : d ^ 2 * 4 ≤ (4 * u - d + 4) * (8 * u)))]
    linarith
  refine le_trans ?_ h2
  have hlow := airyAi_lower_bound hu0
  have hu32 : (3 : ℝ) ≤ u ^ (3 / 2 : ℝ) := by
    calc (3 : ℝ) ≤ u := hu
      _ = u ^ (1 : ℝ) := (Real.rpow_one u).symm
      _ ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hfac : 1 / 2 ≤ 1 - 5 / 48 / u ^ (3 / 2 : ℝ) := by
    have : 5 / 48 / u ^ (3 / 2 : ℝ) ≤ 5 / 48 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hu32
    linarith
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set B : ℝ := u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) with hB
  have hB0 : 0 < B := by positivity
  have hAge : 1 / (4 * Real.sqrt Real.pi) * B ≤ airyAi u := by
    refine le_trans ?_ hlow
    have : 1 / (2 * Real.sqrt Real.pi) * u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (1 - 5 / 48 / u ^ (3 / 2 : ℝ)) =
        1 / (2 * Real.sqrt Real.pi) * B * (1 - 5 / 48 / u ^ (3 / 2 : ℝ)) := by rw [hB]; ring
    rw [this]
    have h0 : 0 ≤ 1 / (2 * Real.sqrt Real.pi) * B := by positivity
    calc 1 / (4 * Real.sqrt Real.pi) * B = 1 / (2 * Real.sqrt Real.pi) * B * (1 / 2) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfac h0
  have hA2 : (1 / (4 * Real.sqrt Real.pi) * B) ^ 2 ≤ airyAi u ^ 2 := pow_le_pow_left₀ (by positivity) hAge 2
  have hB2 : B ^ 2 = u ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
    rw [hB, mul_pow]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
    · rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsq : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsq16 : (1 / (4 * Real.sqrt Real.pi) * B) ^ 2 = B ^ 2 / (16 * Real.pi) := by
    rw [mul_pow, div_pow, one_pow, mul_pow, hsq]; field_simp; norm_num
  have hu32' : u ^ (-(3 / 2 : ℝ)) = u ^ (-(1 / 2 : ℝ)) / u := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) - 1 by norm_num, Real.rpow_sub hu0, Real.rpow_one]
  have : 1 / (128 * Real.pi) * u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) =
      (1 / (4 * Real.sqrt Real.pi) * B) ^ 2 / (8 * u) := by
    rw [hsq16, hB2, hu32']; field_simp; norm_num
  rw [this]
  exact div_le_div_of_nonneg_right hA2 (by positivity)


/-- Pointwise window estimate: for `y = r²`, `r ≥ 3` and `u ∈ [r⁴/4 - r, r⁴/4 + r]`, `y u - (4/3) u^{3/2} ≥ y³/12 - 16/3`. -/
lemma phi_window_ge {r u : ℝ} (hr : 3 ≤ r) (hu1 : r ^ 4 / 4 - r ≤ u) (hu2 : u ≤ r ^ 4 / 4 + r) :
    r ^ 6 / 12 - 16 / 3 ≤ r ^ 2 * u - (4 / 3) * u ^ (3 / 2 : ℝ) := by
  have hr0 : 0 < r := by linarith
  have h3 : (27 : ℝ) ≤ r ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hr 3
    norm_num at this; exact this
  have hr4 : r ^ 4 = r * r ^ 3 := by ring
  have hu0 : 0 < u := by nlinarith
  set s := Real.sqrt u with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg u
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hu32 : u ^ (3 / 2 : ℝ) = s ^ 3 := by
    rw [show (3 / 2 : ℝ) = (1 : ℝ) + 1 / 2 by norm_num, Real.rpow_add hu0, Real.rpow_one, ← Real.sqrt_eq_rpow, ← hs]
    rw [← hs2]; ring
  have hcube := completed_cube_id (r ^ 2) s
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = s - r ^ 2 / 2 := ⟨_, rfl⟩
  have hsq : A * (s + r ^ 2 / 2) = u - r ^ 4 / 4 := by rw [hAdef, ← hs2]; ring
  have hsum : r ^ 2 / 2 ≤ s + r ^ 2 / 2 := by linarith
  have hr2 : 9 ≤ r ^ 2 := by nlinarith
  have hbound : (A * (s + r ^ 2 / 2)) ^ 2 ≤ r ^ 2 := by
    rw [hsq]
    have : |u - r ^ 4 / 4| ≤ r := by rw [abs_le]; constructor <;> linarith
    have := sq_le_sq' (by linarith [(abs_le.mp this).1]) (by linarith [(abs_le.mp this).2] : u - r ^ 4 / 4 ≤ r)
    exact this
  have hA2 : A ^ 2 * r ^ 2 ≤ 4 := by
    have h1 : (r ^ 2 / 2) ^ 2 ≤ (s + r ^ 2 / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsum 2
    have h2 : A ^ 2 * (s + r ^ 2 / 2) ^ 2 ≤ r ^ 2 := by rw [← mul_pow]; exact hbound
    have h3 : A ^ 2 * (r ^ 2 / 2) ^ 2 ≤ r ^ 2 := le_trans (mul_le_mul_of_nonneg_left h1 (sq_nonneg A)) h2
    have : A ^ 2 * (r ^ 4 / 4) ≤ r ^ 2 := by
      have : (r ^ 2 / 2) ^ 2 = r ^ 4 / 4 := by ring
      rwa [this] at h3
    have hr2' : 0 < r ^ 2 := by positivity
    nlinarith [this, hr2']
  have hAsmall : A ≤ r ^ 2 / 4 := by
    have : A ^ 2 ≤ 4 / 9 := by
      have : A ^ 2 * 9 ≤ A ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hr2 (sq_nonneg A)
      linarith
    nlinarith [sq_nonneg (A - 2 / 3)]
  have hs34 : s + r ^ 2 / 4 ≤ r ^ 2 := by
    have : s = A + r ^ 2 / 2 := by rw [hAdef]; ring
    linarith
  have hs0' : 0 ≤ s + r ^ 2 / 4 := by positivity
  have hprod : (s - r ^ 2 / 2) ^ 2 * (s + r ^ 2 / 4) ≤ 4 := by
    rw [← hAdef]
    calc A ^ 2 * (s + r ^ 2 / 4) ≤ A ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hs34 (sq_nonneg A)
      _ ≤ 4 := hA2
  rw [hu32, ← hs2]
  have : (r ^ 2) ^ 3 / 12 = r ^ 6 / 12 := by ring
  rw [this] at hcube
  nlinarith [hcube, hprod]


lemma integrable_uctSpos_exp (y : ℝ) (hy : 0 ≤ y) : Integrable (fun u : ℝ => uctSpos u * Real.exp (y * u)) := by
  have h := (hasU2_airySeedU2 (-1 / 4) 1 1).integrable (y : ℂ) (by simpa using hy)
  have h2 := h.norm
  refine h2.congr (ae_of_all _ fun u => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [abs_of_pos (uctSpos_pos u)]

/-- The real twisted transform of `S_pos` is `≳ y^{-5/2}` for large `y` (`uct:pos-floor` (3)). -/
theorem airyTwistedLaplace_uctSpos_large : ∃ c4 : ℝ, 0 < c4 ∧ ∀ y : ℝ, 9 ≤ y → c4 * y ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace uctSpos y := by
  have hk := ceK_pos
  refine ⟨2 * ceK * (1 / (128 * Real.pi)) * Real.exp (-(16 / 3 : ℝ)), by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt y := ⟨_, rfl⟩
  have hr3 : 3 ≤ r := by
    rw [hrdef]; calc (3 : ℝ) = Real.sqrt 9 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ _ := Real.sqrt_le_sqrt hy
  have hr0 : 0 < r := by linarith
  have hry : r ^ 2 = y := by rw [hrdef]; exact Real.sq_sqrt hy0.le
  subst hry
  set F : ℝ → ℝ := fun u => uctSpos u * Real.exp (r ^ 2 * u) with hF
  have hFint : Integrable F := integrable_uctSpos_exp (r ^ 2) (by positivity)
  have hF0 : ∀ u, 0 ≤ F u := fun u => by rw [hF]; exact mul_nonneg (uctSpos_pos u).le (Real.exp_pos _).le
  set Wd : Set ℝ := Icc (r ^ 4 / 4 - r) (r ^ 4 / 4 + r) with hWd
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (1 / (128 * Real.pi)) * r ^ (-(6 : ℝ)) * Real.exp (r ^ 6 / 12 - 16 / 3) := ⟨_, rfl⟩
  have hlow : ∀ u ∈ Wd, m ≤ F u := by
    intro u hu
    have hu3 : 3 ≤ u := by
      have h3 : (27 : ℝ) ≤ r ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hr3 3
        norm_num at this; exact this
      have : r ^ 4 = r * r ^ 3 := by ring
      have := hu.1
      nlinarith
    have hu0 : 0 < u := by linarith
    have htail := uctSpos_right_tail hu3
    have hphi := phi_window_ge hr3 hu.1 hu.2
    have hu32 : u ^ (3 / 2 : ℝ) ≤ r ^ 6 := by
      have h1 : u ≤ r ^ 4 := by
        have h3 : (27 : ℝ) ≤ r ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hr3 3
          norm_num at this; exact this
        have : r ^ 4 = r * r ^ 3 := by ring
        have := hu.2
        nlinarith
      calc u ^ (3 / 2 : ℝ) ≤ (r ^ 4) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hu0.le h1 (by norm_num)
        _ = r ^ 6 := by
          rw [← Real.rpow_natCast r 4, ← Real.rpow_mul hr0.le, ← Real.rpow_natCast r 6]; norm_num
    have hup : r ^ (-(6 : ℝ)) ≤ u ^ (-(3 / 2 : ℝ)) := by
      have h6 : r ^ (6 : ℝ) = r ^ 6 := by exact_mod_cast Real.rpow_natCast r 6
      rw [Real.rpow_neg hr0.le, Real.rpow_neg hu0.le, h6]
      exact inv_anti₀ (by positivity) hu32
    have hexp : Real.exp (r ^ 6 / 12 - 16 / 3) ≤ Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (r ^ 2 * u) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    calc m = (1 / (128 * Real.pi)) * r ^ (-(6 : ℝ)) * Real.exp (r ^ 6 / 12 - 16 / 3) := hmdef
      _ ≤ (1 / (128 * Real.pi)) * u ^ (-(3 / 2 : ℝ)) * (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (r ^ 2 * u)) := by
          gcongr
      _ = (1 / (128 * Real.pi) * u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) * Real.exp (r ^ 2 * u) := by ring
      _ ≤ F u := by rw [hF]; exact mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
  have hWmeas : MeasurableSet Wd := measurableSet_Icc
  have hvol : volume.real Wd = 2 * r := by
    rw [hWd, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  have h1 := setIntegral_ge_of_const_le hWmeas (by rw [hWd]; simp) hlow hFint.integrableOn
  rw [hvol, smul_eq_mul] at h1
  have h2 : ∫ u in Wd, F u ≤ ∫ u, F u := setIntegral_le_integral hFint (ae_of_all _ hF0)
  have hmpos : 0 < m := by rw [hmdef]; positivity
  unfold airyTwistedLaplace
  have hexp6 : Real.exp (-((r ^ 2) ^ 3) / 12) * Real.exp (r ^ 6 / 12 - 16 / 3) = Real.exp (-(16 / 3 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hy52 : (r ^ 2) ^ (-(5 / 2 : ℝ)) = r ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le]; norm_num
  have hr6 : r * r ^ (-(6 : ℝ)) = r ^ (-(5 : ℝ)) := by
    calc r * r ^ (-(6 : ℝ)) = r ^ (1 : ℝ) * r ^ (-(6 : ℝ)) := by rw [Real.rpow_one]
      _ = r ^ ((1 : ℝ) + -(6 : ℝ)) := (Real.rpow_add hr0 _ _).symm
      _ = _ := by norm_num
  have hlowI : ceK * Real.exp (-((r ^ 2) ^ 3) / 12) * (2 * r * m) ≤
      ceK * Real.exp (-((r ^ 2) ^ 3) / 12) * ∫ u, uctSpos u * Real.exp (r ^ 2 * u) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 2 * r * m ≤ ∫ u in Wd, F u := by linarith [h1]
    exact this.trans h2
  refine le_trans (le_of_eq ?_) hlowI
  rw [hmdef, hy52]
  calc 2 * ceK * (1 / (128 * Real.pi)) * Real.exp (-(16 / 3 : ℝ)) * r ^ (-(5 : ℝ))
      = 2 * ceK * (1 / (128 * Real.pi)) * (Real.exp (-((r ^ 2) ^ 3) / 12) * Real.exp (r ^ 6 / 12 - 16 / 3)) * (r * r ^ (-(6 : ℝ))) := by
        rw [hexp6, hr6]
    _ = _ := by ring


lemma airyTwistedLaplace_uctSpos_pos (y : ℝ) (hy : 0 ≤ y) : 0 < airyTwistedLaplace uctSpos y := by
  unfold airyTwistedLaplace
  have hint := integrable_uctSpos_exp y hy
  have : 0 < ∫ u : ℝ, uctSpos u * Real.exp (y * u) := by
    rw [integral_pos_iff_support_of_nonneg (fun u => mul_nonneg (uctSpos_pos u).le (Real.exp_pos _).le) hint]
    have : Function.support (fun u : ℝ => uctSpos u * Real.exp (y * u)) = Set.univ := by
      ext u; simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (mul_pos (uctSpos_pos u) (Real.exp_pos _)).ne'
    rw [this]; simp
  exact mul_pos (mul_pos ceK_pos (Real.exp_pos _)) this

lemma continuousOn_airyTwistedLaplace_uctSpos : ContinuousOn (airyTwistedLaplace uctSpos) (Set.Ici 0) := by
  have h := (hasU2_airySeedU2 (-1 / 4) 1 1).continuousOn
  have h2 : ContinuousOn (fun y : ℝ => (airyTwistedLaplaceC uctSpos (y : ℂ)).re) (Set.Ici 0) := by
    refine Complex.continuous_re.comp_continuousOn (h.comp Complex.continuous_ofReal.continuousOn fun y hy => ?_)
    simpa using hy
  refine h2.congr fun y hy => ?_
  simp only [airyTwistedLaplaceC_ofReal, Complex.ofReal_re]

/-- **`uct:pos-floor` (3), lower bound.**  `S̃_pos(i c_s x) ≥ c₂ (1+x)^{-5/2}` for all real `x ≥ 0`
(`S̃_pos(i y) = airyTwistedLaplace S_pos y`; the constant `c₂` is absolute). -/
theorem airyTwistedLaplace_uctSpos_floor :
    ∃ c2 : ℝ, 0 < c2 ∧ ∀ x : ℝ, 0 ≤ x → c2 * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace uctSpos (ceCs * x) := by
  obtain ⟨c4, hc4, hlarge⟩ := airyTwistedLaplace_uctSpos_large
  have hcs := ceCs_pos
  obtain ⟨y0, hy0, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 9)).exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num))
    (continuousOn_airyTwistedLaplace_uctSpos.mono Set.Icc_subset_Ici_self)
  set m := airyTwistedLaplace uctSpos y0 with hm
  have hmpos : 0 < m := airyTwistedLaplace_uctSpos_pos y0 hy0.1
  refine ⟨min m (c4 * ceCs ^ (-(5 / 2 : ℝ))), lt_min hmpos (by positivity), fun x hx => ?_⟩
  have hp1 : (1 + x) ^ (-(5 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hp0 : 0 ≤ (1 + x) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (ceCs * x) 9 with h9 | h9
  · have h1 : m ≤ airyTwistedLaplace uctSpos (ceCs * x) := hmin ⟨mul_nonneg hcs.le hx, h9⟩
    calc min m (c4 * ceCs ^ (-(5 / 2 : ℝ))) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ m * 1 :=
          mul_le_mul (min_le_left _ _) hp1 hp0 hmpos.le
      _ ≤ _ := by linarith
  · have hx0 : 0 < x := by
      by_contra h
      have : x = 0 := le_antisymm (not_lt.mp h) hx
      rw [this] at h9; norm_num at h9
    have h1 := hlarge (ceCs * x) h9
    have h2 : (1 + x) ^ (-(5 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
    rw [Real.mul_rpow hcs.le hx0.le] at h1
    calc min m (c4 * ceCs ^ (-(5 / 2 : ℝ))) * (1 + x) ^ (-(5 / 2 : ℝ))
        ≤ (c4 * ceCs ^ (-(5 / 2 : ℝ))) * x ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul (min_le_right _ _) h2 hp0 (by positivity)
      _ = c4 * (ceCs ^ (-(5 / 2 : ℝ)) * x ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ _ := h1

/-- info: 'FormalResearch.SignUncertainty.uctSpos_right_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSpos_right_tail

/-- info: 'FormalResearch.SignUncertainty.airyTwistedLaplace_uctSpos_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplace_uctSpos_large

/-- info: 'FormalResearch.SignUncertainty.airyTwistedLaplace_uctSpos_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplace_uctSpos_floor

end FormalResearch.SignUncertainty
