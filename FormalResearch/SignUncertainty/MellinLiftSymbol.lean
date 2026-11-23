module

public import FormalResearch.SignUncertainty.MellinLiftEigen
public import FormalResearch.SignUncertainty.MellinMajorantHId
public import FormalResearch.SignUncertainty.MellinDecay
public import FormalResearch.SignUncertainty.WindowTranslation
public import FormalResearch.CohnElkies.MellinKernelHolomorphic

/-!
# `O.11ak`, symbol side: the multiplier `Φ_σ(z) = (2π)^{-z} Γ(z) e^{cℋ(1-z/c)} [W((c-z)/c^{2/3}) + σ W(z/c^{2/3})]`

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Theorem `O.11ak`, `(ceo:O11ak.2)` and Proof 1.  For a symbol `W` holomorphic on `Re w > 0` with
`|W(w)| ≤ B (1 + |Im w|)^{-5/2}` on `Re w ≥ 0` and `W(w̄) = conj W(w)`, the multiplier `liftPhi W c σ` satisfies `MellinLiftData c` (holomorphic on `0 < Re z < c`, the decay
`(1 + |Im z|)^{-2}` on closed sub-strips (right half by `norm_mellinK0_vert_le` and the kernel identity `mellin_strip_kernel_eq`, left half by the reflection and the Gamma ratio
`norm_Gamma_ratio_le`), real) and the reflection `mellinMult (c - z) = σ mellinMult z` (`ℋ(1 - ζ) = ℋ(ζ)`).

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `ξ₁ = 1/(2π c)`: the value of `ξ` for which `(2π c ξ)^{cζ} = 1`. -/
noncomputable def liftXi (c : ℝ) : ℝ := 1 / (2 * Real.pi * c)

/-- The two-edge symbol `W((c - z)/c^{2/3}) + σ W(z/c^{2/3})`. -/
noncomputable def liftS (W : ℂ → ℂ) (c σ : ℝ) (z : ℂ) : ℂ :=
  W ((c - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)) + (σ : ℂ) * W (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ))

/-- The multiplier `Φ_σ(z) = (2π)^{-z} Γ(z) e^{cℋ(1 - z/c)} S(z)`. -/
noncomputable def liftPhi (W : ℂ → ℂ) (c σ : ℝ) (z : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) * liftS W c σ z

lemma liftXi_pos {c : ℝ} (hc : 0 < c) : 0 < liftXi c := by unfold liftXi; positivity

/-- `Γ(z) e^{cℋ(1 - z/c)} = Γ(c) K₀(1 - z/c, ξ₁)` on `0 < Re z < c`. -/
theorem gamma_exp_stripH_eq {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re ≤ c) :
    Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) =
      Complex.Gamma (c : ℂ) * mellinK0 c (1 - z / c) (liftXi c) := by
  have hζ0 : 0 ≤ (1 - z / (c : ℂ)).re := by
    have : (1 - z / (c : ℂ)).re = 1 - z.re / c := by simp [Complex.div_re, Complex.normSq_ofReal]; field_simp
    rw [this]; have := (div_le_one hc).mpr hz1; linarith
  have hζ1 : (1 - z / (c : ℂ)).re < 1 := by
    have : (1 - z / (c : ℂ)).re = 1 - z.re / c := by simp [Complex.div_re, Complex.normSq_ofReal]; field_simp
    rw [this]; have : 0 < z.re / c := by positivity
    linarith
  have key := mellin_strip_kernel_eq hc (liftXi_pos hc) hζ0 hζ1
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e1 : (c : ℂ) * (1 - (1 - z / (c : ℂ))) = z := by field_simp; ring
  have e2 : (2 * Real.pi * c * liftXi c : ℂ) = 1 := by
    unfold liftXi; push_cast; field_simp
  rw [e1, e2, Complex.one_cpow, mul_one] at key
  have hGc : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hc)
  rw [← key]
  field_simp


/-- The symbol hypotheses: holomorphic on `Re w > 0`, the `U.2` bound on `Re w ≥ 0`, real. -/
structure LiftSymbolData (W : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ W {w : ℂ | 0 < w.re}
  cont : ContinuousOn W {w : ℂ | 0 ≤ w.re}
  bound : ∃ B : ℝ, ∀ w : ℂ, 0 ≤ w.re → ‖W w‖ ≤ B * (1 + |w.im|) ^ (-(5 / 2 : ℝ))
  real : ∀ w : ℂ, 0 < w.re → W (starRingEnd ℂ w) = starRingEnd ℂ (W w)

section

variable {W : ℂ → ℂ} {c σ : ℝ}

lemma re_one_sub_div {c : ℝ} (hc : 0 < c) (z : ℂ) : (1 - z / (c : ℂ)).re = 1 - z.re / c := by
  simp [Complex.div_re, Complex.normSq_ofReal]; field_simp

lemma re_div_cpow {c : ℝ} (hc : 0 < c) (z : ℂ) :
    (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re = z.re / c ^ (2 / 3 : ℝ) := by
  rw [Complex.div_ofReal_re]

lemma im_div_cpow {c : ℝ} (hc : 0 < c) (z : ℂ) :
    (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).im = z.im / c ^ (2 / 3 : ℝ) := by
  rw [Complex.div_ofReal_im]

theorem liftPhi_eq {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re ≤ c) :
    liftPhi W c σ z = ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * (Complex.Gamma (c : ℂ) * mellinK0 c (1 - z / c) (liftXi c)) *
      liftS W c σ z := by
  unfold liftPhi
  rw [mul_assoc (((2 * Real.pi : ℝ) : ℂ) ^ (-z)), gamma_exp_stripH_eq hc hz0 hz1]

theorem liftPhi_differentiableOn (hW : LiftSymbolData W) {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    DifferentiableOn ℂ (liftPhi W c σ) {z : ℂ | 0 < z.re ∧ z.re < c} := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hb : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hcp : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hcp' : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcp.ne'
  have h1 : DifferentiableOn ℂ (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) {z : ℂ | 0 < z.re ∧ z.re < c} :=
    fun z _ => ((differentiableAt_id.neg).const_cpow (Or.inl hb)).differentiableWithinAt
  have h2 : DifferentiableOn ℂ (fun z : ℂ => mellinK0 c (1 - z / c) (liftXi c)) {z : ℂ | 0 < z.re ∧ z.re < c} := by
    refine (differentiableOn_mellinK0 hc (liftXi c)).comp
      (((differentiableOn_const _).sub (differentiableOn_id.div_const _))) fun z hz => ?_
    show |(1 - z / (c : ℂ)).re| < 1
    rw [re_one_sub_div hc]
    have h0 : 0 < z.re / c := by have := hz.1; positivity
    have h1' : z.re / c < 1 := (div_lt_one hc).mpr hz.2
    rw [abs_lt]; constructor <;> linarith
  have h3 : DifferentiableOn ℂ (fun z : ℂ => liftS W c σ z) {z : ℂ | 0 < z.re ∧ z.re < c} := by
    unfold liftS
    refine DifferentiableOn.add ?_ (DifferentiableOn.const_mul ?_ _)
    · refine hW.diff.comp ((differentiableOn_const _).sub differentiableOn_id |>.div_const _) fun z hz => ?_
      show 0 < ((c - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re
      rw [re_div_cpow hc]
      have : 0 < ((c : ℂ) - z).re := by simp; exact hz.2
      exact div_pos (by simpa using this) hcp
    · refine hW.diff.comp (differentiableOn_id.div_const _) fun z hz => ?_
      show 0 < (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re
      rw [re_div_cpow hc]
      exact div_pos hz.1 hcp
  refine ((h1.mul (h2.const_mul (Complex.Gamma (c : ℂ)))).mul h3).congr fun z hz => ?_
  exact liftPhi_eq hc hz.1 hz.2.le

/-- `mellinMult Φ z = e^{cℋ(1 - z/c)} S(z)`. -/
theorem mellinMult_liftPhi {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) :
    mellinMult (liftPhi W c σ) z = Complex.exp ((c : ℂ) * stripH (1 - z / c)) * liftS W c σ z := by
  unfold mellinMult liftPhi
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hb : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hX : ((2 * Real.pi : ℝ) : ℂ) ^ z * ((2 * Real.pi : ℝ) : ℂ) ^ (-z) = 1 := by
    rw [← Complex.cpow_add _ _ hb]; simp
  calc ((2 * Real.pi : ℝ) : ℂ) ^ z / Complex.Gamma z *
        (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) * liftS W c σ z)
      = (((2 * Real.pi : ℝ) : ℂ) ^ z * ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) * (Complex.Gamma z / Complex.Gamma z) *
          (Complex.exp ((c : ℂ) * stripH (1 - z / c)) * liftS W c σ z) := by ring
    _ = _ := by rw [hX, div_self hG]; ring

theorem stripH_one_sub {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) : stripH (1 - ζ) = stripH ζ := by
  have hz : ζ ∈ hStrip := ⟨by linarith, by linarith⟩
  have h0' : 0 ≤ (1 - ζ).re := by simp; linarith
  have h1' : (1 - ζ).re < 1 := by simp; linarith
  rw [← hInt_eq_stripH h0' h1', ← hInt_eq_stripH h0.le h1]
  exact hInt_one_sub hz

/-- The reflection `𝓜(c - z) = σ 𝓜(z)` for `σ = ±1`. -/
theorem mellinMult_liftPhi_reflect (hσ : σ = 1 ∨ σ = -1) {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re)
    (hz1 : z.re < c) :
    mellinMult (liftPhi W c σ) ((c : ℂ) - z) = (σ : ℂ) * mellinMult (liftPhi W c σ) z := by
  have hσσ : (σ : ℂ) * σ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hz0' : 0 < ((c : ℂ) - z).re := by simp; exact hz1
  rw [mellinMult_liftPhi hc hz0, mellinMult_liftPhi hc hz0']
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e1 : 1 - ((c : ℂ) - z) / c = z / c := by field_simp; ring
  have hre0 : 0 < (1 - z / (c : ℂ)).re := by rw [re_one_sub_div hc]; have := (div_lt_one hc).mpr hz1; linarith
  have hre1 : (1 - z / (c : ℂ)).re < 1 := by
    rw [re_one_sub_div hc]; have : 0 < z.re / c := by positivity
    linarith
  have e2 : stripH (z / c) = stripH (1 - z / c) := by
    have := stripH_one_sub hre0 hre1
    rwa [sub_sub_cancel] at this
  have e3 : liftS W c σ ((c : ℂ) - z) = (σ : ℂ) * liftS W c σ z := by
    unfold liftS
    rw [sub_sub_cancel]
    linear_combination (-(W (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)))) * hσσ
  rw [e1, e2, e3]; ring

end



lemma weight_scale {s0 : ℝ} (hs0 : 0 < s0) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t / s0) ^ (-(5 / 2 : ℝ)) ≤ (max 1 s0) ^ (5 / 2 : ℝ) * (1 + t) ^ (-(5 / 2 : ℝ)) := by
  set m := max 1 s0 with hm
  have hm0 : 0 < m := lt_max_of_lt_left one_pos
  have h1 : (1 + t) / m ≤ 1 + t / s0 := by
    rcases le_total s0 1 with h | h
    · rw [hm, max_eq_left h]
      have : t ≤ t / s0 := by rw [le_div_iff₀ hs0]; nlinarith
      linarith [div_one (1 + t)]
    · rw [hm, max_eq_right h]
      rw [add_div]
      have : 1 / s0 ≤ 1 := (div_le_one hs0).mpr h
      linarith
  have h2 : 0 < (1 + t) / m := by positivity
  calc (1 + t / s0) ^ (-(5 / 2 : ℝ)) ≤ ((1 + t) / m) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos h2 h1 (by norm_num)
    _ = m ^ (5 / 2 : ℝ) * (1 + t) ^ (-(5 / 2 : ℝ)) := by
        rw [Real.div_rpow (by positivity) hm0.le, Real.rpow_neg hm0.le, div_inv_eq_mul]; ring

section

variable {W : ℂ → ℂ} {c σ : ℝ}

theorem liftPhi_conj (hW : LiftSymbolData W) {c : ℝ} (hc : 0 < c) (σ : ℝ) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c) :
    liftPhi W c σ (starRingEnd ℂ z) = starRingEnd ℂ (liftPhi W c σ z) := by
  have hcz0 : 0 < (starRingEnd ℂ z).re := by simpa using hz0
  have hcz1 : (starRingEnd ℂ z).re < c := by simpa using hz1
  rw [liftPhi_eq hc hcz0 hcz1.le, liftPhi_eq hc hz0 hz1.le]
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcp : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  simp only [map_mul]
  have e1 : ((2 * Real.pi : ℝ) : ℂ) ^ (-(starRingEnd ℂ z)) = starRingEnd ℂ (((2 * Real.pi : ℝ) : ℂ) ^ (-z)) := by
    have hargs : (((2 * Real.pi : ℝ) : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj (((2 * Real.pi : ℝ) : ℂ)) (-z) hargs
    rw [Complex.conj_ofReal] at this
    rw [show -(starRingEnd ℂ z) = starRingEnd ℂ (-z) by simp, this]
  have e2 : mellinK0 c (1 - starRingEnd ℂ z / c) (liftXi c) = starRingEnd ℂ (mellinK0 c (1 - z / c) (liftXi c)) := by
    have hb0 : 0 < (1 - z / (c : ℂ)).re := by
      rw [re_one_sub_div hc]; have := (div_lt_one hc).mpr hz1; linarith
    have hb1 : (1 - z / (c : ℂ)).re < 1 := by
      rw [re_one_sub_div hc]; have : 0 < z.re / c := by positivity
      linarith
    have := mellinK0_conj (c := c) (liftXi_pos hc) hb0 hb1
    rw [← this]
    congr 1
    simp [Complex.conj_ofReal]
  have e3 : Complex.Gamma (c : ℂ) = starRingEnd ℂ (Complex.Gamma (c : ℂ)) := by
    rw [← Complex.Gamma_conj, Complex.conj_ofReal]
  have e4 : liftS W c σ (starRingEnd ℂ z) = starRingEnd ℂ (liftS W c σ z) := by
    unfold liftS
    have hA : ((c : ℂ) - starRingEnd ℂ z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
        starRingEnd ℂ (((c : ℂ) - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
      simp [Complex.conj_ofReal]
    have hB : starRingEnd ℂ z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
        starRingEnd ℂ (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
      simp [Complex.conj_ofReal]
    have hAre : 0 < (((c : ℂ) - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re := by
      rw [re_div_cpow hc]; exact div_pos (by simp; exact hz1) hcp
    have hBre : 0 < (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re := by
      rw [re_div_cpow hc]; exact div_pos hz0 hcp
    rw [hA, hB, hW.real _ hAre, hW.real _ hBre]
    simp [Complex.conj_ofReal]
  rw [e1, e2, e4]
  conv_lhs => rw [e3]

end


section

variable {W : ℂ → ℂ} {c σ : ℝ}

/-- Uniform bound of `K₀` on `Re ζ ∈ (0, 1/2]`. -/
lemma norm_K0_half_strip_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s τ : ℝ, 0 ≤ s → s ≤ 1 / 2 →
      ‖mellinK0 c ((s : ℂ) + (τ : ℂ) * Complex.I) (liftXi c)‖ ≤ K := by
  set L := Real.log (Real.pi ^ 2 * liftXi c) with hL
  refine ⟨2 * Real.exp (1 / (4 * c)) * Real.exp (c * (1 / 18 + |L| / 2)), by positivity, fun s τ hs hs2 => ?_⟩
  have hK1 : 1 ≤ 2 * Real.exp (1 / (4 * c)) * Real.exp (c * (1 / 18 + |L| / 2)) := by
    have h1 : 1 ≤ Real.exp (1 / (4 * c)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (1 / 18 + |L| / 2)) := Real.one_le_exp (by positivity)
    nlinarith
  rcases hs.eq_or_lt with h0 | hs
  · subst h0
    have := (norm_mellinK0_imag_le (c := c) (ξ := liftXi c) hc (liftXi_pos hc) τ).2
    have e : ((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I = (τ : ℂ) * Complex.I := by simp
    rw [e]
    refine this.trans ((Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ]) (by norm_num)).trans hK1)
  have h := norm_mellinK0_vert_le (c := c) (ξ := liftXi c) (s := s) (τ := τ) hc (liftXi_pos hc) hs hs2
  refine h.trans ?_
  have hlobe : Real.exp (-(c * (2 * (3 / 56 : ℝ) * s * lobeU τ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have := lobeU_nonneg τ
      have : 0 ≤ c * (2 * (3 / 56 : ℝ) * s * lobeU τ) := by positivity
      linarith)
  have h2 : Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * L)) ≤ Real.exp (c * (1 / 18 + |L| / 2)) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hc.le
    have h3 : s ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hs.le hs2 3
    have h4 : s * L ≤ |L| / 2 := by
      calc s * L ≤ s * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) hs.le
        _ ≤ (1 / 2) * |L| := mul_le_mul_of_nonneg_right hs2 (abs_nonneg _)
        _ = |L| / 2 := by ring
    nlinarith
  calc 2 * Real.exp (1 / (4 * c)) * Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * L)) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * s * lobeU τ)))
      ≤ 2 * Real.exp (1 / (4 * c)) * Real.exp (c * (1 / 18 + |L| / 2)) * 1 := by
        gcongr
    _ = _ := by ring

theorem liftPhi_right_bound (hW : LiftSymbolData W) {c : ℝ} (hc : 0 < c) (σ : ℝ) (hσ : |σ| ≤ 1) {a b : ℝ}
    (ha : c / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ c) :
    ∃ B : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖liftPhi W c σ z‖ ≤ B * (1 + |z.im|) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := norm_K0_half_strip_le hc
  obtain ⟨BW0, hBW0⟩ := hW.bound
  have hcp : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hr : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  set BW : ℝ := |BW0| with hBWdef
  have hBW : ∀ w : ℂ, 0 ≤ w.re → ‖W w‖ ≤ BW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := fun w hw =>
    (hBW0 w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  set m : ℝ := (max 1 (c ^ (2 / 3 : ℝ))) ^ (5 / 2 : ℝ) with hm
  refine ⟨‖Complex.Gamma (c : ℂ)‖ * K * (2 * BW * m), fun z hz1 hz2 => ?_⟩
  have hz0 : 0 < z.re := by linarith
  have hzc : z.re ≤ c := by linarith
  rw [liftPhi_eq hc hz0 hzc, norm_mul, norm_mul, norm_mul]
  have hpw : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith)
  have hKz : ‖mellinK0 c (1 - z / c) (liftXi c)‖ ≤ K := by
    have e : (1 - z / (c : ℂ)) = ((1 - z.re / c : ℝ) : ℂ) + ((-(z.im / c) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_ofReal] <;> field_simp
    rw [e]
    exact hK _ _ (by have := (div_le_one hc).mpr hzc; linarith)
      (by have : 1 / 2 ≤ z.re / c := by rw [le_div_iff₀ hc]; linarith
          linarith)
  have hS : ‖liftS W c σ z‖ ≤ 2 * BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ))) := by
    unfold liftS
    have hAre : 0 ≤ (((c : ℂ) - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re := by
      rw [re_div_cpow hc]; exact div_nonneg (by simp; linarith) hcp.le
    have hBre : 0 ≤ (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re := by
      rw [re_div_cpow hc]; exact div_nonneg hz0.le hcp.le
    have h1 := hBW _ hAre
    have h2 := hBW _ hBre
    rw [im_div_cpow hc] at h1 h2
    have hws := weight_scale hcp (abs_nonneg z.im)
    have e1 : |(((c : ℂ) - z).im) / c ^ (2 / 3 : ℝ)| = |z.im| / c ^ (2 / 3 : ℝ) := by
      rw [abs_div, abs_of_pos hcp]; simp
    have e2 : |z.im / c ^ (2 / 3 : ℝ)| = |z.im| / c ^ (2 / 3 : ℝ) := by
      rw [abs_div, abs_of_pos hcp]
    rw [e1] at h1; rw [e2] at h2
    have hB0 : BW * (1 + |z.im| / c ^ (2 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) ≤ BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hws (abs_nonneg _)
    have hBn : 0 ≤ BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ))) := by positivity
    calc ‖W (((c : ℂ) - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)) + (σ : ℂ) * W (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ))‖
        ≤ ‖W (((c : ℂ) - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ))‖ + ‖(σ : ℂ) * W (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ))‖ := norm_add_le _ _
      _ ≤ BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ))) + |σ| * (BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ)))) := by
        refine add_le_add (h1.trans hB0) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (h2.trans hB0) (abs_nonneg _)
      _ ≤ BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ))) + 1 * (BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ)))) := by
        gcongr
      _ = _ := by ring
  have hG : 0 ≤ ‖Complex.Gamma (c : ℂ)‖ := norm_nonneg _
  calc ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ * (‖Complex.Gamma (c : ℂ)‖ * ‖mellinK0 c (1 - z / c) (liftXi c)‖) * ‖liftS W c σ z‖
      ≤ 1 * (‖Complex.Gamma (c : ℂ)‖ * K) * (2 * BW * (m * (1 + |z.im|) ^ (-(5 / 2 : ℝ)))) := by
        gcongr
    _ = _ := by ring


lemma exists_bound_rect {f : ℂ → ℂ} {c a b : ℝ} (hf : ContinuousOn f {z : ℂ | 0 < z.re ∧ z.re < c}) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < c) : ∃ M : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ≤ 1 → ‖f z‖ ≤ M := by
  set C0 : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Icc a b ×ˢ Icc (-1 : ℝ) 1) with hC0
  have hC0c : IsCompact C0 := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hsub : C0 ⊆ {z : ℂ | 0 < z.re ∧ z.re < c} := by
    rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one, sub_self, Set.mem_setOf_eq]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨M, hM⟩ := hC0c.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨M, fun z h1 h2 h3 => hM z ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨(abs_le.mp h3).1, (abs_le.mp h3).2⟩⟩, ?_⟩⟩
  simp

theorem liftPhi_eq_mult {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) :
    liftPhi W c σ z = ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * mellinMult (liftPhi W c σ) z := by
  rw [mellinMult_liftPhi hc hz0]
  unfold liftPhi; ring

theorem liftPhi_left_bound (hW : LiftSymbolData W) {c : ℝ} (hc : 3 / 2 < c) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) {a : ℝ}
    (ha : 0 < a) :
    ∃ B : ℝ, ∀ z : ℂ, a ≤ z.re → z.re < c / 2 → 1 ≤ |z.im| → ‖liftPhi W c σ z‖ ≤ B * (1 + |z.im|) ^ (-(5 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hσ1 : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  obtain ⟨BR, hBR⟩ := liftPhi_right_bound hW hc0 σ hσ1 (a := c / 2) (b := max (c - a) (c / 2)) le_rfl
    (le_max_right _ _) (max_le (by linarith) (by linarith))
  set D : ℝ := Real.exp (2 * ((c + 1 / 2) * c ^ 2 / 2 + c ^ 3 / 3 + 2)) with hD
  refine ⟨D * (2 * Real.pi) ^ c * |BR|, fun z hz1 hz2 hy => ?_⟩
  have hz0 : 0 < z.re := by linarith
  have hzc : z.re < c := by linarith
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hr1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hz0' : 0 < ((c : ℂ) - z).re := by simp; exact hzc
  -- the reflected value
  have hrefl := mellinMult_liftPhi_reflect (W := W) hσ hc0 (z := (c : ℂ) - z) hz0' (by simp; exact hz0)
  rw [sub_sub_cancel] at hrefl
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hGc : Complex.Gamma ((c : ℂ) - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0'
  have hrne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hmc : mellinMult (liftPhi W c σ) ((c : ℂ) - z) =
      ((2 * Real.pi : ℝ) : ℂ) ^ ((c : ℂ) - z) / Complex.Gamma ((c : ℂ) - z) * liftPhi W c σ ((c : ℂ) - z) := rfl
  rw [liftPhi_eq_mult hc0 hz0, hrefl, hmc]
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  -- norms
  have hn1 : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ = (2 * Real.pi) ^ (-z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp
  have hn2 : ‖((2 * Real.pi : ℝ) : ℂ) ^ ((c : ℂ) - z)‖ = (2 * Real.pi) ^ (c - z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp
  have hprod : (2 * Real.pi) ^ (-z.re) * (2 * Real.pi) ^ (c - z.re) = (2 * Real.pi) ^ (c - 2 * z.re) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hpow_le : (2 * Real.pi) ^ (c - 2 * z.re) ≤ (2 * Real.pi) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hratio := norm_Gamma_ratio_le (c := c) (x1 := z.re) (y := z.im) hz0 (by linarith) hy
  have hzre : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  have hcz : (((c - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * Complex.I) = (c : ℂ) - z := by
    apply Complex.ext <;> simp
  rw [hzre, hcz] at hratio
  have hy0 : |z.im| ^ (2 * z.re - c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  -- the reflected factor bound
  have hB := hBR ((c : ℂ) - z) (by simp; linarith) (by
    simp only [Complex.sub_re, Complex.ofReal_re]
    exact (by linarith : c - z.re ≤ c - a).trans (le_max_left _ _))
  have himn : |((c : ℂ) - z).im| = |z.im| := by simp
  rw [himn] at hB
  have hGn : 0 < ‖Complex.Gamma ((c : ℂ) - z)‖ := norm_pos_iff.mpr hGc
  have hL : ‖(((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * ((σ : ℂ) * (((2 * Real.pi : ℝ) : ℂ) ^ ((c : ℂ) - z) / Complex.Gamma ((c : ℂ) - z) * liftPhi W c σ ((c : ℂ) - z))))‖
      = ((2 * Real.pi) ^ (-z.re) * (2 * Real.pi) ^ (c - z.re)) * (‖Complex.Gamma z‖ / ‖Complex.Gamma ((c : ℂ) - z)‖) *
        ‖liftPhi W c σ ((c : ℂ) - z)‖ := by
    simp only [norm_mul, norm_div, hn1, hn2, hσn]
    ring
  rw [hL, hprod]
  have hBn : 0 ≤ BR * (1 + |z.im|) ^ (-(5 / 2 : ℝ)) := (norm_nonneg _).trans hB
  calc (2 * Real.pi) ^ (c - 2 * z.re) * (‖Complex.Gamma z‖ / ‖Complex.Gamma ((c : ℂ) - z)‖) * ‖liftPhi W c σ ((c : ℂ) - z)‖
      ≤ (2 * Real.pi) ^ c * (D * 1) * (BR * (1 + |z.im|) ^ (-(5 / 2 : ℝ))) := by
        refine mul_le_mul (mul_le_mul hpow_le (hratio.trans (mul_le_mul_of_nonneg_left hy0 (by positivity))) (by positivity)
          (by positivity)) hB (norm_nonneg _) (by positivity)
    _ ≤ (2 * Real.pi) ^ c * (D * 1) * (|BR| * (1 + |z.im|) ^ (-(5 / 2 : ℝ))) := by
        gcongr; exact le_abs_self _
    _ = _ := by ring



/-- Continuity of `Φ_σ` up to the edge `Re z = c`. -/
theorem liftPhi_continuousOn_edge (hW : LiftSymbolData W) {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    ContinuousOn (liftPhi W c σ) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
  have hb : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  have hcp : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have h1 : ContinuousOn (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) {z : ℂ | 0 < z.re ∧ z.re ≤ c} :=
    (Continuous.const_cpow continuous_neg (Or.inl hb)).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => mellinK0 c (1 - z / c) (liftXi c)) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
    refine ((differentiableOn_mellinK0 hc (liftXi c)).continuousOn).comp
      ((continuousOn_const.sub (continuousOn_id.div_const _))) fun z hz => ?_
    show |(1 - z / (c : ℂ)).re| < 1
    rw [re_one_sub_div hc]
    have h0 : 0 < z.re / c := by have := hz.1; positivity
    have h1' : z.re / c ≤ 1 := (div_le_one hc).mpr hz.2
    rw [abs_lt]; constructor <;> linarith
  have h3 : ContinuousOn (fun z : ℂ => liftS W c σ z) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
    unfold liftS
    refine ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)
    · refine hW.cont.comp ((continuousOn_const.sub continuousOn_id).div_const _) fun z hz => ?_
      show 0 ≤ ((c - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re
      rw [re_div_cpow hc]
      exact div_nonneg (by simp; exact hz.2) hcp.le
    · refine hW.cont.comp (continuousOn_id.div_const _) fun z hz => ?_
      show 0 ≤ (z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)).re
      rw [re_div_cpow hc]
      exact div_nonneg hz.1.le hcp.le
  refine ((h1.mul ((continuousOn_const (c := Complex.Gamma (c : ℂ))).mul h2)).mul h3).congr fun z hz => ?_
  exact liftPhi_eq hc hz.1 hz.2


/-- **Contour shift to the edge `Re z = c`**: the lift is also the inverse Mellin integral along `Re z = c`. -/
theorem mellinInv_liftPhi_edge (hW : LiftSymbolData W) {c : ℝ} (hc : 3 / 2 < c) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    mellinInv c (liftPhi W c σ) Δ = mellinInv (c / 2) (liftPhi W c σ) Δ := by
  have hc0 : 0 < c := by linarith
  have hσ1 : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  obtain ⟨B, hB⟩ := liftPhi_right_bound hW hc0 σ hσ1 (a := c / 2) (b := c) le_rfl (by linarith) le_rfl
  have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  set H : ℂ → ℂ := fun z => (Δ : ℂ) ^ (-z) • liftPhi W c σ z with hH
  have hcont : ContinuousOn H {w : ℂ | c / 2 ≤ w.re ∧ w.re ≤ c} :=
    (Continuous.const_cpow continuous_neg (Or.inl hΔ0)).continuousOn.smul
      ((liftPhi_continuousOn_edge hW hc0 σ).mono fun w hw => ⟨by linarith [hw.1], hw.2⟩)
  have hd : DifferentiableOn ℂ H {w : ℂ | c / 2 < w.re ∧ w.re < c} :=
    DifferentiableOn.smul (fun w _ => ((differentiableAt_id.neg).const_cpow (Or.inl hΔ0)).differentiableWithinAt)
      ((liftPhi_differentiableOn hW hc0 σ).mono fun w hw => ⟨by linarith [hw.1], hw.2⟩)
  have key := CohnElkies.strip_shift (H := H) (a := c / 2) (b := c) (by linarith) hcont hd
    (integrable_weight ((Δ ^ (-(c / 2)) + Δ ^ (-c)) * B))
    (fun w hw1 hw2 => by
      have h1 := hB w hw1 hw2
      have h2 := rpow_neg_le_sum hΔ hw1 hw2
      simp only [hH, norm_smul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]
      simp only [Complex.neg_re]
      calc Δ ^ (-w.re) * ‖liftPhi W c σ w‖ ≤ (Δ ^ (-(c / 2)) + Δ ^ (-c)) * (B * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring)
    (tendsto_weight_atTop _) (tendsto_weight_atBot _)
  unfold mellinInv
  congr 1

/-- **The strip multiplier `Φ_σ` of a symbol satisfies the hypotheses of the Mellin hub.** -/
theorem liftPhi_mellinLiftData (hW : LiftSymbolData W) {c : ℝ} (hc : 3 / 2 < c) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    MellinLiftData c (liftPhi W c σ) where
  hol := liftPhi_differentiableOn hW (by linarith) σ
  decay := by
    intro a b ha hab hb
    have hc0 : 0 < c := by linarith
    have hσ1 : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> simp
    obtain ⟨M, hM⟩ := exists_bound_rect (liftPhi_differentiableOn hW hc0 σ).continuousOn ha hab hb
    obtain ⟨BR, hBR⟩ := liftPhi_right_bound hW hc0 σ hσ1 (a := c / 2) (b := max b (c / 2)) le_rfl
      (le_max_right _ _) (max_le hb.le (by linarith))
    obtain ⟨BL, hBL⟩ := liftPhi_left_bound hW hc σ hσ ha
    refine ⟨4 * |M| + |BR| + |BL|, fun z hz1 hz2 => ?_⟩
    have hw : (1 + |z.im|) ^ (-(5 / 2 : ℝ)) ≤ (1 + |z.im|) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by norm_num)
    have hw0 : 0 ≤ (1 + |z.im|) ^ (-2 : ℝ) := by positivity
    rcases le_total |z.im| 1 with hy | hy
    · have h1 := hM z hz1 hz2 hy
      have h4 : (1 / 4 : ℝ) ≤ (1 + |z.im|) ^ (-2 : ℝ) := by
        have : (2 : ℝ) ^ (-2 : ℝ) ≤ (1 + |z.im|) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [abs_nonneg z.im]) (by linarith) (by norm_num)
        have e : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
          rw [Real.rpow_neg (by norm_num)]; norm_num
        rwa [e] at this
      have := le_abs_self M
      nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
    · rcases le_or_gt (c / 2) z.re with hr | hr
      · have h1 := hBR z hr (hz2.trans (le_max_left _ _))
        have : BR * (1 + |z.im|) ^ (-(5 / 2 : ℝ)) ≤ |BR| * (1 + |z.im|) ^ (-2 : ℝ) :=
          (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
        nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
      · have h1 := hBL z hz1 hr hy
        have : BL * (1 + |z.im|) ^ (-(5 / 2 : ℝ)) ≤ |BL| * (1 + |z.im|) ^ (-2 : ℝ) :=
          (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
        nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
  real := fun z hz0 hz1 => liftPhi_conj hW (by linarith) σ hz0 hz1

end


/-! ### The lift symbol `W_X` of a seed `X` with the `U.2` package -/

lemma bsplineE1_conj (ζ : ℂ) : bsplineE1 (starRingEnd ℂ ζ) = starRingEnd ℂ (bsplineE1 ζ) := by
  unfold bsplineE1
  by_cases h : ζ = 0
  · simp [h]
  · have h' : starRingEnd ℂ ζ ≠ 0 := by simpa using h
    simp only [h, h', if_false, map_div₀, map_sub, map_one]
    rw [← Complex.exp_conj]; simp

lemma airyTwistedLaplaceC_conj (X : ℝ → ℝ) (y : ℂ) :
    airyTwistedLaplaceC X (starRingEnd ℂ y) = starRingEnd ℂ (airyTwistedLaplaceC X y) := by
  unfold airyTwistedLaplaceC
  simp only [map_mul]
  have hK : starRingEnd ℂ (ceK : ℂ) = (ceK : ℂ) := Complex.conj_ofReal _
  rw [hK]
  congr 1
  · congr 1
    rw [← Complex.exp_conj]
    congr 1
    have : starRingEnd ℂ (12 : ℂ) = 12 := map_ofNat (starRingEnd ℂ) 12
    simp [map_div₀, map_pow, this]
  · rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    rw [← Complex.exp_conj]; simp

lemma liftSymbol_conj (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (w : ℂ) :
    liftSymbol X δ₀ m (starRingEnd ℂ w) = starRingEnd ℂ (liftSymbol X δ₀ m w) := by
  unfold liftSymbol liftMultiplier
  simp only [map_mul, map_pow]
  congr 1
  · congr 1
    rw [← bsplineE1_conj]; congr 1; simp [Complex.conj_ofReal]
  · rw [← airyTwistedLaplaceC_conj]; congr 1; simp [Complex.conj_ofReal]

theorem liftSymbolData_of_hasU2 {X : ℝ → ℝ} (h : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) :
    LiftSymbolData (liftSymbol X δ₀ m) where
  diff := liftSymbol_differentiableOn h δ₀ m
  cont := liftSymbol_continuousOn h δ₀ m
  bound := by
    obtain ⟨C, hC, hb⟩ := hasU2_norm_liftSymbol_le_unif h
    exact ⟨C, fun w hw => hb m hδ hw⟩
  real := fun w _ => liftSymbol_conj X δ₀ m w


/-- info: 'FormalResearch.SignUncertainty.liftPhi_mellinLiftData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.liftPhi_mellinLiftData

/-- info: 'FormalResearch.SignUncertainty.mellinMult_liftPhi_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.mellinMult_liftPhi_reflect

/-- info: 'FormalResearch.SignUncertainty.liftSymbolData_of_hasU2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.liftSymbolData_of_hasU2

end FormalResearch.SignUncertainty
