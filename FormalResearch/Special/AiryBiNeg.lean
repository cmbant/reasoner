module

public import FormalResearch.Special.AiryBiMono

/-!
# `Bi > 0` on `[-11/10, ∞)` and `Bi` increasing there

Numerical input (all proved): `Ai(0) ≥ 0.346` from `Ai(0) = 3^{-2/3}/Γ(2/3)`, `Γ(2/3) ≤ (√π+1)/2` (convexity of `Γ`:
`Γ(5/3) ≤ (2/3) Γ(3/2) + (1/3) Γ(2)`), `3^{-2/3} ≥ 0.48`.  Hence `Bi(0) = √3 Ai(0) ≥ 0.599` and
`Bi(0) Bi'(0) = √3/(2π)`.

ODE argument on `[m, 0]` where `Bi ≥ 0` (`Bi'' = x Bi ≤ 0`): `Bi' ≥ Bi'(0)`; hence `Bi(x) ≤ Bi(0) + Bi'(0) x`; hence
`Bi'' ≥ x(Bi(0) + Bi'(0) x)` and `Bi'(x) ≤ Bi'(0) + Bi(0) x²/2 + Bi'(0) x³/3`; hence
`Bi(x) ≥ ℓ(x) := Bi(0) + Bi'(0) x + Bi(0) x³/6 + Bi'(0) x⁴/12`.  `ℓ > 0` on `[-11/10, 0]` for the above numerical values
(`ℓ(-11/10) ≥ 0.013`), so a continuity argument gives `Bi > 0` on `[-11/10, 0]`.
Combined with `Bi' > 0` on `[0, ∞)` and the monotonicity of `Bi` this gives `Bi' > 0` and `Bi ≥ 1/100` on
`[-11/10, ∞)` (`airyBi_ge_one_hundredth`; numerically `Bi(-11/10) ≈ 0.0443`).
The first zero of `Bi` is `≈ -1.1737`; this file only gets to `-1.1`.  Not formalised: the location of the first zero.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### Numerical input -/

lemma gamma_two_thirds_le : Real.Gamma (2 / 3) ≤ (√π + 1) / 2 := by
  have hc := Real.convexOn_Gamma.2 (show (3 / 2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
    (show (2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num) (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    (show (0 : ℝ) ≤ 1 / 3 by norm_num) (by norm_num)
  have e1 : (2 / 3 : ℝ) • (3 / 2 : ℝ) + (1 / 3 : ℝ) • (2 : ℝ) = 5 / 3 := by
    simp only [smul_eq_mul]; norm_num
  rw [e1] at hc
  have h53 : Real.Gamma (5 / 3) = 2 / 3 * Real.Gamma (2 / 3) := by
    rw [show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h32 : Real.Gamma (3 / 2) = √π / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [h53, h32, Real.Gamma_two] at hc
  simp only [smul_eq_mul] at hc
  linarith

lemma sqrt_pi_le : √π ≤ 1.7725 := by
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [Real.pi_lt_d4]

lemma three_rpow_neg_two_thirds_ge : (0.48 : ℝ) ≤ (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have h3 : ((3 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 3 = 1 / 9 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hx : 0 ≤ (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  by_contra hlt
  rw [not_le] at hlt
  have := pow_lt_pow_left₀ hlt hx (by norm_num : (3 : ℕ) ≠ 0)
  rw [h3] at this
  norm_num at this

lemma sqrt3_div_two_pi_le : √3 / (2 * π) ≤ 0.2757 := by
  have hs : √(3 : ℝ) ≤ 1.7321 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have := Real.pi_gt_d4
  rw [div_le_iff₀ (by positivity)]
  nlinarith


lemma gamma_third_le : Real.Gamma (1 / 3) ≤ 3 := by
  have hc := Real.convexOn_Gamma.2 (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
    (show (2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num) (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    (show (0 : ℝ) ≤ 1 / 3 by norm_num) (by norm_num)
  have e1 : (2 / 3 : ℝ) • (1 : ℝ) + (1 / 3 : ℝ) • (2 : ℝ) = 4 / 3 := by
    simp only [smul_eq_mul]; norm_num
  rw [e1] at hc
  have h43 : Real.Gamma (4 / 3) = 1 / 3 * Real.Gamma (1 / 3) := by
    rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  rw [Real.Gamma_two, Real.Gamma_one] at hc
  simp only [smul_eq_mul] at hc
  have h43' : Real.Gamma (1 / 3) = 3 * Real.Gamma (4 / 3) := by rw [h43]; ring
  rw [h43']
  linarith

lemma three_rpow_neg_two_thirds_le : (3 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 0.481 := by
  have h3 : ((3 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 3 = 1 / 9 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hx : 0 ≤ (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  by_contra hlt
  rw [not_le] at hlt
  have := pow_lt_pow_left₀ hlt (by norm_num : (0 : ℝ) ≤ 0.481) (by norm_num : (3 : ℕ) ≠ 0)
  rw [h3] at this
  norm_num at this

lemma airyAi_zero_le : airyAi 0 ≤ 0.4 := by
  rw [airyAi_zero_gamma_third]
  have h1 := gamma_third_le
  have h2 := three_rpow_neg_two_thirds_le
  have h3 : √(3 : ℝ) ≤ 1.7321 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 := Real.pi_gt_d4
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hx : 0 < (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have h5 : √(3 : ℝ) / (2 * π) ≤ 0.2757 := sqrt3_div_two_pi_le
  have : (3 : ℝ) ^ (-(2 / 3 : ℝ)) * Real.Gamma (1 / 3) ≤ 0.481 * 3 := by
    nlinarith
  have h6 : 0 ≤ √(3 : ℝ) / (2 * π) := by positivity
  calc √3 / (2 * π) * ((3 : ℝ) ^ (-(2 / 3 : ℝ)) * Real.Gamma (1 / 3))
      ≤ 0.2757 * (0.481 * 3) := mul_le_mul h5 this (by positivity) (by norm_num)
    _ ≤ 0.4 := by norm_num

lemma airyAi_zero_ge : 0.346 ≤ airyAi 0 := by
  rw [airyAi_zero]
  have hG : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h1 := gamma_two_thirds_le
  have h2 := sqrt_pi_le
  have h3 := three_rpow_neg_two_thirds_ge
  rw [le_div_iff₀ hG]
  nlinarith

lemma sqrt3_ge : (1.732 : ℝ) ≤ √3 := by
  rw [Real.le_sqrt' (by norm_num)]; norm_num

lemma airyBi_zero_ge : 0.599 ≤ airyBi 0 := by
  rw [airyBi_zero_real]
  have := airyAi_zero_ge
  have := sqrt3_ge
  nlinarith

lemma airyBi_zero_le : airyBi 0 ≤ 0.7 := by
  rw [airyBi_zero_real]
  have h1 := airyAi_zero_le
  have h2 : √(3 : ℝ) ≤ 1.7321 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have := airyAi_pos (le_refl (0 : ℝ))
  nlinarith

/-- `Bi(0) Bi'(0) = √3/(2π)`. -/
lemma airyBi_mul_airyBiDeriv_zero : airyBi 0 * airyBiDeriv 0 = √3 / (2 * π) := by
  rw [airyBi_zero_real, airyBiDeriv_zero_real]
  have h := airyAi_mul_airyAi'_zero
  have hs : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hp := Real.pi_pos
  have h3 : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have e : √3 * airyAi 0 * -(√3 * airyAi' 0) = -(√3 * √3) * (airyAi 0 * airyAi' 0) := by ring
  rw [e, h, hs]
  field_simp
  nlinarith

lemma pp_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1.1) :
    0.0095 ≤ 0.3588 * (1 - t ^ 3 / 6) - 0.2757 * (t - t ^ 4 / 12) := by
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1),
    mul_nonneg (mul_nonneg (mul_nonneg h0 h0) h0) (sub_nonneg.2 h1), sq_nonneg t, sq_nonneg (t - 1.1)]

/-! ### The ODE comparison on `[m, 0]` -/

/-- The second Picard iterate of `Bi` at `0` (as a function of `x ≤ 0`). -/
noncomputable def airyBiLower (x : ℝ) : ℝ :=
  airyBi 0 + airyBiDeriv 0 * x + airyBi 0 * x ^ 3 / 6 + airyBiDeriv 0 * x ^ 4 / 12

lemma monotoneOn_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h : ∀ x ∈ Icc a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
  · exact fun y _ => (hf y).continuousAt.continuousWithinAt
  · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    rw [(hf y).deriv]
    exact h y (Ioo_subset_Icc_self hy)

lemma airyBi_chain {m : ℝ} (hm : m ≤ 0) (hpos : ∀ y ∈ Icc m 0, 0 ≤ airyBi y) :
    ∀ x ∈ Icc m 0, airyBiDeriv 0 ≤ airyBiDeriv x ∧ airyBiLower x ≤ airyBi x := by
  have hβ1pos : 0 < airyBiDeriv 0 := airyBiDeriv_zero_pos
  -- `Bi'` is antitone on `[m, 0]`
  have hanti : AntitoneOn airyBiDeriv (Icc m 0) := by
    have := monotoneOn_of_hasDerivAt (f := fun x => -airyBiDeriv x) (f' := fun x => -(x * airyBi x))
      (a := m) (b := 0) (fun x => (hasDerivAt_airyBiDeriv x).neg) (fun x hx => by
        have h1 := hpos x hx
        have h2 := hx.2
        nlinarith)
    intro x hx y hy hxy
    have := this hx hy hxy
    simp only at this
    linarith
  have ha1 : ∀ x ∈ Icc m 0, airyBiDeriv 0 ≤ airyBiDeriv x := fun x hx =>
    hanti hx ⟨hm, le_rfl⟩ hx.2
  -- `Bi(x) - β1 x` is monotone, so `Bi x ≤ β0 + β1 x`
  have ha2 : ∀ x ∈ Icc m 0, airyBi x ≤ airyBi 0 + airyBiDeriv 0 * x := by
    have hmono := monotoneOn_of_hasDerivAt (f := fun x => airyBi x - airyBiDeriv 0 * x)
      (f' := fun x => airyBiDeriv x - airyBiDeriv 0) (a := m) (b := 0)
      (fun x => by
        have := (hasDerivAt_airyBi x).sub ((hasDerivAt_id x).const_mul (airyBiDeriv 0))
        exact this.congr_deriv (by simp))
      (fun x hx => by linarith [ha1 x hx])
    intro x hx
    have := hmono hx ⟨hm, le_rfl⟩ hx.2
    simp only [mul_zero, sub_zero] at this
    linarith
  -- `Bi'(x) ≤ β1 + β0 x²/2 + β1 x³/3`
  have hc : ∀ x ∈ Icc m 0, airyBiDeriv x ≤
      airyBiDeriv 0 + airyBi 0 * x ^ 2 / 2 + airyBiDeriv 0 * x ^ 3 / 3 := by
    have hmono := monotoneOn_of_hasDerivAt
      (f := fun x => airyBiDeriv x - (airyBi 0 * x ^ 2 / 2 + airyBiDeriv 0 * x ^ 3 / 3))
      (f' := fun x => x * (airyBi x - airyBi 0 - airyBiDeriv 0 * x)) (a := m) (b := 0)
      (fun x => by
        have h1 := hasDerivAt_airyBiDeriv x
        have h2 := (((hasDerivAt_pow 2 x).const_mul (airyBi 0)).div_const 2).add
            (((hasDerivAt_pow 3 x).const_mul (airyBiDeriv 0)).div_const 3)
        exact (h1.sub h2).congr_deriv (by push_cast; ring))
      (fun x hx => by
        have := ha2 x hx
        have hx0 := hx.2
        nlinarith)
    intro x hx
    have := hmono hx ⟨hm, le_rfl⟩ hx.2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, add_zero,
      sub_zero] at this
    linarith
  -- `Bi(x) ≥ ℓ(x)`
  have hd : ∀ x ∈ Icc m 0, airyBiLower x ≤ airyBi x := by
    have hanti2 := monotoneOn_of_hasDerivAt
      (f := fun x => -(airyBi x - airyBiLower x))
      (f' := fun x => -(airyBiDeriv x - (airyBiDeriv 0 + airyBi 0 * x ^ 2 / 2 + airyBiDeriv 0 * x ^ 3 / 3)))
      (a := m) (b := 0)
      (fun x => by
        have h1 := hasDerivAt_airyBi x
        have h2 : HasDerivAt airyBiLower
            (airyBiDeriv 0 + airyBi 0 * x ^ 2 / 2 + airyBiDeriv 0 * x ^ 3 / 3) x := by
          unfold airyBiLower
          have := ((((hasDerivAt_const x (airyBi 0)).add ((hasDerivAt_id x).const_mul (airyBiDeriv 0))).add
            (((hasDerivAt_pow 3 x).const_mul (airyBi 0)).div_const 6)).add
            (((hasDerivAt_pow 4 x).const_mul (airyBiDeriv 0)).div_const 12))
          exact this.congr_deriv (by push_cast; ring)
        exact (h1.sub h2).neg)
      (fun x hx => by linarith [hc x hx])
    intro x hx
    have := hanti2 hx ⟨hm, le_rfl⟩ hx.2
    simp only [airyBiLower] at this
    norm_num at this
    unfold airyBiLower
    linarith
  exact fun x hx => ⟨ha1 x hx, hd x hx⟩


/-- `Bi(0)·ℓ(x) ≥ 0.0095` on `[-11/10, 0]`; hence `ℓ ≥ 1/100`. -/
lemma airyBiLower_ge {x : ℝ} (hx1 : -(11 / 10 : ℝ) ≤ x) (hx0 : x ≤ 0) : 1 / 100 ≤ airyBiLower x := by
  have hq := airyBi_mul_airyBiDeriv_zero
  have hq' := sqrt3_div_two_pi_le
  have hb0 := airyBi_zero_ge
  have hb1 := airyBi_zero_le
  have hp := pp_poly (t := -x) (by linarith) (by norm_num at hx1 ⊢; linarith)
  have hxc : x ^ 3 ≥ -1.331 := by nlinarith [sq_nonneg x, sq_nonneg (x + 1.1)]
  have h1 : 0 ≤ 1 + x ^ 3 / 6 := by nlinarith
  have h2 : x + x ^ 4 / 12 ≤ 0 := by nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  have hB : 0.3588 ≤ airyBi 0 ^ 2 := by nlinarith
  have e : airyBi 0 * airyBiLower x =
      airyBi 0 ^ 2 * (1 + x ^ 3 / 6) + (airyBi 0 * airyBiDeriv 0) * (x + x ^ 4 / 12) := by
    unfold airyBiLower; ring
  have h3 : 0.0095 ≤ airyBi 0 * airyBiLower x := by
    rw [e]
    have a1 : 0.3588 * (1 + x ^ 3 / 6) ≤ airyBi 0 ^ 2 * (1 + x ^ 3 / 6) :=
      mul_le_mul_of_nonneg_right hB h1
    have a2 : 0.2757 * (x + x ^ 4 / 12) ≤ (airyBi 0 * airyBiDeriv 0) * (x + x ^ 4 / 12) := by
      rw [hq]
      exact mul_le_mul_of_nonpos_right hq' h2
    have a3 : 0.0095 ≤ 0.3588 * (1 + x ^ 3 / 6) + 0.2757 * (x + x ^ 4 / 12) := by
      have := hp
      nlinarith
    linarith
  have hb0pos : 0 < airyBi 0 := by linarith
  by_contra hlt
  rw [not_le] at hlt
  have : airyBi 0 * airyBiLower x < airyBi 0 * (1 / 100) := mul_lt_mul_of_pos_left hlt hb0pos
  nlinarith

/-- **`Bi ≥ 1/100` and `Bi' ≥ Bi'(0)` on `[-11/10, 0]`**: `Bi(x) ≥ ℓ(x) ≥ 1/100`. -/
theorem airyBi_ge_on_Icc {x : ℝ} (hx1 : -(11 / 10 : ℝ) ≤ x) (hx0 : x ≤ 0) :
    airyBiLower x ≤ airyBi x ∧ airyBiDeriv 0 ≤ airyBiDeriv x := by
  set S : Set ℝ := Icc (-(11 / 10 : ℝ)) 0 ∩ {y | airyBi y ≤ 0} with hS
  by_cases hne : S.Nonempty
  · exfalso
    have hSc : IsCompact S :=
      isCompact_Icc.inter_right (isClosed_le (differentiable_airyBi.continuous) continuous_const)
    obtain ⟨m, hmS, hmmax⟩ := hSc.exists_isMaxOn hne continuous_id.continuousOn
    have hmax : ∀ y ∈ S, y ≤ m := fun y hy => by simpa using isMaxOn_iff.mp hmmax y hy
    have hm1 : -(11 / 10 : ℝ) ≤ m := hmS.1.1
    have hm0 : m ≤ 0 := hmS.1.2
    have hBm : airyBi m ≤ 0 := hmS.2
    have hmlt : m < 0 := by
      rcases hm0.lt_or_eq with h | h
      · exact h
      · rw [h] at hBm; exact absurd hBm (not_le.mpr airyBi_zero_pos)
    have hpos : ∀ y ∈ Icc m 0, 0 ≤ airyBi y := by
      intro y hy
      rcases hy.1.lt_or_eq with h | h
      · by_contra hneg
        rw [not_le] at hneg
        have hyS : y ∈ S := ⟨⟨by linarith [hy.1], hy.2⟩, hneg.le⟩
        linarith [hmax y hyS]
      · rw [← h]
        by_contra hneg
        rw [not_le] at hneg
        have hcont := differentiable_airyBi.continuous.continuousAt (x := m)
        have hev : ∀ᶠ t in 𝓝 m, airyBi t < 0 := hcont.eventually (gt_mem_nhds hneg)
        obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
        set t := min (m + ε / 2) 0 with ht
        have ht1 : m < t := lt_min (by linarith) hmlt
        have htS : t ∈ S := ⟨⟨by linarith, min_le_right _ _⟩, (hball (by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left (m + ε / 2) 0])).le⟩
        linarith [hmax t htS]
    have hch := (airyBi_chain hm0 hpos m ⟨le_rfl, hm0⟩).2
    have := airyBiLower_ge hm1 hm0
    linarith
  · have hpos : ∀ y ∈ Icc x 0, 0 ≤ airyBi y := by
      intro y hy
      by_contra hneg
      rw [not_le] at hneg
      exact hne ⟨y, ⟨⟨by linarith [hy.1], hy.2⟩, hneg.le⟩⟩
    have := airyBi_chain hx0 hpos x ⟨le_rfl, hx0⟩
    exact ⟨this.2, this.1⟩


/-- `Bi' > 0` on `[-11/10, ∞)`. -/
theorem airyBiDeriv_pos_of_ge {x : ℝ} (hx : -(11 / 10 : ℝ) ≤ x) : 0 < airyBiDeriv x := by
  rcases le_total x 0 with h | h
  · exact lt_of_lt_of_le airyBiDeriv_zero_pos (airyBi_ge_on_Icc hx h).2
  · exact airyBiDeriv_pos h

/-- **`Bi` is strictly increasing on `[-11/10, ∞)`.** -/
theorem strictMonoOn_airyBi_Ici_neg : StrictMonoOn airyBi (Ici (-(11 / 10 : ℝ))) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
  · exact fun y _ => (hasDerivAt_airyBi y).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    rw [(hasDerivAt_airyBi y).deriv]
    exact airyBiDeriv_pos_of_ge (le_of_lt hy)

/-- **`Bi ≥ 1/100` on `[-11/10, ∞)`** (numerically `Bi(-11/10) ≈ 0.0443`; the first zero of `Bi` is `≈ -1.1737`). -/
theorem airyBi_ge_one_hundredth {x : ℝ} (hx : -(11 / 10 : ℝ) ≤ x) : 1 / 100 ≤ airyBi x := by
  rcases le_total x 0 with h | h
  · have := (airyBi_ge_on_Icc hx h).1
    have := airyBiLower_ge hx h
    linarith
  · have := airyBi_zero_ge
    have hm := strictMonoOn_airyBi_Ici.monotoneOn (show (0 : ℝ) ∈ Ici 0 from le_rfl) h
      h
    linarith

/-- **`Bi > 0` on `[-11/10, ∞)`.** -/
theorem airyBi_pos_of_neg_eleven_tenth_le {x : ℝ} (hx : -(11 / 10 : ℝ) ≤ x) : 0 < airyBi x :=
  lt_of_lt_of_le (by norm_num) (airyBi_ge_one_hundredth hx)

/-- info: 'FormalResearch.Special.airyBi_ge_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_ge_on_Icc

/-- info: 'FormalResearch.Special.airyBi_ge_one_hundredth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_ge_one_hundredth

/-- info: 'FormalResearch.Special.strictMonoOn_airyBi_Ici_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.strictMonoOn_airyBi_Ici_neg

end FormalResearch.Special
