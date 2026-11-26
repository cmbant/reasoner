module

public import FormalResearch.SignUncertainty.CtOuterBlaschke
public import FormalResearch.SignUncertainty.CtOuterStrip
public import FormalResearch.SignUncertainty.CtOuterDefs
public import FormalResearch.CohnElkies.MellinT3Complete
public import FormalResearch.CohnElkies.MellinPhaseBounds
public import FormalResearch.SignUncertainty.HankelEdgePhase

/-!
# `ct:boas` Step 2: the contour-shift inequality `ct:S0-ineq`

`constant_terms_lower.tex`, `ct:boas` Step 2 (`ct:S0-ineq`).  **Proved.**  For `τ₀ > 0`, `0 < σ ≤ min(τ₀/4, 1/4)` and every
`|τ| ≥ 3τ₀/2`:
`Re S̃₀(σ + iτ) + σ m(τ₀) ≤ -(4/5) σ (m(|τ|) - m(τ₀))` (`S0_ineq`, `m = hankelEdgeM`).

Route as in the TeX: `Re g(σ+iτ) - Re g(iτ) ≤ 3π²σ²/(20 cosh²(πτ/2))` (`re_stripG_diff_le`, from the norm formula
`re_stripG_eq` and `sin²(π/8) < 0.15`), `Re g(iτ) = -m(|τ|)` (`re_stripG_imag`), integration in `σ` by monotonicity
(`re_stripS0Tilde_le_aux`, using `hasDerivAt_stripS0Tilde` and `Re S̃₀(iτ) = 0`), and `π²σ²/20 ≤ Δ_{3/2}/5`
(`sigma_le_delta32`, mean value theorem with `mat:P3` for `τ₀ ≤ 1` and `mat:T4`(f)(M2) for `τ₀ > 1`; the constants
`π²/64` and `1/6` replace the TeX's `π²/60` and `0.24`, with the same conclusion).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `Re g(s + iτ) = ½ log (‖sin‖²/(‖cos‖² ‖πζ/2‖²))`, `ζ = s + iτ`. -/
lemma re_stripG_eq {s τ : ℝ} (hτ : τ ≠ 0) :
    (stripG ((s : ℂ) + (τ : ℂ) * Complex.I)).re =
      (1 / 2) * Real.log ((Real.sin (π * s / 2) ^ 2 + Real.sinh (π * τ / 2) ^ 2) /
        ((Real.cos (π * s / 2) ^ 2 + Real.sinh (π * τ / 2) ^ 2) * ((π / 2) ^ 2 * (s ^ 2 + τ ^ 2)))) := by
  set ζ : ℂ := (s : ℂ) + (τ : ℂ) * Complex.I with hζ
  have hζ0 : ζ ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [hζ] at this; exact hτ this
  have hw : (π : ℂ) * ζ / 2 ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (mul_ne_zero this hζ0) two_ne_zero
  have hre : ((π : ℂ) * ζ / 2).re = π * s / 2 := by simp [hζ]
  have him : ((π : ℂ) * ζ / 2).im = π * τ / 2 := by simp [hζ]
  have hsin := CtOuter.norm_sin_sq ((π : ℂ) * ζ / 2)
  have hcos := CtOuter.norm_cos_sq ((π : ℂ) * ζ / 2)
  rw [hre, him] at hsin hcos
  have hnw : ‖(π : ℂ) * ζ / 2‖ ^ 2 = (π / 2) ^ 2 * (s ^ 2 + τ ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hζ]; ring
  have hsh : 0 < Real.sinh (π * τ / 2) ^ 2 := by
    have h : Real.sinh (π * τ / 2) ≠ 0 := by
      rw [Ne, Real.sinh_eq_zero]; exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hτ) two_ne_zero
    positivity
  have hcpos : 0 < ‖Complex.cos ((π : ℂ) * ζ / 2)‖ ^ 2 := by
    rw [hcos]
    positivity
  have hcn : 0 < ‖Complex.cos ((π : ℂ) * ζ / 2)‖ := by
    by_contra h; rw [not_lt] at h
    have : ‖Complex.cos ((π : ℂ) * ζ / 2)‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this] at hcpos; simp at hcpos
  have hwn : 0 < ‖(π : ℂ) * ζ / 2‖ := norm_pos_iff.mpr hw
  unfold stripG
  rw [if_neg hζ0, Complex.log_re, Complex.tan, norm_div, norm_div]
  have hs0 : 0 < ‖Complex.sin ((π : ℂ) * ζ / 2)‖ ^ 2 := by
    rw [hsin]
    positivity
  have hsn : 0 < ‖Complex.sin ((π : ℂ) * ζ / 2)‖ := by
    by_contra h; rw [not_lt] at h
    have : ‖Complex.sin ((π : ℂ) * ζ / 2)‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this] at hs0; simp at hs0
  -- log of a ratio of norms equals half the log of the ratio of squares
  have key : ∀ x : ℝ, 0 < x → Real.log x = (1 / 2) * Real.log (x ^ 2) := by
    intro x hx; rw [Real.log_pow]; push_cast; ring
  rw [key _ (by positivity)]
  congr 1
  rw [div_pow, div_pow, hsin, hcos, hnw]
  field_simp

lemma sin_sq_le_pi_eighth {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ π / 8) : Real.sin x ^ 2 ≤ 0.15 := by
  have h1 : Real.sin x ≤ Real.sin (π / 8) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hx
  have h0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
  have h2 : Real.sin (π / 8) ^ 2 = (1 - Real.cos (π / 4)) / 2 := by
    have := Real.cos_two_mul (π / 8)
    have h := Real.sin_sq_add_cos_sq (π / 8)
    have e : 2 * (π / 8) = π / 4 := by ring
    rw [e] at this
    rw [this]
    nlinarith [h]
  rw [Real.cos_pi_div_four] at h2
  have h3 : Real.sqrt 2 > 1.41 := by
    rw [gt_iff_lt, Real.lt_sqrt (by norm_num)]; norm_num
  calc Real.sin x ^ 2 ≤ Real.sin (π / 8) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ 0.15 := by rw [h2]; linarith

set_option maxHeartbeats 800000 in
lemma re_stripG_diff_le {s τ : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) (hτ : 0 < τ) :
    (stripG ((s : ℂ) + (τ : ℂ) * Complex.I)).re - (stripG (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)).re ≤
      3 * π ^ 2 * s ^ 2 / (20 * Real.cosh (π * τ / 2) ^ 2) := by
  rw [re_stripG_eq hτ.ne', re_stripG_eq hτ.ne']
  set x : ℝ := π * s / 2 with hx
  set y : ℝ := π * τ / 2 with hy
  have hy0 : 0 < y := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hxπ : x ≤ π / 8 := by rw [hx]; nlinarith [Real.pi_pos]
  have hSh : y ^ 2 ≤ Real.sinh y ^ 2 := by
    have := (sinh_gt_id hy0).le
    nlinarith
  have hA : Real.sin x ^ 2 ≤ x ^ 2 := by
    have h1 := Real.sin_le hx0
    have h2 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
    nlinarith
  have hA15 := sin_sq_le_pi_eighth hx0 hxπ
  have hA0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have hCh : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := by nlinarith [Real.cosh_sq y]
  have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq x]
  have hShpos : 0 < Real.sinh y ^ 2 := by
    have := Real.sinh_pos_iff.mpr hy0; positivity
  have hC1 : 1 ≤ Real.cosh y ^ 2 := by nlinarith
  set A := Real.sin x ^ 2 with hAd
  set Sh := Real.sinh y ^ 2 with hShd
  set u : ℝ := A / Real.cosh y ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu15 : u ≤ 0.15 := by
    rw [hu, div_le_iff₀ (by linarith)]; nlinarith
  have h1u : 0 < 1 - u := by linarith
  have hπ2 : 0 < (π / 2) ^ 2 := by positivity
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hxs : x ^ 2 = (π / 2) ^ 2 * s ^ 2 := by rw [hx]; ring
  have hys : y ^ 2 = (π / 2) ^ 2 * τ ^ 2 := by rw [hy]; ring
  simp only [mul_zero, zero_div, Real.sin_zero, Real.cos_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add, one_pow]
  -- the two arguments
  set P := (A + Sh) / ((Real.cos x ^ 2 + Sh) * ((π / 2) ^ 2 * (s ^ 2 + τ ^ 2))) with hP
  set P0 := Sh / ((1 + Sh) * ((π / 2) ^ 2 * τ ^ 2)) with hP0
  have hPpos : 0 < P := by
    rw [hP, hcos]
    have : 0 < 1 - A + Sh := by linarith
    positivity
  have hP0pos : 0 < P0 := by positivity
  have hden : 0 < 1 - A + Sh := by linarith
  have hkey : A * τ ^ 2 ≤ Sh * s ^ 2 := by
    have h1 : A * τ ^ 2 ≤ x ^ 2 * τ ^ 2 := mul_le_mul_of_nonneg_right hA hτ2.le
    have h2 : y ^ 2 * s ^ 2 ≤ Sh * s ^ 2 := mul_le_mul_of_nonneg_right hSh hs2
    have : x ^ 2 * τ ^ 2 = y ^ 2 * s ^ 2 := by rw [hxs, hys]; ring
    linarith
  have hPle : P ≤ P0 / (1 - u) := by
    have e : P0 / (1 - u) = Sh / ((1 - A + Sh) * ((π / 2) ^ 2 * τ ^ 2)) := by
      have hc : 0 < 1 + Sh := by linarith
      have h1u' : 1 - u = (1 - A + Sh) / (1 + Sh) := by rw [hu, hCh]; field_simp; ring
      rw [hP0, h1u']
      field_simp
    rw [e, hP, hcos, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_nonneg (mul_nonneg hden.le hπ2.le) (sub_nonneg.2 hkey)
    nlinarith [this]
  have hlog : Real.log P ≤ Real.log P0 - Real.log (1 - u) := by
    have := Real.log_le_log hPpos hPle
    rwa [Real.log_div hP0pos.ne' h1u.ne'] at this
  have hl1 : -Real.log (1 - u) ≤ u / (1 - u) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1u)
    rw [Real.log_inv] at this
    have e : (1 - u)⁻¹ - 1 = u / (1 - u) := by field_simp; ring
    linarith
  have hl2 : u / (1 - u) ≤ 6 / 5 * u := by
    rw [div_le_iff₀ h1u]; nlinarith
  have hu2 : u ≤ x ^ 2 / Real.cosh y ^ 2 := by
    rw [hu]; exact div_le_div_of_nonneg_right hA (by positivity)
  have hfin : 3 / 5 * (x ^ 2 / Real.cosh y ^ 2) = 3 * π ^ 2 * s ^ 2 / (20 * Real.cosh y ^ 2) := by
    rw [hxs]; field_simp; ring
  have : (1 / 2 : ℝ) * Real.log P - 1 / 2 * Real.log P0 ≤ 3 / 5 * (x ^ 2 / Real.cosh y ^ 2) := by
    linarith only [hlog, hl1, hl2, hu2]
  linarith only [this, hfin]

set_option maxHeartbeats 600000 in
lemma re_stripG_neg_im {s τ : ℝ} (hτ : τ ≠ 0) :
    (stripG ((s : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I)).re = (stripG ((s : ℂ) + (τ : ℂ) * Complex.I)).re := by
  rw [re_stripG_eq hτ, re_stripG_eq (neg_ne_zero.2 hτ)]
  have : π * -τ / 2 = -(π * τ / 2) := by ring
  rw [this, Real.sinh_neg, neg_sq, neg_sq]

lemma re_stripG_imag {τ : ℝ} (hτ : 0 < τ) :
    (stripG (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)).re = -hankelEdgeM τ := by
  rw [re_stripG_eq hτ.ne']
  unfold hankelEdgeM ceEll
  set y : ℝ := π * τ / 2 with hy
  have hy0 : 0 < y := by positivity
  have hsh : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy0
  have hch : 0 < Real.cosh y := Real.cosh_pos y
  have hcs : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := by nlinarith [Real.cosh_sq y]
  simp only [mul_zero, zero_div, Real.sin_zero, Real.cos_zero, zero_pow two_ne_zero, zero_add, one_pow]
  have e : Real.sinh y ^ 2 / ((1 + Real.sinh y ^ 2) * ((π / 2) ^ 2 * τ ^ 2)) = (Real.tanh y / y) ^ 2 := by
    rw [← hcs, Real.tanh_eq_sinh_div_cosh, hy]
    field_simp
  rw [e, Real.log_pow, ← Real.log_inv, inv_div]
  push_cast; ring

/-- `Re S̃₀(σ + iτ) ≤ -σ m(|τ|) + π²σ³/(20 cosh²(πτ/2))` for `0 ≤ σ ≤ 1/4`, `τ > 0`
(`ct:S0-ineq`, first display). -/
lemma re_stripS0Tilde_le_aux {σ τ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 4) (hτ : τ ≠ 0) :
    (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
      -σ * hankelEdgeM |τ| + π ^ 2 * σ ^ 3 / (20 * Real.cosh (π * τ / 2) ^ 2) := by
  set φ : ℝ → ℝ := fun s => (stripS0Tilde ((s : ℂ) + (τ : ℂ) * Complex.I)).re with hφ
  set ψ : ℝ → ℝ := fun s => φ s - (-s * hankelEdgeM |τ| + π ^ 2 * s ^ 3 / (20 * Real.cosh (π * τ / 2) ^ 2)) with hψ
  have hd : ∀ s : ℝ, |s| < 1 → HasDerivAt φ (stripG ((s : ℂ) + (τ : ℂ) * Complex.I)).re s := by
    intro s hs
    have hS := FormalResearch.CohnElkies.hasDerivAt_stripS0Tilde (ζ₀ := (s : ℂ) + (τ : ℂ) * Complex.I)
      (by simpa using hs)
    have h1 : HasDerivAt (fun z : ℂ => stripS0Tilde (z + (τ : ℂ) * Complex.I)) (stripG ((s : ℂ) + (τ : ℂ) * Complex.I)) (s : ℂ) :=
      hS.comp_add_const (s : ℂ) ((τ : ℂ) * Complex.I)
    have h2 := h1.comp_ofReal
    have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h2
    exact h3
  have hψd : ∀ s ∈ Set.Icc (0 : ℝ) σ, HasDerivAt ψ ((stripG ((s : ℂ) + (τ : ℂ) * Complex.I)).re -
      (-hankelEdgeM |τ| + 3 * π ^ 2 * s ^ 2 / (20 * Real.cosh (π * τ / 2) ^ 2))) s := by
    intro s hs
    have h0 := hd s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
    have h1 : HasDerivAt (fun s : ℝ => -s * hankelEdgeM |τ| + π ^ 2 * s ^ 3 / (20 * Real.cosh (π * τ / 2) ^ 2))
        (-hankelEdgeM |τ| + 3 * π ^ 2 * s ^ 2 / (20 * Real.cosh (π * τ / 2) ^ 2)) s := by
      have a1 : HasDerivAt (fun s : ℝ => -s * hankelEdgeM |τ|) (-hankelEdgeM |τ|) s := by
        simpa using ((hasDerivAt_id s).neg.mul_const (hankelEdgeM |τ|))
      have a2 : HasDerivAt (fun s : ℝ => π ^ 2 * s ^ 3 / (20 * Real.cosh (π * τ / 2) ^ 2))
          (3 * π ^ 2 * s ^ 2 / (20 * Real.cosh (π * τ / 2) ^ 2)) s := by
        have := ((hasDerivAt_pow 3 s).const_mul (π ^ 2)).div_const (20 * Real.cosh (π * τ / 2) ^ 2)
        refine this.congr_deriv ?_
        push_cast; ring
      exact a1.add a2
    exact h0.sub h1
  have hanti : AntitoneOn ψ (Set.Icc 0 σ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 σ) ?_ ?_ ?_
    · exact fun s hs => (hψd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hψd s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hψd s ⟨hs.1.le, hs.2.le⟩).deriv]
      have hdiff : (stripG ((s : ℂ) + (τ : ℂ) * Complex.I)).re + hankelEdgeM |τ| ≤
          3 * π ^ 2 * s ^ 2 / (20 * Real.cosh (π * τ / 2) ^ 2) := by
        rcases lt_or_gt_of_ne hτ with hneg | hpos
        · have h := re_stripG_diff_le hs.1.le (by linarith [hs.2]) (neg_pos.2 hneg)
          rw [re_stripG_imag (neg_pos.2 hneg), re_stripG_neg_im hτ] at h
          rw [abs_of_neg hneg]
          have hc : Real.cosh (π * -τ / 2) = Real.cosh (π * τ / 2) := by
            rw [← Real.cosh_neg]; congr 1; ring
          rw [hc] at h
          linarith
        · have h := re_stripG_diff_le hs.1.le (by linarith [hs.2]) hpos
          rw [re_stripG_imag hpos] at h
          rw [abs_of_pos hpos]
          linarith
      linarith
  have h0 : ψ 0 = 0 := by
    have hre : (stripS0Tilde (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)).re = 0 := by
      rw [Complex.ofReal_zero, zero_add, FormalResearch.CohnElkies.stripS0Tilde_imag τ]
      simp
    simp only [hψ, hφ]
    rw [hre]; simp
  have := hanti (Set.mem_Icc.2 ⟨le_rfl, hσ0⟩) (Set.mem_Icc.2 ⟨hσ0, le_rfl⟩) hσ0
  rw [h0] at this
  simp only [hψ, hφ] at this
  linarith

lemma hankelEdgeM'_ge {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) ≤ hankelEdgeM' t ∧ π ^ 2 * t / (6 + π ^ 2 * t ^ 2) ≤ hankelEdgeM' t := by
  have h1 := (CtOuter.mPrime_bounds ht).1
  rw [CtOuter.mPrime_eq_hankelEdgeM' ht] at h1
  refine ⟨h1, ?_⟩
  have h2 := abs_edgePhiDeriv2_ge ht.ne'
  have hpos : 0 < hankelEdgeM' t := lt_of_lt_of_le (by positivity) h1
  have : |edgePhiDeriv2 t| = hankelEdgeM' t := by
    have e : hankelEdgeM' t = -edgePhiDeriv2 t := rfl
    rw [← abs_neg, ← e, abs_of_pos hpos]
  rw [abs_of_pos ht] at h2
  linarith

/-- `Δ_{3/2}` lower bound: for `σ ≤ min(τ₀/4, 1/4)`, `π²σ²/20 ≤ (1/5)(m(3τ₀/2) - m(τ₀))`. -/
lemma sigma_le_delta32 {τ0 σ : ℝ} (hτ0 : 0 < τ0) (hσ : σ ≤ τ0 / 4) (hσ4 : σ ≤ 1 / 4) (hσ0 : 0 ≤ σ) :
    π ^ 2 * σ ^ 2 / 20 ≤ (1 / 5) * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) := by
  have hlt : τ0 < 3 * τ0 / 2 := by linarith
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope hankelEdgeM hankelEdgeM'
    hlt (hankelEdgeM_continuousOn.mono (fun x hx => le_trans hτ0.le hx.1))
    (fun x hx => hankelEdgeM_hasDerivAt (lt_trans hτ0 hx.1))
  have hξ0 : 0 < ξ := lt_trans hτ0 hξ.1
  have hd : hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 = hankelEdgeM' ξ * (τ0 / 2) := by
    have : 3 * τ0 / 2 - τ0 = τ0 / 2 := by ring
    rw [this] at hξe
    field_simp at hξe ⊢
    linarith
  obtain ⟨hb1, hb2⟩ := hankelEdgeM'_ge hξ0
  have hπ := Real.pi_pos
  have hπ2 : π ^ 2 < 9.87 := by nlinarith [Real.pi_lt_d4]
  have hπ2' : 9.8 < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  rcases le_or_gt τ0 1 with h1 | h1
  · -- `τ₀ ≤ 1`
    have hξ1 : ξ ≤ 3 / 2 := by linarith [hξ.2]
    have hden : 6 + π ^ 2 * ξ ^ 2 ≤ 6 + 9.87 * (9 / 4) := by
      have : ξ ^ 2 ≤ 9 / 4 := by nlinarith
      nlinarith
    have hm : π ^ 2 * τ0 / (6 + 9.87 * (9 / 4)) ≤ hankelEdgeM' ξ := by
      refine le_trans ?_ hb2
      refine div_le_div₀ (by positivity) (by nlinarith [hξ.1]) (by positivity) hden
    have hmain : π ^ 2 * τ0 ^ 2 / 64 ≤ hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 := by
      rw [hd]
      have h2 : π ^ 2 * τ0 / (6 + 9.87 * (9 / 4)) * (τ0 / 2) ≤ hankelEdgeM' ξ * (τ0 / 2) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      refine le_trans ?_ h2
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [sq_nonneg τ0, mul_pos hπ hτ0]
    have hs2 : σ ^ 2 ≤ (τ0 / 4) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
    nlinarith [sq_nonneg τ0]
  · -- `τ₀ > 1`
    have hξ1 : 1 < ξ := lt_trans h1 hξ.1
    have hm : 1 / (3 * τ0) ≤ hankelEdgeM' ξ := by
      refine le_trans ?_ hb1
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hξ.2]
    have hmain : 1 / 6 ≤ hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 := by
      rw [hd]
      have h2 : 1 / (3 * τ0) * (τ0 / 2) ≤ hankelEdgeM' ξ * (τ0 / 2) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      refine le_trans (le_of_eq ?_) h2
      field_simp; norm_num
    have hs2 : σ ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hσ0 hσ4 2
    nlinarith

/-- **`ct:S0-ineq`** (`constant_terms_lower.tex`, Step 2 of `ct:boas`): for `τ₀ > 0`, `0 < σ ≤ min(τ₀/4, 1/4)` and every
`|τ| ≥ 3τ₀/2`, `Re S̃₀(σ + iτ) + σ m(τ₀) ≤ -(4/5) σ (m(|τ|) - m(τ₀))`, with `m = hankelEdgeM`. -/
theorem S0_ineq {τ0 σ τ : ℝ} (hτ0 : 0 < τ0) (hσ0 : 0 < σ) (hσ : σ ≤ τ0 / 4) (hσ4 : σ ≤ 1 / 4)
    (hτ : 3 * τ0 / 2 ≤ |τ|) :
    (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re + σ * hankelEdgeM τ0 ≤
      -(4 / 5) * σ * (hankelEdgeM |τ| - hankelEdgeM τ0) := by
  have hτne : τ ≠ 0 := by
    intro h; rw [h, abs_zero] at hτ; linarith
  have h1 := re_stripS0Tilde_le_aux hσ0.le hσ4 hτne
  have hc : 1 ≤ Real.cosh (π * τ / 2) ^ 2 := by
    have := Real.one_le_cosh (π * τ / 2); nlinarith
  have h2 : π ^ 2 * σ ^ 3 / (20 * Real.cosh (π * τ / 2) ^ 2) ≤ π ^ 2 * σ ^ 3 / 20 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  have h3 := sigma_le_delta32 hτ0 hσ hσ4 hσ0.le
  have hmono : hankelEdgeM (3 * τ0 / 2) ≤ hankelEdgeM |τ| :=
    hankelEdgeM_strictMonoOn.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (abs_nonneg _)) hτ
  have h4 : π ^ 2 * σ ^ 3 / 20 ≤ σ * ((1 / 5) * (hankelEdgeM |τ| - hankelEdgeM τ0)) := by
    have : π ^ 2 * σ ^ 3 / 20 = σ * (π ^ 2 * σ ^ 2 / 20) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left (h3.trans ?_) hσ0.le
    linarith
  linarith

/-- info: 'FormalResearch.SignUncertainty.S0_ineq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms S0_ineq

end FormalResearch.SignUncertainty
