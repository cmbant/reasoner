module

public import FormalResearch.SignUncertainty.CtSdSegGeom
public import FormalResearch.SignUncertainty.CtSdSeg

/-!
# Size of the second-integration kernel `Q` on the connecting segment (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("Tail and connecting arc").  **Proved.**
With `F, F', F''` bounded by `C_F ρ, C_F ρ⁻¹, C_F ρ⁻³` (`ρ² = R`), `G = κU + w²` with `R²/4 ≤ |G| ≤ 2R²`, `|G'| ≤ 2R`, `|G''| ≤ 2`,
the kernel `Q = ((F/G)'/G)'` of `seg_ibp2` is `O(C_F ρ⁻¹¹) = O(C_F R^{-11/2})`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtSd

section generic

variable {F F1 F2 G G1 G2 : ℂ → ℂ} {z : ℂ} {f0 f1 f2 g0 gu γ1 γ2 : ℝ}

lemma norm_sub_mul_le {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D)
    (hA : 0 ≤ A) (hC : 0 ≤ C) : ‖a * b - c * d‖ ≤ A * B + C * D := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  exact add_le_add (mul_le_mul ha hb (norm_nonneg _) hA) (mul_le_mul hc hd (norm_nonneg _) hC)

lemma norm_div_sq_le {n : ℂ} {N : ℝ} {g : ℂ} (hn : ‖n‖ ≤ N) (hGl : g0 ≤ ‖g‖) (hg0 : 0 < g0) (hN : 0 ≤ N) :
    ‖n / g ^ 2‖ ≤ N / g0 ^ 2 := by
  rw [norm_div, norm_pow]
  have hden : g0 ^ 2 ≤ ‖g‖ ^ 2 := pow_le_pow_left₀ hg0.le hGl 2
  calc ‖n‖ / ‖g‖ ^ 2 ≤ N / ‖g‖ ^ 2 := div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ N / g0 ^ 2 := div_le_div_of_nonneg_left hN (by positivity) hden

lemma norm_segH_le (hF : ‖F z‖ ≤ f0) (hF1 : ‖F1 z‖ ≤ f1) (hGl : g0 ≤ ‖G z‖) (hGu : ‖G z‖ ≤ gu)
    (hG1 : ‖G1 z‖ ≤ γ1) (hg0 : 0 < g0) (hf0 : 0 ≤ f0) (hf1 : 0 ≤ f1) :
    ‖segH F F1 G G1 z‖ ≤ (f1 * gu + f0 * γ1) / g0 ^ 2 := by
  unfold segH
  have hnum := norm_sub_mul_le hF1 hGu hF hG1 hf1 hf0
  exact norm_div_sq_le hnum hGl hg0 (by
    have : 0 ≤ gu := (norm_nonneg _).trans hGu
    have : 0 ≤ γ1 := (norm_nonneg _).trans hG1
    positivity)

lemma norm_segHd_le (hF : ‖F z‖ ≤ f0) (hF1 : ‖F1 z‖ ≤ f1) (hF2 : ‖F2 z‖ ≤ f2) (hGl : g0 ≤ ‖G z‖) (hGu : ‖G z‖ ≤ gu)
    (hG1 : ‖G1 z‖ ≤ γ1) (hG2 : ‖G2 z‖ ≤ γ2) (hg0 : 0 < g0) (hf0 : 0 ≤ f0) (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) :
    ‖segHd F F1 F2 G G1 G2 z‖ ≤
      (f2 * gu + f0 * γ2) / g0 ^ 2 + 2 * ((f1 * gu + f0 * γ1) / g0 ^ 2) * γ1 / g0 := by
  have hgu : 0 ≤ gu := (norm_nonneg _).trans hGu
  have hγ1 : 0 ≤ γ1 := (norm_nonneg _).trans hG1
  have hγ2 : 0 ≤ γ2 := (norm_nonneg _).trans hG2
  have hGn : 0 < ‖G z‖ := lt_of_lt_of_le hg0 hGl
  have hH := norm_segH_le hF hF1 hGl hGu hG1 hg0 hf0 hf1
  unfold segHd
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_div_sq_le (norm_sub_mul_le hF2 hGu hF hG2 hf2 hf0 |>.trans (le_refl _)) hGl hg0 (by positivity)
  · have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_div, norm_mul, norm_mul, h2n]
    unfold segH at hH
    have h2 : ‖(F1 z * G z - F z * G1 z) / G z ^ 2‖ ≤ (f1 * gu + f0 * γ1) / g0 ^ 2 := hH
    calc 2 * ‖(F1 z * G z - F z * G1 z) / G z ^ 2‖ * ‖G1 z‖ / ‖G z‖
        ≤ 2 * ((f1 * gu + f0 * γ1) / g0 ^ 2) * γ1 / g0 := by
          have h0 : 0 ≤ (f1 * gu + f0 * γ1) / g0 ^ 2 := by positivity
          calc 2 * ‖(F1 z * G z - F z * G1 z) / G z ^ 2‖ * ‖G1 z‖ / ‖G z‖
              ≤ 2 * ((f1 * gu + f0 * γ1) / g0 ^ 2) * γ1 / ‖G z‖ := by
                gcongr
            _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hg0 hGl

lemma norm_segQ_le' (hF : ‖F z‖ ≤ f0) (hF1 : ‖F1 z‖ ≤ f1) (hF2 : ‖F2 z‖ ≤ f2) (hGl : g0 ≤ ‖G z‖) (hGu : ‖G z‖ ≤ gu)
    (hG1 : ‖G1 z‖ ≤ γ1) (hG2 : ‖G2 z‖ ≤ γ2) (hg0 : 0 < g0) (hf0 : 0 ≤ f0) (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) :
    ‖segQ F F1 F2 G G1 G2 z‖ ≤
      (((f2 * gu + f0 * γ2) / g0 ^ 2 + 2 * ((f1 * gu + f0 * γ1) / g0 ^ 2) * γ1 / g0) * gu +
        (f1 * gu + f0 * γ1) / g0 ^ 2 * γ1) / g0 ^ 2 := by
  have hgu : 0 ≤ gu := (norm_nonneg _).trans hGu
  have hγ1 : 0 ≤ γ1 := (norm_nonneg _).trans hG1
  have hγ2 : 0 ≤ γ2 := (norm_nonneg _).trans hG2
  have hH := norm_segH_le hF hF1 hGl hGu hG1 hg0 hf0 hf1
  have hHd := norm_segHd_le hF hF1 hF2 hGl hGu hG1 hG2 hg0 hf0 hf1 hf2
  unfold segQ
  refine norm_div_sq_le (N := ((f2 * gu + f0 * γ2) / g0 ^ 2 + 2 * ((f1 * gu + f0 * γ1) / g0 ^ 2) * γ1 / g0) * gu +
        (f1 * gu + f0 * γ1) / g0 ^ 2 * γ1) ?_ hGl hg0 (by positivity)
  exact norm_sub_mul_le hHd hGu hH hG1 (by positivity) (by positivity) |>.trans (le_refl _)

end generic

/-- The arithmetic of the `R^{-11/2}` bound (`R = ρ²`). -/
lemma segQ_const_bound {Cf ρ : ℝ} (hCf : 0 ≤ Cf) (hρ : 0 < ρ) :
    (((Cf / ρ ^ 3 * (2 * ρ ^ 4) + Cf * ρ * 2) / (ρ ^ 4 / 4) ^ 2 +
        2 * ((Cf / ρ * (2 * ρ ^ 4) + Cf * ρ * (2 * ρ ^ 2)) / (ρ ^ 4 / 4) ^ 2) * (2 * ρ ^ 2) / (ρ ^ 4 / 4)) *
          (2 * ρ ^ 4) +
      (Cf / ρ * (2 * ρ ^ 4) + Cf * ρ * (2 * ρ ^ 2)) / (ρ ^ 4 / 4) ^ 2 * (2 * ρ ^ 2)) / (ρ ^ 4 / 4) ^ 2
      ≤ 40000 * Cf / ρ ^ 11 := by
  have : (((Cf / ρ ^ 3 * (2 * ρ ^ 4) + Cf * ρ * 2) / (ρ ^ 4 / 4) ^ 2 +
        2 * ((Cf / ρ * (2 * ρ ^ 4) + Cf * ρ * (2 * ρ ^ 2)) / (ρ ^ 4 / 4) ^ 2) * (2 * ρ ^ 2) / (ρ ^ 4 / 4)) *
          (2 * ρ ^ 4) +
      (Cf / ρ * (2 * ρ ^ 4) + Cf * ρ * (2 * ρ ^ 2)) / (ρ ^ 4 / 4) ^ 2 * (2 * ρ ^ 2)) / (ρ ^ 4 / 4) ^ 2
      = 36864 * Cf / ρ ^ 11 := by
    field_simp
    ring
  rw [this]
  have : 0 ≤ Cf / ρ ^ 11 := by positivity
  have h2 : 36864 * Cf / ρ ^ 11 = 36864 * (Cf / ρ ^ 11) := by ring
  have h3 : 40000 * Cf / ρ ^ 11 = 40000 * (Cf / ρ ^ 11) := by ring
  rw [h2, h3]; nlinarith

section csrfam

/-- The amplitude `F = csr · g_W` and its first two derivatives (`csr' = csr/(2w)`, `csr'' = -csr/(4w²)`). -/
noncomputable def csrF (gW : ℂ → ℂ) (w : ℂ) : ℂ := csr w * gW w

noncomputable def csrF1 (gW gW1 : ℂ → ℂ) (w : ℂ) : ℂ := csr w / (2 * w) * gW w + csr w * gW1 w

noncomputable def csrF2 (gW gW1 gW2 : ℂ → ℂ) (w : ℂ) : ℂ :=
  -csr w / (4 * w ^ 2) * gW w + 2 * (csr w / (2 * w)) * gW1 w + csr w * gW2 w

/-- `G = P' = κU + w²` and its derivatives. -/
noncomputable def GG (U : ℝ) (w : ℂ) : ℂ := (kap : ℂ) * U + w ^ 2
noncomputable def GG1 (w : ℂ) : ℂ := 2 * w
noncomputable def GG2 (_ : ℂ) : ℂ := 2

lemma hasDerivAt_csrF {gW gW1 : ℂ → ℂ} {w : ℂ} (hs : w ∈ slitPlane) (hg : HasDerivAt gW (gW1 w) w) :
    HasDerivAt (csrF gW) (csrF1 gW gW1 w) w := by
  have := (hasDerivAt_csr hs).mul hg
  exact this

lemma hasDerivAt_csrF1 {gW gW1 gW2 : ℂ → ℂ} {w : ℂ} (hs : w ∈ slitPlane) (hg : HasDerivAt gW (gW1 w) w)
    (hg1 : HasDerivAt gW1 (gW2 w) w) : HasDerivAt (csrF1 gW gW1) (csrF2 gW gW1 gW2 w) w := by
  have hw : w ≠ 0 := slitPlane_ne_zero hs
  have h2 : HasDerivAt (fun w : ℂ => 2 * w) 2 w := by simpa using (hasDerivAt_id w).const_mul (2 : ℂ)
  have hd : HasDerivAt (fun w => csr w / (2 * w)) (-csr w / (4 * w ^ 2)) w := by
    have := (hasDerivAt_csr hs).div h2 (mul_ne_zero two_ne_zero hw)
    refine this.congr_deriv ?_
    field_simp
    ring
  have := (hd.mul hg).add ((hasDerivAt_csr hs).mul hg1)
  refine this.congr_deriv ?_
  unfold csrF2
  field_simp
  ring

lemma hasDerivAt_GG (U : ℝ) (w : ℂ) : HasDerivAt (GG U) (GG1 w) w := by
  unfold GG GG1
  have := (hasDerivAt_pow 2 w).const_add ((kap : ℂ) * U)
  convert this using 1
  norm_num

lemma hasDerivAt_GG1 (w : ℂ) : HasDerivAt GG1 (GG2 w) w := by
  unfold GG1 GG2
  simpa using (hasDerivAt_id w).const_mul (2 : ℂ)

lemma hasDerivAt_PhU_only (U : ℝ) (w : ℂ) : HasDerivAt (PhU U) (GG U w) w := by
  unfold PhU GG
  have h1 : HasDerivAt (fun w : ℂ => (kap : ℂ) * U * w) ((kap : ℂ) * U) w := by
    simpa using (hasDerivAt_id w).const_mul ((kap : ℂ) * U)
  have h2 : HasDerivAt (fun w : ℂ => w ^ 3 / 3) (w ^ 2) w := by
    have := (hasDerivAt_pow 3 w).div_const 3
    convert this using 1
    norm_num
  exact h1.add h2

end csrfam

section pointwise

variable {ρ t : ℝ} (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
include hρ ht0 ht1

lemma norm_segPt_sq_bounds : ρ ^ 2 / 2 ≤ ‖segPt (ρ ^ 2) t‖ ∧ ‖segPt (ρ ^ 2) t‖ ≤ ρ ^ 2 := by
  have hR : 0 ≤ ρ ^ 2 := by positivity
  refine ⟨?_, norm_segPt_le hR ht0 ht1⟩
  have := norm_segPt_ge hR ht0 ht1
  have hs := sqrt3_bounds
  nlinarith

lemma norm_csr_seg_bounds : ρ / 2 ≤ ‖csr (segPt (ρ ^ 2) t)‖ ∧ ‖csr (segPt (ρ ^ 2) t)‖ ≤ ρ := by
  obtain ⟨h1, h2⟩ := norm_segPt_sq_bounds hρ ht0 ht1
  rw [norm_csr]
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ρ]
  · apply Real.sqrt_le_iff.2
    exact ⟨hρ.le, h2⟩

lemma norm_csr_div_seg_le : ‖csr (segPt (ρ ^ 2) t) / (2 * segPt (ρ ^ 2) t)‖ ≤ 1 / ρ := by
  obtain ⟨h1, h2⟩ := norm_segPt_sq_bounds hρ ht0 ht1
  obtain ⟨c1, c2⟩ := norm_csr_seg_bounds hρ ht0 ht1
  rw [norm_div, norm_mul]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n, div_le_div_iff₀ (by nlinarith [sq_nonneg ρ]) hρ]
  nlinarith [sq_nonneg ρ, norm_nonneg (csr (segPt (ρ ^ 2) t))]

lemma norm_csr_coef2_seg_le : ‖-csr (segPt (ρ ^ 2) t) / (4 * segPt (ρ ^ 2) t ^ 2)‖ ≤ 1 / ρ ^ 3 := by
  obtain ⟨h1, h2⟩ := norm_segPt_sq_bounds hρ ht0 ht1
  obtain ⟨c1, c2⟩ := norm_csr_seg_bounds hρ ht0 ht1
  rw [norm_div, norm_neg, norm_mul, norm_pow]
  have h4n : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4n]
  have hp : 0 < ρ ^ 2 / 2 := by positivity
  have hsq : (ρ ^ 2 / 2) ^ 2 ≤ ‖segPt (ρ ^ 2) t‖ ^ 2 := pow_le_pow_left₀ hp.le h1 2
  have hw0 : 0 < ‖segPt (ρ ^ 2) t‖ := lt_of_lt_of_le hp h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : 0 ≤ ρ ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right c2 h3]

end pointwise

section remainder

variable {U ρ Cg t : ℝ} {gW gW1 gW2 : ℂ → ℂ}

/-- Pointwise bound for the kernel `Q` on the segment. -/
lemma norm_segQ_csr_le (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hCg : 0 ≤ Cg)
    (hU : kap * |U| ≤ (ρ ^ 2) ^ 2 / 16)
    (b0 : ‖gW (segPt (ρ ^ 2) t)‖ ≤ Cg) (b1 : ‖gW1 (segPt (ρ ^ 2) t)‖ ≤ Cg / ρ ^ 2)
    (b2 : ‖gW2 (segPt (ρ ^ 2) t)‖ ≤ Cg / ρ ^ 4) :
    ‖segQ (csrF gW) (csrF1 gW gW1) (csrF2 gW gW1 gW2) (GG U) GG1 GG2 (segPt (ρ ^ 2) t)‖ ≤
      40000 * (4 * Cg) / ρ ^ 11 := by
  have hR : 0 ≤ ρ ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := norm_segPt_sq_bounds hρ ht0 ht1
  obtain ⟨c1, c2⟩ := norm_csr_seg_bounds hρ ht0 ht1
  have cd := norm_csr_div_seg_le hρ ht0 ht1
  have c2' := norm_csr_coef2_seg_le hρ ht0 ht1
  set w := segPt (ρ ^ 2) t with hw
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hρ3 : 0 < ρ ^ 3 := by positivity
  have hρ4 : 0 < ρ ^ 4 := by positivity
  have hCg1 : 0 ≤ Cg / ρ ^ 2 := by positivity
  have hCg2 : 0 ≤ Cg / ρ ^ 4 := by positivity
  have n0 := norm_nonneg (csr w)
  have nn0 := norm_nonneg (gW w)
  have hF : ‖csrF gW w‖ ≤ 4 * Cg * ρ := by
    unfold csrF; rw [norm_mul]
    calc ‖csr w‖ * ‖gW w‖ ≤ ρ * Cg := mul_le_mul c2 b0 nn0 hρ.le
      _ ≤ 4 * Cg * ρ := by nlinarith
  have hF1 : ‖csrF1 gW gW1 w‖ ≤ 4 * Cg / ρ := by
    unfold csrF1
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have e1 : ‖csr w / (2 * w)‖ * ‖gW w‖ ≤ 1 / ρ * Cg := mul_le_mul cd b0 nn0 (by positivity)
    have e2 : ‖csr w‖ * ‖gW1 w‖ ≤ ρ * (Cg / ρ ^ 2) := mul_le_mul c2 b1 (norm_nonneg _) hρ.le
    have e3 : ρ * (Cg / ρ ^ 2) = Cg / ρ := by field_simp
    have e4 : 1 / ρ * Cg = Cg / ρ := by ring
    have : 0 ≤ Cg / ρ := by positivity
    have e5 : 4 * Cg / ρ = 4 * (Cg / ρ) := by ring
    rw [e5]; linarith
  have hF2 : ‖csrF2 gW gW1 gW2 w‖ ≤ 4 * Cg / ρ ^ 3 := by
    unfold csrF2
    have t2 := norm_add_le (-csr w / (4 * w ^ 2) * gW w) (2 * (csr w / (2 * w)) * gW1 w)
    refine (norm_add_le _ _).trans ?_
    have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    simp only [norm_mul, h2n] at t2 ⊢
    have e1 : ‖-csr w / (4 * w ^ 2)‖ * ‖gW w‖ ≤ 1 / ρ ^ 3 * Cg := mul_le_mul c2' b0 nn0 (by positivity)
    have e2 : 2 * ‖csr w / (2 * w)‖ * ‖gW1 w‖ ≤ 2 * (1 / ρ) * (Cg / ρ ^ 2) :=
      mul_le_mul (by linarith) b1 (norm_nonneg _) (by positivity)
    have e3 : ‖csr w‖ * ‖gW2 w‖ ≤ ρ * (Cg / ρ ^ 4) := mul_le_mul c2 b2 (norm_nonneg _) hρ.le
    have f1 : 1 / ρ ^ 3 * Cg = Cg / ρ ^ 3 := by ring
    have f2 : 2 * (1 / ρ) * (Cg / ρ ^ 2) = 2 * (Cg / ρ ^ 3) := by field_simp
    have f3 : ρ * (Cg / ρ ^ 4) = Cg / ρ ^ 3 := by field_simp
    have f4 : 4 * Cg / ρ ^ 3 = 4 * (Cg / ρ ^ 3) := by ring
    rw [f4]; linarith
  have hGl : ρ ^ 4 / 4 ≤ ‖GG U w‖ := by
    have := norm_G_segPt_ge hR ht0 ht1 hU
    unfold GG
    nlinarith
  have hGu : ‖GG U w‖ ≤ 2 * ρ ^ 4 := by
    have := norm_G_segPt_le hR ht0 ht1 hU
    unfold GG
    nlinarith
  have hG1 : ‖GG1 w‖ ≤ 2 * ρ ^ 2 := by
    unfold GG1; rw [norm_mul]
    have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2n]; linarith
  have hG2 : ‖GG2 w‖ ≤ 2 := by unfold GG2; simp
  have key := norm_segQ_le' (f0 := 4 * Cg * ρ) (f1 := 4 * Cg / ρ) (f2 := 4 * Cg / ρ ^ 3) (g0 := ρ ^ 4 / 4)
    (gu := 2 * ρ ^ 4) (γ1 := 2 * ρ ^ 2) (γ2 := 2) hF hF1 hF2 hGl hGu hG1 hG2 (by positivity) (by positivity)
    (by positivity) (by positivity)
  exact key.trans (segQ_const_bound (by positivity) hρ)

/-- Size of the first and second boundary quantities `F/G`, `H/G` at a segment point (the analytic data of the join). -/
lemma norm_seg_bdry_le (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hCg : 0 ≤ Cg)
    (hU : kap * |U| ≤ (ρ ^ 2) ^ 2 / 16)
    (b0 : ‖gW (segPt (ρ ^ 2) t)‖ ≤ Cg) (b1 : ‖gW1 (segPt (ρ ^ 2) t)‖ ≤ Cg / ρ ^ 2) :
    ‖csrF gW (segPt (ρ ^ 2) t) / (Complex.I * GG U (segPt (ρ ^ 2) t))‖ ≤ 16 * Cg / ρ ^ 3 ∧
    ‖segH (csrF gW) (csrF1 gW gW1) (GG U) GG1 (segPt (ρ ^ 2) t) / (Complex.I * GG U (segPt (ρ ^ 2) t))‖ ≤
      1024 * Cg / ρ ^ 9 := by
  have hR : 0 ≤ ρ ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := norm_segPt_sq_bounds hρ ht0 ht1
  obtain ⟨c1, c2⟩ := norm_csr_seg_bounds hρ ht0 ht1
  have cd := norm_csr_div_seg_le hρ ht0 ht1
  set w := segPt (ρ ^ 2) t with hw
  have hρ4 : 0 < ρ ^ 4 := by positivity
  have nn0 := norm_nonneg (gW w)
  have n0 := norm_nonneg (csr w)
  have hF : ‖csrF gW w‖ ≤ 4 * Cg * ρ := by
    unfold csrF; rw [norm_mul]
    calc ‖csr w‖ * ‖gW w‖ ≤ ρ * Cg := mul_le_mul c2 b0 nn0 hρ.le
      _ ≤ 4 * Cg * ρ := by nlinarith
  have hF1 : ‖csrF1 gW gW1 w‖ ≤ 4 * Cg / ρ := by
    unfold csrF1
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have e1 : ‖csr w / (2 * w)‖ * ‖gW w‖ ≤ 1 / ρ * Cg := mul_le_mul cd b0 nn0 (by positivity)
    have e2 : ‖csr w‖ * ‖gW1 w‖ ≤ ρ * (Cg / ρ ^ 2) := mul_le_mul c2 b1 (norm_nonneg _) hρ.le
    have e3 : ρ * (Cg / ρ ^ 2) = Cg / ρ := by field_simp
    have e4 : 1 / ρ * Cg = Cg / ρ := by ring
    have : 0 ≤ Cg / ρ := by positivity
    have e5 : 4 * Cg / ρ = 4 * (Cg / ρ) := by ring
    rw [e5]; linarith
  have hGl : ρ ^ 4 / 4 ≤ ‖GG U w‖ := by
    have := norm_G_segPt_ge hR ht0 ht1 hU
    unfold GG
    nlinarith
  have hGu : ‖GG U w‖ ≤ 2 * ρ ^ 4 := by
    have := norm_G_segPt_le hR ht0 ht1 hU
    unfold GG
    nlinarith
  have hG1 : ‖GG1 w‖ ≤ 2 * ρ ^ 2 := by
    unfold GG1; rw [norm_mul]
    have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2n]; linarith
  have hGn : 0 < ‖GG U w‖ := by linarith
  have hH := norm_segH_le (f0 := 4 * Cg * ρ) (f1 := 4 * Cg / ρ) (g0 := ρ ^ 4 / 4) (gu := 2 * ρ ^ 4)
    (γ1 := 2 * ρ ^ 2) hF hF1 hGl hGu hG1 (by positivity) (by positivity) (by positivity)
  have eI : ∀ x : ℂ, ‖x / (Complex.I * GG U w)‖ = ‖x‖ / ‖GG U w‖ := by
    intro x; rw [norm_div, norm_mul, Complex.norm_I, one_mul]
  refine ⟨?_, ?_⟩
  · rw [eI, div_le_iff₀ hGn]
    have : 16 * Cg / ρ ^ 3 * ‖GG U w‖ ≥ 16 * Cg / ρ ^ 3 * (ρ ^ 4 / 4) := by
      apply mul_le_mul_of_nonneg_left hGl (by positivity)
    have e : 16 * Cg / ρ ^ 3 * (ρ ^ 4 / 4) = 4 * Cg * ρ := by field_simp; ring
    linarith
  · rw [eI, div_le_iff₀ hGn]
    have e0 : (4 * Cg / ρ * (2 * ρ ^ 4) + 4 * Cg * ρ * (2 * ρ ^ 2)) / (ρ ^ 4 / 4) ^ 2 = 256 * Cg / ρ ^ 5 := by
      field_simp; ring
    rw [e0] at hH
    have : 1024 * Cg / ρ ^ 9 * ‖GG U w‖ ≥ 1024 * Cg / ρ ^ 9 * (ρ ^ 4 / 4) :=
      mul_le_mul_of_nonneg_left hGl (by positivity)
    have e : 1024 * Cg / ρ ^ 9 * (ρ ^ 4 / 4) = 256 * Cg / ρ ^ 5 := by field_simp; ring
    linarith

end remainder

/-- The base point and direction of the connecting segment `R e^{iπ/6} → R`. -/
noncomputable def segZ0 (R : ℝ) : ℂ := (R : ℂ) * d6
noncomputable def segD (R : ℝ) : ℂ := (R : ℂ) - (R : ℂ) * d6

lemma segPt_eq (R t : ℝ) : segPt R t = segZ0 R + (t : ℂ) * segD R := rfl

lemma norm_segD_le (R : ℝ) (hR : 0 ≤ R) : ‖segD R‖ ≤ 2 * R := by
  unfold segD
  have : (R : ℂ) - (R : ℂ) * d6 = (R : ℂ) * (1 - d6) := by ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  have : ‖1 - d6‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_d6]; simp; norm_num
  nlinarith

/-- **The connecting segment.**  Two integrations by parts along `R e^{iπ/6} → R` for `csr · g_W · e^{iPh_U}`:
the integral equals the explicit boundary terms plus `(1/i)² ∫ Q e^{iPh}`, and the latter is `O(C_g R^{-9/2})`
(`R = ρ²`).  Hypotheses: `g_W` is `C²` along the segment with `|g_W| ≤ C_g`, `|g_W'| ≤ C_g/R`, `|g_W''| ≤ C_g/R²`;
`κ|U| ≤ R²/16`. -/
theorem seg_rem (hρ : 0 < ρ) (hCg : 0 ≤ Cg) (hU : kap * |U| ≤ (ρ ^ 2) ^ 2 / 16)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt gW (gW1 (segPt (ρ ^ 2) t)) (segPt (ρ ^ 2) t))
    (hg1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt gW1 (gW2 (segPt (ρ ^ 2) t)) (segPt (ρ ^ 2) t))
    (hc2 : ContinuousOn (fun t : ℝ => gW2 (segPt (ρ ^ 2) t)) (Icc 0 1))
    (b0 : ∀ t ∈ Icc (0 : ℝ) 1, ‖gW (segPt (ρ ^ 2) t)‖ ≤ Cg)
    (b1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖gW1 (segPt (ρ ^ 2) t)‖ ≤ Cg / ρ ^ 2)
    (b2 : ∀ t ∈ Icc (0 : ℝ) 1, ‖gW2 (segPt (ρ ^ 2) t)‖ ≤ Cg / ρ ^ 4) :
    lineInt (segZ0 (ρ ^ 2)) (segD (ρ ^ 2)) 0 1 (fun z => csr z * gW z * Complex.exp (Complex.I * PhU U z)) =
      (csrF gW (segZ0 (ρ ^ 2) + ((1 : ℝ) : ℂ) * segD (ρ ^ 2)) /
            (Complex.I * GG U (segZ0 (ρ ^ 2) + ((1 : ℝ) : ℂ) * segD (ρ ^ 2))) *
          Complex.exp (Complex.I * PhU U (segZ0 (ρ ^ 2) + ((1 : ℝ) : ℂ) * segD (ρ ^ 2))) -
        csrF gW (segZ0 (ρ ^ 2) + ((0 : ℝ) : ℂ) * segD (ρ ^ 2)) /
            (Complex.I * GG U (segZ0 (ρ ^ 2) + ((0 : ℝ) : ℂ) * segD (ρ ^ 2))) *
          Complex.exp (Complex.I * PhU U (segZ0 (ρ ^ 2) + ((0 : ℝ) : ℂ) * segD (ρ ^ 2)))) -
      (1 / Complex.I) *
        (segH (csrF gW) (csrF1 gW gW1) (GG U) GG1 (segZ0 (ρ ^ 2) + ((1 : ℝ) : ℂ) * segD (ρ ^ 2)) /
              (Complex.I * GG U (segZ0 (ρ ^ 2) + ((1 : ℝ) : ℂ) * segD (ρ ^ 2))) *
            Complex.exp (Complex.I * PhU U (segZ0 (ρ ^ 2) + ((1 : ℝ) : ℂ) * segD (ρ ^ 2))) -
          segH (csrF gW) (csrF1 gW gW1) (GG U) GG1 (segZ0 (ρ ^ 2) + ((0 : ℝ) : ℂ) * segD (ρ ^ 2)) /
              (Complex.I * GG U (segZ0 (ρ ^ 2) + ((0 : ℝ) : ℂ) * segD (ρ ^ 2))) *
            Complex.exp (Complex.I * PhU U (segZ0 (ρ ^ 2) + ((0 : ℝ) : ℂ) * segD (ρ ^ 2)))) +
      (1 / Complex.I) ^ 2 *
        lineInt (segZ0 (ρ ^ 2)) (segD (ρ ^ 2)) 0 1
          (fun z => segQ (csrF gW) (csrF1 gW gW1) (csrF2 gW gW1 gW2) (GG U) GG1 GG2 z *
            Complex.exp (Complex.I * PhU U z)) ∧
    ‖lineInt (segZ0 (ρ ^ 2)) (segD (ρ ^ 2)) 0 1
          (fun z => segQ (csrF gW) (csrF1 gW gW1) (csrF2 gW gW1 gW2) (GG U) GG1 GG2 z *
            Complex.exp (Complex.I * PhU U z))‖ ≤ 320000 * Cg / ρ ^ 9 := by
  have hR : 0 ≤ ρ ^ 2 := by positivity
  have hsl : ∀ t ∈ Icc (0 : ℝ) 1, segPt (ρ ^ 2) t ∈ slitPlane := by
    intro t ht
    have h := segPt_re_ge hR ht.1 ht.2
    have hs := sqrt3_bounds
    exact mem_slit_of_re_nonneg (by nlinarith [mul_nonneg hR ht.1]) (by
      intro h0
      rw [h0] at h
      simp at h
      nlinarith [sq_nonneg ρ, pow_pos hρ 2])
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, GG U (segZ0 (ρ ^ 2) + (t : ℂ) * segD (ρ ^ 2)) ≠ 0 := by
    intro t ht h0
    have := norm_G_segPt_ge hR ht.1 ht.2 hU
    have e : GG U (segPt (ρ ^ 2) t) = (kap : ℂ) * U + segPt (ρ ^ 2) t ^ 2 := rfl
    rw [segPt_eq] at this
    unfold GG at h0
    rw [h0, norm_zero] at this
    nlinarith [pow_pos hρ 4]
  refine ⟨?_, ?_⟩
  · refine seg_ibp2 (k := Complex.I) Complex.I_ne_zero (by norm_num) (P := PhU U) (F := csrF gW) (F1 := csrF1 gW gW1)
      (F2 := csrF2 gW gW1 gW2) (G := GG U) (G1 := GG1) (G2 := GG2) ?_ ?_ ?_ ?_ ?_ hne ?_ ?_
    · intro t ht; exact hasDerivAt_PhU_only U _
    · intro t ht; exact hasDerivAt_csrF (hsl t ht) (hg t ht)
    · intro t ht; exact hasDerivAt_csrF1 (hsl t ht) (hg t ht) (hg1 t ht)
    · intro t ht; exact hasDerivAt_GG U _
    · intro t ht; exact hasDerivAt_GG1 _
    · have hpt : Continuous fun t : ℝ => segPt (ρ ^ 2) t := by
        simp only [segPt_eq]; fun_prop
      have hcs : ContinuousOn (fun t : ℝ => csr (segPt (ρ ^ 2) t)) (Icc 0 1) := by
        intro t ht
        have h := segPt_re_ge hR ht.1 ht.2
        have hs := sqrt3_bounds
        have hre : 0 ≤ (segPt (ρ ^ 2) t).re := by nlinarith [mul_nonneg hR ht.1]
        exact ((continuousAt_csr (Or.inl hre)).comp (f := fun t : ℝ => segPt (ρ ^ 2) t)
          hpt.continuousAt).continuousWithinAt
      have c0 := continuousOn_line_of_hasDerivAt (z₀ := segZ0 (ρ ^ 2)) (d := segD (ρ ^ 2)) (f := gW) (f' := gW1) hg
      have c1 := continuousOn_line_of_hasDerivAt (z₀ := segZ0 (ρ ^ 2)) (d := segD (ρ ^ 2)) (f := gW1) (f' := gW2) hg1
      have hw0 : ∀ t ∈ Icc (0 : ℝ) 1, segPt (ρ ^ 2) t ≠ 0 := fun t ht => slitPlane_ne_zero (hsl t ht)
      have cw : ContinuousOn (fun t : ℝ => segPt (ρ ^ 2) t) (Icc 0 1) := hpt.continuousOn
      unfold csrF2
      simp only [segPt_eq] at hcs hw0 cw hc2 ⊢
      refine ContinuousOn.add (ContinuousOn.add ?_ ?_) (hcs.mul hc2)
      · refine ContinuousOn.mul (ContinuousOn.div hcs.neg (continuousOn_const.mul (cw.pow 2)) ?_) c0
        intro t ht
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hw0 t ht))
      · refine ContinuousOn.mul (continuousOn_const.mul (ContinuousOn.div hcs (continuousOn_const.mul cw) ?_)) c1
        intro t ht
        exact mul_ne_zero (by norm_num) (hw0 t ht)
    · exact continuousOn_const
  · rw [lineInt]
    have hbd : ∀ t ∈ Ι (0 : ℝ) 1, ‖segQ (csrF gW) (csrF1 gW gW1) (csrF2 gW gW1 gW2) (GG U)
        GG1 GG2 (segZ0 (ρ ^ 2) + (t : ℂ) * segD (ρ ^ 2)) *
          Complex.exp (Complex.I * PhU U (segZ0 (ρ ^ 2) + (t : ℂ) * segD (ρ ^ 2))) * segD (ρ ^ 2)‖ ≤
        40000 * (4 * Cg) / ρ ^ 11 * (2 * ρ ^ 2) := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hq := norm_segQ_csr_le hρ ht'.1 ht'.2 hCg hU (b0 t ht') (b1 t ht') (b2 t ht')
      have him := im_PhU_segPt_nonneg hR ht'.1 ht'.2 hU
      have he : ‖Complex.exp (Complex.I * PhU U (segPt (ρ ^ 2) t))‖ ≤ 1 := by
        rw [norm_exp_I_mul]; exact Real.exp_le_one_iff.2 (by linarith)
      have hd := norm_segD_le (ρ ^ 2) hR
      rw [norm_mul, norm_mul]
      have hq0 := norm_nonneg (segQ (csrF gW) (csrF1 gW gW1) (csrF2 gW gW1 gW2) (GG U) GG1 GG2 (segPt (ρ ^ 2) t))
      have hC : 0 ≤ 40000 * (4 * Cg) / ρ ^ 11 := by positivity
      calc _ ≤ 40000 * (4 * Cg) / ρ ^ 11 * 1 * (2 * ρ ^ 2) := by
            refine mul_le_mul (mul_le_mul hq he (norm_nonneg _) hC) hd (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) hbd
    refine this.trans ?_
    have e : 40000 * (4 * Cg) / ρ ^ 11 * (2 * ρ ^ 2) = 320000 * Cg / ρ ^ 9 := by field_simp; ring
    rw [e]; simp


end FormalResearch.SignUncertainty.CtSd
