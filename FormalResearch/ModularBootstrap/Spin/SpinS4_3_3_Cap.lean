/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_3
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_1

/-!
# Section 3.1 Helpers (`s4:3.3`): `D_4` Symmetry, Dilations, and Airy-Window Cap Integrals

Supporting lemmas for `SpinS4_3_3` (`Spin/SpinS4_3_3.lean`):
1. `lintegral_xi_d_s4_3`, `lintegral_prod_scale_s4_3`: `ℝ≥0∞` Jacobians for `(ξ+d, ξ-d)` and
   positive dilations.
2. `spinLambda_pow_sub_one_le`, `rpow_three_halves_split`, `sq_mul_exp_neg_le`: elementary
   dilation-factor and Airy-tail bounds.
3. `spinS4_3_3_cap_term`: single `(j, ℓ)` cap integral bound via `spinS22b` (Part c) with `R := 1`.
4. `spinS4_d4_four_quadrants`: `D_4` 4-quadrant reduction for `|spinG| * W_c` on gap-disc subregions.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

lemma lintegral_xi_d_s4_3 {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y : ℝ × ℝ, f y = ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, f (q.1 + q.2, q.1 - q.2) := by
  let e₁ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toEquiv :=
        { toFun := fun q => (q.1, q.1 + q.2)
          invFun := fun q => (q.1, q.2 - q.1)
          left_inv := fun ⟨x, y⟩ => by simp
          right_inv := fun ⟨x, z⟩ => by simp }
      measurable_toFun := measurable_fst.prodMk (measurable_fst.add measurable_snd)
      measurable_invFun := measurable_fst.prodMk (measurable_snd.sub measurable_fst) }
  let e₂ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toEquiv :=
        { toFun := fun q => (q.1 + q.2, q.1 - q.2)
          invFun := fun q => ((q.1 + q.2) / 2, (q.1 - q.2) / 2)
          left_inv := fun ⟨u, v⟩ => Prod.ext (by ring) (by ring)
          right_inv := fun ⟨a, b⟩ => Prod.ext (by ring) (by ring) }
      measurable_toFun := (measurable_fst.add measurable_snd).prodMk (measurable_fst.sub measurable_snd)
      measurable_invFun :=
        ((measurable_fst.add measurable_snd).div_const 2).prodMk
          ((measurable_fst.sub measurable_snd).div_const 2) }
  have h1 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g → ∫⁻ q : ℝ × ℝ, g (e₁ q) = ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
      lintegral_prod (fun q => g (e₁ q)) (hg.comp e₁.measurable).aemeasurable]
    refine lintegral_congr fun x => ?_
    simpa [e₁] using lintegral_add_left_eq_self (fun y => g (x, y)) x
  have he_map : Measure.map e₂ (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2) • (volume : Measure (ℝ × ℝ)) := by
    let s1 : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
      { toEquiv :=
          { toFun := fun q => (q.1, -2 * q.2 + q.1)
            invFun := fun q => (q.1, (q.1 - q.2) / 2)
            left_inv := fun ⟨x, y⟩ => Prod.ext rfl (by ring)
            right_inv := fun ⟨x, z⟩ => Prod.ext rfl (by ring) }
        measurable_toFun := measurable_fst.prodMk ((measurable_const.mul measurable_snd).add measurable_fst)
        measurable_invFun := measurable_fst.prodMk ((measurable_fst.sub measurable_snd).div_const 2) }
    have hcomp : ∀ q : ℝ × ℝ, s1 (e₁ q) = e₂ q := fun q => by
      simp [s1, e₁, e₂]; exact Prod.ext rfl (by ring)
    have hmap_s1 : Measure.map s1 (volume : Measure (ℝ × ℝ)) =
        ENNReal.ofReal (1 / 2) • (volume : Measure (ℝ × ℝ)) := by
      ext s hs
      rw [Measure.map_apply s1.measurable hs, Measure.smul_apply, smul_eq_mul,
        ← lintegral_indicator_one hs, ← lintegral_indicator_one (s1.measurable hs)]
      have h_lhs : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
          ∫⁻ q : ℝ × ℝ, g (s1 q) = ENNReal.ofReal (1 / 2) * ∫⁻ q : ℝ × ℝ, g q := by
        intro g hg
        rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
          lintegral_prod (fun q => g (s1 q)) (hg.comp s1.measurable).aemeasurable,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        let m : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ (-2 : ℝ) (by norm_num)
        have hm : Measure.map m (volume : Measure ℝ) = ENNReal.ofReal (1 / 2) • (volume : Measure ℝ) := by
          have h := Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0)
          rwa [show |(-2 : ℝ)⁻¹| = 1 / 2 by norm_num] at h
        have hl : ∫⁻ y : ℝ, g (x, -2 * y + x) = ENNReal.ofReal (1 / 2) * ∫⁻ z : ℝ, g (x, z + x) := by
          have h := (lintegral_map_equiv (μ := (volume : Measure ℝ)) (fun z => g (x, z + x)) m).symm
          rwa [hm, lintegral_smul_measure, smul_eq_mul] at h
        have hshift : ∫⁻ z : ℝ, g (x, z + x) = ∫⁻ z : ℝ, g (x, z) :=
          lintegral_add_right_eq_self (fun z => g (x, z)) x
        have heq : (fun y : ℝ => g (s1 (x, y))) = fun y : ℝ => g (x, -2 * y + x) := by
          ext y; simp [s1]
        rw [heq, hl, hshift]
      have hl1 := h_lhs (s.indicator 1) (measurable_const.indicator hs)
      have hind : (fun q => (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (s1 q)) =
          (s1 ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞) := by ext q; rfl
      rw [hind, lintegral_indicator_one (s1.measurable hs)] at hl1
      exact hl1.symm
    have hmap_e1 : Measure.map e₁ (volume : Measure (ℝ × ℝ)) = volume := by
      ext s hs
      rw [Measure.map_apply e₁.measurable hs, ← lintegral_indicator_one hs,
        ← lintegral_indicator_one (e₁.measurable hs)]
      have hl1 := h1 (s.indicator 1) (measurable_const.indicator hs)
      have hind : (fun q => (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (e₁ q)) =
          (e₁ ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞) := by ext q; rfl
      rw [hind] at hl1; exact hl1.symm
    have he2_eq : (e₂ : ℝ × ℝ → ℝ × ℝ) = s1 ∘ e₁ := (funext hcomp).symm
    have hmap_comp : Measure.map (s1 ∘ e₁) (volume : Measure (ℝ × ℝ)) =
        Measure.map s1 (Measure.map e₁ (volume : Measure (ℝ × ℝ))) :=
      (Measure.map_map s1.measurable e₁.measurable).symm
    rw [he2_eq, hmap_comp, hmap_e1, hmap_s1]
  have hl : ∫⁻ q : ℝ × ℝ, f (q.1 + q.2, q.1 - q.2) = ENNReal.ofReal (1 / 2) * ∫⁻ y : ℝ × ℝ, f y := by
    have h := (lintegral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) f e₂).symm
    rw [he_map, lintegral_smul_measure, smul_eq_mul] at h
    exact h
  rw [hl, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

lemma lintegral_prod_scale_s4_3 {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x : ℝ × ℝ, f (c₁ * x.1, c₂ * x.2) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) * ∫⁻ y : ℝ × ℝ, f y := by
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.mulLeft₀ c₁ hc₁.ne').prodCongr (MeasurableEquiv.mulLeft₀ c₂ hc₂.ne')
  have hmap : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) • (volume : Measure (ℝ × ℝ)) := by
    have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (c₁ * ·) (c₂ * ·) := rfl
    rw [he, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ (measurable_const_mul c₁) (measurable_const_mul c₂),
      Real.map_volume_mul_left hc₁.ne', Real.map_volume_mul_left hc₂.ne',
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      abs_of_pos (inv_pos.mpr hc₁), abs_of_pos (inv_pos.mpr hc₂),
      ENNReal.ofReal_mul (inv_pos.mpr hc₁).le]
  have h := (lintegral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) f e).symm
  rw [hmap, lintegral_smul_measure, smul_eq_mul] at h
  exact h

private lemma exp_sub_one_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp t - 1 ≤ 2 * t := by
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h1t_pos : 0 < 1 - t := by linarith
  have hexp_inv : Real.exp t ≤ (1 - t)⁻¹ := by
    rw [← inv_inv (Real.exp t), ← Real.exp_neg]
    exact inv_anti₀ h1t_pos h1
  calc Real.exp t - 1 ≤ (1 - t)⁻¹ - 1 := sub_le_sub_right hexp_inv 1
    _ = t / (1 - t) := by field_simp [h1t_pos.ne']; ring
    _ ≤ t / (1 / 2) := div_le_div_of_nonneg_left ht0 (by norm_num) (by linarith)
    _ = 2 * t := by ring

lemma spinLambda_pow_sub_one_le {c : ℝ} {N : ℕ} (hc : 49 ≤ c)
    (hN_bound : 24 * (N : ℝ) / (c - 1) ≤ 1 / 2) :
    spinLambda ((c - 1) / 12) ^ N - 1 ≤ 48 * (N : ℝ) / (c - 1) := by
  let n := c - 1
  let a := n / 12
  have hn48 : 48 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have ha2 : 2 < a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have ha2_pos : 0 < a - 2 := by linarith
  have hlam_eq : spinLambda a = Real.sqrt (1 + 2 / (a - 2)) := by
    unfold spinLambda spinGamma
    rw [show 1 - 2 / a = (a - 2) / a by field_simp [ha0.ne'], ← Real.sqrt_inv, inv_div,
      show a / (a - 2) = 1 + 2 / (a - 2) by field_simp [ha2_pos.ne']; ring]
  have hlam_le_add : spinLambda a ≤ 1 + 1 / (a - 2) := by
    rw [hlam_eq]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hsq : (1 + 1 / (a - 2)) ^ 2 = 1 + 2 / (a - 2) + (1 / (a - 2)) ^ 2 := by ring
    linarith [sq_nonneg (1 / (a - 2))]
  have hlam_le_exp : spinLambda a ≤ Real.exp (24 / n) := by
    have ha2_ge : n / 24 ≤ a - 2 := by dsimp [a]; linarith
    have h1 : 1 / (a - 2) ≤ 24 / n :=
      (one_div_le_one_div_of_le (by positivity) ha2_ge).trans_eq (by ring)
    exact hlam_le_add.trans (by
      calc 1 + 1 / (a - 2) ≤ 1 + 24 / n := by linarith
        _ = 24 / n + 1 := add_comm _ _
        _ ≤ Real.exp (24 / n) := Real.add_one_le_exp (24 / n))
  have hlam_nn : 0 ≤ spinLambda a := (lt_trans zero_lt_one (spinLambda_gt_one_s4 ha2)).le
  calc spinLambda a ^ N - 1
      ≤ Real.exp (24 / n) ^ N - 1 :=
        sub_le_sub_right (pow_le_pow_left₀ hlam_nn hlam_le_exp N) 1
    _ = Real.exp (24 * (N : ℝ) / n) - 1 := by
        rw [← Real.exp_nat_mul]; congr 2; ring
    _ ≤ 2 * (24 * (N : ℝ) / n) := exp_sub_one_le_two_mul (by positivity) hN_bound
    _ = 48 * (N : ℝ) / n := by ring

lemma rpow_three_halves_split {u r : ℝ} (hu1 : 1 ≤ u) (hur : r ≤ u) (hr0 : 0 ≤ r) :
    (1 / 2 : ℝ) * r ^ (3 / 2 : ℝ) + (1 / 2 : ℝ) * u ≤ u ^ (3 / 2 : ℝ) := by
  have hr_le : r ^ (3 / 2 : ℝ) ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hr0 hur (by norm_num)
  have hu_le : u ≤ u ^ (3 / 2 : ℝ) := by
    calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
      _ ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  linarith

lemma sq_mul_exp_neg_le {u c : ℝ} (hu0 : 0 ≤ u) (hc0 : 0 < c) :
    u ^ 2 * Real.exp (-c * u) ≤ 4 / c ^ 2 := by
  have hx0 : 0 ≤ (c / 2) * u := by positivity
  have hx : (c / 2) * u ≤ Real.exp ((c / 2) * u) := by
    linarith [Real.add_one_le_exp ((c / 2) * u)]
  have hsq : ((c / 2) * u) ^ 2 ≤ Real.exp (c * u) := by
    calc ((c / 2) * u) ^ 2 ≤ (Real.exp ((c / 2) * u)) ^ 2 :=
          pow_le_pow_left₀ hx0 hx 2
      _ = Real.exp (2 * ((c / 2) * u)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ = Real.exp (c * u) := by ring_nf
  have hexp_mul : Real.exp (c * u) * Real.exp (-c * u) = 1 := by
    rw [← Real.exp_add]; simp
  calc u ^ 2 * Real.exp (-c * u)
      = (4 / c ^ 2) * (((c / 2) * u) ^ 2 * Real.exp (-c * u)) := by
          field_simp [hc0.ne']; ring
    _ ≤ (4 / c ^ 2) * (Real.exp (c * u) * Real.exp (-c * u)) := by
          gcongr
    _ = 4 / c ^ 2 := by rw [hexp_mul, mul_one]

lemma spinS4_3_3_cap_term
    {c R C_22b κ D bStar ε : ℝ} {Φ : ℝ × ℝ → ℝ}
    (hR : 2 ≤ R) (hε_pos : 0 < ε) (hn_pos : 0 < c - 1)
    (hε_eq : (c - 1) * ε ^ (3 / 2 : ℝ) = 1)
    (hC22_pos : 0 < C_22b) (hκ_pos : 0 < κ)
    (hD0 : 0 ≤ D) (hbStar0 : 0 ≤ bStar)
    (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    (hS_int : IntegrableOn (fun d : ℝ => spinSlitIntegral ((c - 1) / 12) Φ d) (Icc (-D) D))
    (hS_le : ∫ d in Icc (-D) D, spinSlitIntegral ((c - 1) / 12) Φ d ≤ C_22b)
    (hS_ae : ∀ᵐ d ∂(volume.restrict (Icc (-D) D)),
      IntegrableOn (fun s : ℝ => ((c - 1) / 12) * Real.exp (12 * ((c - 1) / 12) * spinL s) *
        |spinDeltaA ((c - 1) / 12) Φ (s + d) (s - d)|) {s : ℝ | bStar ≤ |s|})
    (hfold_c : ∀ ξ d : ℝ, |ξ| < bStar → |d| ≤ D →
      IntegrableOn (fun s : ℝ => ((c - 1) / 12) * Real.exp (12 * ((c - 1) / 12) * spinL s) *
        |spinDeltaA ((c - 1) / 12) Φ (s + d) (s - d)|) {s : ℝ | bStar ≤ |s|} →
      ε ≤ bStar - |ξ| → bStar - |ξ| ≤ xiStar →
      ((c - 1) / 12) * Real.exp ((c - 1) * spinL ξ) * |spinDeltaA ((c - 1) / 12) Φ (ξ + d) (ξ - d)| ≤
        C_22b * (1 + spinSlitIntegral ((c - 1) / 12) Φ d) * (bStar - |ξ|)⁻¹ *
          Real.exp (-κ * (c - 1) * (bStar - |ξ|) ^ (3 / 2 : ℝ)))
    (ha2 : 2 < (c - 1) / 12)
    {A_cap : Set (ℝ × ℝ)} (hA_meas : MeasurableSet A_cap)
    (hA_sub : ∀ y ∈ A_cap, 0 < y.1 ∧ 0 < y.2 ∧
      (y.1 + y.2) / 2 ≤ bStar - ε * (R / 2) ∧ bStar - xiStar ≤ (y.1 + y.2) / 2 ∧
      |(y.1 - y.2) / 2| ≤ D) :
    let n := c - 1
    let a := n / 12
    ∫⁻ y in A_cap, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
      ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) *
        Real.exp (-(κ * (2 : ℝ) ^ (-(5 / 2 : ℝ))) * R ^ (3 / 2 : ℝ))) := by
  intro n a
  let c_22 : ℝ := κ * (2 : ℝ) ^ (-(5 / 2 : ℝ))
  let F_bd : ℝ → ℝ → ℝ≥0∞ := fun ξ d =>
    (Icc (0 : ℝ) (bStar - ε * (R / 2))).indicator (fun ξ =>
      (Icc (-D) D).indicator (fun d =>
        ENNReal.ofReal (C_22b * (1 + spinSlitIntegral a Φ d) * ε⁻¹ *
          Real.exp (-c_22 * R ^ (3 / 2 : ℝ)) * Real.exp (-(κ / (2 * ε)) * (bStar - ξ)))) d) ξ
  have hS_ae_prod : ∀ᵐ q : ℝ × ℝ ∂volume, q.2 ∈ Icc (-D) D →
      IntegrableOn (fun s : ℝ => a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + q.2) (s - q.2)|)
        {s : ℝ | bStar ≤ |s|} := by
    rw [ae_restrict_iff' measurableSet_Icc] at hS_ae
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hS_ae
  have hpt : ∀ ξ d : ℝ, (ξ + d, ξ - d) ∈ A_cap →
      IntegrableOn (fun s : ℝ => a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|)
        {s : ℝ | bStar ≤ |s|} →
      ENNReal.ofReal (|spinDeltaA a Φ (ξ + d) (ξ - d)| * spinWc a (ξ + d) * spinWc a (ξ - d)) ≤
        F_bd ξ d := by
    intro ξ d hy hS_d
    obtain ⟨hy1, hy2, hξ_ub, hξ_lb, hd_bd⟩ := hA_sub (ξ + d, ξ - d) hy
    have hsum : (ξ + d + (ξ - d)) / 2 = ξ := by ring
    have hdiff : (ξ + d - (ξ - d)) / 2 = d := by ring
    rw [hsum] at hξ_ub hξ_lb
    rw [hdiff] at hd_bd
    have hξ0 : 0 < ξ := by linarith
    have hξ_lt : |ξ| < bStar := by
      rw [abs_of_pos hξ0]; linarith [show 0 < ε * (R / 2) by positivity]
    have hδ_lo : ε ≤ bStar - |ξ| := by
      rw [abs_of_pos hξ0]
      have : ε * 1 ≤ ε * (R / 2) := mul_le_mul_of_nonneg_left (by linarith) hε_pos.le
      linarith
    have hδ_hi : bStar - |ξ| ≤ xiStar := by rw [abs_of_pos hξ0]; linarith
    have hw : spinWc a (ξ + d) * spinWc a (ξ - d) ≤ a * Real.exp (n * spinL ξ) := by
      have h := spinWc_mul_le_exp ha2.le hy1.le hy2.le
      simpa [a, n, hsum, show 12 * (n / 12) = n by ring] using h
    have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
      unfold spinSlitIntegral
      exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet fun _ _ => by positivity
    have hfb := hfold_c ξ d hξ_lt hd_bd hS_d hδ_lo hδ_hi
    have hξ_mem : ξ ∈ Icc (0 : ℝ) (bStar - ε * (R / 2)) := ⟨hξ0.le, hξ_ub⟩
    have hd_mem : d ∈ Icc (-D) D := abs_le.mp hd_bd
    simp only [F_bd, Set.indicator_of_mem hξ_mem, Set.indicator_of_mem hd_mem]
    refine ENNReal.ofReal_le_ofReal ?_
    have hδ_pos : 0 < bStar - |ξ| := lt_of_lt_of_le hε_pos hδ_lo
    have hinv_le : (bStar - |ξ|)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε_pos hδ_lo
    let u := (bStar - |ξ|) / ε
    have hu_ge_R2 : R / 2 ≤ u := by
      dsimp [u]; rw [le_div_iff₀ hε_pos]; linarith
    have hu1 : 1 ≤ u := by linarith
    have hu_split := rpow_three_halves_split hu1 hu_ge_R2 (by positivity)
    have hn_rpow : n * (bStar - |ξ|) ^ (3 / 2 : ℝ) = u ^ (3 / 2 : ℝ) := by
      dsimp [u]
      rw [Real.div_rpow hδ_pos.le hε_pos.le, div_eq_mul_inv n _, div_eq_mul_inv _ _]
      calc n * ((bStar - |ξ|) ^ (3 / 2 : ℝ) * (ε ^ (3 / 2 : ℝ))⁻¹)
          = (n * ε ^ (3 / 2 : ℝ)) * ((bStar - |ξ|) ^ (3 / 2 : ℝ) * (ε ^ (3 / 2 : ℝ))⁻¹) := by
              rw [hε_eq]
        _ = (bStar - |ξ|) ^ (3 / 2 : ℝ) * (ε ^ (3 / 2 : ℝ))⁻¹ := by rw [one_mul]
    have hexp_le : Real.exp (-κ * n * (bStar - |ξ|) ^ (3 / 2 : ℝ)) ≤
        Real.exp (-c_22 * R ^ (3 / 2 : ℝ)) * Real.exp (-(κ / (2 * ε)) * (bStar - ξ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hsub_eq : bStar - |ξ| = bStar - ξ := by rw [abs_of_pos hξ0]
      have hdiv_eq : κ * ((1 / 2 : ℝ) * (R / 2) ^ (3 / 2 : ℝ) + (1 / 2 : ℝ) * u) =
          c_22 * R ^ (3 / 2 : ℝ) + (κ / (2 * ε)) * (bStar - ξ) := by
        dsimp [c_22, u]
        rw [hsub_eq, Real.div_rpow (by positivity) (by positivity),
          show (2 : ℝ) ^ (-(5 / 2 : ℝ)) = (1 / 2 : ℝ) / (2 : ℝ) ^ (3 / 2 : ℝ) by
            rw [Real.rpow_neg (by norm_num)]; norm_num]
        field_simp [hε_pos.ne']; ring
      have hle : κ * ((1 / 2 : ℝ) * (R / 2) ^ (3 / 2 : ℝ) + (1 / 2 : ℝ) * u) ≤
          κ * (n * (bStar - |ξ|) ^ (3 / 2 : ℝ)) := by
        rw [hn_rpow]; exact mul_le_mul_of_nonneg_left hu_split hκ_pos.le
      linarith
    calc |spinDeltaA a Φ (ξ + d) (ξ - d)| * spinWc a (ξ + d) * spinWc a (ξ - d)
        = |spinDeltaA a Φ (ξ + d) (ξ - d)| * (spinWc a (ξ + d) * spinWc a (ξ - d)) := by ring
      _ ≤ |spinDeltaA a Φ (ξ + d) (ξ - d)| * (a * Real.exp (n * spinL ξ)) :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ = a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| := by ring
      _ ≤ C_22b * (1 + spinSlitIntegral a Φ d) * (bStar - |ξ|)⁻¹ *
            Real.exp (-κ * n * (bStar - |ξ|) ^ (3 / 2 : ℝ)) := by
          simpa [a, n] using hfb
      _ ≤ C_22b * (1 + spinSlitIntegral a Φ d) * ε⁻¹ *
            (Real.exp (-c_22 * R ^ (3 / 2 : ℝ)) * Real.exp (-(κ / (2 * ε)) * (bStar - ξ))) := by
          gcongr
      _ = C_22b * (1 + spinSlitIntegral a Φ d) * ε⁻¹ *
            Real.exp (-c_22 * R ^ (3 / 2 : ℝ)) * Real.exp (-(κ / (2 * ε)) * (bStar - ξ)) := by ring
  have hmeas_y : Measurable (A_cap.indicator (fun y : ℝ × ℝ =>
      ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2))) := by
    have hG : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
      unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
    have hDa : Continuous (fun p : ℝ × ℝ => spinDa a Φ p.1 p.2) := by
      unfold spinDa
      exact (((hG.sub (hG.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).sub
        (hG.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).add
        (hG.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
    have hDelta : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
      unfold spinDeltaA
      exact hDa.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
    have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
    exact (ENNReal.continuous_ofReal.comp
      ((hDelta.abs.mul (hWc.comp continuous_fst)).mul (hWc.comp continuous_snd))).measurable.indicator hA_meas
  have hstep_ae : ∫⁻ y in A_cap, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
      ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, F_bd q.1 q.2 := by
    rw [← lintegral_indicator hA_meas, lintegral_xi_d_s4_3 hmeas_y]
    refine mul_le_mul_of_nonneg_left (lintegral_mono_ae ?_) zero_le
    filter_upwards [hS_ae_prod] with q hq_int
    by_cases hq : (q.1 + q.2, q.1 - q.2) ∈ A_cap
    · have hd_mem : q.2 ∈ Icc (-D) D := by
        have hdiff : (q.1 + q.2 - (q.1 - q.2)) / 2 = q.2 := by ring
        have := (hA_sub _ hq).2.2.2.2; rw [hdiff] at this; exact abs_le.mp this
      rw [Set.indicator_of_mem hq]
      exact hpt q.1 q.2 hq (hq_int hd_mem)
    · rw [Set.indicator_of_notMem hq]; exact zero_le _
  let c_d : ℝ := C_22b * ε⁻¹ * Real.exp (-c_22 * R ^ (3 / 2 : ℝ))
  have hcd_nn : 0 ≤ c_d := by positivity
  let g1 : ℝ → ℝ≥0∞ := (Icc (0 : ℝ) (bStar - ε * (R / 2))).indicator
    (fun ξ => ENNReal.ofReal (Real.exp (-(κ / (2 * ε)) * (bStar - ξ))))
  let g2 : ℝ → ℝ≥0∞ := (Icc (-D) D).indicator
    (fun d => ENNReal.ofReal (c_d * (1 + spinSlitIntegral a Φ d)))
  have hF_le : ∀ ξ d : ℝ, F_bd ξ d ≤ g1 ξ * g2 d := by
    intro ξ d
    by_cases hξ : ξ ∈ Icc (0 : ℝ) (bStar - ε * (R / 2)) <;> by_cases hd : d ∈ Icc (-D) D
    · simp only [F_bd, g1, g2, Set.indicator_of_mem hξ, Set.indicator_of_mem hd]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal (le_of_eq (by dsimp [c_d]; ring))
    · simp [F_bd, g1, g2, Set.indicator_of_mem hξ, Set.indicator_of_notMem hd]
    · simp [F_bd, g1, g2, Set.indicator_of_notMem hξ, Set.indicator_of_mem hd]
    · simp [F_bd, g1, g2, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hd]
  have hg1_meas : AEMeasurable g1 volume :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub continuous_id)))).measurable.indicator
      measurableSet_Icc |>.aemeasurable
  have hg2_meas : AEMeasurable g2 volume :=
    ((ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      ((aemeasurable_const.add hS_int.aestronglyMeasurable.aemeasurable).const_mul c_d)).indicator
      measurableSet_Icc)
  have hprod : ∫⁻ q : ℝ × ℝ, g1 q.1 * g2 q.2 = (∫⁻ ξ : ℝ, g1 ξ) * (∫⁻ d : ℝ, g2 d) := by
    rw [Measure.volume_eq_prod]; exact lintegral_prod_mul hg1_meas hg2_meas
  have hξ_int : ∫⁻ ξ : ℝ, g1 ξ ≤ ENNReal.ofReal (2 * ε / κ) := by
    let h_Ioi : ℝ → ℝ≥0∞ := fun t => (Ioi (0 : ℝ)).indicator
      (fun t => ENNReal.ofReal (Real.exp (-(κ / (2 * ε)) * t))) t
    have hpt_ξ : ∀ ξ : ℝ, g1 ξ ≤ h_Ioi (bStar - ξ) := by
      intro ξ
      by_cases hξ : ξ ∈ Icc (0 : ℝ) (bStar - ε * (R / 2))
      · have ht_mem : bStar - ξ ∈ Ioi (0 : ℝ) := by
          have : 0 < ε * (R / 2) := by positivity
          linarith [hξ.2]
        simp only [g1, h_Ioi, Set.indicator_of_mem hξ, Set.indicator_of_mem ht_mem, le_rfl]
      · simp [g1, Set.indicator_of_notMem hξ]
    have hshift : ∫⁻ ξ : ℝ, h_Ioi (bStar - ξ) = ∫⁻ t : ℝ, h_Ioi t := by
      have hm_neg : Measure.map Neg.neg (volume : Measure ℝ) = volume :=
        (Measure.measurePreserving_neg volume).map_eq
      have hm_sub : ∫⁻ ξ : ℝ, h_Ioi (bStar + (-ξ)) = ∫⁻ z : ℝ, h_Ioi (bStar + z) := by
        have h := (lintegral_map_equiv (μ := (volume : Measure ℝ)) (fun z => h_Ioi (bStar + z))
          (MeasurableEquiv.neg ℝ)).symm
        simpa [hm_neg] using h
      simpa [sub_eq_add_neg] using hm_sub.trans (lintegral_add_left_eq_self h_Ioi bStar)
    have hIoi_val : ∫⁻ t : ℝ, h_Ioi t = ENNReal.ofReal (2 * ε / κ) := by
      have hk2_pos : 0 < κ / (2 * ε) := by positivity
      have hint := exp_neg_integrableOn_Ioi (0 : ℝ) hk2_pos
      have heval := integral_exp_mul_Ioi (by linarith : -(κ / (2 * ε)) < 0) (0 : ℝ)
      rw [lintegral_indicator measurableSet_Ioi,
        ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
      congr 1
      calc ∫ t in Ioi (0 : ℝ), Real.exp (-(κ / (2 * ε)) * t)
          = -Real.exp (-(κ / (2 * ε)) * 0) / (-(κ / (2 * ε))) := heval
        _ = 2 * ε / κ := by rw [mul_zero, Real.exp_zero]; field_simp [hκ_pos.ne', hε_pos.ne']
    calc ∫⁻ ξ : ℝ, g1 ξ ≤ ∫⁻ ξ : ℝ, h_Ioi (bStar - ξ) := lintegral_mono hpt_ξ
      _ = ∫⁻ t : ℝ, h_Ioi t := hshift
      _ = ENNReal.ofReal (2 * ε / κ) := hIoi_val
  have hd_int : ∫⁻ d : ℝ, g2 d ≤ ENNReal.ofReal (c_d * (2 * D + C_22b)) := by
    rw [lintegral_indicator measurableSet_Icc]
    have hint : IntegrableOn (fun d : ℝ => c_d * (1 + spinSlitIntegral a Φ d)) (Icc (-D) D) :=
      ((integrableOn_const (hs := measure_Icc_lt_top.ne)).add hS_int).const_mul c_d
    have hnn : ∀ d ∈ Icc (-D) D, 0 ≤ c_d * (1 + spinSlitIntegral a Φ d) := fun d _ => by
      have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
        unfold spinSlitIntegral
        exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet fun _ _ => by positivity
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Icc hnn)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, integral_add (integrableOn_const (hs := measure_Icc_lt_top.ne)) hS_int]
    have h1 : ∫ _ in Icc (-D) D, (1 : ℝ) = 2 * D := by
      rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (by linarith) hcd_nn
  calc ∫⁻ y in A_cap, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)
      ≤ ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, F_bd q.1 q.2 := hstep_ae
    _ ≤ ENNReal.ofReal 2 * ((∫⁻ ξ : ℝ, g1 ξ) * (∫⁻ d : ℝ, g2 d)) := by
        rw [← hprod]; gcongr; exact hF_le _ _
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (2 * ε / κ) * ENNReal.ofReal (c_d * (2 * D + C_22b))) := by
        gcongr
    _ = ENNReal.ofReal (2 * ((2 * ε / κ) * (c_d * (2 * D + C_22b)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    _ = ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) * Real.exp (-c_22 * R ^ (3 / 2 : ℝ))) := by
        congr 1; dsimp [c_d]; field_simp [hε_pos.ne', hκ_pos.ne']; ring

lemma spinS4_d4_four_quadrants {a x₁ L : ℝ} (ha : 2 < a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    let g : ℝ × ℝ → ℝ := fun q => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
    let E_all : Set (ℝ × ℝ) :=
      {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧ spinLongDist q ≤ L}
    let E_pp : Set (ℝ × ℝ) :=
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ (q.1 + q.2) / 2 ≤ L}
    ∫ q in E_all, g q = 4 * ∫ q in E_pp, g q := by
  intro g E_all E_pp
  have ha0 : 0 < a := by linarith
  have hG_int : Integrable g := integrable_spinG_wc ha0 hΦ
  have hmE_all : MeasurableSet E_all := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4) := by fun_prop
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact (isOpen_lt h1 continuous_const).measurableSet.inter
      (isClosed_le h2 continuous_const).measurableSet
  let E1 : Set (ℝ × ℝ) := {q ∈ E_all | 0 < q.1 ∧ 0 < q.2}
  let E2 : Set (ℝ × ℝ) := {q ∈ E_all | q.1 < 0 ∧ 0 < q.2}
  let E3 : Set (ℝ × ℝ) := {q ∈ E_all | 0 < q.1 ∧ q.2 < 0}
  let E4 : Set (ℝ × ℝ) := {q ∈ E_all | q.1 < 0 ∧ q.2 < 0}
  have hE1_eq : E1 = E_pp := by
    ext q
    simp only [E1, E_all, E_pp, Set.mem_sep_iff, Set.mem_setOf_eq, spinLongDist]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp1, hp2⟩
      rw [abs_of_pos hp1, abs_of_pos hp2] at h2
      exact ⟨hp1, hp2, by linarith, by linarith⟩
    · rintro ⟨hp1, hp2, h1, h2⟩
      exact ⟨⟨by linarith, by rw [abs_of_pos hp1, abs_of_pos hp2]; linarith⟩, hp1, hp2⟩
  have hmE1 : MeasurableSet E1 := hmE_all.inter
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet)
  have hmE2 : MeasurableSet E2 := hmE_all.inter
    ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet)
  have hmE3 : MeasurableSet E3 := hmE_all.inter
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet)
  have hmE4 : MeasurableSet E4 := hmE_all.inter
    ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet)
  have hnull_axes : volume {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0} = 0 := by
    have h1 : ({q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0} : Set (ℝ × ℝ)) =
        ((({0} : Set ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0} : Set ℝ))) := by
      ext q; simp [Set.mem_prod]
    rw [h1]
    exact measure_union_null (by rw [Measure.volume_eq_prod, Measure.prod_prod]; simp)
      (by rw [Measure.volume_eq_prod, Measure.prod_prod]; simp)
  have hae_E : E_all =ᵐ[volume] E1 ∪ E2 ∪ E3 ∪ E4 := by
    refine Filter.eventuallyEqSet_iff'.2 ?_
    rw [ae_iff]
    refine measure_mono_null (fun q hq => ?_) hnull_axes
    by_contra hnz
    push Not at hnz
    apply hq; apply propext
    rcases lt_or_gt_of_ne hnz.1 with hx | hx <;> rcases lt_or_gt_of_ne hnz.2 with hy | hy
    · exact ⟨fun h => Or.inr ⟨h, hx, hy⟩, by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
    · exact ⟨fun h => Or.inl (Or.inl (Or.inr ⟨h, hx, hy⟩)),
        by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
    · exact ⟨fun h => Or.inl (Or.inr ⟨h, hx, hy⟩),
        by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
    · exact ⟨fun h => Or.inl (Or.inl (Or.inl ⟨h, hx, hy⟩)),
        by rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h⟩
  have hg_nl : ∀ x y : ℝ, g (-x, y) = g (x, y) := fun x y => by
    dsimp [g]; rw [spinG_d4_neg_left hΦ, spinWc_even]
  have hg_nr : ∀ x y : ℝ, g (x, -y) = g (x, y) := fun x y => by
    dsimp [g]; rw [spinG_d4_neg_right hΦ, spinWc_even]
  have hE2_eq : ∫ q in E2, g q = ∫ q in E1, g q := by
    let e := MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)
    have hpre : e ⁻¹' E2 = E1 := by
      ext q
      simp only [Set.mem_preimage, e, MeasurableEquiv.prodCongr_apply, MeasurableEquiv.neg_apply,
        MeasurableEquiv.refl_apply, E2, E1, E_all, Set.mem_sep_iff, Set.mem_setOf_eq, spinLongDist]
      constructor
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; rw [abs_neg] at h2; exact ⟨⟨by linarith, h2⟩, by linarith, hq2⟩
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; rw [abs_neg]; exact ⟨⟨by linarith, h2⟩, by linarith, hq2⟩
    rw [← integral_indicator hmE1, ← integral_indicator hmE2, ← hmp.integral_comp' (E2.indicator g)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have heq : e q = (-q.1, q.2) := rfl
    by_cases hq : q ∈ E1
    · have hq2 : e q ∈ E2 := by rwa [← hpre] at hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq2, heq, hg_nl]
    · have hq2 : e q ∉ E2 := by rwa [← hpre] at hq
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq2]
  have hE3_eq : ∫ q in E3, g q = ∫ q in E1, g q := by
    let e := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)
    have hmp : MeasurePreserving e volume volume :=
      (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
    have hpre : e ⁻¹' E3 = E1 := by
      ext q
      simp only [Set.mem_preimage, e, MeasurableEquiv.prodCongr_apply, MeasurableEquiv.neg_apply,
        MeasurableEquiv.refl_apply, E3, E1, E_all, Set.mem_sep_iff, Set.mem_setOf_eq, spinLongDist]
      constructor
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; rw [abs_neg] at h2; exact ⟨⟨by linarith, h2⟩, hq1, by linarith⟩
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; rw [abs_neg]; exact ⟨⟨by linarith, h2⟩, hq1, by linarith⟩
    rw [← integral_indicator hmE1, ← integral_indicator hmE3, ← hmp.integral_comp' (E3.indicator g)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have heq : e q = (q.1, -q.2) := rfl
    by_cases hq : q ∈ E1
    · have hq3 : e q ∈ E3 := by rwa [← hpre] at hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq3, heq, hg_nr]
    · have hq3 : e q ∉ E3 := by rwa [← hpre] at hq
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq3]
  have hE4_eq : ∫ q in E4, g q = ∫ q in E1, g q := by
    let e := MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.neg ℝ)
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
    have hpre : e ⁻¹' E4 = E1 := by
      ext q
      simp only [Set.mem_preimage, e, MeasurableEquiv.prodCongr_apply, MeasurableEquiv.neg_apply,
        E4, E1, E_all, Set.mem_sep_iff, Set.mem_setOf_eq, spinLongDist]
      constructor
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; rw [abs_neg, abs_neg] at h2; exact ⟨⟨by linarith, h2⟩, by linarith, by linarith⟩
      · rintro ⟨⟨h1, h2⟩, hq1, hq2⟩; rw [abs_neg, abs_neg]; exact ⟨⟨by linarith, h2⟩, by linarith, by linarith⟩
    rw [← integral_indicator hmE1, ← integral_indicator hmE4, ← hmp.integral_comp' (E4.indicator g)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have heq : e q = (-q.1, -q.2) := rfl
    by_cases hq : q ∈ E1
    · have hq4 : e q ∈ E4 := by rwa [← hpre] at hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq4, heq, hg_nl, hg_nr]
    · have hq4 : e q ∉ E4 := by rwa [← hpre] at hq
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq4]
  have hu : ∀ {S T : Set (ℝ × ℝ)}, Disjoint S T → MeasurableSet S → MeasurableSet T →
      ∫ q in S ∪ T, g q = (∫ q in S, g q) + ∫ q in T, g q := by
    intro S T hd hS hT
    rw [← integral_indicator (hS.union hT), ← integral_indicator hS, ← integral_indicator hT,
      ← integral_add (hG_int.indicator hS) (hG_int.indicator hT)]
    congr 1; ext q
    by_cases h1 : q ∈ S <;> by_cases h2 : q ∈ T
    · exact absurd h2 (Set.disjoint_left.mp hd h1)
    · rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
    · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
    · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
        Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hd12 : Disjoint E1 E2 := Set.disjoint_left.mpr fun q h1 h2 => absurd h1.2.1 h2.2.1.not_gt
  have hd123 : Disjoint (E1 ∪ E2) E3 := Set.disjoint_left.mpr fun q h12 h3 => by
    rcases h12 with h | h
    · exact absurd h.2.2 h3.2.2.not_gt
    · exact absurd h.2.1 h3.2.1.not_gt
  have hd1234 : Disjoint (E1 ∪ E2 ∪ E3) E4 := Set.disjoint_left.mpr fun q h123 h4 => by
    rcases h123 with (h | h) | h
    · exact absurd h.2.1 h4.2.1.not_gt
    · exact absurd h.2.2 h4.2.2.not_gt
    · exact absurd h.2.1 h4.2.1.not_gt
  rw [setIntegral_congr_set hae_E,
    hu hd1234 ((hmE1.union hmE2).union hmE3) hmE4,
    hu hd123 (hmE1.union hmE2) hmE3,
    hu hd12 hmE1 hmE2, hE2_eq, hE3_eq, hE4_eq, hE1_eq]
  ring

end FormalResearch.ModularBootstrap.Spin
