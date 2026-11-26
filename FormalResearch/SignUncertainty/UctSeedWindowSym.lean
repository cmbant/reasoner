module

public import FormalResearch.SignUncertainty.UctSeedEdgeKW
public import FormalResearch.SignUncertainty.UctAiryTransPhi
public import FormalResearch.SignUncertainty.UctSeedWindowDiff

/-!
# Uniform symbol bounds for `W^seed` on the scaled strip (F2a, `uct:seed-asymp` (1))

With `ς = c^{-1/3}` and `ζ = ς w` (`0 ≤ Re w ≤ 1`) the symbol `Sy(w) = W^seed(ς w)` satisfies `|Sy(w)| ≤ C_W (1+|Im w|)^{-5/2}`
uniformly in `c ≥ c₁` and `0 ≤ δ ≤ 1` (`seedSy_bound`): `Sy = T(a)⁻¹ Z e^{-h} T(c_s w) T(a(1-ςw))` with
`|T(c_s w)| ≤ C_T(1+|Im w|)^{-5/2}` (`seedT_unif`, `F_{*,δ}` is affine in `δ`), `|T(a)⁻¹T(a(1-ζ))| ≤ 8`
(`seed_ratio_bound`, from `uct_airy_trans_phi`) and `|Z e^{-h}| ≤ C_Z` (`seedZh_bound`).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

lemma seedScale_mul_liftEps {c : ℝ} (hc : 0 < c) : seedScale c * liftEps c = ceCs := by
  unfold seedScale liftEps
  have : c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc]; norm_num
  calc ceCs * c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) = ceCs * (c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by ring
    _ = ceCs := by rw [this, mul_one]

lemma liftSymbol_zero_order (X : ℝ → ℝ) (δ₀ : ℝ) (w : ℂ) :
    liftSymbol X δ₀ 0 w = airyTwistedLaplaceC X ((ceCs : ℂ) * w) := by
  simp [liftSymbol, liftMultiplier]

/-- `T_δ(c_s w)` is bounded by `C_T (1+|Im w|)^{-5/2}` uniformly in `δ ∈ [0,1]` (`F_{*,δ}` is affine in `δ`). -/
theorem seedT_unif : ∃ CT : ℝ, 0 < CT ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, 0 ≤ w.re →
    ‖seedT δ ((ceCs : ℂ) * w)‖ ≤ CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C0, hC0, h0⟩ := hasU2_norm_liftSymbol_le_unif (hasU2_uctFstarDelta 0)
  obtain ⟨C1, hC1, h1⟩ := hasU2_norm_liftSymbol_le_unif (hasU2_uctFstarDelta 1)
  refine ⟨C0 + C1, by positivity, fun δ hδ0 hδ1 w hw => ?_⟩
  have hy : 0 ≤ ((ceCs : ℂ) * w).re := by
    rw [re_mul_real]; exact mul_nonneg ceCs_pos.le hw
  have hlin : seedT δ ((ceCs : ℂ) * w) = (1 - (δ : ℂ)) * seedT 0 ((ceCs : ℂ) * w) + (δ : ℂ) * seedT 1 ((ceCs : ℂ) * w) := by
    unfold seedT
    rw [airyTwistedLaplaceC_uctFstarDelta δ hy, airyTwistedLaplaceC_uctFstarDelta 0 hy,
      airyTwistedLaplaceC_uctFstarDelta 1 hy]
    push_cast; ring
  have b0 := h0 0 (δ₀ := 0) le_rfl hw
  have b1 := h1 0 (δ₀ := 0) le_rfl hw
  rw [liftSymbol_zero_order] at b0 b1
  have b0' : ‖seedT 0 ((ceCs : ℂ) * w)‖ ≤ C0 * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := b0
  have b1' : ‖seedT 1 ((ceCs : ℂ) * w)‖ ≤ C1 * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := b1
  rw [hlin]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hp : 0 ≤ (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have n1 : ‖(1 - (δ : ℂ))‖ = 1 - δ := by
    rw [show (1 - (δ : ℂ)) = ((1 - δ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have n2 : ‖(δ : ℂ)‖ = δ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
  rw [n1, n2]
  nlinarith [mul_le_mul_of_nonneg_left b0' (by linarith : 0 ≤ 1 - δ), mul_le_mul_of_nonneg_left b1' hδ0,
    mul_nonneg hC0.le hp, mul_nonneg hC1.le hp, mul_nonneg hδ0 (mul_nonneg hC1.le hp), mul_nonneg (by linarith : 0 ≤ 1 - δ) (mul_nonneg hC0.le hp)]

lemma phi_sub_one_bound : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ c δ : ℝ, 0 < c → 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, 0 ≤ w.re →
    2 * c ^ (-(1 / 3 : ℝ)) ≤ ‖w‖ → ‖uctPhi c δ w - 1‖ ≤ C0 * c ^ (-(2 / 3 : ℝ)) * ‖w‖ ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := uct_airy_trans_phi 0
  refine ⟨C, hC, fun c δ hc hδ0 hδ1 w hw hwn => ?_⟩
  have := h c δ hc hδ0 hδ1 w hw hwn
  simpa using this

lemma rpow_neg_two_thirds_le {x c : ℝ} (hx : 1 ≤ x) (hc : x ^ 3 ≤ c) : c ^ (-(2 / 3 : ℝ)) ≤ 1 / x := by
  have hc0 : 0 < c := by have : 0 < x ^ 3 := by positivity
                         linarith
  have h23 : x ≤ c ^ (2 / 3 : ℝ) := by
    have h : (x ^ 3) ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hc (by norm_num)
    have e : (x ^ 3) ^ (2 / 3 : ℝ) = x ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [e] at h; nlinarith
  rw [Real.rpow_neg hc0.le]
  have : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  rw [inv_le_comm₀ this (one_div_pos.mpr (by linarith))]
  simpa [one_div, inv_inv] using h23


lemma liftEps_le_quarter {c : ℝ} (hc : 64 ≤ c) : liftEps c ≤ 1 / 4 := by
  have hc0 : 0 < c := by linarith
  have h1 : (64 : ℝ) ^ (1 / 3 : ℝ) = 4 := by
    rw [show (64 : ℝ) = 4 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have h2 : 4 ≤ c ^ (1 / 3 : ℝ) := by
    rw [← h1]; exact Real.rpow_le_rpow (by norm_num) hc (by norm_num)
  unfold liftEps
  rw [Real.rpow_neg hc0.le]
  have hp : 0 < c ^ (1 / 3 : ℝ) := by linarith
  rw [inv_le_comm₀ hp (by norm_num)]
  simpa using h2

/-- `|T(a)⁻¹ T(a(1-ζ))| ≤ 8` for `0 ≤ Re ζ ≤ ς`, uniformly in `c ≥ c₁`, `δ ∈ [0,1]`. -/
theorem seed_ratio_bound : ∃ c1 : ℝ, 64 ≤ c1 ∧ ∀ c δ : ℝ, c1 ≤ c → 0 ≤ δ → δ ≤ 1 → ∀ ζ : ℂ, 0 ≤ ζ.re →
    ζ.re ≤ liftEps c → ‖(seedT δ (seedScale c : ℂ))⁻¹ * seedT δ ((seedScale c : ℂ) * (1 - ζ))‖ ≤ 8 := by
  obtain ⟨C0, hC0, hphi⟩ := phi_sub_one_bound
  set x : ℝ := 4 * C0 + 4 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  refine ⟨max 64 (x ^ 3), le_max_left _ _, fun c δ hc hδ0 hδ1 ζ hζ0 hζς => ?_⟩
  have hc64 : 64 ≤ c := (le_max_left _ _).trans hc
  have hcx : x ^ 3 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hς := liftEps_le_quarter hc64
  have hςe : liftEps c = c ^ (-(1 / 3 : ℝ)) := rfl
  have hp := rpow_neg_two_thirds_le hx1 hcx
  have hp0 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
  have hC0p : C0 * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 4 := by
    calc C0 * c ^ (-(2 / 3 : ℝ)) ≤ C0 * (1 / x) := mul_le_mul_of_nonneg_left hp hC0
      _ ≤ 1 / 4 := by
        rw [mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
  -- φ(1)
  have hK : ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) ≠ 0 := by
    have : c ^ (5 / 6 : ℝ) / uctCAi ≠ 0 := div_ne_zero (Real.rpow_pos_of_pos hc0 _).ne' uctCAi_ne
    exact_mod_cast this
  set K : ℂ := ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) with hKdef
  have hφ1 : ‖uctPhi c δ 1 - 1‖ ≤ 1 / 4 := by
    have := hphi c δ hc0 hδ0 hδ1 1 (by simp) (by rw [norm_one]; rw [← hςe]; linarith)
    rw [norm_one, Real.one_rpow, mul_one] at this
    exact this.trans hC0p
  have hφ1n : 3 / 4 ≤ ‖uctPhi c δ 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(uctPhi c δ 1 - 1))
    rw [norm_neg, norm_one, show (1 : ℂ) - -(uctPhi c δ 1 - 1) = uctPhi c δ 1 by ring] at this
    have := norm_sub_norm_le (uctPhi c δ 1) 1
    rw [norm_one] at this
    linarith
  -- φ(1-ζ)
  set w2 : ℂ := 1 - ζ with hw2
  have hw2re : 3 / 4 ≤ w2.re := by simp only [hw2, Complex.sub_re, Complex.one_re]; linarith
  have hw2n : 3 / 4 ≤ ‖w2‖ := hw2re.trans (Complex.re_le_norm _)
  have hφ2 : ‖uctPhi c δ w2 - 1‖ ≤ 1 / 2 := by
    have := hphi c δ hc0 hδ0 hδ1 w2 (by linarith) (by rw [← hςe]; linarith)
    refine this.trans ?_
    have h2 : ‖w2‖ ^ (-(2 : ℝ)) ≤ (3 / 4 : ℝ) ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hw2n (by norm_num)
    have h3 : (3 / 4 : ℝ) ^ (-(2 : ℝ)) = 16 / 9 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h3] at h2
    nlinarith [mul_nonneg hC0 hp0, mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 hp0)]
  have hφ2n : ‖uctPhi c δ w2‖ ≤ 3 / 2 := by
    have := norm_add_le (uctPhi c δ w2 - 1) 1
    rw [sub_add_cancel, norm_one] at this
    linarith
  have hS : (3 / 4 : ℝ) ^ (3 : ℝ) ≤ ‖w2‖ ^ (5 / 2 : ℝ) := by
    calc (3 / 4 : ℝ) ^ (3 : ℝ) ≤ (3 / 4 : ℝ) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ ≤ ‖w2‖ ^ (5 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hw2n (by norm_num)
  have hS' : 27 / 64 ≤ ‖w2‖ ^ (5 / 2 : ℝ) := by
    have : (3 / 4 : ℝ) ^ (3 : ℝ) = 27 / 64 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rwa [this] at hS
  have hw20 : w2 ≠ 0 := by intro h; rw [h, norm_zero] at hw2n; linarith
  have hSn : ‖w2 ^ (5 / 2 : ℂ)‖ = ‖w2‖ ^ (5 / 2 : ℝ) := by
    have := Complex.norm_cpow_of_ne_zero hw20 (5 / 2 : ℂ)
    simpa using this
  have hφ10 : uctPhi c δ 1 ≠ 0 := fun h => by rw [h, norm_zero] at hφ1n; linarith
  have hid : (seedT δ (seedScale c : ℂ))⁻¹ * seedT δ ((seedScale c : ℂ) * w2) =
      uctPhi c δ w2 * (w2 ^ (5 / 2 : ℂ))⁻¹ * (uctPhi c δ 1)⁻¹ := by
    have e1 := uctPhi_one c δ
    have e2 : uctPhi c δ w2 = K * w2 ^ (5 / 2 : ℂ) * seedT δ ((seedScale c : ℂ) * w2) := uctPhi_eq_seedT c δ w2
    have hS0 : w2 ^ (5 / 2 : ℂ) ≠ 0 := by
      intro h; have : ‖w2 ^ (5 / 2 : ℂ)‖ = 0 := by rw [h, norm_zero]
      rw [hSn] at this; linarith
    have hT1 : seedT δ (seedScale c : ℂ) ≠ 0 := by
      intro h; apply hφ10; rw [e1, h, mul_zero]
    rw [e1, e2]
    simp only [← hKdef]
    field_simp
  rw [hid, norm_mul, norm_mul, norm_inv, norm_inv, hSn]
  have hpos1 : 0 < ‖uctPhi c δ 1‖ := by linarith
  have hpos2 : 0 < ‖w2‖ ^ (5 / 2 : ℝ) := by linarith
  have : ‖uctPhi c δ w2‖ * (‖w2‖ ^ (5 / 2 : ℝ))⁻¹ * ‖uctPhi c δ 1‖⁻¹ ≤ (3 / 2) * (64 / 27) * (4 / 3) := by
    have a1 : (‖w2‖ ^ (5 / 2 : ℝ))⁻¹ ≤ 64 / 27 := by
      rw [inv_le_comm₀ hpos2 (by norm_num)]; linarith
    have a2 : ‖uctPhi c δ 1‖⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ hpos1 (by norm_num)]; linarith
    have := mul_le_mul (mul_le_mul hφ2n a1 (by positivity) (by norm_num)) a2 (by positivity) (by norm_num)
    exact this
  linarith


theorem seedZh_bound (ε : ℝ) : ∃ CZ : ℝ, 0 ≤ CZ ∧ ∀ ζ ∈ closedStrip,
    ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖ ≤ CZ := by
  obtain ⟨Ce, hCe⟩ := norm_exp_neg_outerHbar_le
  obtain ⟨M, hM0, hM⟩ := poly_exp_le_n 6
  have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-(1 / 2 : ℝ)) (1 / 2)) := isCompact_Icc.reProdIm isCompact_Icc
  have hZc : ContinuousOn (uctSeedZ ε) {ζ : ℂ | -1 < ζ.re ∧ ζ.re < 2} :=
    (differentiableOn_uctSeedZ ε).continuousOn
  obtain ⟨C0, hC0⟩ := hcomp.exists_bound_of_continuousOn
    (hZc.mono (fun ζ hζ => ⟨by linarith [hζ.1.1], by linarith [hζ.1.2]⟩))
  have hCe0 : 0 ≤ max Ce 0 := le_max_right _ _
  have hC00 : 0 ≤ max C0 0 := le_max_right _ _
  refine ⟨max (max C0 0 * (max Ce 0 * (5 / 4))) (32 * π ^ 2 * max Ce 0 * M), by positivity, fun ζ hζ => ?_⟩
  have hE := hCe ζ hζ
  set x : ℝ := |ζ.im| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  have hE' : ‖Complex.exp (-outerHbar ζ)‖ ≤ max Ce 0 * (1 + ζ.im ^ 2) :=
    hE.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  rw [norm_mul]
  rcases lt_or_ge x (1 / 2) with hlt | hge
  · have hZ : ‖uctSeedZ ε ζ‖ ≤ max C0 0 :=
      (hC0 ζ ⟨⟨hζ.1, hζ.2⟩, abs_le.mp hlt.le⟩).trans (le_max_left _ _)
    have h1 : 1 + ζ.im ^ 2 ≤ 5 / 4 := by
      have : ζ.im ^ 2 = x ^ 2 := (sq_abs _).symm
      nlinarith
    calc ‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖ ≤ max C0 0 * (max Ce 0 * (1 + ζ.im ^ 2)) :=
          mul_le_mul hZ hE' (norm_nonneg _) hC00
      _ ≤ max C0 0 * (max Ce 0 * (5 / 4)) := by gcongr
      _ ≤ _ := le_max_left _ _
  · have hZ := uctSeedZ_bound ε hζ hge
    have h1 : 1 + ζ.im ^ 2 ≤ (1 + x) ^ 2 := by
      have : ζ.im ^ 2 = x ^ 2 := (sq_abs _).symm
      nlinarith
    have hM' := hM x hx0
    calc ‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖
        ≤ (32 * π ^ 2 * (1 + x) ^ 4 * Real.exp (-(π * x))) * (max Ce 0 * (1 + x) ^ 2) :=
          mul_le_mul hZ (hE'.trans (mul_le_mul_of_nonneg_left h1 hCe0)) (norm_nonneg _) (by positivity)
      _ = 32 * π ^ 2 * max Ce 0 * ((1 + x) ^ 6 * Real.exp (-(π * x))) := by ring
      _ ≤ 32 * π ^ 2 * max Ce 0 * M := by gcongr
      _ ≤ _ := le_max_right _ _

/-- **Uniform symbol bound**: `|W^seed(ς w)| ≤ C_W (1+|Im w|)^{-5/2}` on `0 ≤ Re w ≤ 1`, uniformly in `c ≥ c₁`, `δ ∈ [0,1]`. -/
theorem seedSy_bound (ε : ℝ) : ∃ c1 CW : ℝ, 64 ≤ c1 ∧ 0 < CW ∧ ∀ c δ : ℝ, c1 ≤ c → 0 ≤ δ → δ ≤ 1 →
    ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖seedW ε δ c ((liftEps c : ℂ) * w)‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨c1, hc1, hratio⟩ := seed_ratio_bound
  obtain ⟨CT, hCT, hT⟩ := seedT_unif
  obtain ⟨CZ, hCZ, hZ⟩ := seedZh_bound ε
  refine ⟨c1, 8 * (CZ + 1) * CT, by linarith, by positivity, fun c δ hc hδ0 hδ1 w hw0 hw1 => ?_⟩
  have hc0 : 0 < c := by linarith
  have hς0 : 0 < liftEps c := by unfold liftEps; exact Real.rpow_pos_of_pos hc0 _
  have hς1 := liftEps_le_quarter (by linarith : 64 ≤ c)
  set ζ : ℂ := (liftEps c : ℂ) * w with hζ
  have hζre : ζ.re = liftEps c * w.re := by rw [hζ]; exact re_mul_real _ _
  have hζ0 : 0 ≤ ζ.re := by rw [hζre]; positivity
  have hζ1 : ζ.re ≤ liftEps c := by rw [hζre]; nlinarith
  have hcl : ζ ∈ closedStrip := ⟨hζ0, by linarith⟩
  have haζ : (seedScale c : ℂ) * ζ = (ceCs : ℂ) * w := by
    rw [hζ, ← mul_assoc, ← Complex.ofReal_mul, seedScale_mul_liftEps hc0]
  have hr := hratio c δ hc hδ0 hδ1 ζ hζ0 hζ1
  have hz := hZ ζ hcl
  have hTw := hT δ hδ0 hδ1 w hw0
  unfold seedW
  rw [haζ]
  have e : (seedT δ (seedScale c : ℂ))⁻¹ * (uctSeedZ ε ζ * Complex.exp (-outerHbar ζ) * seedT δ ((ceCs : ℂ) * w) *
      seedT δ ((seedScale c : ℂ) * (1 - ζ))) =
      ((seedT δ (seedScale c : ℂ))⁻¹ * seedT δ ((seedScale c : ℂ) * (1 - ζ))) *
        (uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)) * seedT δ ((ceCs : ℂ) * w) := by ring
  rw [e, norm_mul, norm_mul]
  have hp : 0 ≤ (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have h1 := mul_le_mul hr hz (norm_nonneg _) (by norm_num)
  have h2 := mul_le_mul h1 hTw (norm_nonneg _) (by positivity)
  calc _ ≤ 8 * CZ * (CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := h2
    _ ≤ _ := by nlinarith [mul_nonneg hCT.le hp, mul_nonneg hCZ (mul_nonneg hCT.le hp)]

/-- info: 'FormalResearch.SignUncertainty.seedT_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedT_unif

/-- info: 'FormalResearch.SignUncertainty.seedSy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedSy_bound

end FormalResearch.SignUncertainty
