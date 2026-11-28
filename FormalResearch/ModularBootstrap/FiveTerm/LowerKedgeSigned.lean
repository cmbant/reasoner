module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeSaddle
public import FormalResearch.SignUncertainty.FineOrderSigned

/-!
# Signed CFU Pairing `cts:Kedge-signed` for Virasoro (`LowerKedgeSigned`)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C6 (`cts:cauchy-dual`)
Step 4, equation `(cts:Kedge-signed)`.

Unconditionally combines:
* `virasoro_kedge_saddle` and `virasoro_kedge1_saddle` (`LowerKedgeSaddle`),
* `virasoroHalfCubic_uReal_virPhiInv` and `virasoroHalfCubic_spec` (`LowerKedgeHalfCubicData`),
* `virXPrime_eq_virasoroXiInf` (`LowerKedgeCfu`) matching `(virXPrime ((virPhiInv c x).re)).re` to
  the physical Langer coordinate `√(3 * virasoroDeltaChart c ((virasoroPhi c x).re) / c)`,
* `fs_pairing_principal`, `fs_aux`, and `fs_pairing_coeffs` (`FineOrderSigned`, Lemma FS.1(3))

to prove both signed pairing bounds against real-symmetric holomorphic `F * b` on `[-R, R]`
inside the Virasoro CFU window (`cu_sign * c^{2/3}`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FineOrderSigned
open FormalResearch.SignUncertainty.FineOrderSigned.HalfCubicInternal

noncomputable section

/-! ### 1. Exact coordinate match `virXPrime(aInv(x)) = √(3 Δ_c(φ_c(x)) / c)` -/

private lemma virXPrime_virPhiInv_props :
    ∃ r_x : ℝ, 0 < r_x ∧
      ∀ {c x : ℝ}, 2 ≤ c → ‖virPhiInv c (x : ℂ)‖ < r_x → (virPhiInv c (x : ℂ)).im = 0 →
        (virasoroPhi c (x : ℂ)).im = 0 →
        ContinuousAt virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ) ∧
        xiStar / 2 ≤ (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).re ∧
        (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).im = 0 ∧
        (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).re =
          √(3 * virasoroDeltaChart c ((virasoroPhi c (x : ℂ)).re) / c) := by
  have hev_re : ∀ᶠ a : ℂ in 𝓝 (0 : ℂ), xiStar / 2 ≤ (virXPrime a).re := by
    have hc := Complex.continuous_re.continuousAt.comp contDiffAt_virXPrime.continuousAt
    have h0 : xiStar / 2 < (virXPrime 0).re := by
      rw [virXPrime_zero, Complex.ofReal_re]; linarith [xiStar_pos]
    exact (hc.eventually (isOpen_Ioi.mem_nhds h0)).mono fun _ h => h.le
  have hev_an : ∀ᶠ a : ℂ in 𝓝 (0 : ℂ), ContinuousAt virXPrime a := by
    obtain ⟨u, hu_nhds, hu_cd⟩ := contDiffAt_virXPrime.contDiffOn (m := 0) (by simp) (fun h => by simp at h)
    have hu_cont : ContinuousOn virXPrime u := contDiffOn_zero.mp hu_cd
    filter_upwards [interior_mem_nhds.mpr hu_nhds] with a ha
    exact (hu_cont a (interior_subset ha)).continuousAt (mem_nhds_iff.mpr ⟨interior u, interior_subset, isOpen_interior, ha⟩)
  obtain ⟨r_x, hr_x, h_spec⟩ := Metric.eventually_nhds_iff_ball.mp
    (hev_an.and (hev_re.and (virXPrime_conj.and virXPrime_eq_virasoroXiInf)))
  refine ⟨r_x, hr_x, fun {c x} hc hnorm him_inv him_phi => ?_⟩
  have hc0 : 0 < c := by linarith
  set a : ℝ := (virPhiInv c (x : ℂ)).re
  have ha_c : (a : ℂ) = virPhiInv c (x : ℂ) := Complex.ext rfl him_inv.symm
  have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) r_x := by
    rwa [mem_ball_zero_iff, ha_c]
  obtain ⟨hca, hre_ge, hconj, hxi⟩ := h_spec (a : ℂ) ha_ball
  have hx_im : (virXPrime (a : ℂ)).im = 0 := by
    have h1 := hconj
    rw [Complex.conj_ofReal] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  have hx_pos : 0 < (virXPrime (a : ℂ)).re := lt_of_lt_of_le (half_pos xiStar_pos) hre_ge
  refine ⟨hca, hre_ge, hx_im, ?_⟩
  set ut : ℝ := (virasoroPhi c (x : ℂ)).re
  have hut_c : (ut : ℂ) = virasoroPhi c (x : ℂ) := Complex.ext rfl him_phi.symm
  have hmul : (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * (a : ℂ) =
      (ut : ℂ) * ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [ha_c]; unfold virPhiInv; rw [← hut_c]
    have h2 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add zero_lt_two]; simp
    calc (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
          ((((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * (ut : ℂ))
        = ((((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * (ut : ℂ) := by
          push_cast; ring
      _ = (ut : ℂ) * ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
          rw [h2, one_mul]; ring
  have hxi_re : ((virXPrime (a : ℂ)).re) ^ 2 / 3 =
      (virasoroXiChartC c (ut : ℂ)).re := by
    have hsq : virXPrime (a : ℂ) = (((virXPrime (a : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hx_im
    have hre := congrArg Complex.re hxi
    rw [hmul] at hre
    change (virXPrime (a : ℂ) ^ 2 / 3).re = (virasoroXiChartC c (ut : ℂ)).re at hre
    rw [hsq, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re] at hre
    exact hre
  have hdelta_eq : 3 * virasoroDeltaChart c ut / c = ((virXPrime (a : ℂ)).re) ^ 2 := by
    unfold virasoroDeltaChart
    have hc_ne : c ≠ 0 := hc0.ne'
    calc 3 * (c * (virasoroXiChartC c (ut : ℂ)).re) / c
        = 3 * (virasoroXiChartC c (ut : ℂ)).re := by field_simp
      _ = 3 * (((virXPrime (a : ℂ)).re) ^ 2 / 3) := by rw [← hxi_re]
      _ = ((virXPrime (a : ℂ)).re) ^ 2 := by ring
  rw [hdelta_eq, Real.sqrt_sq hx_pos.le]

/-! ### 2. Small-argument control on `virPhiInv c` and continuity of `K_edge` pullback -/

private lemma virPhiInv_norm_lt_of_bound {c R a_bd C_phi : ℝ} (hc_pos : 0 < c)
    (ha_pos : 0 < a_bd)
    (hc_big : 2 ^ (2 / 3 : ℝ) * (C_phi + 1) / (a_bd / 2) ≤ c)
    (hR_le : R ≤ (a_bd / 8) * c ^ (2 / 3 : ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ R)
    (hφ_close : ‖virasoroPhi c z - z‖ ≤ C_phi * c ^ (-(1 / 3 : ℝ))) :
    ‖virPhiInv c z‖ < a_bd := by
  have hscale_pos : 0 < (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by positivity
  have htri : ‖virasoroPhi c z‖ ≤ ‖z‖ + C_phi * c ^ (-(1 / 3 : ℝ)) := by
    have h1 := norm_add_le (virasoroPhi c z - z) z
    rw [sub_add_cancel] at h1
    linarith
  have hpow_mul : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hc_pos]; simp
  have hpow_neg1 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) = c⁻¹ := by
    rw [← Real.rpow_add hc_pos, show -(2 / 3 : ℝ) + -(1 / 3 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h2pow_le : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 4 := by
    have h1 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
    norm_num at h1; exact h1
  have h_inv_bd : (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi * c⁻¹ < a_bd / 2 := by
    have hc_gt : 2 ^ (2 / 3 : ℝ) * C_phi / (a_bd / 2) < c := by
      have h1 : 2 ^ (2 / 3 : ℝ) * C_phi < 2 ^ (2 / 3 : ℝ) * (C_phi + 1) := by
        nlinarith [Real.rpow_pos_of_pos zero_lt_two (2 / 3 : ℝ)]
      have h2 : 2 ^ (2 / 3 : ℝ) * C_phi / (a_bd / 2) < 2 ^ (2 / 3 : ℝ) * (C_phi + 1) / (a_bd / 2) :=
        div_lt_div_of_pos_right h1 (by positivity)
      exact h2.trans_le hc_big
    rw [div_lt_iff₀ (by positivity)] at hc_gt
    rw [← div_eq_mul_inv, div_lt_iff₀ hc_pos]
    linarith
  unfold virPhiInv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale_pos]
  calc ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) * ‖virasoroPhi c z‖
      ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) * (R + C_phi * c ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (htri.trans (by linarith)) hscale_pos.le
    _ ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) *
          ((a_bd / 8) * c ^ (2 / 3 : ℝ) + C_phi * c ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hscale_pos.le
    _ = (2 : ℝ) ^ (2 / 3 : ℝ) * (a_bd / 8) * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) +
          (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) := by ring
    _ = (2 : ℝ) ^ (2 / 3 : ℝ) * (a_bd / 8) + (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi * c⁻¹ := by
        rw [hpow_mul, hpow_neg1, mul_one]
    _ ≤ 4 * (a_bd / 8) + (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi * c⁻¹ := by
        have : (2 : ℝ) ^ (2 / 3 : ℝ) * (a_bd / 8) ≤ 4 * (a_bd / 8) :=
          mul_le_mul_of_nonneg_right h2pow_le (by positivity)
        linarith
    _ < a_bd / 2 + a_bd / 2 := by linarith
    _ = a_bd := by ring

private lemma virasoroHalfCubicAux_uReal_eq :
    virasoroHalfCubicAux.uReal = virasoroHalfCubic.uReal := by
  funext n a
  unfold HalfCubicData.uReal HalfCubicData.aHat
  rw [virasoroHalfCubicAux_spec.2.2.1]

private lemma virasoroHalfCubicAux_rAShrunk_eq :
    virasoroHalfCubicAux.rAShrunk = virasoroHalfCubic.rAShrunk := by
  unfold HalfCubicData.rAShrunk
  rw [virasoroHalfCubicAux_spec.1, virasoroHalfCubicAux_spec.2.1]

private lemma chain_conds_of_radius {d : HalfCubicData} {c R : ℝ}
    (hs1_pos : 0 < d.s₁) (hc_pos : 0 < c) (hc_s1 : d.s₁ ^ (-3 : ℝ) < c)
    (hR_kap : R ≤ (d.s₁ ^ 2 / (16 * CtSd.kap)) * c ^ (2 / 3 : ℝ))
    {x : ℝ} (hx : |x| ≤ R) :
    1 ≤ d.s₁ / c ^ (-(1 / 3 : ℝ)) ∧
    d.s₁ / c ^ (-(1 / 3 : ℝ)) < Rs d / c ^ (-(1 / 3 : ℝ)) ∧
    CtSd.kap * |x| ≤ (d.s₁ / c ^ (-(1 / 3 : ℝ))) ^ 2 / 16 := by
  have hlam_pos : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc_pos _
  have hs1_cubed : 1 ≤ (d.s₁ / c ^ (-(1 / 3 : ℝ))) ^ (3 : ℕ) := by
    have hc_pow : (c ^ (-(1 / 3 : ℝ))) ^ (3 : ℕ) = c⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc_pos.le]
      norm_num [Real.rpow_neg_one]
    rw [div_pow, hc_pow, div_inv_eq_mul]
    have hlt : d.s₁ ^ (-3 : ℝ) = (d.s₁ ^ (3 : ℕ))⁻¹ := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs1_pos.le, Real.rpow_natCast]
    rw [hlt] at hc_s1
    have h1 : (d.s₁ ^ (3 : ℕ))⁻¹ < c := hc_s1
    rw [inv_lt_iff_one_lt_mul₀ (pow_pos hs1_pos 3), mul_comm] at h1
    exact h1.le
  have hR1 : 1 ≤ d.s₁ / c ^ (-(1 / 3 : ℝ)) := by
    by_contra hlt
    have hlt' : d.s₁ / c ^ (-(1 / 3 : ℝ)) < 1 := lt_of_not_ge hlt
    have hpow : (d.s₁ / c ^ (-(1 / 3 : ℝ))) ^ (3 : ℕ) < 1 ^ (3 : ℕ) :=
      pow_lt_pow_left₀ hlt' (div_nonneg hs1_pos.le hlam_pos.le) (by norm_num)
    norm_num at hpow
    linarith
  have hss : d.s₁ < Rs d := (radii_chain d).2.2.2.2.2.2.2.2.2.1
  have hRR : d.s₁ / c ^ (-(1 / 3 : ℝ)) < Rs d / c ^ (-(1 / 3 : ℝ)) :=
    div_lt_div_of_pos_right hss hlam_pos
  have hRc_sq : (d.s₁ / c ^ (-(1 / 3 : ℝ))) ^ 2 = d.s₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
    rw [div_pow, ← Real.rpow_natCast (c ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc_pos.le]
    have h1 : (-(1 / 3 : ℝ) : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) := by norm_num
    rw [h1, Real.rpow_neg hc_pos.le, div_inv_eq_mul]
  have hkap_pos : 0 < CtSd.kap := by unfold CtSd.kap CtAiry.kap; positivity
  have hUR : CtSd.kap * |x| ≤ (d.s₁ / c ^ (-(1 / 3 : ℝ))) ^ 2 / 16 := by
    rw [hRc_sq]
    calc CtSd.kap * |x| ≤ CtSd.kap * R := mul_le_mul_of_nonneg_left hx hkap_pos.le
      _ ≤ CtSd.kap * ((d.s₁ ^ 2 / (16 * CtSd.kap)) * c ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hR_kap hkap_pos.le
      _ = (d.s₁ ^ 2 * c ^ (2 / 3 : ℝ)) / 16 := by field_simp [hkap_pos.ne']
  exact ⟨hR1, hRR, hUR⟩

private lemma kedge_pullback_continuous {c R ρ : ℝ}
    (hc_pos : 0 < c) (hc_2 : 2 ≤ c) (hRρ : R < ρ)
    (hInv_d : DifferentiableOn ℂ (virPhiInv c) (ball 0 ρ))
    (hX_c : ∀ x : ℝ, |x| ≤ R → ContinuousAt virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ))
    (hX_ge : ∀ x : ℝ, |x| ≤ R → xiStar / 2 ≤ (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).re)
    (hX_eq : ∀ x : ℝ, |x| ≤ R → (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).re =
        √(3 * virasoroDeltaChart c ((virasoroPhi c (x : ℂ)).re) / c)) :
    let xR : ℝ → ℝ := fun x => √(3 * virasoroDeltaChart c ((virasoroPhi c (x : ℂ)).re) / c)
    ContinuousOn (fun x => virasoroKedgeEps c (c ^ (-2 : ℝ)) (xR x)) (Icc (-R) R) ∧
    ContinuousOn (fun x => virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x)) (Icc (-R) R) := by
  intro xR
  have hε_mem : c ^ (-2 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2) := by
    refine ⟨Real.rpow_pos_of_pos hc_pos _, ?_⟩
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc_pos.le, Real.rpow_natCast]
    have h4 : (4 : ℝ) ≤ c ^ 2 := by nlinarith only [hc_2]
    rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
    linarith only [h4]
  obtain ⟨hk0_c, hk1_c⟩ := continuous_virasoroKedgeEps hc_pos hε_mem
  have ha_cont : ContinuousOn (fun x : ℝ => (virPhiInv c (x : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.continuousOn.comp
      (hInv_d.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact (abs_le.2 hx).trans_lt hRρ) (mapsTo_univ _ _)
  have hxprime_cont : ContinuousOn (fun x : ℝ =>
      (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).re) (Icc (-R) R) := fun x hx => by
    have hax : |x| ≤ R := abs_le.2 hx
    have hc_at : ContinuousAt (fun r : ℝ => (virXPrime (r : ℂ)).re) ((virPhiInv c (x : ℂ)).re) :=
      (Complex.continuous_re.continuousAt.comp (hX_c x hax)).comp Complex.continuous_ofReal.continuousAt
    exact ContinuousAt.comp_continuousWithinAt (g := fun r : ℝ => (virXPrime (r : ℂ)).re) hc_at (ha_cont x hx)
  have hxR_cont : ContinuousOn xR (Icc (-R) R) := hxprime_cont.congr fun x hx => (hX_eq x (abs_le.2 hx)).symm
  have hxR_maps : MapsTo xR (Icc (-R) R) (Ici (xiStar / 2)) := fun x hx => by
    have hax : |x| ≤ R := abs_le.2 hx
    change xiStar / 2 ≤ xR x
    dsimp only [xR]
    rw [← hX_eq x hax]
    exact hX_ge x hax
  exact ⟨hk0_c.comp hxR_cont hxR_maps, hk1_c.comp hxR_cont hxR_maps⟩

/-! ### 3. Main Theorem `virasoro_kedge_signed` (`cts:Kedge-signed`) -/

/-- **Paper label `cts:Kedge-signed`** (`cts:cauchy-dual`, Step 4):
Unconditional signed CFU pairing estimates on `[-R, R]` (`cl c^{2/3} ≤ R ≤ cu_sign c^{2/3}`)
against real-symmetric holomorphic `F * b` for both `K_edge^ε(x_R(u); c) - fsK(u)` and
`c⁻¹ K_{edge,1}^ε(x_R(u); c)` at `ε = c^{-2}`, where `x_R(u) = √(3 Δ_c(φ_c(u)) / c)`. -/
theorem virasoro_kedge_signed :
    ∃ cu_sign : ℝ, 0 < cu_sign ∧ cu_sign ≤ virasoroC1 ∧
      ∀ {cl : ℝ}, 0 < cl →
        ∃ c_sign C_eta C_rem C_ext : ℝ, 10000 ≤ c_sign ∧ 0 ≤ C_eta ∧ 0 ≤ C_rem ∧ 0 ≤ C_ext ∧
          ∀ {c R ρ Bn MF : ℝ} {F b : ℂ → ℂ},
            c_sign ≤ c → 1 ≤ R → R < ρ →
            cl * c ^ (2 / 3 : ℝ) ≤ R → R ≤ cu_sign * c ^ (2 / 3 : ℝ) → 0 ≤ Bn →
            DifferentiableOn ℂ F (ball 0 ρ) → DifferentiableOn ℂ b (ball 0 ρ) →
            (∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0) →
            (∀ x : ℝ, |x| ≤ R → (b (x : ℂ)).im = 0) →
            (∀ z ∈ closedBall (0 : ℂ) R, ‖b z‖ ≤ Bn) →
            (∫ x in (-R)..R, ‖F (x : ℂ)‖ ≤ MF) →
            (let etaF := ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)
             let xR : ℝ → ℝ := fun x => √(3 * virasoroDeltaChart c ((virasoroPhi c (x : ℂ)).re) / c)
             |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
                 (virasoroKedgeEps c (c ^ (-2 : ℝ)) (xR x) - fsK x)| ≤
               Bn * (C_eta * c⁻¹ * etaF + (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ))) * MF) ∧
             |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
                 (c⁻¹ * virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x))| ≤
               Bn * (C_eta * c⁻¹ * etaF + (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(5 / 2 : ℝ))) * MF)) := by
  obtain ⟨c_inv, cu_max, hc_inv_ge2, hcu_pos, hcu_le, hPhiInv⟩ := virasoroHalfCubic_uReal_virPhiInv
  obtain ⟨a_cut, c₀, C_ext0, ha_pos, _ha_sh, hc0_2, hc0_n, hC0_nn, hSaddle0⟩ := virasoro_kedge_saddle
  obtain ⟨a_cut1, c₀1, C_ext1, ha1_pos, _ha1_sh, hc01_2, hc01_n, hC1_nn, hSaddle1⟩ := virasoro_kedge1_saddle
  obtain ⟨cc_ch, C_phi, hCphi_nn, hCh⟩ := virasoroChart_holds
  obtain ⟨r_x, hr_x, hXProps⟩ := virXPrime_virPhiInv_props
  have hs1_pos : 0 < virasoroHalfCubic.s₁ := virasoroHalfCubic.hs₁
  have hc1_pos : 0 < virasoroC1 := virasoroC1_pos
  let a_bd : ℝ := min (min a_cut a_cut1) r_x
  have ha_bd_pos : 0 < a_bd := lt_min (lt_min ha_pos ha1_pos) hr_x
  let cu_sign : ℝ := min (min cu_max (4 * virasoroC1 ^ 2)) (min (a_bd / 8) (virasoroHalfCubic.s₁ ^ 2 / (16 * CtSd.kap)))
  have hkap_pos : 0 < CtSd.kap := by unfold CtSd.kap CtAiry.kap; positivity
  have hcu_sign_pos : 0 < cu_sign :=
    lt_min (lt_min hcu_pos (by positivity)) (lt_min (by positivity) (by positivity))
  have hcu_sign_le : cu_sign ≤ virasoroC1 := ((min_le_left _ _).trans (min_le_left _ _)).trans hcu_le
  refine ⟨cu_sign, hcu_sign_pos, hcu_sign_le, fun {cl} hcl => ?_⟩
  have hKE_nn : 0 ≤ virPoly.K_b := virPoly.hKb
  have hKO_nn : 0 ≤ (4 / (3 * (virRsIn / 2))) * virPoly.K_b := by
    have := virRsIn_pos; exact mul_nonneg (by positivity) hKE_nn
  obtain ⟨C_eta0, C_rem0, hCe0, hCr0, hPair0⟩ :=
    fs_pairing_principal virasoroHalfCubic hKE_nn hKO_nn
      (fun n a hn ha => virasoroHalfCubic_spec.2.2.2.2.2.1 n a hn ha)
      (fun n a hn ha => virasoroHalfCubic_spec.2.2.2.2.2.2 n a hn ha)
      (cu := cu_sign) hcl hC0_nn
  obtain ⟨M_C1, M_T1, C_rem1, hMC1, hMT1, hCr1, hAux⟩ := fs_aux virasoroHalfCubicAux
  let C_eta1 : ℝ := 12 * M_C1 + 32 * cu_sign ^ (1 / 2 : ℝ) * M_T1
  have hCe1 : 0 ≤ C_eta1 := by dsimp [C_eta1]; positivity
  let c_s₁ : ℝ := virasoroHalfCubic.s₁ ^ (-3 : ℝ) + 1
  let c_inv_big : ℝ := 2 ^ (2 / 3 : ℝ) * (C_phi + 1) / (a_bd / 2) + 1
  let c_sign : ℝ := max (max 10000 (max c_inv cc_ch))
    (max (max c₀ c₀1) (max c_s₁ c_inv_big))
  have hcs_10000 : 10000 ≤ c_sign := (le_max_left _ _).trans (le_max_left _ _)
  let C_eta := max C_eta0 C_eta1
  let C_rem := max C_rem0 C_rem1
  let C_ext := max C_ext0 C_ext1
  refine ⟨c_sign, C_eta, C_rem, C_ext, hcs_10000, le_max_of_le_left hCe0, le_max_of_le_left hCr0,
    le_max_of_le_left hC0_nn, fun {c R ρ Bn MF F b} hc hR1 hRρ hRlo hRhi hBn hFd hbd hFr hbr hb_bd hMF => ?_⟩
  have hc_10000 : 10000 ≤ c := hcs_10000.trans hc
  have hc_pos : 0 < c := by linarith only [hc_10000]
  have hc_1 : 1 ≤ c := by linarith only [hc_10000]
  have hc_inv : c_inv ≤ c := ((le_max_left c_inv cc_ch).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hc)
  have hc_ch : cc_ch ≤ c := ((le_max_right c_inv cc_ch).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hc)
  have hc_c0 : c₀ ≤ c := ((le_max_left c₀ c₀1).trans (le_max_left _ _)).trans ((le_max_right _ _).trans hc)
  have hc_c01 : c₀1 ≤ c := ((le_max_right c₀ c₀1).trans (le_max_left _ _)).trans ((le_max_right _ _).trans hc)
  have hc_s1 : c_s₁ ≤ c := ((le_max_left c_s₁ c_inv_big).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hc)
  have hc_ibig : c_inv_big ≤ c := ((le_max_right c_s₁ c_inv_big).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hc)
  have hR_le_cu : R ≤ cu_max * c ^ (2 / 3 : ℝ) :=
    hRhi.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _))
      (Real.rpow_nonneg hc_pos.le _))
  have hR_le_rmax : R ≤ lowerRmax virasoroC1 c := by
    unfold lowerRmax
    exact hRhi.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _))
      (Real.rpow_nonneg hc_pos.le _))
  have hR_le_a : R ≤ (a_bd / 8) * c ^ (2 / 3 : ℝ) :=
    hRhi.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _))
      (Real.rpow_nonneg hc_pos.le _))
  have hR_le_kap : R ≤ (virasoroHalfCubic.s₁ ^ 2 / (16 * CtSd.kap)) * c ^ (2 / 3 : ℝ) :=
    hRhi.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _))
      (Real.rpow_nonneg hc_pos.le _))
  obtain ⟨ρ_inv, hRρ_inv, hInv_d, hInv_sh, hInv_im, hInv_u⟩ := hPhiInv hc_inv hR1 hR_le_cu
  obtain ⟨_, _, hφ_close, _, _⟩ := hCh c hc_ch
  have hφ_im : ∀ x : ℝ, |x| ≤ R → (virasoroPhi c (x : ℂ)).im = 0 := fun x hx => by
    have h1 : (virPhiInv c (x : ℂ)).im = 0 := hInv_im x hx
    unfold virPhiInv at h1
    rw [Complex.im_ofReal_mul] at h1
    have hsc : (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1).resolve_left hsc
  have hAx_lt : ∀ x : ℝ, |x| ≤ R → ‖virPhiInv c (x : ℂ)‖ < a_bd := fun x hx => by
    have hzx : ‖(x : ℂ)‖ ≤ R := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx
    exact virPhiInv_norm_lt_of_bound hc_pos ha_bd_pos (by dsimp [c_inv_big] at hc_ibig; linarith) hR_le_a hzx
      (hφ_close (x : ℂ) (hzx.trans hR_le_rmax)).1
  have hc2 : 2 ≤ c := by linarith only [hc_10000]
  have hX_all : ∀ x : ℝ, |x| ≤ R →
      ContinuousAt virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ) ∧
      xiStar / 2 ≤ (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).re ∧
      (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).im = 0 ∧
      (virXPrime (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ)).re =
        √(3 * virasoroDeltaChart c ((virasoroPhi c (x : ℂ)).re) / c) := fun x hx =>
    hXProps hc2 ((hAx_lt x hx).trans_le (min_le_right _ _)) (hInv_im x hx) (hφ_im x hx)
  set xR : ℝ → ℝ := fun x => √(3 * virasoroDeltaChart c ((virasoroPhi c (x : ℂ)).re) / c)
  have hR_nn : 0 ≤ R := by linarith only [hR1]
  obtain ⟨hk0_c, hk1_c⟩ := kedge_pullback_continuous hc_pos hc2 (lt_min hRρ hRρ_inv)
    (hInv_d.mono (ball_subset_ball (min_le_right _ _)))
    (fun x hx => (hX_all x hx).1) (fun x hx => (hX_all x hx).2.1) (fun x hx => (hX_all x hx).2.2.2)
  let ρ' := min ρ ρ_inv
  have hRρ' : R < ρ' := lt_min hRρ hRρ_inv
  have hFd' : DifferentiableOn ℂ F (ball 0 ρ') := hFd.mono (ball_subset_ball (min_le_left _ _))
  have hbd' : DifferentiableOn ℂ b (ball 0 ρ') := hbd.mono (ball_subset_ball (min_le_left _ _))
  have hInv_d' : DifferentiableOn ℂ (virPhiInv c) (ball 0 ρ') :=
    hInv_d.mono (ball_subset_ball (min_le_right _ _))
  have hInv_sh' : ∀ z ∈ ball (0 : ℂ) ρ', virPhiInv c z ∈ ball (0 : ℂ) virasoroHalfCubic.rAShrunk :=
    fun z hz => hInv_sh z (ball_subset_ball (min_le_right _ _) hz)
  have hfsK_c : Continuous fsK := continuous_iff_continuousAt.2 fun x => (hasDerivAt_fsK x).continuousAt
  have hfsKp_c : Continuous fsKp := by
    unfold fsKp
    have hcAi : Continuous airyAi := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAi x).continuousAt
    have hcAi' : Continuous airyAi' := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAi' x).continuousAt
    have hcBi : Continuous airyBi := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBi x).continuousAt
    have hcBi' : Continuous airyBiDeriv := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBiDeriv x).continuousAt
    exact continuous_const.mul ((continuous_const.mul hcAi').mul hcBi' |>.add
      ((continuous_const.mul continuous_id).mul hcAi |>.mul hcBi))
  have hF_re_c : ContinuousOn (fun x : ℝ => (F (x : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.continuousOn.comp
      (hFd'.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.2 hx).trans_lt hRρ')
      (mapsTo_univ _ _)
  have hb_re_c : ContinuousOn (fun x : ℝ => (b (x : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.continuousOn.comp
      (hbd'.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.2 hx).trans_lt hRρ')
      (mapsTo_univ _ _)
  have hL0_int : IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re *
      (virasoroKedgeEps c (c ^ (-2 : ℝ)) (xR x) - fsK x)) volume (-R) R :=
    ((hF_re_c.mul hb_re_c).mul (hk0_c.sub hfsK_c.continuousOn)).intervalIntegrable_of_Icc
      (by linarith only [hR_nn])
  have hL0_saddle : ∀ x : ℝ, |x| ≤ R →
      let lam := c ^ (-(1 / 3 : ℝ))
      let R_c := virasoroHalfCubic.s₁ / lam
      let R₀ := Rs virasoroHalfCubic / lam
      let ax := (virPhiInv c (x : ℂ)).re
      ∀ (hR1' : 1 ≤ R_c) (hRR' : R_c < R₀) (hUR' : CtSd.kap * |virasoroHalfCubic.uReal c ax| ≤ R_c ^ 2 / 16),
      |virasoroKedgeEps c (c ^ (-2 : ℝ)) (xR x) -
        fsOpCh (fsChain hR1' hRR' hUR') (virasoroHalfCubic.uReal c ax)
          (fun w => virasoroHalfCubic.B c ax ((lam : ℂ) * w))| ≤ C_ext0 * c ^ (-(3 / 2 : ℝ)) := by
    intro x hx lam R_c R₀ ax hR1' hRR' hUR'
    have hax_abs : |ax| < a_cut := by
      have ha_c : (ax : ℂ) = virPhiInv c (x : ℂ) := Complex.ext rfl (hInv_im x hx).symm
      have hax_eq : |ax| = ‖virPhiInv c (x : ℂ)‖ := by rw [← ha_c, Complex.norm_real, Real.norm_eq_abs]
      rw [hax_eq]
      exact (hAx_lt x hx).trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hx_eq := (hX_all x hx).2.2.2
    dsimp only [xR]
    rw [← hx_eq]
    exact hSaddle0 hc_c0 hax_abs hR1' hRR' hUR'
  have hBound0 := hPair0 (n := c) (R := R) (ρ := ρ') (Bn := Bn) (MF := MF)
    (F := F) (b := b) (aInv := virPhiInv c)
    (hc0_n.trans hc_c0) hR1 hRρ' hRlo hRhi hBn hFd' hbd' hInv_d' hInv_sh'
    hFr hbr hInv_im hInv_u hb_bd hMF hL0_saddle hL0_int
  have hηF_nn : 0 ≤ ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun θ _ =>
      div_nonneg (mul_nonneg hR_nn (norm_nonneg _)) (Real.exp_pos _).le
  have hMF_nn : 0 ≤ MF :=
    le_trans (intervalIntegral.integral_nonneg (by linarith only [hR_nn]) fun _ _ => norm_nonneg _) hMF
  have hRes0 : |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
      (virasoroKedgeEps c (c ^ (-2 : ℝ)) (xR x) - fsK x)| ≤
      Bn * (C_eta * c⁻¹ * (∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) +
        (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ))) * MF) := by
    refine hBound0.trans (mul_le_mul_of_nonneg_left ?_ hBn)
    gcongr
    · exact le_max_left _ _
    · exact le_max_left _ _
    · exact le_max_left _ _
  -- Part 2: `virasoroKedge1Eps` via `fs_aux` + `fs_pairing_coeffs`
  have hc_aux_n0 : virasoroHalfCubicAux.n₀ ≤ c := hc01_n.trans hc_c01
  obtain ⟨hcK_d, hcKp_d, hcK_bd, hcKp_bd, hAux_exp⟩ := hAux c hc_aux_n0
  set cK : ℂ → ℂ := fun u => virasoroHalfCubicAux.CnStar c (virPhiInv c u)
  set cJ : ℂ → ℂ := fun _ => 0
  set cKp : ℂ → ℂ := fun u => virasoroHalfCubicAux.TnStar c (virPhiInv c u)
  have hcK_d' : DifferentiableOn ℂ cK (ball 0 ρ') :=
    hcK_d.comp hInv_d' fun z hz => by rw [virasoroHalfCubicAux_rAShrunk_eq]; exact hInv_sh' z hz
  have hcJ_d' : DifferentiableOn ℂ cJ (ball 0 ρ') := differentiableOn_const 0
  have hcKp_d' : DifferentiableOn ℂ cKp (ball 0 ρ') :=
    hcKp_d.comp hInv_d' fun z hz => by rw [virasoroHalfCubicAux_rAShrunk_eq]; exact hInv_sh' z hz
  have hcK_real : ∀ x : ℝ, |x| ≤ R → (cK (x : ℂ)).im = 0 := fun x hx => by
    have ha_c : (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ) = virPhiInv c (x : ℂ) :=
      Complex.ext rfl (hInv_im x hx).symm
    have hax_mem : virPhiInv c (x : ℂ) ∈ ball (0 : ℂ) virasoroHalfCubicAux.rAShrunk := by
      rw [virasoroHalfCubicAux_rAShrunk_eq]
      exact hInv_sh' _ (mem_ball_zero_iff.2 (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx.trans_lt hRρ'))
    have hax_abs : |(virPhiInv c (x : ℂ)).re| < virasoroHalfCubicAux.rAShrunk := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, ha_c, ← mem_ball_zero_iff]; exact hax_mem
    dsimp [cK]
    rw [← ha_c]
    exact (hcKp_bd _ hax_abs).1
  have hcKp_real : ∀ x : ℝ, |x| ≤ R → (cKp (x : ℂ)).im = 0 := fun x hx => by
    have ha_c : (((virPhiInv c (x : ℂ)).re : ℝ) : ℂ) = virPhiInv c (x : ℂ) :=
      Complex.ext rfl (hInv_im x hx).symm
    have hax_mem : virPhiInv c (x : ℂ) ∈ ball (0 : ℂ) virasoroHalfCubicAux.rAShrunk := by
      rw [virasoroHalfCubicAux_rAShrunk_eq]
      exact hInv_sh' _ (mem_ball_zero_iff.2 (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx.trans_lt hRρ'))
    have hax_abs : |(virPhiInv c (x : ℂ)).re| < virasoroHalfCubicAux.rAShrunk := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, ha_c, ← mem_ball_zero_iff]; exact hax_mem
    dsimp [cKp]
    rw [← ha_c]
    exact (hcKp_bd _ hax_abs).2
  have hR_pos : 0 < R := by linarith only [hR1]
  have hcK_bd' : ∀ θ ∈ Icc (0 : ℝ) π, ‖cK (circleMap 0 R θ)‖ ≤ M_C1 := fun θ _ =>
    (hcK_bd _ (by
      rw [virasoroHalfCubicAux_rAShrunk_eq]
      exact hInv_sh' _ (mem_ball_zero_iff.2 (by simpa [abs_of_pos hR_pos] using hRρ')))).1
  have hcKp_bd' : ∀ θ ∈ Icc (0 : ℝ) π, ‖cKp (circleMap 0 R θ)‖ ≤ M_T1 := fun θ _ =>
    (hcK_bd _ (by
      rw [virasoroHalfCubicAux_rAShrunk_eq]
      exact hInv_sh' _ (mem_ball_zero_iff.2 (by simpa [abs_of_pos hR_pos] using hRρ')))).2
  set err1 : ℝ → ℝ := fun x => c⁻¹ * virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x) -
    (c⁻¹ * (cK (x : ℂ)).re * fsK x + c ^ (-(2 / 3 : ℝ)) * (cJ (x : ℂ)).re * fsJ x +
      c ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp x)
  have herr1_bd : ∀ x ∈ Icc (-R) R,
      |err1 x| ≤ C_rem1 * c ^ (-(5 / 3 : ℝ)) + C_ext1 * c ^ (-(5 / 2 : ℝ)) := by
    intro x hx
    have hax_abs_x : |x| ≤ R := abs_le.2 hx
    set ax := (virPhiInv c (x : ℂ)).re
    have hax_lt1 : |ax| < a_cut1 := by
      have ha_c : (ax : ℂ) = virPhiInv c (x : ℂ) := Complex.ext rfl (hInv_im x hax_abs_x).symm
      have hax_eq : |ax| = ‖virPhiInv c (x : ℂ)‖ := by rw [← ha_c, Complex.norm_real, Real.norm_eq_abs]
      rw [hax_eq]
      exact (hAx_lt x hax_abs_x).trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hax_sh : (ax : ℂ) ∈ ball (0 : ℂ) virasoroHalfCubicAux.rAShrunk := by
      have ha_c : (ax : ℂ) = virPhiInv c (x : ℂ) := Complex.ext rfl (hInv_im x hax_abs_x).symm
      rw [ha_c, virasoroHalfCubicAux_rAShrunk_eq]
      exact hInv_sh' _ (mem_ball_zero_iff.2 (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hax_abs_x.trans_lt hRρ'))
    have hu_aux : virasoroHalfCubicAux.uReal c ax = x := by
      rw [virasoroHalfCubicAux_uReal_eq]; exact hInv_u x hax_abs_x
    have hcs1_aux : virasoroHalfCubicAux.s₁ ^ (-3 : ℝ) < c := by
      rw [virasoroHalfCubicAux_spec.2.1]; dsimp [c_s₁] at hc_s1; linarith only [hc_s1]
    have hR_kap_aux : R ≤ (virasoroHalfCubicAux.s₁ ^ 2 / (16 * CtSd.kap)) * c ^ (2 / 3 : ℝ) := by
      rw [virasoroHalfCubicAux_spec.2.1]; exact hR_le_kap
    obtain ⟨hR1_a, hRR_a, hUR_a⟩ := chain_conds_of_radius virasoroHalfCubicAux.hs₁ hc_pos hcs1_aux hR_kap_aux hax_abs_x
    have hUR_u : CtSd.kap * |virasoroHalfCubicAux.uReal c ax| ≤
        (virasoroHalfCubicAux.s₁ / c ^ (-(1 / 3 : ℝ))) ^ 2 / 16 := by
      rw [hu_aux]; exact hUR_a
    have hsad1 := hSaddle1 hc_c01 hax_lt1 hR1_a hRR_a hUR_u
    rw [(hX_all x hax_abs_x).2.2.2] at hsad1
    have ha_c : (ax : ℂ) = virPhiInv c (x : ℂ) := Complex.ext rfl (hInv_im x hax_abs_x).symm
    have haux_b := hAux_exp ax (by simpa [Complex.norm_real, Real.norm_eq_abs, mem_ball_zero_iff] using hax_sh)
      hR1_a hRR_a hUR_u
    set u' : ℝ := virasoroHalfCubicAux.uReal c ax
    set Lop := fsOpCh (fsChain hR1_a hRR_a hUR_u) u'
      (fun w => virasoroHalfCubicAux.B c ax (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * w))
    have hsplit_e : err1 x =
        c⁻¹ * (virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x) - Lop) +
        (c⁻¹ * Lop - (c⁻¹ * (cK (x : ℂ)).re * fsK u' + c ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp u')) := by
      have hfsK_eq : fsK u' = fsK x := congrArg fsK hu_aux
      have hfsKp_eq : fsKp u' = fsKp x := congrArg fsKp hu_aux
      dsimp [err1, cK, cJ, cKp]
      rw [← ha_c, hfsK_eq, hfsKp_eq]
      simp only [mul_zero, zero_mul, add_zero]
      ring
    have h1 : |c⁻¹ * (virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x) - Lop)| ≤ C_ext1 * c ^ (-(5 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hc_pos)]
      have hpow52 : c⁻¹ * c ^ (-(3 / 2 : ℝ)) = c ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc_pos]; norm_num
      calc c⁻¹ * |virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x) - Lop|
          ≤ c⁻¹ * (C_ext1 * c ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hsad1 (inv_pos.mpr hc_pos).le
        _ = C_ext1 * c ^ (-(5 / 2 : ℝ)) := by rw [← mul_assoc, mul_comm c⁻¹ C_ext1, mul_assoc, hpow52]
    have h2 : |c⁻¹ * Lop - (c⁻¹ * (cK (x : ℂ)).re * fsK u' + c ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp u')| ≤
        C_rem1 * c ^ (-(5 / 3 : ℝ)) := by
      have hsub_eq : c⁻¹ * Lop - (c⁻¹ * (cK (x : ℂ)).re * fsK u' + c ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp u') =
          c⁻¹ * (Lop - ((virasoroHalfCubicAux.CnStar c (ax : ℂ)).re * fsK u' +
            c ^ (-(1 / 3 : ℝ)) * (virasoroHalfCubicAux.TnStar c (ax : ℂ)).re * fsKp u')) := by
        dsimp [cK, cKp]
        rw [← ha_c]
        have hpow43 : c⁻¹ * c ^ (-(1 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
          rw [← Real.rpow_neg_one c, ← Real.rpow_add hc_pos]; norm_num
        calc c⁻¹ * Lop - (c⁻¹ * (virasoroHalfCubicAux.CnStar c (ax : ℂ)).re * fsK u' +
              c ^ (-(4 / 3 : ℝ)) * (virasoroHalfCubicAux.TnStar c (ax : ℂ)).re * fsKp u')
            = c⁻¹ * Lop - (c⁻¹ * (virasoroHalfCubicAux.CnStar c (ax : ℂ)).re * fsK u' +
                (c⁻¹ * c ^ (-(1 / 3 : ℝ))) * (virasoroHalfCubicAux.TnStar c (ax : ℂ)).re * fsKp u') := by
              rw [hpow43]
          _ = _ := by ring
      have hpow53 : c⁻¹ * c ^ (-(2 / 3 : ℝ)) = c ^ (-(5 / 3 : ℝ)) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc_pos]; norm_num
      rw [hsub_eq, abs_mul, abs_of_pos (inv_pos.mpr hc_pos)]
      calc c⁻¹ * |Lop - ((virasoroHalfCubicAux.CnStar c (ax : ℂ)).re * fsK u' +
              c ^ (-(1 / 3 : ℝ)) * (virasoroHalfCubicAux.TnStar c (ax : ℂ)).re * fsKp u')|
          ≤ c⁻¹ * (C_rem1 * c ^ (-(2 / 3 : ℝ))) := mul_le_mul_of_nonneg_left haux_b (inv_pos.mpr hc_pos).le
        _ = C_rem1 * c ^ (-(5 / 3 : ℝ)) := by rw [← mul_assoc, mul_comm c⁻¹ C_rem1, mul_assoc, hpow53]
    rw [hsplit_e]
    exact (abs_add_le _ _).trans (by linarith only [h1, h2])
  have hcK_re_c : ContinuousOn (fun x : ℝ => (cK (x : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.continuousOn.comp
      (hcK_d'.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.2 hx).trans_lt hRρ')
      (mapsTo_univ _ _)
  have hcKp_re_c : ContinuousOn (fun x : ℝ => (cKp (x : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.continuousOn.comp
      (hcKp_d'.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.2 hx).trans_lt hRρ')
      (mapsTo_univ _ _)
  have herr1_int : IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * err1 x) volume (-R) R := by
    have hsum_c : ContinuousOn (fun x : ℝ => c⁻¹ * (cK (x : ℂ)).re * fsK x +
        c ^ (-(2 / 3 : ℝ)) * (cJ (x : ℂ)).re * fsJ x +
        c ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp x) (Icc (-R) R) := by
      have hcJ_re_c : ContinuousOn (fun x : ℝ => (cJ (x : ℂ)).re) (Icc (-R) R) := continuousOn_const
      have hfsJ_c : Continuous fsJ :=
        (continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAi x).continuousAt).mul
          (continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBi x).continuousAt)
      exact (((continuousOn_const.mul hcK_re_c).mul hfsK_c.continuousOn).add
        ((continuousOn_const.mul hcJ_re_c).mul hfsJ_c.continuousOn)).add
        ((continuousOn_const.mul hcKp_re_c).mul hfsKp_c.continuousOn)
    exact ((hF_re_c.mul hb_re_c).mul ((continuousOn_const.mul hk1_c).sub hsum_c)).intervalIntegrable_of_Icc
      (by linarith only [hR_nn])
  have hBound1 := fs_pairing_coeffs hc_1 hR1 hRρ' hcl hRlo hRhi hBn (by norm_num : (0 : ℝ) ≤ 0) hMC1 hMT1
    (by positivity) hFd' hbd' hcJ_d' hcK_d' hcKp_d' hFr hbr (fun _ _ => rfl) hcK_real hcKp_real
    hb_bd (fun _ _ => by simp [cJ]) hcK_bd' hcKp_bd' hMF herr1_bd herr1_int
  have hcongr1 : ∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
      (c⁻¹ * virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x)) =
      ∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
        (c⁻¹ * (cK (x : ℂ)).re * fsK x + c ^ (-(2 / 3 : ℝ)) * (cJ (x : ℂ)).re * fsJ x +
          c ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp x + err1 x) :=
    intervalIntegral.integral_congr fun x _ => by dsimp [err1]; ring
  have hBound1' : |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
      (c⁻¹ * (cK (x : ℂ)).re * fsK x + c ^ (-(2 / 3 : ℝ)) * (cJ (x : ℂ)).re * fsJ x +
        c ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp x + err1 x)| ≤
      Bn * (C_eta1 * c⁻¹ * (∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) +
        (C_rem1 * c ^ (-(5 / 3 : ℝ)) + C_ext1 * c ^ (-(5 / 2 : ℝ))) * MF) := by
    refine hBound1.trans_eq ?_
    dsimp [C_eta1]
    simp only [mul_zero, add_zero]
  have hRes1 : |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
      (c⁻¹ * virasoroKedge1Eps c (c ^ (-2 : ℝ)) (xR x))| ≤
      Bn * (C_eta * c⁻¹ * (∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) +
        (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(5 / 2 : ℝ))) * MF) := by
    rw [hcongr1]
    refine hBound1'.trans (mul_le_mul_of_nonneg_left ?_ hBn)
    gcongr
    · exact le_max_right _ _
    · exact le_max_right _ _
    · exact le_max_right _ _
  exact ⟨hRes0, hRes1⟩

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_kedge_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_kedge_signed
