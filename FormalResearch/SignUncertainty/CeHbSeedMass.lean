module

public import FormalResearch.CohnElkies.AirySeedFloors

/-!
# Uniform `γ₂` Version of `lem:hb-seed-mass`

Refines `FormalResearch.CohnElkies.hb_seed_mass_exists` so that `γ₂ > 0` is chosen prior to `V_max`,
allowing `thm:ce-hb-lift` (`CeHbLift.lean`) to pick `v₀` depending on `γ₂` and `H̃_N` as in
`ce_lift_proofs.tex` (Step 1 of `thm:ce-hb-lift`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

theorem hb_seed_mass_exists_unif (S : HBSeedSpec) {b ε₀ : ℝ} (hb : 0 < b)
    (hb_nodes : ∀ j : Fin S.m₀, j.val + 1 < S.m₀ → 0 < ceSb b (S.nodes j))
    (hε : 0 ≤ ε₀) :
    ∃ γ₂ > 0, ∀ {V_max : ℝ}, 0 ≤ V_max → ∃ δ₁ > 0, ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ v ∈ Icc (0 : ℝ) V_max, ∀ δ ∈ Ioc (0 : ℝ) δ₁, ∀ r_val : ℝ, |r_val| ≤ ε₀ * δ →
        let γ₁ := (γ₂ * (1 + |airyDerivFirstZero|) + v) / S.I_N
        let F := fun u : ℝ => S.G_N u - γ₁ * δ * S.H_N u + γ₂ * δ * ceSb b u +
          r_val * ceG1 (airyZero 1) u
        let u₀ := S.lastNode - 2 * γ₁ * δ
        0 < γ₁ ∧
        (Integrable F ∧ ∫ u : ℝ, F u = -v * δ + r_val) ∧
        (∀ x ≥ |u₀| + ceBeta1 * δ / 2,
          (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
            ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2), F (-x + t) * bspline 4 (ceBeta1 * δ / 2) t) ∧
        (∀ j : Fin S.m₀, j.val + 1 < S.m₀ → ∀ u, |u - S.nodes j| ≤ ceBeta1 * δ →
          δ / 2 ≤ F u) := by
  classical
  have hne : (Finset.univ : Finset (Fin S.m₀)).Nonempty := ⟨⟨0, S.m₀_pos⟩, Finset.mem_univ _⟩
  have hex_site : ∀ j : Fin S.m₀, ∃ r_j > 0,
      j.val + 1 < S.m₀ → ∀ u, |u - S.nodes j| ≤ r_j → ceSb b (S.nodes j) / 2 ≤ ceSb b u := by
    intro j
    by_cases hj : j.val + 1 < S.m₀
    · obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.mp (continuous_ceSb b).continuousAt
        (ceSb b (S.nodes j) / 2) (half_pos (hb_nodes j hj))
      refine ⟨ρ / 2, half_pos hρ, fun _ u hu => ?_⟩
      have hsub := abs_sub_lt_iff.mp (by simpa [Real.dist_eq] using hball (by rw [Real.dist_eq]; linarith))
      linarith
    · exact ⟨1, one_pos, fun h => absurd h hj⟩
  let r_fn_j : Fin S.m₀ → ℝ := fun j => Classical.choose (hex_site j)
  let r_site : ℝ := min S.r_node (Finset.univ.inf' hne r_fn_j)
  have hr_site : 0 < r_site := lt_min S.r_node_pos
    ((Finset.lt_inf'_iff hne).mpr fun j _ => (Classical.choose_spec (hex_site j)).1)
  let s_val : Fin S.m₀ → ℝ := fun j => if h : j.val + 1 < S.m₀ then ceSb b (S.nodes j) / 2 else 1
  let s : ℝ := Finset.univ.inf' hne s_val
  have hs_pos : 0 < s := (Finset.lt_inf'_iff hne).mpr fun j _ => by
    dsimp [s_val]; split_ifs with h; exact half_pos (hb_nodes j h); exact one_pos
  let R_site : ℝ := r_site + Finset.univ.sup' hne (fun j => |S.nodes j|)
  have hR_site : 0 ≤ R_site := by
    have h0 : |S.nodes ⟨0, S.m₀_pos⟩| ≤ Finset.univ.sup' hne (fun j => |S.nodes j|) :=
      Finset.le_sup' (fun j => |S.nodes j|) (Finset.mem_univ _)
    linarith [abs_nonneg (S.nodes ⟨0, S.m₀_pos⟩)]
  obtain ⟨t_g1, -, ht_g1_max⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, neg_nonpos.mpr hR_site, hR_site⟩ (continuous_ceG1 (airyZero 1)).continuousOn
  let M_g1 : ℝ := max (ceG1 (airyZero 1) t_g1) 0
  have h_g1_site : ∀ j : Fin S.m₀, ∀ u, |u - S.nodes j| ≤ r_site → ceG1 (airyZero 1) u ≤ M_g1 := by
    intro j u hu
    have hj_le : |S.nodes j - 0| ≤ Finset.univ.sup' hne (fun k => |S.nodes k|) := by
      rw [sub_zero]; exact Finset.le_sup' (fun k => |S.nodes k|) (Finset.mem_univ j)
    have hu_abs : |u| ≤ R_site := by simpa [sub_zero] using (abs_sub_le u (S.nodes j) 0).trans (add_le_add hu hj_le)
    exact (ht_g1_max (abs_le.mp hu_abs)).trans (le_max_left _ _)
  let γ₂ : ℝ := max (max 1 (2 * ε₀)) ((ceBeta1 * S.A_G + ε₀ * M_g1 + 1) / s)
  have hγ₂_pos : 0 < γ₂ := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  have hγ₂_eps : 2 * ε₀ ≤ γ₂ := (le_max_right _ _).trans (le_max_left _ _)
  have hγ₂_site : ceBeta1 * S.A_G + ε₀ * M_g1 + 1 ≤ γ₂ * s := (div_le_iff₀ hs_pos).mp (le_max_right _ _)
  obtain ⟨C_b, hC_b_pos, h_sb_floor⟩ := ceSb_lower_floor hb
  refine ⟨γ₂, hγ₂_pos, fun {V_max} hV => ?_⟩
  let γ₁_max : ℝ := (γ₂ * (1 + |airyDerivFirstZero|) + V_max) / S.I_N
  have hγ₁_max_nn : 0 ≤ γ₁_max := div_nonneg (by positivity) S.I_N_pos.le
  let D : OscFloorSeedData :=
    { c_lin := γ₂ * C_b / 2, c_osc := S.c_osc_G / 2, C_r := S.C_r_G
      y₁ := max 25 (max S.y₁_G (|S.lastNode| + γ₁_max + 1)), ϑ_c := S.ϑ_c_G
      c_lin_pos := by positivity, c_osc_pos := half_pos S.c_osc_G_pos
      C_r_nonneg := S.C_r_G_nonneg, y₁_ge := le_max_left _ _ }
  obtain ⟨c₁, hc₁, c₂, hc₂, hgain⟩ := bspline_floor_smoothing_gain (m := 4) (by norm_num) D
  let δ₁ : ℝ := min (1 / 2) (min (r_site / ceBeta1) (1 / (2 * (γ₁_max * S.A_H * ceBeta1 + 1))))
  have hδ₁_pos : 0 < δ₁ := lt_min (by norm_num)
    (lt_min (div_pos hr_site ceBeta1_pos) (div_pos one_pos (by positivity [ceBeta1_pos, S.A_H_nonneg])))
  refine ⟨δ₁, hδ₁_pos, c₁, hc₁, c₂, hc₂, fun v hv δ hδ r_val hr => ?_⟩
  intro γ₁ F u₀
  have hδ_pos : 0 < δ := hδ.1
  have hδ_half : δ ≤ 1 / 2 := hδ.2.trans (min_le_left _ _)
  have hγ₁_pos : 0 < γ₁ := div_pos (add_pos_of_pos_of_nonneg (mul_pos hγ₂_pos (by positivity)) hv.1) S.I_N_pos
  have hγ₁_le : γ₁ ≤ γ₁_max := div_le_div_of_nonneg_right (by linarith [hv.2]) S.I_N_pos.le
  have hF1_int := S.integrable_G.sub (S.integrable_H.const_mul (γ₁ * δ))
  have hF12_int := hF1_int.add ((ceSb_integrable b).const_mul (γ₂ * δ))
  have hF_int : Integrable F := hF12_int.add (ceG1_integrable.const_mul r_val)
  have hF_eval : ∫ u : ℝ, F u = -v * δ + r_val := by
    have h1 : ∫ u : ℝ, F u =
        (∫ u : ℝ, (S.G_N u - γ₁ * δ * S.H_N u) + γ₂ * δ * ceSb b u) +
          ∫ u : ℝ, r_val * ceG1 (airyZero 1) u :=
      integral_add hF12_int (ceG1_integrable.const_mul r_val)
    have h2 : (∫ u : ℝ, (S.G_N u - γ₁ * δ * S.H_N u) + γ₂ * δ * ceSb b u) =
        (∫ u : ℝ, S.G_N u - γ₁ * δ * S.H_N u) + ∫ u : ℝ, γ₂ * δ * ceSb b u :=
      integral_add hF1_int ((ceSb_integrable b).const_mul (γ₂ * δ))
    have h3 : (∫ u : ℝ, S.G_N u - γ₁ * δ * S.H_N u) =
        (∫ u : ℝ, S.G_N u) - ∫ u : ℝ, γ₁ * δ * S.H_N u :=
      integral_sub S.integrable_G (S.integrable_H.const_mul (γ₁ * δ))
    rw [h1, h2, h3, integral_const_mul, integral_const_mul, integral_const_mul,
      S.integral_G, S.integral_H, ceSb_integral, ceG1_integral_eq_one]
    dsimp [γ₁]; field_simp [S.I_N_pos.ne']; ring
  have hu₀_neg : u₀ < 0 := by
    have ha1_neg : airyZero 1 < 0 := airyZero_neg 1
    have hlast : S.lastNode ≤ airyZero 1 := S.last_le_a1
    dsimp [u₀, HBSeedSpec.lastNode] at *; linarith [mul_pos hγ₁_pos hδ_pos]
  have hF_cont : Continuous F :=
    ((S.continuous_G.sub (continuous_const.mul S.continuous_H)).add
      (continuous_const.mul (continuous_ceSb b))).add
      (continuous_const.mul (continuous_ceG1 (airyZero 1)))
  have hGH_tail : ∀ u ≤ u₀, S.G_N u / 2 ≤ S.G_N u - γ₁ * δ * S.H_N u := fun u hu => by
    have h_lt : u < S.lastNode := by
      have : 0 < 2 * γ₁ * δ := by positivity
      dsimp [u₀, HBSeedSpec.lastNode] at hu ⊢; linarith
    have hden_pos : 0 < S.lastNode - u := by linarith
    have hdiv_le : γ₁ * δ / (S.lastNode - u) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hden_pos two_pos]; dsimp [u₀, HBSeedSpec.lastNode] at hu ⊢; linarith
    rw [S.H_eq_div_tail u h_lt]
    change S.G_N u / 2 ≤ S.G_N u - γ₁ * δ * (S.G_N u / (S.lastNode - u))
    rw [show S.G_N u - γ₁ * δ * (S.G_N u / (S.lastNode - u)) =
      S.G_N u * (1 - γ₁ * δ / (S.lastNode - u)) by ring]
    calc S.G_N u / 2 = S.G_N u * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (S.G_nonneg_tail u h_lt.le)
  have hSb_tail : ∀ u ≤ S.lastNode,
      (γ₂ / 2) * δ * ceSb b u ≤ γ₂ * δ * ceSb b u + r_val * ceG1 (airyZero 1) u := fun u hu => by
    have hg1_le := ceG1_le_ceSb hb.le (hu.trans S.last_le_a1)
    have hr_le : -r_val ≤ (γ₂ / 2) * δ := by
      linarith [(abs_le.mp hr).1, mul_le_mul_of_nonneg_right hγ₂_eps hδ_pos.le]
    have hterm : -((γ₂ / 2) * δ * ceSb b u) ≤ r_val * ceG1 (airyZero 1) u := calc
      -((γ₂ / 2) * δ * ceSb b u) ≤ -((γ₂ / 2) * δ * ceG1 (airyZero 1) u) := by gcongr
      _ = (-((γ₂ / 2) * δ)) * ceG1 (airyZero 1) u := by ring
      _ ≤ r_val * ceG1 (airyZero 1) u := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  have hlin : ∀ y ≥ |u₀|, D.c_lin * δ * (1 + y) ^ (-(3 / 2 : ℝ)) ≤ F (-y) := fun y hy => by
    have hy_u0 : -y ≤ u₀ := by rw [abs_of_neg hu₀_neg] at hy; linarith
    have hy_last : -y ≤ S.lastNode := by
      dsimp [u₀, HBSeedSpec.lastNode] at hy_u0 ⊢; linarith [mul_pos hγ₁_pos hδ_pos]
    have hG_nn : 0 ≤ S.G_N (-y) := S.G_nonneg_tail (-y) hy_last
    have hfloor := h_sb_floor (-y) (hy_last.trans S.last_le_a1)
    rw [abs_neg, abs_of_nonneg (le_trans (abs_nonneg _) hy)] at hfloor
    have h1 := hGH_tail (-y) hy_u0; have h2 := hSb_tail (-y) hy_last
    dsimp [D, F]
    calc (γ₂ * C_b / 2) * δ * (1 + y) ^ (-(3 / 2 : ℝ))
        = (γ₂ / 2) * δ * (C_b * (1 + y) ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ (γ₂ / 2) * δ * ceSb b (-y) := mul_le_mul_of_nonneg_left hfloor (by positivity)
      _ ≤ _ := by linarith
  have hosc : ∃ r : ℝ → ℝ, ∀ y ≥ D.y₁,
      |r y| ≤ D.C_r * y ^ (-(1 / 2 : ℝ)) ∧
        D.c_osc * y ^ (-(3 / 2 : ℝ)) * (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + D.ϑ_c) + r y) ^ 2 ≤ F (-y) := by
    obtain ⟨r, hr_tail⟩ := S.G_osc_tail
    refine ⟨r, fun y hy => ?_⟩
    have hy_G : S.y₁_G ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
    have hy_u0_bd : |S.lastNode| + γ₁_max + 1 ≤ y :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hy
    have hy_u0 : |u₀| ≤ y := by
      have hlast_neg : S.lastNode < 0 := lt_of_le_of_lt S.last_le_a1 (airyZero_neg 1)
      have heq_abs : -u₀ = |S.lastNode| + 2 * γ₁ * δ := by
        rw [abs_of_neg hlast_neg]; dsimp [u₀, HBSeedSpec.lastNode]; ring
      rw [abs_of_neg hu₀_neg, heq_abs]
      nlinarith [mul_le_mul_of_nonneg_right hγ₁_le hδ_pos.le]
    have hy_u0_le : -y ≤ u₀ := by rw [abs_of_neg hu₀_neg] at hy_u0; linarith
    have hy_last : -y ≤ S.lastNode := by
      dsimp [u₀, HBSeedSpec.lastNode] at hy_u0_le ⊢; linarith [mul_pos hγ₁_pos hδ_pos]
    have h_sb_nn : 0 ≤ (γ₂ / 2) * δ * ceSb b (-y) :=
      mul_nonneg (by positivity) (ceSb_pos_of_le hb.le (hy_last.trans S.last_le_a1)).le
    obtain ⟨hr_bd, hG_osc⟩ := hr_tail y hy_G
    have h1 := hGH_tail (-y) hy_u0_le; have h2 := hSb_tail (-y) hy_last
    exact ⟨hr_bd, by dsimp [D, F] at *; linarith⟩
  have hsat : SatisfiesH D F δ u₀ := ⟨hu₀_neg, hF_cont.locallyIntegrable, hlin, hosc⟩
  have hpresc : ∀ j : Fin S.m₀, j.val + 1 < S.m₀ → ∀ u, |u - S.nodes j| ≤ ceBeta1 * δ →
      δ / 2 ≤ F u := fun j hj u hu => by
    have h_rad : ceBeta1 * δ ≤ r_site := by
      rw [mul_comm]
      exact (le_div_iff₀ ceBeta1_pos).mp (hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hu_r : |u - S.nodes j| ≤ r_site := hu.trans h_rad
    have hu_rj : |u - S.nodes j| ≤ r_fn_j j :=
      hu_r.trans ((min_le_right _ _).trans (Finset.inf'_le r_fn_j (Finset.mem_univ j)))
    have hG_bd : -(S.A_G * ceBeta1 * δ) ≤ S.G_N u := by
      have h1 := (abs_le.mp ((S.G_lip_near j hj u (hu_r.trans (min_le_left _ _))).trans
        (mul_le_mul_of_nonneg_left hu S.A_G_nonneg))).1
      linarith
    have hH_abs : |S.H_N u| ≤ S.A_H * ceBeta1 * δ :=
      (S.H_lip_near j hj u (hu_r.trans (min_le_left _ _))).trans
        (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hu S.A_H_nonneg)
    have hH_term : -(γ₁_max * S.A_H * ceBeta1 * δ ^ 2) ≤ -(γ₁ * δ * S.H_N u) := by
      have habs : γ₁ * δ * S.H_N u ≤ γ₁_max * S.A_H * ceBeta1 * δ ^ 2 := calc
        γ₁ * δ * S.H_N u ≤ γ₁ * δ * |S.H_N u| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hγ₁_pos.le hδ_pos.le)
        _ ≤ γ₁_max * δ * (S.A_H * ceBeta1 * δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hγ₁_le hδ_pos.le) hH_abs (abs_nonneg _)
            (mul_nonneg hγ₁_max_nn hδ_pos.le)
        _ = γ₁_max * S.A_H * ceBeta1 * δ ^ 2 := by ring
      linarith
    have hH_sq_le : γ₁_max * S.A_H * ceBeta1 * δ ^ 2 ≤ δ / 2 := by
      have h2 := hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
      rw [le_div_iff₀ (by positivity [ceBeta1_pos, S.A_H_nonneg])] at h2
      nlinarith only [mul_le_mul_of_nonneg_left h2 hδ_pos.le, hδ_pos, h2]
    have hs_sb : s ≤ ceSb b u := by
      have hle : s ≤ s_val j := Finset.inf'_le s_val (Finset.mem_univ j)
      have hs1 : s ≤ ceSb b (S.nodes j) / 2 := by
        dsimp [s_val] at hle; simp only [hj, ↓reduceIte] at hle; exact hle
      exact hs1.trans ((Classical.choose_spec (hex_site j)).2 hj u hu_rj)
    have hSb_term : γ₂ * s * δ ≤ γ₂ * δ * ceSb b u := by
      rw [show γ₂ * δ * ceSb b u = γ₂ * ceSb b u * δ by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs_sb hγ₂_pos.le) hδ_pos.le
    have hr_term : -(ε₀ * M_g1 * δ) ≤ r_val * ceG1 (airyZero 1) u := by
      have h1 : -r_val ≤ ε₀ * δ := by linarith [(abs_le.mp hr).1]
      have h2 := mul_le_mul h1 (h_g1_site j u hu_r) (sq_nonneg _) (mul_nonneg hε hδ_pos.le)
      linarith
    have hsite_mul : δ ≤ (γ₂ * s - ceBeta1 * S.A_G - ε₀ * M_g1) * δ := by
      have : 1 ≤ γ₂ * s - ceBeta1 * S.A_G - ε₀ * M_g1 := by linarith
      linarith only [mul_le_mul_of_nonneg_right this hδ_pos.le]
    dsimp [F]; linarith
  exact ⟨hγ₁_pos, ⟨hF_int, hF_eval⟩, fun x hx => hgain F δ u₀ hδ_pos hδ_half hsat x hx, hpresc⟩

end FormalResearch.SignUncertainty
