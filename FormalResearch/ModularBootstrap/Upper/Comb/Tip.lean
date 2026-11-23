module

public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw

/-!
# Reference Blaschke Comb I: Tip and Midpoint Bounds (Lemma A_tip)

Formalizes Lemma $A_{\mathrm{tip}}$ (`rem:analytictip`) of
`CFT/modular_bootstrap/paper/remainder.tex` (lines 105--180):

* `(A-tip.1)`: `rhoU_tip_asymptotic` and `cumulN_tip_asymptotic`:
  $\rho_U(\xi_* + r) = 3 k_{\mathrm{tip}} r^{1/2}(1 + O(r))$ and
  $N(\xi_* + r) = k_{\mathrm{tip}} r^{3/2}(1 + O(r))$ uniformly for $0 \le r \le r_0$.
* `(A-tip.2)`: `logDeriv_rhoU_tip_bounds`:
  $\frac{1}{2r} \le (\log \rho_U)'(\xi_* + r) \le \frac{1}{2r} + \frac{\pi}{4\sqrt{2}}$ for all $r > 0$.
* `(A-tip.3)` & tip-neighbourhood quantile bounds: `quantile_tip_bounds` (exact $(a - 1/4)$-powers
  for all $a > 1/4$, and $a$-powers for $a \ge 1$) and `siteRadius_asymptotic`.
* Far-left midpoint remainder $e_L$ scaling consequences: `lambdaComb_mul_rpow_tendsto_zero`,
  `siteRadius_three_eventually_ge`, and `eL_tip_consequences`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: `(A-tip.1)` — Uniform tip asymptotics of `ρ_U` and `N` -/

/-- **(A-tip.1), density**: for all $r \ge 0$,
$3 k_{\mathrm{tip}} r^{1/2} \le \rho_U(\xi_* + r) \le 3 k_{\mathrm{tip}} r^{1/2} (1 + \frac{\pi}{4\sqrt{2}} r)$.
In particular, $\rho_U(\xi_* + r) = 3 k_{\mathrm{tip}} r^{1/2}(1 + O(r))$ uniformly on $[0, r_0]$. -/
theorem rhoU_tip_asymptotic :
    ∀ r : ℝ, 0 ≤ r →
      3 * kTip * √r ≤ rhoU (xiStar + r) ∧
        rhoU (xiStar + r) ≤ 3 * kTip * √r * (1 + (π / (4 * √2)) * r) := by
  intro r hr
  refine ⟨(le_max_left _ _).trans (rhoU_ge_max hr), ?_⟩
  have hpi := Real.pi_pos
  have hsq := (rhoU_sq_bounds hr).2
  have h16 : (16 / 9 : ℝ) / (9 * kTip ^ 2) = π / (2 * √2) := by
    rw [nine_mul_kTip_sq]
    have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hpi.ne']
    nlinarith [hsq2]
  have hsq' : rhoU (xiStar + r) ^ 2 ≤ 9 * kTip ^ 2 * r * (1 + (π / (2 * √2)) * r) := by
    have hk9 : 9 * kTip ^ 2 ≠ 0 := by have := kTip_pos; positivity
    calc rhoU (xiStar + r) ^ 2 ≤ 9 * kTip ^ 2 * r + (16 / 9) * r ^ 2 := hsq
      _ = 9 * kTip ^ 2 * r * (1 + ((16 / 9) / (9 * kTip ^ 2)) * r) := by
          field_simp [kTip_pos.ne']
      _ = 9 * kTip ^ 2 * r * (1 + (π / (2 * √2)) * r) := by rw [h16]
  have h_lin : 9 * kTip ^ 2 * r * (1 + (π / (2 * √2)) * r) ≤
      (3 * kTip * √r * (1 + (π / (4 * √2)) * r)) ^ 2 := by
    have h1 : 1 + (π / (2 * √2)) * r ≤ (1 + (π / (4 * √2)) * r) ^ 2 := by
      have hexp : (1 + (π / (4 * √2)) * r) ^ 2 =
          1 + (π / (2 * √2)) * r + ((π / (4 * √2)) * r) ^ 2 := by ring
      have hsqn : 0 ≤ ((π / (4 * √2)) * r) ^ 2 := sq_nonneg _
      linarith
    have hsq_r : √r ^ 2 = r := Real.sq_sqrt hr
    have hk_pos : 0 < kTip := kTip_pos
    calc 9 * kTip ^ 2 * r * (1 + (π / (2 * √2)) * r)
        ≤ 9 * kTip ^ 2 * √r ^ 2 * (1 + (π / (4 * √2)) * r) ^ 2 := by
            rw [hsq_r]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (3 * kTip * √r * (1 + (π / (4 * √2)) * r)) ^ 2 := by ring
  have hrhs_nn : 0 ≤ 3 * kTip * √r * (1 + (π / (4 * √2)) * r) := by
    have := kTip_pos; positivity
  nlinarith [rhoU_nonneg (xiStar + r), hsq'.trans h_lin]

/-- **(A-tip.1), cumulative count**: for all $r \ge 0$,
$k_{\mathrm{tip}} r^{3/2} \le N(\xi_* + r) \le k_{\mathrm{tip}} r^{3/2}(1 + C_1 r)$ ($C_1 = 3\pi/(20\sqrt{2})$),
giving $N(\xi_* + r) = k_{\mathrm{tip}} r^{3/2}(1 + O(r))$ uniformly on $[0, r_0]$. -/
theorem cumulN_tip_asymptotic (r₀ : ℝ) :
    ∃ C > 0, ∀ r ∈ Icc (0 : ℝ) r₀,
      |cumulN (xiStar + r) - kTip * r ^ (3 / 2 : ℝ)| ≤ C * kTip * r ^ (3 / 2 : ℝ) * r := by
  refine ⟨c1K0, c1K0_pos, fun r hr => ?_⟩
  have hN := cumulN_bounds hr.1
  rw [abs_of_nonneg (sub_nonneg.mpr hN.1)]
  linarith [hN.2]

/-! ### Section 2: `(A-tip.2)` — Sharp log-derivative sandwich for `ρ_U` -/

/-- **(A-tip.2)**: for all $r > 0$,
$\frac{1}{2r} \le (\log \rho_U)'(\xi_* + r) \le \frac{1}{2r} + \frac{\pi}{4\sqrt{2}}$. -/
theorem logDeriv_rhoU_tip_bounds {r : ℝ} (hr : 0 < r) :
    1 / (2 * r) ≤ rhoUDeriv (xiStar + r) / rhoU (xiStar + r) ∧
      rhoUDeriv (xiStar + r) / rhoU (xiStar + r) ≤ 1 / (2 * r) + π / (4 * √2) := by
  have hpi := Real.pi_pos
  have hrho_pos : 0 < rhoU (xiStar + r) := rhoU_pos (by linarith)
  have hΦ_pos : 0 < rhoUSq r := by unfold rhoUSq; exact sq_pos_of_pos hrho_pos
  have h_id : rhoUDeriv (xiStar + r) / rhoU (xiStar + r) - 1 / (2 * r) =
      (r * rhoUSqDeriv r - rhoUSq r) / (2 * r * rhoUSq r) := by
    have hd1 := hasDerivAt_rhoUSq hr
    have h_deriv_eq : rhoUSqDeriv r = 2 * rhoU (xiStar + r) * rhoUDeriv (xiStar + r) := by
      have h_rho : HasDerivAt (fun t => rhoU (xiStar + t)) (rhoUDeriv (xiStar + r)) r := by
        have h1 := (hasDerivAt_rhoU (by linarith : xiStar < xiStar + r)).comp r
          ((hasDerivAt_id r).const_add xiStar)
        exact (h1.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv (mul_one _)
      have hd2 : HasDerivAt rhoUSq (2 * rhoU (xiStar + r) * rhoUDeriv (xiStar + r)) r :=
        ((h_rho.pow 2).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv
          (by simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat])
      exact hd1.unique hd2
    unfold rhoUSq
    rw [h_deriv_eq]
    field_simp [hr.ne', hrho_pos.ne']
  have h_diff_fn : ∀ δ : ℝ, 0 < δ → δ ≤ r →
      0 ≤ (r * rhoUSqDeriv r - rhoUSq r) - (δ * rhoUSqDeriv δ - rhoUSq δ) ∧
        (r * rhoUSqDeriv r - rhoUSq r) - (δ * rhoUSqDeriv δ - rhoUSq δ) ≤
          (16 / 9) * (r ^ 2 - δ ^ 2) := by
    intro δ hδ hδr
    let g1 : ℝ → ℝ := fun s => s * rhoUSqDeriv s - rhoUSq s
    let g2 : ℝ → ℝ := fun s => (16 / 9 : ℝ) * s ^ 2 - g1 s
    have hcont : ContinuousOn g1 (Icc δ r) := fun s hs => by
      have hs_pos := lt_of_lt_of_le hδ hs.1
      exact ((continuousAt_id.mul (hasDerivAt_rhoUSqDeriv hs_pos).continuousAt).sub
        (hasDerivAt_rhoUSq hs_pos).continuousAt).continuousWithinAt
    have hderiv_s : ∀ s : ℝ, 0 < s → HasDerivAt g1 (s * rhoUSqSecond s) s := by
      intro s hs
      have hd := ((hasDerivAt_id s).mul (hasDerivAt_rhoUSqDeriv hs)).sub (hasDerivAt_rhoUSq hs)
      refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      simp only [id_eq, one_mul]; ring
    have hm1 := monotoneOn_of_deriv_nonneg (convex_Icc δ r) hcont
      (fun s hs => by
        rw [interior_Icc] at hs
        exact (hderiv_s s (lt_of_lt_of_le hδ hs.1.le)).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        have hs_pos := lt_of_lt_of_le hδ hs.1.le
        rw [(hderiv_s s hs_pos).deriv]
        exact mul_nonneg hs_pos.le (rhoUSqSecond_bounds hs_pos).1)
    have hcont2 : ContinuousOn g2 (Icc δ r) :=
      (continuousOn_const.mul (continuousOn_id.pow 2)).sub hcont
    have hm2 := monotoneOn_of_deriv_nonneg (convex_Icc δ r) hcont2
      (fun s hs => by
        rw [interior_Icc] at hs
        have hs_pos := lt_of_lt_of_le hδ hs.1.le
        have h1 : HasDerivAt (fun x : ℝ => (16 / 9 : ℝ) * x ^ 2) (32 / 9 * s) s :=
          ((hasDerivAt_pow 2 s).const_mul (16 / 9 : ℝ)).congr_deriv
            (by simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring)
        exact (h1.sub (hderiv_s s hs_pos)).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        have hs_pos := lt_of_lt_of_le hδ hs.1.le
        have h1 : HasDerivAt (fun x : ℝ => (16 / 9 : ℝ) * x ^ 2) (32 / 9 * s) s :=
          ((hasDerivAt_pow 2 s).const_mul (16 / 9 : ℝ)).congr_deriv
            (by simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring)
        have hd : HasDerivAt g2 (32 / 9 * s - s * rhoUSqSecond s) s :=
          (h1.sub (hderiv_s s hs_pos)).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
        rw [hd.deriv]
        have h2 := (rhoUSqSecond_bounds hs_pos).2
        nlinarith)
    have h1 := hm1 (left_mem_Icc.mpr hδr) (right_mem_Icc.mpr hδr) hδr
    have h2 := hm2 (left_mem_Icc.mpr hδr) (right_mem_Icc.mpr hδr) hδr
    dsimp [g1, g2] at h1 h2
    exact ⟨by linarith, by linarith⟩
  have h_tend0 : Tendsto (fun δ : ℝ => δ * rhoUSqDeriv δ - rhoUSq δ) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ * rhoUSqDeriv δ) (𝓝[>] 0) (𝓝 0) := by
      simpa using (continuous_id.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul tendsto_rhoUSqDeriv_zero
    have h2 : Tendsto rhoUSq (𝓝[>] 0) (𝓝 0) := by
      unfold rhoUSq
      have hc : ContinuousWithinAt (fun t => rhoU (xiStar + t) ^ 2) (Ici 0) 0 :=
        ((continuousOn_rhoU.comp (continuous_const.add continuous_id).continuousOn
          (fun t ht => by change xiStar ≤ xiStar + t; exact le_add_of_nonneg_right ht)).pow 2).continuousWithinAt
          (le_rfl : (0 : ℝ) ∈ Ici 0)
      have h0 : rhoU xiStar ^ 2 = 0 := by rw [rhoU_xiStar]; norm_num
      simpa [add_zero, h0] using hc.tendsto.mono_left (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
    simpa using h1.sub h2
  have h_lb_num : 0 ≤ r * rhoUSqDeriv r - rhoUSq r := by
    have ht : Tendsto (fun δ : ℝ => (r * rhoUSqDeriv r - rhoUSq r) - (δ * rhoUSqDeriv δ - rhoUSq δ))
        (𝓝[>] 0) (𝓝 (r * rhoUSqDeriv r - rhoUSq r)) := by
      simpa using tendsto_const_nhds.sub h_tend0
    refine le_of_tendsto_of_tendsto tendsto_const_nhds ht ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
    exact (h_diff_fn δ hδ.1 hδ.2.le).1
  have h_ub_num : r * rhoUSqDeriv r - rhoUSq r ≤ (16 / 9) * r ^ 2 := by
    have ht1 : Tendsto (fun δ : ℝ => (r * rhoUSqDeriv r - rhoUSq r) - (δ * rhoUSqDeriv δ - rhoUSq δ))
        (𝓝[>] 0) (𝓝 (r * rhoUSqDeriv r - rhoUSq r)) := by
      simpa using tendsto_const_nhds.sub h_tend0
    have ht2 : Tendsto (fun δ : ℝ => (16 / 9 : ℝ) * (r ^ 2 - δ ^ 2)) (𝓝[>] 0) (𝓝 ((16 / 9) * r ^ 2)) := by
      have hc : Continuous (fun δ : ℝ => (16 / 9 : ℝ) * (r ^ 2 - δ ^ 2)) := by fun_prop
      simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    refine le_of_tendsto_of_tendsto ht1 ht2 ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
    exact (h_diff_fn δ hδ.1 hδ.2.le).2
  have h_diff_ge : 0 ≤ rhoUDeriv (xiStar + r) / rhoU (xiStar + r) - 1 / (2 * r) := by
    rw [h_id]; exact div_nonneg h_lb_num (by positivity)
  have h_diff_le : rhoUDeriv (xiStar + r) / rhoU (xiStar + r) - 1 / (2 * r) ≤ π / (4 * √2) := by
    rw [h_id]
    have hΦ_lb : 9 * kTip ^ 2 * r ≤ rhoUSq r := (rhoU_sq_bounds hr.le).1
    have h81 : (16 / 9 : ℝ) / (2 * (9 * kTip ^ 2)) = π / (4 * √2) := by
      rw [nine_mul_kTip_sq]
      have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [hpi.ne']
      nlinarith [hsq2]
    calc (r * rhoUSqDeriv r - rhoUSq r) / (2 * r * rhoUSq r)
        ≤ ((16 / 9) * r ^ 2) / (2 * r * (9 * kTip ^ 2 * r)) := by
          gcongr; have := kTip_pos; positivity
      _ = (16 / 9 : ℝ) / (2 * (9 * kTip ^ 2)) := by
          have hk9 : 9 * kTip ^ 2 ≠ 0 := by have := kTip_pos; positivity
          field_simp [hr.ne', hk9]
      _ = π / (4 * √2) := h81
  exact ⟨by linarith, by linarith⟩

/-! ### Section 3: `(A-tip.3)` — Quantile bounds on any fixed tip neighbourhood -/

/-- **(A-tip.3), tip-neighbourhood quantile bounds**:
For every fixed $r_0 > 0$, there exist constants $0 < c_1 \le C_1$, $0 < c_2 \le C_2$, $C_3 > 0$
(depending only on $r_0$) such that for all $c' > 0$ and $a > 1/4$ with $r_a = \chi_a - \xi_* \le r_0$:
1. $c_1 \lambda (a - 1/4)^{2/3} \le r_a \le C_1 \lambda (a - 1/4)^{2/3}$,
2. $c_2 \lambda (a - 1/4)^{-1/3} \le \chi'_a \le C_2 \lambda (a - 1/4)^{-1/3}$,
3. $|\chi''_a| \le C_3 \lambda (a - 1/4)^{-4/3}$
(and in particular for $a \ge 1$, the same holds with $(a - 1/4)$ replaced by $a$). -/
theorem quantile_tip_bounds {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ c₁ C₁ c₂ C₂ C₃ : ℝ,
      0 < c₁ ∧ 0 < C₁ ∧ 0 < c₂ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ {c' a : ℝ}, 0 < c' → 1 / 4 < a → siteRadius c' a ≤ r₀ →
        (c₁ * lambdaComb c' * phiQuantile a ≤ siteRadius c' a ∧
          siteRadius c' a ≤ C₁ * lambdaComb c' * phiQuantile a) ∧
        (c₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) ≤ chiDeriv c' a ∧
          chiDeriv c' a ≤ C₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ))) ∧
        |chiSecond c' a| ≤ C₃ * lambdaComb c' * (a - 1 / 4) ^ (-(4 / 3 : ℝ)) := by
  have hk_pos : 0 < kTip := kTip_pos
  have hc1_pos : 0 < 1 + c1K0 * r₀ := by have := c1K0_pos; positivity
  set c₁ := (1 + c1K0 * r₀) ^ (-(2 / 3 : ℝ))
  set C₁ := (1 : ℝ)
  set M_rho := 1 + (π / (4 * √2)) * r₀
  have hM_pos : 0 < M_rho := by positivity
  set c₂ := (2 / 3 : ℝ) / M_rho
  set C₂ := (2 / 3 : ℝ) * (1 + c1K0 * r₀) ^ (1 / 3 : ℝ)
  set C₃ := C₂ ^ 2 / c₁
  refine ⟨c₁, C₁, c₂, C₂, C₃, by positivity, by positivity, by positivity, by positivity,
    by positivity, fun {c' a} hc' ha hr_le => ?_⟩
  have hr_pos : 0 < siteRadius c' a := sub_pos.mpr (xiStar_lt_chiQuantile hc' ha)
  have ha_pos : 0 < a - 1 / 4 := sub_pos.mpr ha
  have hl_pos : 0 < lambdaComb c' := by unfold lambdaComb; positivity
  have h_eq : c' * cumulN (xiStar + siteRadius c' a) = a - 1 / 4 := by
    have hspec := (chiQuantile_spec hc' ha.le).2
    unfold siteRadius; simpa [add_sub_cancel] using hspec
  have h_rpow_id : c' * kTip * (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) = a - 1 / 4 := by
    rw [Real.mul_rpow hl_pos.le (by unfold phiQuantile; positivity)]
    have hl32 : lambdaComb c' ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
      unfold lambdaComb
      rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
        Real.rpow_neg_one]
    have hp32 : phiQuantile a ^ (3 / 2 : ℝ) = a - 1 / 4 := by
      unfold phiQuantile
      rw [← Real.rpow_mul ha_pos.le, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one]
    rw [hl32, hp32]; field_simp [hc'.ne', hk_pos.ne']
  have hr_ub : siteRadius c' a ≤ C₁ * lambdaComb c' * phiQuantile a := by
    simpa [C₁] using (siteRadius_bounds hc' ha.le).2
  have hN_ub : (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) ≤
      siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * r₀) := by
    have hN := (cumulN_bounds hr_pos.le).2
    have h1 : c' * kTip * (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) ≤
        c' * kTip * (siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * r₀)) := by
      rw [h_rpow_id, ← h_eq]
      have h2 : cumulN (xiStar + siteRadius c' a) ≤
          kTip * siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * r₀) :=
        hN.trans (by gcongr; exact c1K0_pos.le)
      linarith [mul_le_mul_of_nonneg_left h2 hc'.le]
    exact le_of_mul_le_mul_left h1 (mul_pos hc' hk_pos)
  have hr_lb : c₁ * lambdaComb c' * phiQuantile a ≤ siteRadius c' a := by
    have h_div : (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) * (1 + c1K0 * r₀)⁻¹ ≤
        siteRadius c' a ^ (3 / 2 : ℝ) := by
      rwa [mul_inv_le_iff₀ hc1_pos]
    have hp_nn : 0 ≤ phiQuantile a := by unfold phiQuantile; positivity
    have hr23 := Real.rpow_le_rpow
      (mul_nonneg (Real.rpow_nonneg (mul_nonneg hl_pos.le hp_nn) _) (inv_nonneg.mpr hc1_pos.le))
      h_div (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hl_pos.le hp_nn) _) (inv_nonneg.mpr hc1_pos.le),
      ← Real.rpow_mul (mul_nonneg hl_pos.le hp_nn),
      ← Real.rpow_mul hr_pos.le, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one,
      Real.rpow_one, ← Real.rpow_neg_one, ← Real.rpow_mul hc1_pos.le,
      show (-1 : ℝ) * (2 / 3) = -(2 / 3) by norm_num] at hr23
    exact hr23.trans_eq' (by dsimp [c₁]; ring)
  -- Derivative bounds
  have h_c_lam : (c' * kTip)⁻¹ = lambdaComb c' ^ (3 / 2 : ℝ) := by
    unfold lambdaComb
    rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
      Real.rpow_neg_one, mul_comm]
  have h_l_split : lambdaComb c' ^ (3 / 2 : ℝ) / lambdaComb c' ^ (1 / 2 : ℝ) = lambdaComb c' := by
    rw [← Real.rpow_sub hl_pos, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, Real.rpow_one]
  have hχ_eq : chiQuantile c' a = xiStar + siteRadius c' a := by unfold siteRadius; ring
  have hc1_pos' : 0 < c₁ := by dsimp [c₁]; positivity
  have hcd_ub : chiDeriv c' a ≤ C₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
    have h_rho_lb : 3 * kTip * siteRadius c' a ^ (1 / 2 : ℝ) ≤ rhoU (chiQuantile c' a) := by
      rw [hχ_eq, ← Real.sqrt_eq_rpow]
      exact (le_max_left _ _).trans (rhoU_ge_max hr_pos.le)
    have hp_nn : 0 ≤ phiQuantile a := by unfold phiQuantile; positivity
    have hr_sqrt_lb : (c₁ * lambdaComb c' * phiQuantile a) ^ (1 / 2 : ℝ) ≤ siteRadius c' a ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg (mul_nonneg hc1_pos'.le hl_pos.le) hp_nn) hr_lb (by norm_num)
    have hr_sqrt_eq : (c₁ * lambdaComb c' * phiQuantile a) ^ (1 / 2 : ℝ) =
        (1 + c1K0 * r₀) ^ (-(1 / 3 : ℝ)) * lambdaComb c' ^ (1 / 2 : ℝ) * (a - 1 / 4) ^ (1 / 3 : ℝ) := by
      rw [mul_assoc, Real.mul_rpow hc1_pos'.le (mul_nonneg hl_pos.le hp_nn),
        Real.mul_rpow hl_pos.le hp_nn]
      dsimp [c₁]
      rw [← Real.rpow_mul hc1_pos.le, show -(2 / 3 : ℝ) * (1 / 2) = -(1 / 3) by norm_num]
      unfold phiQuantile
      rw [← Real.rpow_mul ha_pos.le, show (2 / 3 : ℝ) * (1 / 2) = 1 / 3 by norm_num, mul_assoc]
    rw [hr_sqrt_eq] at hr_sqrt_lb
    have h1_neg : ((1 + c1K0 * r₀) ^ (-(1 / 3 : ℝ)))⁻¹ = (1 + c1K0 * r₀) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_neg hc1_pos.le, neg_neg]
    have ha_neg : ((a - 1 / 4) ^ (1 / 3 : ℝ))⁻¹ = (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_neg ha_pos.le]
    have hden_pos : 0 < c' * (3 * kTip * ((1 + c1K0 * r₀) ^ (-(1 / 3 : ℝ)) *
        lambdaComb c' ^ (1 / 2 : ℝ) * (a - 1 / 4) ^ (1 / 3 : ℝ))) := by positivity
    calc chiDeriv c' a = 2 / (c' * rhoU (chiQuantile c' a)) := rfl
      _ ≤ 2 / (c' * (3 * kTip * siteRadius c' a ^ (1 / 2 : ℝ))) := by gcongr
      _ ≤ 2 / (c' * (3 * kTip * ((1 + c1K0 * r₀) ^ (-(1 / 3 : ℝ)) *
            lambdaComb c' ^ (1 / 2 : ℝ) * (a - 1 / 4) ^ (1 / 3 : ℝ)))) := by gcongr
      _ = (2 / 3) * (c' * kTip)⁻¹ * ((1 + c1K0 * r₀) ^ (-(1 / 3 : ℝ)))⁻¹ *
            (lambdaComb c' ^ (1 / 2 : ℝ))⁻¹ * ((a - 1 / 4) ^ (1 / 3 : ℝ))⁻¹ := by ring
      _ = (2 / 3) * (1 + c1K0 * r₀) ^ (1 / 3 : ℝ) *
            (lambdaComb c' ^ (3 / 2 : ℝ) / lambdaComb c' ^ (1 / 2 : ℝ)) *
            (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by rw [h_c_lam, h1_neg, ha_neg]; ring
      _ = C₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by rw [h_l_split]
  have hcd_lb : c₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) ≤ chiDeriv c' a := by
    have h_rho_ub : rhoU (chiQuantile c' a) ≤ 3 * kTip * siteRadius c' a ^ (1 / 2 : ℝ) * M_rho := by
      rw [hχ_eq, ← Real.sqrt_eq_rpow]
      have h1 := (rhoU_tip_asymptotic (siteRadius c' a) hr_pos.le).2
      have hle_M : 1 + (π / (4 * √2)) * siteRadius c' a ≤ M_rho := by
        dsimp [M_rho]; have hpi := Real.pi_pos; gcongr
      calc rhoU (xiStar + siteRadius c' a)
          ≤ 3 * kTip * √(siteRadius c' a) * (1 + (π / (4 * √2)) * siteRadius c' a) := h1
        _ ≤ 3 * kTip * √(siteRadius c' a) * M_rho := by gcongr
    have hr_sqrt_ub : siteRadius c' a ^ (1 / 2 : ℝ) ≤ (lambdaComb c' * phiQuantile a) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hr_pos.le (by simpa [C₁] using hr_ub) (by norm_num)
    have hr_sqrt_eq : (lambdaComb c' * phiQuantile a) ^ (1 / 2 : ℝ) =
        lambdaComb c' ^ (1 / 2 : ℝ) * (a - 1 / 4) ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow hl_pos.le (by unfold phiQuantile; positivity)]
      unfold phiQuantile
      rw [← Real.rpow_mul ha_pos.le, show (2 / 3 : ℝ) * (1 / 2) = 1 / 3 by norm_num]
    rw [hr_sqrt_eq] at hr_sqrt_ub
    have ha_neg : ((a - 1 / 4) ^ (1 / 3 : ℝ))⁻¹ = (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_neg ha_pos.le]
    have hrho_pos : 0 < rhoU (chiQuantile c' a) := rhoU_pos (xiStar_lt_chiQuantile hc' ha)
    calc c₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ))
        = (2 / 3) / M_rho * (lambdaComb c' ^ (3 / 2 : ℝ) / lambdaComb c' ^ (1 / 2 : ℝ)) *
            ((a - 1 / 4) ^ (1 / 3 : ℝ))⁻¹ := by rw [h_l_split, ha_neg]
      _ = 2 / (c' * (3 * kTip * (lambdaComb c' ^ (1 / 2 : ℝ) * (a - 1 / 4) ^ (1 / 3 : ℝ)) * M_rho)) := by
            rw [← h_c_lam]; field_simp [hc'.ne', hk_pos.ne', hM_pos.ne']
      _ ≤ 2 / (c' * (3 * kTip * siteRadius c' a ^ (1 / 2 : ℝ) * M_rho)) := by gcongr
      _ ≤ 2 / (c' * rhoU (chiQuantile c' a)) := by gcongr
      _ = chiDeriv c' a := rfl
  -- Second derivative bound
  have h_sec_ub : |chiSecond c' a| ≤ C₃ * lambdaComb c' * (a - 1 / 4) ^ (-(4 / 3 : ℝ)) := by
    have hcd_pos : 0 < chiDeriv c' a := by
      unfold chiDeriv; exact div_pos two_pos (mul_pos hc' (rhoU_pos (xiStar_lt_chiQuantile hc' ha)))
    have hld := (logDeriv_rhoU_bounds hr_pos).2
    have hld_pos := (logDeriv_rhoU_bounds hr_pos).1
    rw [← hχ_eq] at hld hld_pos
    have h_abs : |chiSecond c' a| = chiDeriv c' a ^ 2 * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) := by
      unfold chiSecond
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) hld_pos.le)]
    rw [h_abs]
    have hr_pow : phiQuantile a = (a - 1 / 4) ^ (2 / 3 : ℝ) := rfl
    have h_pow_comb : (a - 1 / 4) ^ (-(1 / 3 : ℝ)) * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) /
        (a - 1 / 4) ^ (2 / 3 : ℝ) = (a - 1 / 4) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add ha_pos, ← Real.rpow_sub ha_pos]; norm_num
    calc chiDeriv c' a ^ 2 * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a))
        ≤ (C₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ))) ^ 2 * (1 / siteRadius c' a) := by
          gcongr
      _ ≤ (C₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ))) ^ 2 *
            (1 / (c₁ * lambdaComb c' * phiQuantile a)) := by
          have hp_pos : 0 < phiQuantile a := by unfold phiQuantile; positivity
          gcongr
      _ = (C₂ ^ 2 / c₁) * lambdaComb c' *
            ((a - 1 / 4) ^ (-(1 / 3 : ℝ)) * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) / (a - 1 / 4) ^ (2 / 3 : ℝ)) := by
            rw [hr_pow]; field_simp [hl_pos.ne', hc1_pos'.ne']
      _ = C₃ * lambdaComb c' * (a - 1 / 4) ^ (-(4 / 3 : ℝ)) := by rw [h_pow_comb]
  exact ⟨⟨hr_lb, hr_ub⟩, ⟨hcd_lb, hcd_ub⟩, h_sec_ub⟩

/-- **(A-tip.3), small-argument expansion**:
when $\lambda \Phi_a \le 1$, $|r_a - \lambda \Phi_a| \le \frac{2 C_1}{3} (\lambda \Phi_a)^2$. -/
theorem siteRadius_asymptotic {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    |siteRadius c' a - lambdaComb c' * phiQuantile a| ≤
      (2 * c1K0 / 3) * (lambdaComb c' * phiQuantile a) ^ 2 := by
  have h := siteRadius_bounds hc' ha
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Section 4: Consequences for the far-left midpoint remainder `e_L` -/

/-- $\lambda c'^{3/5} = k_{\mathrm{tip}}^{-2/3} c'^{-1/15} \to 0$ as $c' \to \infty$. -/
theorem lambdaComb_mul_rpow_tendsto_zero :
    Tendsto (fun c' : ℝ => lambdaComb c' * c' ^ (3 / 5 : ℝ)) atTop (𝓝 0) := by
  have hk_pos : 0 < kTip := kTip_pos
  have heq : (fun c' : ℝ => lambdaComb c' * c' ^ (3 / 5 : ℝ)) =ᶠ[atTop]
      fun c' => kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(1 / 15 : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with c' hc'
    unfold lambdaComb
    rw [Real.mul_rpow hk_pos.le hc'.le, mul_assoc, ← Real.rpow_add hc']
    norm_num
  refine Tendsto.congr' heq.symm ?_
  simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 15)).const_mul
    (kTip ^ (-(2 / 3 : ℝ))))

/-- On cells $n \ge 3$ ($x \ge \chi_3$), $x - \xi_* \ge r_3 \ge c_0 \lambda$ for large $c'$. -/
theorem siteRadius_three_eventually_ge :
    ∃ c₀ > 0, ∀ᶠ c' in atTop, c₀ * lambdaComb c' ≤ siteRadius c' 3 := by
  set c₀ := (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile 3
  refine ⟨c₀, by have := c1K0_pos; dsimp [c₀]; unfold phiQuantile; positivity, ?_⟩
  have h_ev : ∀ᶠ c' in atTop, lambdaComb c' * phiQuantile 3 ≤ 1 := by
    have ht := tendsto_lambdaComb_atTop.mul_const (phiQuantile 3)
    simp only [zero_mul] at ht
    exact ht.eventually_le_const zero_lt_one
  filter_upwards [eventually_gt_atTop 0, h_ev] with c' hc' hr3_bd
  have hr3 : siteRadius c' 3 ≤ 1 := (siteRadius_bounds hc' (by norm_num)).2.trans hr3_bd
  have hlb := (siteRadius_le_one_bounds hc' (by norm_num) hr3).1
  refine hlb.trans_eq' ?_
  dsimp [c₀]; ring

/-- Consequences for any $e_L$ satisfying the Lemma K4 bound $0 \le e_L(c', x) \le C_L \lambda / (x - \xi_*)$:
$e_L \to 0$ uniformly on $x - \xi_* \ge c'^{-3/5}$, and $e_L$ is uniformly bounded on $x \ge \chi_3$
for large $c'$. -/
theorem eL_tip_consequences (eL : ℝ → ℝ → ℝ) (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hK4 : ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar < x → 0 ≤ eL c' x ∧ eL c' x ≤ C_L * lambdaComb c' / (x - xiStar)) :
    (∀ ε > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, c' ^ (-(3 / 5 : ℝ)) ≤ x - xiStar → |eL c' x| ≤ ε) ∧
    (∃ M > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, chiQuantile c' 3 ≤ x → |eL c' x| ≤ M) := by
  constructor
  · intro ε hε
    have ht := (lambdaComb_mul_rpow_tendsto_zero.const_mul C_L).eventually_le_const (by linarith)
    filter_upwards [eventually_gt_atTop 0, hK4, ht] with c' hc' hbd h_eps x hx
    have hx_gt : xiStar < x := by
      have : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
      linarith
    obtain ⟨h0, h1⟩ := hbd x hx_gt
    rw [abs_of_nonneg h0]
    have h_inv : (x - xiStar)⁻¹ ≤ c' ^ (3 / 5 : ℝ) := by
      rw [Real.rpow_neg hc'.le (3 / 5 : ℝ)] at hx
      have hpos1 : 0 < (c' ^ (3 / 5 : ℝ))⁻¹ := by positivity
      simpa using inv_anti₀ hpos1 hx
    have hl_nn : 0 ≤ lambdaComb c' := by have := kTip_pos; unfold lambdaComb; positivity
    calc eL c' x ≤ C_L * lambdaComb c' / (x - xiStar) := h1
      _ = C_L * lambdaComb c' * (x - xiStar)⁻¹ := by ring
      _ ≤ C_L * lambdaComb c' * c' ^ (3 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left h_inv (mul_nonneg hC_L hl_nn)
      _ = C_L * (lambdaComb c' * c' ^ (3 / 5 : ℝ)) := by ring
      _ ≤ ε := h_eps
  · obtain ⟨c₀, hc₀, h3⟩ := siteRadius_three_eventually_ge
    refine ⟨C_L / c₀ + 1, by positivity, ?_⟩
    filter_upwards [eventually_gt_atTop 0, hK4, h3] with c' hc' hbd hr3 x hx
    have hx_gt : xiStar < x := lt_of_lt_of_le (xiStar_lt_chiQuantile hc' (by norm_num)) hx
    obtain ⟨h0, h1⟩ := hbd x hx_gt
    rw [abs_of_nonneg h0]
    have hl_pos : 0 < lambdaComb c' := by have := kTip_pos; unfold lambdaComb; positivity
    have hx_ge : c₀ * lambdaComb c' ≤ x - xiStar := by
      have : siteRadius c' 3 ≤ x - xiStar := by unfold siteRadius; linarith
      exact hr3.trans this
    have hpos : 0 < c₀ * lambdaComb c' := by positivity
    calc eL c' x ≤ C_L * lambdaComb c' / (x - xiStar) := h1
      _ ≤ C_L * lambdaComb c' / (c₀ * lambdaComb c') :=
          div_le_div_of_nonneg_left (mul_nonneg hC_L hl_pos.le) hpos hx_ge
      _ = C_L / c₀ := by field_simp [hc₀.ne', hl_pos.ne']
      _ ≤ C_L / c₀ + 1 := by linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.rhoU_tip_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.rhoU_tip_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.cumulN_tip_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.cumulN_tip_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.logDeriv_rhoU_tip_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.logDeriv_rhoU_tip_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.quantile_tip_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.quantile_tip_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.siteRadius_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.siteRadius_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.eL_tip_consequences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.eL_tip_consequences

end FormalResearch.ModularBootstrap.Upper.Comb