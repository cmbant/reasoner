module

public import FormalResearch.SignUncertainty.ShellLaplaceBase

/-!
# Conditional Mellin Origin Floor and Subsequential Core of Theorem H.14 (`ce_shells.tex`)

Source: `CFT/sign_uncertainty/paper/ce_shells.tex` (PR 240, commit `58dd780c8`).

* `ShellReductionPackage`, `shell_reduction_pointwise`, `shell_reduction_lower`: Mellin
  three-lines / origin-floor inequality (`eq:ce-three-lines`, `eq:ce-origin-floor`,
  `liminf h_c(0)/M[f_c] ≥ sup_{y>0} ℒ_y(2 Q_∞)`) inside Theorem `H.14`.
* `ShellGapPackage`, `theorem_H14_subseq_bounds`, `theorem_H14_strict_gap`: conditional
  subsequential core of Theorem `H.14` (`thm:ce-shell-gap`).

**Scope boundary:** `ShellReductionPackage` and `ShellGapPackage` package the boundedness ratios
(`h0_ratio_bdd`, `pq_ratio_bdd`), extracted subsequence `φ`, limits `P_inf`/`Q_inf`, pointwise
convergence, right-tail envelope, Mellin–Laplace limits, convergent threshold `u_thresh_tendsto`,
and zero-offset shell signs (`t ∈ D.S \ {D.tm}`) as input fields. Not formalized here:
`Theorem HB--CE.L` (`thm:ce-shell-reduction`), the derivation of boundedness and locally uniform
convergence from Euclidean radial Cohn–Elkies pairs, `o(c^{1/3})` shell offsets, and the full
infimal `R_d^{CE}` quantification in `(eq:strict-gap)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis
open FormalResearch.Montel

/-! ### Section 3: Theorem H.14 Mellin Origin Floor and Conditional Subsequential Core -/

/-- Packaged Mellin three-lines (`eq:ce-three-lines`), origin floor (`eq:ce-origin-floor`),
and Airy–Laplace convergence (`eq:ce-laplace-limit`) for a radial Cohn–Elkies sequence
(supporting the origin-floor step inside Theorem `H.14`). -/
structure ShellReductionPackage where
  c : ℕ → ℝ
  c_pos : ∀ k, 0 < c k
  c_tendsto : Tendsto c atTop atTop
  p : ℕ → ℝ → ℝ
  q : ℕ → ℝ → ℝ
  p_cont : ∀ k, ContinuousOn (p k) (Ici 0)
  q_cont : ∀ k, ContinuousOn (q k) (Ici 0)
  p_int : ∀ k, IntegrableOn (fun Δ => p k Δ * shellRho0 (c k) Δ) (Ioi 0)
  q_int : ∀ k, IntegrableOn (fun Δ => q k Δ * shellRho0 (c k) Δ) (Ioi 0)
  q_nonzero : ∀ k, ∃ Δ : ℝ, 0 ≤ Δ ∧ q k Δ ≠ 0
  h0 : ℕ → ℝ
  h0_nonneg : ∀ k, 0 ≤ h0 k
  h0_ratio_bdd : ∃ C : ℝ, ∀ k, h0 k / shellMass (c k) (fun Δ => 2 * q k Δ) ≤ C
  pq_ratio_bdd : ∃ C : ℝ, ∀ k, shellMass (c k) (p k) / shellMass (c k) (q k) ≤ C
  Mtilde_hhat : ℕ → ℝ → ℝ
  Mtilde_h : ℕ → ℝ → ℝ
  Mtilde_f : ℕ → ℝ → ℝ
  E_strip : ℕ → ℝ → ℝ
  E_strip_pos : ∀ k σ, σ ∈ Ioo 0 1 → 0 < E_strip k σ
  mellin_refl : ∀ k σ, σ ∈ Ioo 0 1 → Mtilde_hhat k (1 - σ) = Mtilde_h k σ
  mellin_sub : ∀ k σ, σ ∈ Ioo 0 1 → Mtilde_h k σ = Mtilde_hhat k σ - Mtilde_f k σ
  mellin_anti : ∀ k σ, σ ∈ Ioo 0 1 → Mtilde_f k σ = -Mtilde_f k (1 - σ)
  mellin_nonneg : ∀ k σ, σ ∈ Ioo 0 1 → 0 ≤ Mtilde_hhat k σ
  three_lines : ∀ k σ, σ ∈ Ioo 0 1 →
    Mtilde_hhat k (1 - σ) ≤
      E_strip k σ * h0 k ^ (1 - σ) * shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ
  Q_inf : ℂ → ℂ
  Q_inf_in : InAiryClass Q_inf
  laplace_limit_f : ∀ y : ℝ, 0 < y →
    Tendsto (fun k =>
      (E_strip k ((y / shellCs) * (c k) ^ (-(1 / 3 : ℝ))))⁻¹ *
        Mtilde_f k (1 - (y / shellCs) * (c k) ^ (-(1 / 3 : ℝ))) /
        shellMass (c k) (fun Δ => 2 * q k Δ))
      atTop (𝓝 (airyLaplace (fun u => 2 * (Q_inf (u : ℂ)).re) y))

lemma ShellReductionPackage.f_mass_pos (R : ShellReductionPackage) (k : ℕ) :
    0 < shellMass (R.c k) (fun Δ => 2 * R.q k Δ) := by
  refine shellMass_pos_of_continuousOn (R.c_pos k) (continuousOn_const.mul (R.q_cont k))
    (((R.q_int k).const_mul 2).congr (Eventually.of_forall fun Δ => by ring)) ?_
  obtain ⟨Δ, hΔ, hne⟩ := R.q_nonzero k
  exact ⟨Δ, hΔ, mul_ne_zero two_ne_zero hne⟩

lemma ShellReductionPackage.hhat_mass_ratio_bdd (R : ShellReductionPackage) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k,
      shellMass (R.c k) (fun Δ => R.p k Δ + R.q k Δ) / shellMass (R.c k) (fun Δ => 2 * R.q k Δ) ≤ B := by
  obtain ⟨Cp, hCp⟩ := R.pq_ratio_bdd
  refine ⟨max 0 (Cp / 2 + 1 / 2), le_max_left _ _, fun k => ?_⟩
  have hfpos : 0 < shellMass (R.c k) (fun Δ => 2 * R.q k Δ) := R.f_mass_pos k
  have h2q : shellMass (R.c k) (fun Δ => 2 * R.q k Δ) = 2 * shellMass (R.c k) (R.q k) := by
    unfold shellMass
    have heq : (fun Δ => |2 * R.q k Δ| * shellRho0 (R.c k) Δ) =
        fun Δ => 2 * (|R.q k Δ| * shellRho0 (R.c k) Δ) := by
      ext Δ; rw [abs_mul, abs_of_pos two_pos]; ring
    rw [heq, integral_const_mul]
  have hle : shellMass (R.c k) (fun Δ => R.p k Δ + R.q k Δ) ≤
      shellMass (R.c k) (R.p k) + shellMass (R.c k) (R.q k) := by
    unfold shellMass
    have hp_abs := abs_mul_shellRho0_integrableOn (R.c_pos k) (R.p_int k)
    have hq_abs := abs_mul_shellRho0_integrableOn (R.c_pos k) (R.q_int k)
    have hadd_int : IntegrableOn (fun Δ => |R.p k Δ + R.q k Δ| * shellRho0 (R.c k) Δ) (Ioi 0) :=
      abs_mul_shellRho0_integrableOn (R.c_pos k)
        (((R.p_int k).add (R.q_int k)).congr (Eventually.of_forall fun Δ => by simp only [Pi.add_apply]; ring))
    have hrhs_int : IntegrableOn (fun Δ => |R.p k Δ| * shellRho0 (R.c k) Δ +
        |R.q k Δ| * shellRho0 (R.c k) Δ) (Ioi 0) := hp_abs.add hq_abs
    rw [← integral_add hp_abs hq_abs]
    refine setIntegral_mono_on hadd_int hrhs_int measurableSet_Ioi fun Δ hΔ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (shellRho0_nonneg (R.c_pos k) hΔ.le)
  have hqpos : 0 < shellMass (R.c k) (R.q k) := by linarith
  calc shellMass (R.c k) (fun Δ => R.p k Δ + R.q k Δ) / shellMass (R.c k) (fun Δ => 2 * R.q k Δ)
      ≤ (shellMass (R.c k) (R.p k) + shellMass (R.c k) (R.q k)) /
          (2 * shellMass (R.c k) (R.q k)) := by
        rw [h2q]; exact div_le_div_of_nonneg_right hle (by positivity)
    _ = (shellMass (R.c k) (R.p k) / shellMass (R.c k) (R.q k)) / 2 + 1 / 2 := by
        field_simp [hqpos.ne']
    _ ≤ Cp / 2 + 1 / 2 := by gcongr; exact hCp k
    _ ≤ max 0 (Cp / 2 + 1 / 2) := le_max_right _ _

/-- Finite-`c` Mellin origin-floor + three-lines bound. -/
theorem shell_reduction_pointwise (R : ShellReductionPackage) (k : ℕ) {σ : ℝ} (hσ : σ ∈ Ioo 0 1) :
    (R.E_strip k σ)⁻¹ * R.Mtilde_f k (1 - σ) / shellMass (R.c k) (fun Δ => 2 * R.q k Δ) ≤
      (R.h0 k / shellMass (R.c k) (fun Δ => 2 * R.q k Δ)) ^ (1 - σ) *
        (shellMass (R.c k) (fun Δ => R.p k Δ + R.q k Δ) /
          shellMass (R.c k) (fun Δ => 2 * R.q k Δ)) ^ σ := by
  have hfpos := R.f_mass_pos k
  have hEst := R.E_strip_pos k σ hσ
  have hfloor : R.Mtilde_f k (1 - σ) ≤ R.Mtilde_hhat k (1 - σ) := by
    rw [R.mellin_refl k σ hσ, R.mellin_sub k σ hσ, R.mellin_anti k σ hσ]
    linarith [R.mellin_nonneg k σ hσ]
  have h3 := hfloor.trans (R.three_lines k σ hσ)
  have hmul : (R.E_strip k σ)⁻¹ * R.Mtilde_f k (1 - σ) / shellMass (R.c k) (fun Δ => 2 * R.q k Δ) ≤
      (R.h0 k ^ (1 - σ) * shellMass (R.c k) (fun Δ => R.p k Δ + R.q k Δ) ^ σ) /
        shellMass (R.c k) (fun Δ => 2 * R.q k Δ) := by
    rw [div_le_div_iff₀ hfpos hfpos]
    have h4 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hEst).le
    have h5 : (R.E_strip k σ)⁻¹ *
        (R.E_strip k σ * R.h0 k ^ (1 - σ) * shellMass (R.c k) (fun Δ => R.p k Δ + R.q k Δ) ^ σ) =
        R.h0 k ^ (1 - σ) * shellMass (R.c k) (fun Δ => R.p k Δ + R.q k Δ) ^ σ := by
      field_simp [hEst.ne']
    rw [h5] at h4
    exact mul_le_mul_of_nonneg_right h4 hfpos.le
  refine hmul.trans_eq ?_
  have hMsplit : shellMass (R.c k) (fun Δ => 2 * R.q k Δ) =
      shellMass (R.c k) (fun Δ => 2 * R.q k Δ) ^ (1 - σ) *
        shellMass (R.c k) (fun Δ => 2 * R.q k Δ) ^ σ := by
    rw [← Real.rpow_add hfpos, sub_add_cancel, Real.rpow_one]
  rw [Real.div_rpow (R.h0_nonneg k) hfpos.le,
    Real.div_rpow (shellMass_nonneg (R.c_pos k) _) hfpos.le]
  conv_lhs => rhs; rw [hMsplit]
  field_simp [(Real.rpow_pos_of_pos hfpos _).ne']

private lemma liminf_rpow_le {a b σ L : ℕ → ℝ} {l A B : ℝ}
    (ha_nn : ∀ k, 0 ≤ a k) (ha_bdd : ∀ k, a k ≤ A)
    (hb_nn : ∀ k, 0 ≤ b k) (hb_bdd : ∀ k, b k ≤ B)
    (hσ_nn : ∀ᶠ k in atTop, 0 ≤ σ k)
    (hσ_tend : Tendsto σ atTop (𝓝 0))
    (hL_tend : Tendsto L atTop (𝓝 l))
    (hineq : ∀ᶠ k in atTop, L k ≤ a k ^ (1 - σ k) * b k ^ σ k) :
    l ≤ Filter.liminf a atTop := by
  have hcb_ge : Filter.IsCoboundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) atTop a :=
    Filter.isCoboundedUnder_ge_of_le atTop ha_bdd
  have hα_nn : 0 ≤ Filter.liminf a atTop :=
    Filter.le_liminf_of_le hcb_ge (Eventually.of_forall fun k => ha_nn k)
  by_contra hlt
  push Not at hlt
  let M : ℝ := (Filter.liminf a atTop + l) / 2
  have hαM : Filter.liminf a atTop < M := by dsimp [M]; linarith
  have hMl : M < l := by dsimp [M]; linarith
  have hMpos : 0 < M := lt_of_le_of_lt hα_nn hαM
  have hfreq : ∃ᶠ k in atTop, a k < M := by
    by_contra hno
    rw [Filter.not_frequently] at hno
    have hle : M ≤ Filter.liminf a atTop :=
      Filter.le_liminf_of_le hcb_ge (hno.mono fun _ h => not_lt.mp h)
    linarith
  have hev_σ1 : ∀ᶠ k in atTop, 0 ≤ 1 - σ k := by
    filter_upwards [hσ_tend.eventually (eventually_lt_nhds zero_lt_one)] with k hk
    linarith
  have hBpos : 0 < max 1 B := lt_of_lt_of_le one_pos (le_max_left 1 B)
  have hRHS_lim : Tendsto (fun k => M ^ (1 - σ k) * (max 1 B) ^ σ k) atTop (𝓝 M) := by
    have hsub : Tendsto (fun k => 1 - σ k) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hσ_tend
    have h1 : Tendsto (fun k => M ^ (1 - σ k)) atTop (𝓝 (M ^ (1 : ℝ))) :=
      (tendsto_const_nhds (x := M)).rpow hsub (Or.inl hMpos.ne')
    have h2 : Tendsto (fun k => (max 1 B) ^ σ k) atTop (𝓝 ((max 1 B) ^ (0 : ℝ))) :=
      (tendsto_const_nhds (x := max 1 B)).rpow hσ_tend (Or.inl hBpos.ne')
    simpa using h1.mul h2
  have hgap : ∀ᶠ k in atTop, M ^ (1 - σ k) * (max 1 B) ^ σ k < L k := by
    have hmid : (M + l) / 2 < l := by linarith
    have h1 := hRHS_lim.eventually (eventually_lt_nhds (by linarith : M < (M + l) / 2))
    have h2 := hL_tend.eventually (eventually_gt_nhds hmid)
    filter_upwards [h1, h2] with k hk1 hk2
    exact hk1.trans hk2
  have hcomb := hfreq.and_eventually (hineq.and (hev_σ1.and (hσ_nn.and hgap)))
  obtain ⟨k, haM, hLle, h1σ, hσ0, hltL⟩ := hcomb.exists
  have h1 : a k ^ (1 - σ k) ≤ M ^ (1 - σ k) := Real.rpow_le_rpow (ha_nn k) haM.le h1σ
  have h2 : b k ^ σ k ≤ (max 1 B) ^ σ k :=
    Real.rpow_le_rpow (hb_nn k) ((hb_bdd k).trans (le_max_right 1 B)) hσ0
  have h3 : a k ^ (1 - σ k) * b k ^ σ k ≤ M ^ (1 - σ k) * (max 1 B) ^ σ k :=
    mul_le_mul h1 h2 (Real.rpow_nonneg (hb_nn k) _) (Real.rpow_nonneg hMpos.le _)
  linarith

/-- **Mellin origin-floor inequality inside Theorem `H.14` (`thm:ce-shell-gap`)**: under
`ShellReductionPackage`, for every `y > 0`, `liminf h_c(0)/M[f_c]` dominates
`airyLaplace (2 Q_∞) y` and its supremum over `y > 0`. (Does not formalize `Theorem HB--CE.L`.) -/
theorem shell_reduction_lower (R : ShellReductionPackage) :
    (∀ y : ℝ, 0 < y →
      airyLaplace (fun u => 2 * (R.Q_inf (u : ℂ)).re) y ≤
        Filter.liminf (fun k => R.h0 k / shellMass (R.c k) (fun Δ => 2 * R.q k Δ)) atTop) ∧
    (BddAbove {v : ℝ | ∃ y : ℝ, 0 < y ∧ v = airyLaplace (fun u => 2 * (R.Q_inf (u : ℂ)).re) y}) ∧
    (sSup {v : ℝ | ∃ y : ℝ, 0 < y ∧ v = airyLaplace (fun u => 2 * (R.Q_inf (u : ℂ)).re) y} ≤
      Filter.liminf (fun k => R.h0 k / shellMass (R.c k) (fun Δ => 2 * R.q k Δ)) atTop) := by
  obtain ⟨Ch, hCh⟩ := R.h0_ratio_bdd
  obtain ⟨B, hB_nn, hB⟩ := R.hhat_mass_ratio_bdd
  have hpt : ∀ y : ℝ, 0 < y →
      airyLaplace (fun u => 2 * (R.Q_inf (u : ℂ)).re) y ≤
        Filter.liminf (fun k => R.h0 k / shellMass (R.c k) (fun Δ => 2 * R.q k Δ)) atTop := by
    intro y hy
    let σ : ℕ → ℝ := fun k => (y / shellCs) * (R.c k) ^ (-(1 / 3 : ℝ))
    have hσ_pos : ∀ k, 0 < σ k := fun k =>
      mul_pos (div_pos hy shellCs_pos) (Real.rpow_pos_of_pos (R.c_pos k) _)
    have hσ_tend : Tendsto σ atTop (𝓝 0) := by
      have hc_inv : Tendsto (fun k => (R.c k) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp R.c_tendsto
      simpa [σ] using hc_inv.const_mul (y / shellCs)
    have hσ_mem : ∀ᶠ k in atTop, σ k ∈ Ioo 0 1 := by
      filter_upwards [hσ_tend.eventually (eventually_lt_nhds zero_lt_one)] with k hk1
      exact ⟨hσ_pos k, hk1⟩
    refine liminf_rpow_le (A := Ch) (B := B)
      (fun k => div_nonneg (R.h0_nonneg k) (R.f_mass_pos k).le) hCh
      (fun k => div_nonneg (shellMass_nonneg (R.c_pos k) _) (R.f_mass_pos k).le) hB
      (Eventually.of_forall fun k => (hσ_pos k).le) hσ_tend (R.laplace_limit_f y hy) ?_
    exact hσ_mem.mono fun k hk => shell_reduction_pointwise R k hk
  have hne : {v : ℝ | ∃ y : ℝ, 0 < y ∧ v = airyLaplace (fun u => 2 * (R.Q_inf (u : ℂ)).re) y}.Nonempty :=
    ⟨_, ⟨1, one_pos, rfl⟩⟩
  have hbdd : BddAbove {v : ℝ | ∃ y : ℝ, 0 < y ∧ v = airyLaplace (fun u => 2 * (R.Q_inf (u : ℂ)).re) y} :=
    ⟨Filter.liminf (fun k => R.h0 k / shellMass (R.c k) (fun Δ => 2 * R.q k Δ)) atTop,
      by rintro _ ⟨y, hy, rfl⟩; exact hpt y hy⟩
  exact ⟨hpt, hbdd, csSup_le hne (by rintro _ ⟨y, hy, rfl⟩; exact hpt y hy)⟩

/-- Packaged subsequential input data for the conditional core of Theorem `H.14` (`thm:ce-shell-gap`).
Assumes bounded ratios (`h0_ratio_bdd`, `pq_ratio_bdd`), subsequence `φ`, limits `P_inf`/`Q_inf`,
pointwise limits, right-tail envelope, Mellin–Laplace limits, convergent threshold `u_thresh_tendsto`,
and exact zero-offset shell signs (`t ∈ D.S \ {D.tm}`). -/
structure ShellGapPackage (D : ShellHBData) where
  c : ℕ → ℝ
  c_pos : ∀ k, 0 < c k
  c_tendsto : Tendsto c atTop atTop
  p : ℕ → ℝ → ℝ
  q : ℕ → ℝ → ℝ
  p_cont : ∀ k, ContinuousOn (p k) (Ici 0)
  q_cont : ∀ k, ContinuousOn (q k) (Ici 0)
  p_int : ∀ k, IntegrableOn (fun Δ => p k Δ * shellRho0 (c k) Δ) (Ioi 0)
  q_int : ∀ k, IntegrableOn (fun Δ => q k Δ * shellRho0 (c k) Δ) (Ioi 0)
  q_nonzero : ∀ k, ∃ Δ : ℝ, 0 ≤ Δ ∧ q k Δ ≠ 0
  h0 : ℕ → ℝ
  h0_nonneg : ∀ k, 0 ≤ h0 k
  h0_ratio_bdd : ∃ C : ℝ, ∀ k, h0 k / shellMass (c k) (fun Δ => 2 * q k Δ) ≤ C
  pq_ratio_bdd : ∃ C : ℝ, ∀ k, shellMass (c k) (p k) / shellMass (c k) (q k) ≤ C
  hhat_nonneg : ∀ k Δ, 0 < Δ → 0 ≤ p k Δ + q k Δ
  h_nonpos_shell : ∀ k, ∀ t ∈ D.S, t ≠ D.tm →
    shellWindowProfile (c k) (fun Δ => p k Δ - q k Δ) t ≤ 0
  u_thresh : ℕ → ℝ
  u_ustar : ℝ
  u_thresh_tendsto : Tendsto u_thresh atTop (𝓝 u_ustar)
  h_nonpos_tail : ∀ k u, u ≤ u_thresh k →
    shellWindowProfile (c k) (fun Δ => p k Δ - q k Δ) u ≤ 0
  f_integral_nonpos : ∀ k, (∫ Δ in Ioi (0 : ℝ), (2 * q k Δ) * shellRho0 (c k) Δ) ≤ 0
  Mtilde_hhat : ℕ → ℝ → ℝ
  Mtilde_h : ℕ → ℝ → ℝ
  Mtilde_f : ℕ → ℝ → ℝ
  E_strip : ℕ → ℝ → ℝ
  E_strip_pos : ∀ k σ, σ ∈ Ioo 0 1 → 0 < E_strip k σ
  mellin_refl : ∀ k σ, σ ∈ Ioo 0 1 → Mtilde_hhat k (1 - σ) = Mtilde_h k σ
  mellin_sub : ∀ k σ, σ ∈ Ioo 0 1 → Mtilde_h k σ = Mtilde_hhat k σ - Mtilde_f k σ
  mellin_anti : ∀ k σ, σ ∈ Ioo 0 1 → Mtilde_f k σ = -Mtilde_f k (1 - σ)
  mellin_nonneg : ∀ k σ, σ ∈ Ioo 0 1 → 0 ≤ Mtilde_hhat k σ
  three_lines : ∀ k σ, σ ∈ Ioo 0 1 →
    Mtilde_hhat k (1 - σ) ≤
      E_strip k σ * h0 k ^ (1 - σ) * shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ
  φ : ℕ → ℕ
  φ_strictMono : StrictMono φ
  P_inf : ℂ → ℂ
  Q_inf : ℂ → ℂ
  P_inf_in : InAiryClass P_inf
  Q_inf_in : InAiryClass Q_inf
  P_tendsto_pt : ∀ u : ℝ,
    Tendsto (fun k => shellWindowProfile (c (φ k)) (p (φ k)) u /
      shellMass (c (φ k)) (fun Δ => 2 * q (φ k) Δ)) atTop (𝓝 (P_inf (u : ℂ)).re)
  Q_tendsto_pt : ∀ u : ℝ,
    Tendsto (fun k => shellWindowProfile (c (φ k)) (q (φ k)) u /
      shellMass (c (φ k)) (fun Δ => 2 * q (φ k) Δ)) atTop (𝓝 (Q_inf (u : ℂ)).re)
  tail_env : ∃ b₀ C₀ ν₀ : ℝ, b₀ ≤ u_ustar - 1 ∧ 0 ≤ C₀ ∧ ∀ k, ∀ u : ℝ, b₀ ≤ u →
    |shellWindowProfile (c (φ k)) (p (φ k)) u /
        shellMass (c (φ k)) (fun Δ => 2 * q (φ k) Δ)| +
      |shellWindowProfile (c (φ k)) (q (φ k)) u /
        shellMass (c (φ k)) (fun Δ => 2 * q (φ k) Δ)| ≤
      C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)
  laplace_limit_f : ∀ y : ℝ, 0 < y →
    Tendsto (fun k =>
      (E_strip (φ k) ((y / shellCs) * (c (φ k)) ^ (-(1 / 3 : ℝ))))⁻¹ *
        Mtilde_f (φ k) (1 - (y / shellCs) * (c (φ k)) ^ (-(1 / 3 : ℝ))) /
        shellMass (c (φ k)) (fun Δ => 2 * q (φ k) Δ))
      atTop (𝓝 (airyLaplace (fun u => 2 * (Q_inf (u : ℂ)).re) y))
  laplace_limit_h : ∀ y : ℝ, 0 < y →
    Tendsto (fun k =>
      (E_strip (φ k) ((y / shellCs) * (c (φ k)) ^ (-(1 / 3 : ℝ))))⁻¹ *
        Mtilde_h (φ k) ((y / shellCs) * (c (φ k)) ^ (-(1 / 3 : ℝ))) /
        shellMass (c (φ k)) (fun Δ => 2 * q (φ k) Δ))
      atTop (𝓝 (airyLaplace (fun u => (P_inf (u : ℂ) - Q_inf (u : ℂ)).re) y))

/-- Project a `ShellGapPackage` onto its convergent subsequence `φ` as a `ShellReductionPackage`. -/
noncomputable def ShellGapPackage.toShellReductionPackage {D : ShellHBData} (G : ShellGapPackage D) :
    ShellReductionPackage where
  c := fun k => G.c (G.φ k)
  c_pos := fun k => G.c_pos (G.φ k)
  c_tendsto := G.c_tendsto.comp G.φ_strictMono.tendsto_atTop
  p := fun k => G.p (G.φ k)
  q := fun k => G.q (G.φ k)
  p_cont := fun k => G.p_cont (G.φ k)
  q_cont := fun k => G.q_cont (G.φ k)
  p_int := fun k => G.p_int (G.φ k)
  q_int := fun k => G.q_int (G.φ k)
  q_nonzero := fun k => G.q_nonzero (G.φ k)
  h0 := fun k => G.h0 (G.φ k)
  h0_nonneg := fun k => G.h0_nonneg (G.φ k)
  h0_ratio_bdd := let ⟨C, hC⟩ := G.h0_ratio_bdd; ⟨C, fun k => hC (G.φ k)⟩
  pq_ratio_bdd := let ⟨C, hC⟩ := G.pq_ratio_bdd; ⟨C, fun k => hC (G.φ k)⟩
  Mtilde_hhat := fun k => G.Mtilde_hhat (G.φ k)
  Mtilde_h := fun k => G.Mtilde_h (G.φ k)
  Mtilde_f := fun k => G.Mtilde_f (G.φ k)
  E_strip := fun k => G.E_strip (G.φ k)
  E_strip_pos := fun k => G.E_strip_pos (G.φ k)
  mellin_refl := fun k => G.mellin_refl (G.φ k)
  mellin_sub := fun k => G.mellin_sub (G.φ k)
  mellin_anti := fun k => G.mellin_anti (G.φ k)
  mellin_nonneg := fun k => G.mellin_nonneg (G.φ k)
  three_lines := fun k => G.three_lines (G.φ k)
  Q_inf := G.Q_inf
  Q_inf_in := G.Q_inf_in
  laplace_limit_f := G.laplace_limit_f

/-- **Conditional subsequential core of Theorem `H.14` (`thm:ce-shell-gap`)**: under
`ShellGapPackage D`, the packaged subsequential limits `(P_∞ + Q_∞, Q_∞)` satisfy
`(eq:ce-laplace-constraint)`, `liminf h_c(0)/M[f_c] ≥ sup_{y>0} ℒ_y(2 Q_∞)`, `P_∞ - Q_∞` is
positive arbitrarily far right, `u_* ≤ t_m`, and if `u_* = t_m` then `2 Q_k → G_N/‖G_N‖₁`
pointwise along `φ` and in `L¹`, `M[p + q]/M[2q] → 0` along `φ`, and `∀ y > 0, airyLaplace G_N y ≤ 0`.
Locally uniform convergence, full-sequence `M[hhat_c]/M[f_c] → 0`, `o(c^{1/3})` shell offsets,
and derivation of boundedness/compactness from Euclidean pairs remain external. -/
theorem theorem_H14_subseq_bounds (D : ShellHBData) (G : ShellGapPackage D) :
    TwoProfileFeasibleWitness D G.u_ustar (fun z => G.P_inf z + G.Q_inf z) G.Q_inf ∧
    (∀ y : ℝ, 0 < y →
      airyLaplace (fun u => 2 * (G.Q_inf (u : ℂ)).re) y ≤
        Filter.liminf (fun k => G.h0 (G.φ k) /
          shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ)) atTop) ∧
    (∀ M : ℝ, ∃ u : ℝ, M < u ∧ 0 < (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re) ∧
    G.u_ustar ≤ D.tm ∧
    (G.u_ustar = D.tm →
      (∀ u : ℝ, Tendsto (fun k =>
        shellWindowProfile (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) u /
          shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ)) atTop (𝓝 (D.normG u))) ∧
      Tendsto (fun k => ∫ u : ℝ,
        |shellWindowProfile (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) u /
            shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) - D.normG u|) atTop (𝓝 0) ∧
      Tendsto (fun k =>
        shellMass (G.c (G.φ k)) (fun Δ => G.p (G.φ k) Δ + G.q (G.φ k) Δ) /
          shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ)) atTop (𝓝 0) ∧
      (∀ y : ℝ, 0 < y → airyLaplace (fun u => (D.G (u : ℂ)).re) y ≤ 0)) := by
  let R := G.toShellReductionPackage
  let Pk : ℕ → ℝ → ℝ := fun k u =>
    shellWindowProfile (G.c (G.φ k)) (G.p (G.φ k)) u /
      shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ)
  let Qk : ℕ → ℝ → ℝ := fun k u =>
    shellWindowProfile (G.c (G.φ k)) (G.q (G.φ k)) u /
      shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ)
  let Sk : ℕ → ℝ → ℝ := fun k u => Pk k u + Qk k u
  let Q2k : ℕ → ℝ → ℝ := fun k u => 2 * Qk k u
  let Hk : ℕ → ℝ → ℝ := fun k u => Pk k u - Qk k u
  have hf_pos : ∀ k, 0 < shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := R.f_mass_pos
  have hP_int : ∀ k, Integrable (Pk k) := fun k => by
    have hi := (integrable_shellWindowProfile_iff (G.c_pos (G.φ k)) (G.p (G.φ k))).mpr (G.p_int (G.φ k))
    exact hi.div_const _
  have hQ_int : ∀ k, Integrable (Qk k) := fun k => by
    have hi := (integrable_shellWindowProfile_iff (G.c_pos (G.φ k)) (G.q (G.φ k))).mpr (G.q_int (G.φ k))
    exact hi.div_const _
  have hQ2_int : ∀ k, Integrable (Q2k k) := fun k => (hQ_int k).const_mul 2
  have hS_int : ∀ k, Integrable (Sk k) := fun k => (hP_int k).add (hQ_int k)
  have hSk_eq : ∀ k u, Sk k u =
      shellWindowProfile (G.c (G.φ k)) (fun Δ => G.p (G.φ k) Δ + G.q (G.φ k) Δ) u /
        shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := by
    intro k u; dsimp [Sk, Pk, Qk]
    rw [← add_div]; congr 1
    unfold shellWindowProfile; dsimp only; split_ifs <;> ring
  have hQ2k_eq : ∀ k u, Q2k k u =
      shellWindowProfile (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) u /
        shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := by
    intro k u; dsimp [Q2k, Qk]
    rw [mul_div_assoc']; congr 1
    unfold shellWindowProfile; dsimp only; split_ifs <;> ring
  have hHk_eq : ∀ k u, Hk k u =
      shellWindowProfile (G.c (G.φ k)) (fun Δ => G.p (G.φ k) Δ - G.q (G.φ k) Δ) u /
        shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := by
    intro k u; dsimp [Hk, Pk, Qk]
    rw [← sub_div]; congr 1
    unfold shellWindowProfile; dsimp only; split_ifs <;> ring
  have hSk_nn : ∀ k u, 0 ≤ Sk k u := fun k u => by
    rw [hSk_eq]
    refine div_nonneg ?_ (hf_pos k).le
    unfold shellWindowProfile; dsimp only; split_ifs with h
    · exact mul_nonneg (div_nonneg (Real.rpow_nonneg (G.c_pos _).le _) shellBeta1_pos.le)
        (mul_nonneg (G.hhat_nonneg _ _ h) (shellRho0_nonneg (G.c_pos _) h.le))
    · exact le_rfl
  have hQ2k_l1 : ∀ k, ∫ u : ℝ, |Q2k k u| = 1 := fun k => by
    have heq : (fun u => |Q2k k u|) = fun u =>
        |shellWindowProfile (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) u| /
          shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := by
      ext u; rw [hQ2k_eq, abs_div, abs_of_pos (hf_pos k)]
    rw [heq, integral_div, integral_abs_shellWindowProfile (G.c_pos _), div_self (hf_pos k).ne']
  have hQ2k_int_nonpos : ∀ k, ∫ u : ℝ, Q2k k u ≤ 0 := fun k => by
    have heq : (fun u => Q2k k u) = fun u =>
        shellWindowProfile (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) u /
          shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := funext (hQ2k_eq k)
    rw [heq, integral_div, integral_shellWindowProfile (G.c_pos _)]
    exact div_nonpos_of_nonpos_of_nonneg (G.f_integral_nonpos (G.φ k)) (hf_pos k).le
  have hS_lim : ∀ u : ℝ, Tendsto (fun k => Sk k u) atTop (𝓝 ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)).re)) :=
    fun u => by simpa [Complex.add_re] using (G.P_tendsto_pt u).add (G.Q_tendsto_pt u)
  have hQ2_lim : ∀ u : ℝ, Tendsto (fun k => Q2k k u) atTop (𝓝 (2 * (G.Q_inf (u : ℂ)).re)) :=
    fun u => (G.Q_tendsto_pt u).const_mul 2
  have hH_lim : ∀ u : ℝ, Tendsto (fun k => Hk k u) atTop (𝓝 ((G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re)) :=
    fun u => by simpa [Complex.sub_re] using (G.P_tendsto_pt u).sub (G.Q_tendsto_pt u)
  have hS_nn : ∀ u : ℝ, 0 ≤ (G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)).re := fun u =>
    ge_of_tendsto (hS_lim u) (Eventually.of_forall fun k => hSk_nn k u)
  have hQ2_l1 : ∫ u : ℝ, ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖ ≤ 1 := by
    have hfatou : ∫⁻ u : ℝ, ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖ₑ ∂volume ≤ 1 := by
      have heq_lim : ∀ u : ℝ, ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖ₑ =
          Filter.liminf (fun k => ENNReal.ofReal |Q2k k u|) atTop := by
        intro u
        have hre : ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖ = |2 * (G.Q_inf (u : ℂ)).re| := by
          have hc : G.Q_inf (u : ℂ) = ((G.Q_inf (u : ℂ)).re : ℂ) := Complex.ext rfl (G.Q_inf_in.2.2.2 u)
          conv_lhs => rw [hc, show (2 : ℂ) * ((G.Q_inf (u : ℂ)).re : ℂ) =
            ((2 * (G.Q_inf (u : ℂ)).re : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
        have hlim : Tendsto (fun k => ENNReal.ofReal |Q2k k u|) atTop
            (𝓝 (ENNReal.ofReal |2 * (G.Q_inf (u : ℂ)).re|)) :=
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hQ2_lim u).abs)
        rw [← hre, ofReal_norm] at hlim
        exact hlim.liminf_eq.symm
      calc ∫⁻ u : ℝ, ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖ₑ ∂volume
          = ∫⁻ u : ℝ, Filter.liminf (fun k => ENNReal.ofReal |Q2k k u|) atTop ∂volume := by
            simp_rw [heq_lim]
        _ ≤ Filter.liminf (fun k => ∫⁻ u : ℝ, ENNReal.ofReal |Q2k k u| ∂volume) atTop :=
            lintegral_liminf_le' fun k =>
              ENNReal.continuous_ofReal.measurable.comp_aemeasurable
                (hQ2_int k).abs.aestronglyMeasurable.aemeasurable
        _ ≤ 1 := by
            have hk_eq : ∀ k, ∫⁻ u : ℝ, ENNReal.ofReal |Q2k k u| ∂volume = 1 := fun k => by
              rw [← ofReal_integral_eq_lintegral_ofReal (hQ2_int k).abs
                (Eventually.of_forall fun _ => abs_nonneg _), hQ2k_l1 k, ENNReal.ofReal_one]
            simp_rw [hk_eq]; simp
    have hq2_int : Integrable (fun u : ℝ => (2 : ℂ) * G.Q_inf (u : ℂ)) := G.Q_inf_in.2.1.const_mul 2
    have hof : ENNReal.ofReal (∫ u : ℝ, ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖) =
        ∫⁻ u : ℝ, ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖ₑ ∂volume :=
      ofReal_integral_norm_eq_lintegral_enorm hq2_int
    rw [← ENNReal.ofReal_one] at hfatou
    rw [← hof] at hfatou
    exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp hfatou
  obtain ⟨b₀, C₀, ν₀, hb₀_le, hC₀, htail_env⟩ := G.tail_env
  have hQ2k_nonneg_left : ∀ k, ∀ u ≤ G.u_thresh (G.φ k), 0 ≤ Q2k k u := fun k u hu => by
    have hS0 := hSk_nn k u
    have hH0 : Hk k u ≤ 0 := by
      rw [hHk_eq]
      exact div_nonpos_of_nonpos_of_nonneg (G.h_nonpos_tail (G.φ k) u hu) (hf_pos k).le
    dsimp [Q2k, Sk, Hk] at hS0 hH0 ⊢; linarith
  have hev_b₀ : ∀ᶠ k in atTop, b₀ ≤ G.u_thresh (G.φ k) := by
    have ht := G.u_thresh_tendsto.comp G.φ_strictMono.tendsto_atTop
    exact ht.eventually (eventually_ge_nhds (by linarith))
  have hdom0 := integrableOn_airyEnv_Ici (2 * C₀) ν₀ 0 b₀ (by positivity)
  have hQ2_tail_lim : Tendsto (fun k => ∫ u in Ioi b₀, Q2k k u) atTop
      (𝓝 (∫ u in Ioi b₀, 2 * (G.Q_inf (u : ℂ)).re)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun u => (2 * C₀) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (0 * u))
      (fun k => (hQ2_int k).aestronglyMeasurable.restrict)
      (hdom0.mono_set Ioi_subset_Ici_self) ?_ ?_
    · intro k
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hbd := htail_env k u (mem_Ioi.mp hu).le
      dsimp [Q2k]
      rw [abs_mul, abs_of_pos two_pos, zero_mul, Real.exp_zero, mul_one]
      have : |Qk k u| ≤ C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) :=
        (le_add_of_nonneg_left (abs_nonneg _)).trans hbd
      linarith
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => hQ2_lim u
  have hQ2_int_real : ∫ u : ℝ, 2 * (G.Q_inf (u : ℂ)).re ≤ 0 := by
    have hQ2i : Integrable (fun u : ℝ => 2 * (G.Q_inf (u : ℂ)).re) := G.Q_inf_in.2.1.re.const_mul 2
    have hleft_nn : ∀ u ∈ Iic b₀, 0 ≤ 2 * (G.Q_inf (u : ℂ)).re := fun u hu => by
      have hev : ∀ᶠ k in atTop, 0 ≤ Q2k k u := hev_b₀.mono fun k hk =>
        hQ2k_nonneg_left k u ((mem_Iic.mp hu).trans hk)
      exact ge_of_tendsto (hQ2_lim u) hev
    have hfatou_le : ENNReal.ofReal (∫ u in Iic b₀, 2 * (G.Q_inf (u : ℂ)).re) ≤
        ENNReal.ofReal (-(∫ u in Ioi b₀, 2 * (G.Q_inf (u : ℂ)).re)) := by
      have hlim_rhs : Tendsto (fun k => ENNReal.ofReal (-(∫ u in Ioi b₀, Q2k k u))) atTop
          (𝓝 (ENNReal.ofReal (-(∫ u in Ioi b₀, 2 * (G.Q_inf (u : ℂ)).re)))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hQ2_tail_lim.neg
      have heq_lim : ∀ u : ℝ, ENNReal.ofReal (2 * (G.Q_inf (u : ℂ)).re) =
          Filter.liminf (fun k => ENNReal.ofReal (Q2k k u)) atTop := fun u =>
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hQ2_lim u)).liminf_eq.symm
      rw [ofReal_integral_eq_lintegral_ofReal (hQ2i.integrableOn (s := Iic b₀))
        (ae_restrict_of_forall_mem measurableSet_Iic hleft_nn)]
      calc ∫⁻ u in Iic b₀, ENNReal.ofReal (2 * (G.Q_inf (u : ℂ)).re)
          = ∫⁻ u in Iic b₀, Filter.liminf (fun k => ENNReal.ofReal (Q2k k u)) atTop := by
            simp_rw [heq_lim]
        _ ≤ Filter.liminf (fun k => ∫⁻ u in Iic b₀, ENNReal.ofReal (Q2k k u)) atTop :=
            lintegral_liminf_le' fun k =>
              ENNReal.continuous_ofReal.measurable.comp_aemeasurable
                (hQ2_int k).aestronglyMeasurable.aemeasurable.restrict
        _ ≤ Filter.liminf (fun k => ENNReal.ofReal (-(∫ u in Ioi b₀, Q2k k u))) atTop := by
            refine Filter.liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
            filter_upwards [hev_b₀] with k hk
            have hk_nn : ∀ u ∈ Iic b₀, 0 ≤ Q2k k u := fun u hu =>
              hQ2k_nonneg_left k u ((mem_Iic.mp hu).trans hk)
            rw [← ofReal_integral_eq_lintegral_ofReal ((hQ2_int k).integrableOn (s := Iic b₀))
              (ae_restrict_of_forall_mem measurableSet_Iic hk_nn)]
            have hsp := integral_add_compl (measurableSet_Iic (a := b₀)) (hQ2_int k)
            rw [compl_Iic] at hsp
            exact ENNReal.ofReal_le_ofReal (by linarith [hQ2k_int_nonpos k])
        _ = ENNReal.ofReal (-(∫ u in Ioi b₀, 2 * (G.Q_inf (u : ℂ)).re)) := hlim_rhs.liminf_eq
    have hsp := integral_add_compl (measurableSet_Iic (a := b₀)) hQ2i
    rw [compl_Iic] at hsp
    have hrhs_nn : 0 ≤ -(∫ u in Ioi b₀, 2 * (G.Q_inf (u : ℂ)).re) := by
      have h1 : ∀ᶠ k in atTop, 0 ≤ -(∫ u in Ioi b₀, Q2k k u) := by
        filter_upwards [hev_b₀] with k hk
        have hsp' := integral_add_compl (measurableSet_Iic (a := b₀)) (hQ2_int k)
        rw [compl_Iic] at hsp'
        have hk0 : 0 ≤ ∫ u in Iic b₀, Q2k k u := setIntegral_nonneg measurableSet_Iic
          fun u hu => hQ2k_nonneg_left k u ((mem_Iic.mp hu).trans hk)
        linarith [hQ2k_int_nonpos k]
      exact ge_of_tendsto hQ2_tail_lim.neg h1
    have hle := (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp hfatou_le
    linarith
  have hH_shell : ∀ t ∈ D.S, t ≠ D.tm → ((G.P_inf (t : ℂ) + G.Q_inf (t : ℂ)) - 2 * G.Q_inf (t : ℂ)).re ≤ 0 := by
    intro t ht htm
    have heq : ((G.P_inf (t : ℂ) + G.Q_inf (t : ℂ)) - 2 * G.Q_inf (t : ℂ)).re =
        (G.P_inf (t : ℂ) - G.Q_inf (t : ℂ)).re := by ring_nf
    rw [heq]
    exact le_of_tendsto (hH_lim t) (Eventually.of_forall fun k => by
      rw [hHk_eq]; exact div_nonpos_of_nonpos_of_nonneg (G.h_nonpos_shell _ t ht htm) (hf_pos k).le)
  have hH_left : ∀ u : ℝ, u ≤ G.u_ustar →
      ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re ≤ 0 := by
    have hlt_left : ∀ u : ℝ, u < G.u_ustar → (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re ≤ 0 := by
      intro u hu
      have hev : ∀ᶠ k in atTop, u ≤ G.u_thresh (G.φ k) :=
        ((G.u_thresh_tendsto.comp G.φ_strictMono.tendsto_atTop).eventually (eventually_gt_nhds hu)).mono
          fun _ h => h.le
      exact le_of_tendsto (hH_lim u) (hev.mono fun k hk => by
        rw [hHk_eq]; exact div_nonpos_of_nonpos_of_nonneg (G.h_nonpos_tail _ u hk) (hf_pos k).le)
    intro u hu
    have heq : ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re =
        (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re := by ring_nf
    rw [heq]
    rcases hu.eq_or_lt with rfl | hlt
    · have hc : Continuous (fun x : ℝ => (G.P_inf (x : ℂ) - G.Q_inf (x : ℂ)).re) :=
        Complex.continuous_re.comp (((G.P_inf_in.1.sub G.Q_inf_in.1).continuous).comp Complex.continuous_ofReal)
      have hseq : Tendsto (fun k : ℕ => G.u_ustar - 1 / ((k : ℝ) + 1)) atTop (𝓝 G.u_ustar) := by
        simpa only [sub_zero] using
          (tendsto_const_nhds (x := G.u_ustar)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      exact le_of_tendsto (hc.continuousAt.tendsto.comp hseq)
        (Eventually.of_forall fun k => hlt_left _ (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]))
    · exact hlt_left u hlt
  have hQ2_tail_neg : (1 / 2 : ℝ) ≤ ∫ u in Ioi G.u_ustar, max (-((2 : ℂ) * G.Q_inf (u : ℂ)).re) 0 := by
    have hneg_lim : Tendsto (fun k => ∫ u in Ioi b₀, max (-(Q2k k u)) 0) atTop
        (𝓝 (∫ u in Ioi b₀, max (-(2 * (G.Q_inf (u : ℂ)).re)) 0)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun u => (2 * C₀) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (0 * u))
        (fun k => ((hQ2_int k).neg.sup (integrable_zero _ _ _)).aestronglyMeasurable.restrict)
        (hdom0.mono_set Ioi_subset_Ici_self) ?_ ?_
      · intro k
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
        have hbd := htail_env k u (mem_Ioi.mp hu).le
        have hmx : ‖max (-(Q2k k u)) 0‖ ≤ |Q2k k u| := by
          rw [Real.norm_of_nonneg (le_max_right _ _)]
          exact max_le (neg_le_abs _) (abs_nonneg _)
        have h2 : |Q2k k u| ≤ (2 * C₀) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
          have : |Qk k u| ≤ C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) :=
            (le_add_of_nonneg_left (abs_nonneg _)).trans hbd
          dsimp [Q2k]; rw [abs_mul, abs_of_pos two_pos]; linarith
        simpa using hmx.trans h2
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
        exact ((continuous_neg.max continuous_const).continuousAt.tendsto.comp (hQ2_lim u))
    have hk_half : ∀ᶠ k in atTop, (1 / 2 : ℝ) ≤ ∫ u in Ioi b₀, max (-(Q2k k u)) 0 := by
      filter_upwards [hev_b₀] with k hk
      have hneg_eq : (fun u => max (-(Q2k k u)) 0) = fun u => (|Q2k k u| - Q2k k u) / 2 := by
        ext u
        have := posPart_eq_abs_add_div_two (-(Q2k k u))
        simpa [abs_neg, sub_eq_add_neg] using this
      have hint_neg : Integrable (fun u => max (-(Q2k k u)) 0) := by
        rw [hneg_eq]; exact ((hQ2_int k).abs.sub (hQ2_int k)).div_const 2
      have hleft_zero : ∫ u in Iic b₀, max (-(Q2k k u)) 0 = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
        exact max_eq_right (neg_nonpos.mpr (hQ2k_nonneg_left k u ((mem_Iic.mp hu).trans hk)))
      have hsp := integral_add_compl (measurableSet_Iic (a := b₀)) hint_neg
      rw [compl_Iic, hleft_zero, zero_add] at hsp
      rw [hsp, hneg_eq, integral_div, integral_sub (hQ2_int k).abs (hQ2_int k), hQ2k_l1 k]
      linarith [hQ2k_int_nonpos k]
    have hIoi_b0 : (1 / 2 : ℝ) ≤ ∫ u in Ioi b₀, max (-(2 * (G.Q_inf (u : ℂ)).re)) 0 :=
      ge_of_tendsto hneg_lim hk_half
    have hIoc_zero : ∫ u in Ioc b₀ G.u_ustar, max (-(2 * (G.Q_inf (u : ℂ)).re)) 0 = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      have hHu := hH_left u (mem_Ioc.mp hu).2
      have hSu := hS_nn u
      have h2Q_nn : 0 ≤ 2 * (G.Q_inf (u : ℂ)).re := by
        have hre : ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re =
            (G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)).re - 2 * (G.Q_inf (u : ℂ)).re := by
          simp [Complex.add_re]
        linarith
      exact max_eq_right (neg_nonpos.mpr h2Q_nn)
    have hsplit_union : Ioi b₀ = Ioc b₀ G.u_ustar ∪ Ioi G.u_ustar :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith : b₀ ≤ G.u_ustar)).symm
    have hint_neg : IntegrableOn (fun (u : ℝ) => max (-(2 * (G.Q_inf (u : ℂ)).re)) 0) (Ioi b₀) := by
      have hneg_eq : (fun (u : ℝ) => max (-(2 * (G.Q_inf (u : ℂ)).re)) 0) =
          fun (u : ℝ) => (|2 * (G.Q_inf (u : ℂ)).re| - 2 * (G.Q_inf (u : ℂ)).re) / 2 := by
        ext u
        have hpp := posPart_eq_abs_add_div_two (-(2 * (G.Q_inf (u : ℂ)).re))
        rw [abs_neg] at hpp
        rw [hpp]; ring
      have hQ2i : Integrable (fun u : ℝ => 2 * (G.Q_inf (u : ℂ)).re) :=
        (by simpa using G.Q_inf_in.2.1.re : Integrable (fun u : ℝ => (G.Q_inf (u : ℂ)).re)).const_mul 2
      rw [hneg_eq]
      exact ((hQ2i.abs.sub hQ2i).div_const 2).integrableOn
    have hadd_set := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint_neg.mono_set Ioc_subset_Ioi_self) (hint_neg.mono_set (Ioi_subset_Ioi (by linarith : b₀ ≤ G.u_ustar)))
    rw [← hsplit_union, hIoc_zero, zero_add] at hadd_set
    have hre2 : (fun u : ℝ => max (-((2 : ℂ) * G.Q_inf (u : ℂ)).re) 0) =
        fun (u : ℝ) => max (-(2 * (G.Q_inf (u : ℂ)).re)) 0 := by
      ext u
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    rw [hre2, ← hadd_set]
    exact hIoi_b0
  have hH_L : ∀ y : ℝ, 0 ≤ y →
      0 ≤ ∫ u : ℝ, ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re * Real.exp (y * u) := by
    have hH_in : InAiryClass (fun z => G.P_inf z - G.Q_inf z) := G.P_inf_in.sub G.Q_inf_in
    have hL_pos : ∀ y : ℝ, 0 < y → 0 ≤ ∫ u : ℝ, (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re * Real.exp (y * u) := by
      intro y hy
      let σ : ℕ → ℝ := fun k => (y / shellCs) * (G.c (G.φ k)) ^ (-(1 / 3 : ℝ))
      have hσ_pos : ∀ k, 0 < σ k := fun k =>
        mul_pos (div_pos hy shellCs_pos) (Real.rpow_pos_of_pos (G.c_pos _) _)
      have hσ_tend : Tendsto σ atTop (𝓝 0) := by
        simpa [σ] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
          (G.c_tendsto.comp G.φ_strictMono.tendsto_atTop)).const_mul (y / shellCs)
      have hσ_mem : ∀ᶠ k in atTop, σ k ∈ Ioo 0 1 := by
        filter_upwards [hσ_tend.eventually (eventually_lt_nhds zero_lt_one)] with k hk1
        exact ⟨hσ_pos k, hk1⟩
      have hnn_k : ∀ᶠ k in atTop, 0 ≤ (G.E_strip (G.φ k) (σ k))⁻¹ *
          G.Mtilde_h (G.φ k) (σ k) / shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := by
        filter_upwards [hσ_mem] with k hk
        have hEst := G.E_strip_pos (G.φ k) (σ k) hk
        have hm1 : 1 - σ k ∈ Ioo 0 1 := ⟨by linarith [hk.2], by linarith [hk.1]⟩
        have hMh : 0 ≤ G.Mtilde_h (G.φ k) (σ k) := by
          rw [← G.mellin_refl (G.φ k) (σ k) hk]
          exact G.mellin_nonneg (G.φ k) (1 - σ k) hm1
        exact div_nonneg (mul_nonneg (inv_pos.mpr hEst).le hMh) (hf_pos k).le
      have hL_lim := ge_of_tendsto (G.laplace_limit_h y hy) hnn_k
      unfold airyLaplace at hL_lim
      exact nonneg_of_mul_nonneg_right hL_lim (Real.exp_pos _)
    intro y hy
    have heq_sub : (fun u : ℝ => ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re *
          Real.exp (y * u)) =
        fun (u : ℝ) => (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re * Real.exp (y * u) := by
      ext u; simp [Complex.add_re]; ring
    rw [heq_sub]
    rcases hy.eq_or_lt with rfl | hypos
    · have hcont : ContinuousOn (fun s : ℝ => ∫ u : ℝ, (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re * Real.exp (s * u))
          (Ici 0) := hH_in.laplace_continuousOn_Ici
      have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[Ici 0] 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          tendsto_one_div_add_atTop_nhds_zero_nat
          (Eventually.of_forall fun n => mem_Ici.mpr (by positivity))
      exact ge_of_tendsto ((hcont 0 (mem_Ici.mpr le_rfl)).tendsto.comp hseq)
        (Eventually.of_forall fun n => hL_pos _ (by positivity : 0 < (1 : ℝ) / ((n : ℝ) + 1)))
    · exact hL_pos y hypos
  have htwo : TwoProfileFeasibleWitness D G.u_ustar (fun z => G.P_inf z + G.Q_inf z) G.Q_inf := by
    refine ⟨G.P_inf_in.add G.Q_inf_in, G.Q_inf_in, hS_nn, hQ2_l1, ?_, hQ2_tail_neg, hH_shell, hH_left, hH_L⟩
    have heq : (fun u : ℝ => ((2 : ℂ) * G.Q_inf (u : ℂ)).re) = fun (u : ℝ) => 2 * (G.Q_inf (u : ℂ)).re := by
      ext u; simp
    rw [heq]; exact hQ2_int_real
  have hone : OneProfileFeasible D G.u_ustar :=
    (one_profile_feasible_iff D G.u_ustar).mp ⟨_, _, htwo⟩
  have hle_tm : G.u_ustar ≤ D.tm :=
    (one_profile_threshold_le_and_endpoint_iff D).1 G.u_ustar hone
  have hH_pos_far : ∀ M : ℝ, ∃ u : ℝ, M < u ∧ 0 < (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re := by
    intro M
    by_contra hnone
    push Not at hnone
    have hH_in : InAiryClass (fun z => G.P_inf z - G.Q_inf z) := G.P_inf_in.sub G.Q_inf_in
    have hH_ne : ∃ z : ℂ, G.P_inf z - G.Q_inf z ≠ 0 := by
      by_contra h0
      push Not at h0
      have hall0 : ∀ u : ℝ, max (-((2 : ℂ) * G.Q_inf (u : ℂ)).re) 0 = 0 := by
        intro u
        have hHu := h0 (u : ℂ)
        have heq : ((2 : ℂ) * G.Q_inf (u : ℂ)).re = (G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)).re := by
          have := congrArg Complex.re hHu; simp only [Complex.sub_re, Complex.zero_re] at this
          simp [Complex.add_re]; linarith
        rw [heq]
        exact max_eq_right (neg_nonpos.mpr (hS_nn u))
      have hint0 : ∫ u in Ioi G.u_ustar, max (-((2 : ℂ) * G.Q_inf (u : ℂ)).re) 0 = 0 := by
        simp_rw [hall0, integral_zero]
      linarith
    let M' := M + 1
    have hx₀ : ∃ x₀ : ℝ, M' < x₀ ∧ (G.P_inf (x₀ : ℂ) - G.Q_inf (x₀ : ℂ)).re < 0 := by
      by_contra hno
      push Not at hno
      have hzero : ∀ x : ℝ, M' < x → x < M' + 1 → G.P_inf (x : ℂ) - G.Q_inf (x : ℂ) = 0 := by
        intro x hx1 hx2
        have hle0 := hnone x (by dsimp [M'] at hx1; linarith)
        have hge0 : 0 ≤ (G.P_inf (x : ℂ) - G.Q_inf (x : ℂ)).re := hno x hx1
        exact Complex.ext (le_antisymm hle0 hge0) (hH_in.2.2.2 x)
      obtain ⟨z, hz⟩ := hH_ne
      exact hz (airy_entire_eq_zero_of_real_interval hH_in.1 (by linarith : M' < M' + 1) hzero z)
    obtain ⟨x₀, hMx₀, hx₀neg⟩ := hx₀
    have hH_re_int : Integrable (fun u : ℝ => -(G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re) :=
      (by simpa using hH_in.2.1.re : Integrable (fun u : ℝ => (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re)).neg
    have hH_re_exp : ∀ y : ℝ, 0 ≤ y →
        Integrable (fun u : ℝ => -(G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re * Real.exp (y * u)) := fun y hy =>
      (hH_in.integrable_exp_nonneg hy).neg.congr
        (Eventually.of_forall fun u => by simp only [Pi.neg_apply]; ring)
    obtain ⟨Y, hY_pos, hY⟩ := laplace_pos_eventually_of_nonneg_tail
      hH_in.to_polyLeftAiryRightBound.1.neg hH_re_int hH_re_exp
      hMx₀ (fun u hu => neg_nonneg.mpr (hnone u (by dsimp [M'] at hu; linarith)))
      (neg_pos.mpr hx₀neg)
    have hpos := hY Y le_rfl
    have heq_neg : ∫ u : ℝ, -(G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re * Real.exp (Y * u) =
        -(∫ u : ℝ, (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re * Real.exp (Y * u)) := by
      simp_rw [neg_mul]; rw [integral_neg]
    have hL0 := hH_L Y hY_pos.le
    have hre_sub : (fun u : ℝ => ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re *
          Real.exp (Y * u)) =
        fun (u : ℝ) => (G.P_inf (u : ℂ) - G.Q_inf (u : ℂ)).re * Real.exp (Y * u) := by
      ext u; simp [Complex.add_re]; ring
    rw [hre_sub] at hL0
    simp_rw [Pi.neg_apply] at hpos
    rw [heq_neg] at hpos
    linarith
  refine ⟨htwo, (shell_reduction_lower R).1, hH_pos_far, hle_tm, fun heq_tm => ?_⟩
  let H : ℂ → ℂ := fun z => G.P_inf z - G.Q_inf z
  let S : ℂ → ℂ := fun z => G.P_inf z + G.Q_inf z
  have hH_in : InAiryClass H := G.P_inf_in.sub G.Q_inf_in
  have hS_in : InAiryClass S := G.P_inf_in.add G.Q_inf_in
  have hH_ne : ∃ z : ℂ, H z ≠ 0 := by
    obtain ⟨H', hH'⟩ := (one_profile_feasible_iff D G.u_ustar).mp ⟨_, _, htwo⟩
    by_contra h0; push Not at h0
    have hall0 : ∀ u : ℝ, max (-((2 : ℂ) * G.Q_inf (u : ℂ)).re) 0 = 0 := by
      intro u
      have hHu := h0 (u : ℂ)
      have heq : ((2 : ℂ) * G.Q_inf (u : ℂ)).re = (S (u : ℂ)).re := by
        have := congrArg Complex.re hHu; simp only [H, Complex.sub_re, Complex.zero_re] at this
        simp [S, Complex.add_re]; linarith
      rw [heq]; exact max_eq_right (neg_nonpos.mpr (hS_nn u))
    have hint0 : ∫ u in Ioi G.u_ustar, max (-((2 : ℂ) * G.Q_inf (u : ℂ)).re) 0 = 0 := by
      simp_rw [hall0, integral_zero]
    linarith
  have hHint_re : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re := by
    have hre : ∫ x : ℝ, (H (x : ℂ)).re = (∫ x : ℝ, H (x : ℂ)).re := integral_re hH_in.2.1
    have hre_eq : (fun u : ℝ => ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re *
        Real.exp (0 * u)) = fun x : ℝ => (H (x : ℂ)).re := by
      ext x; simp [H, Complex.add_re]; ring
    rw [← hre, ← hre_eq]
    exact hH_L 0 le_rfl
  obtain ⟨C_H, ν_H, hC_H, hb_H⟩ := hH_in.2.2.1
  have hH_shell_d : ∀ t ∈ D.S, t ≠ D.tm → (H (t : ℂ)).re ≤ 0 := fun t ht htm => by
    have ht' := hH_shell t ht htm
    have heq : ((G.P_inf (t : ℂ) + G.Q_inf (t : ℂ)) - 2 * G.Q_inf (t : ℂ)).re = (H (t : ℂ)).re := by
      simp [H, Complex.add_re]; ring
    linarith
  have hH_left_d : ∀ u : ℝ, u ≤ D.tm → (H (u : ℂ)).re ≤ 0 := fun u hu => by
    have := hH_left u (hu.trans heq_tm.symm.le)
    have : ((G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)) - 2 * G.Q_inf (u : ℂ)).re = (H (u : ℂ)).re := by
      simp [H, Complex.add_re]; ring
    linarith
  obtain ⟨b, _, hH_eq, hnz⟩ := D.uniqueness hH_in.1 hH_in.2.1 hC_H hb_H hH_in.2.2.2 hHint_re
    hH_shell_d hH_left_d
  obtain ⟨hb_pos, _, _⟩ := hnz hH_ne
  have hS_int_le : ∫ u : ℝ, (S (u : ℂ)).re ≤ 0 := by
    have hSeq : (fun u : ℝ => (S (u : ℂ)).re) =
        fun (u : ℝ) => 2 * (G.Q_inf (u : ℂ)).re - b * (D.G (u : ℂ)).re := by
      ext u
      have hu : (S (u : ℂ)).re - 2 * (G.Q_inf (u : ℂ)).re = (H (u : ℂ)).re := by
        simp [S, H, Complex.add_re]; ring
      rw [hH_eq (u : ℂ), Complex.neg_re, Complex.re_ofReal_mul] at hu
      linarith
    have hQ2_re_int : Integrable (fun u : ℝ => 2 * (G.Q_inf (u : ℂ)).re) := by
      simpa using G.Q_inf_in.2.1.re.const_mul 2
    have hD_re_int : Integrable (fun u : ℝ => (D.G (u : ℂ)).re) := by simpa using D.G_int.re
    have hD_re_zero : ∫ u : ℝ, (D.G (u : ℂ)).re = 0 := by
      have hre : ∫ u : ℝ, (D.G (u : ℂ)).re = (∫ u : ℝ, D.G (u : ℂ)).re := integral_re D.G_int
      rw [hre, D.G_integral_zero, Complex.zero_re]
    rw [hSeq, integral_sub hQ2_re_int (hD_re_int.const_mul b),
      integral_const_mul b (fun (u : ℝ) => (D.G (u : ℂ)).re), hD_re_zero, mul_zero, sub_zero]
    exact hQ2_int_real
  have hS_zero : ∀ u : ℝ, (S (u : ℂ)).re = 0 := by
    have hS_re_int : Integrable (fun u : ℝ => (S (u : ℂ)).re) := by simpa using hS_in.2.1.re
    have hS_nn' : ∀ u : ℝ, 0 ≤ (S (u : ℂ)).re := hS_nn
    have h0 : ∫ u : ℝ, (S (u : ℂ)).re = 0 := le_antisymm hS_int_le (integral_nonneg hS_nn')
    have hae : (fun u : ℝ => (S (u : ℂ)).re) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg hS_nn' hS_re_int).mp h0
    exact congrFun ((Continuous.ae_eq_iff_eq volume hS_in.to_polyLeftAiryRightBound.1 continuous_const).mp hae)
  have hQ2_eq : ∀ u : ℝ, 2 * (G.Q_inf (u : ℂ)).re = b * (D.G (u : ℂ)).re := by
    intro u
    have h1 : (S (u : ℂ)).re - 2 * (G.Q_inf (u : ℂ)).re = (H (u : ℂ)).re := by
      simp [S, H, Complex.add_re]; ring
    rw [hS_zero u, hH_eq (u : ℂ), Complex.neg_re, Complex.re_ofReal_mul] at h1
    linarith
  have hb_mul_eq : b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ = 1 := by
    have hle1 : b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ ≤ 1 := by
      have heq : (fun u : ℝ => ‖(2 : ℂ) * G.Q_inf (u : ℂ)‖) = fun (u : ℝ) => b * ‖D.G (u : ℂ)‖ := by
        ext u
        have hc1 : G.Q_inf (u : ℂ) = ((G.Q_inf (u : ℂ)).re : ℂ) := Complex.ext rfl (G.Q_inf_in.2.2.2 u)
        have hc2 : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
        rw [show (2 : ℂ) * G.Q_inf (u : ℂ) = ((2 * (G.Q_inf (u : ℂ)).re : ℝ) : ℂ) from by
          rw [hc1]; push_cast; rfl]
        rw [Complex.norm_real, Real.norm_eq_abs, hQ2_eq u, abs_mul, abs_of_pos hb_pos]
        congr 1; conv_rhs => rw [hc2, Complex.norm_real, Real.norm_eq_abs]
      rw [← integral_const_mul, ← heq]
      exact hQ2_l1
    have hge1 : 1 ≤ b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
      have hneg_eq : (fun u : ℝ => max (-((2 : ℂ) * G.Q_inf (u : ℂ)).re) 0) =
          fun (u : ℝ) => b * ((‖D.G (u : ℂ)‖ - (D.G (u : ℂ)).re) / 2) := by
        ext u
        have hre : ((2 : ℂ) * G.Q_inf (u : ℂ)).re = b * (D.G (u : ℂ)).re := by
          simpa using hQ2_eq u
        have hc2 : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
        have hnr : ‖D.G (u : ℂ)‖ = |(D.G (u : ℂ)).re| := by
          conv_lhs => rw [hc2, Complex.norm_real, Real.norm_eq_abs]
        have hmax_mul : max (-(b * (D.G (u : ℂ)).re)) 0 = b * max (-(D.G (u : ℂ)).re) 0 := by
          rcases le_total ((D.G (u : ℂ)).re) 0 with hx | hx
          · rw [max_eq_left (by nlinarith), max_eq_left (neg_nonneg.mpr hx)]; ring
          · rw [max_eq_right (by nlinarith), max_eq_right (neg_nonpos.mpr hx), mul_zero]
        rw [hre, hmax_mul, hnr, ← abs_neg ((D.G (u : ℂ)).re), posPart_eq_abs_add_div_two]
        ring
      have hGre_int : Integrable (fun u : ℝ => (D.G (u : ℂ)).re) := by simpa using D.G_int.re
      have hint_b : Integrable (fun u : ℝ => b * ((‖D.G (u : ℂ)‖ - (D.G (u : ℂ)).re) / 2)) :=
        ((D.G_int.norm.sub hGre_int).div_const 2).const_mul b
      have hnr : ∀ u : ℝ, ‖D.G (u : ℂ)‖ = |(D.G (u : ℂ)).re| := fun u => by
        have hc2 : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
        conv_lhs => rw [hc2, Complex.norm_real, Real.norm_eq_abs]
      have h12 : (1 / 2 : ℝ) ≤ ∫ u : ℝ, b * ((‖D.G (u : ℂ)‖ - (D.G (u : ℂ)).re) / 2) := by
        have hsub : ∫ u in Ioi G.u_ustar, b * ((‖D.G (u : ℂ)‖ - (D.G (u : ℂ)).re) / 2) ≤
            ∫ u : ℝ, b * ((‖D.G (u : ℂ)‖ - (D.G (u : ℂ)).re) / 2) :=
          setIntegral_le_integral hint_b (Eventually.of_forall fun u =>
            mul_nonneg hb_pos.le (by
              have hpp := posPart_eq_abs_add_div_two (-(D.G (u : ℂ)).re)
              rw [abs_neg, ← hnr u] at hpp
              linarith [le_max_right (-(D.G (u : ℂ)).re) 0]))
        have hsub1 : ∫ u in Ioi G.u_ustar, max (-(2 * G.Q_inf (u : ℂ)).re) 0 =
            ∫ u in Ioi G.u_ustar, b * ((‖D.G (u : ℂ)‖ - (D.G (u : ℂ)).re) / 2) :=
          setIntegral_congr_fun measurableSet_Ioi fun u _ => congrFun hneg_eq u
        exact (hQ2_tail_neg.trans_eq hsub1).trans hsub
      have hD_re_zero : ∫ u : ℝ, (D.G (u : ℂ)).re = 0 := by
        have hre : ∫ u : ℝ, (D.G (u : ℂ)).re = (∫ u : ℝ, D.G (u : ℂ)).re := integral_re D.G_int
        rw [hre, D.G_integral_zero, Complex.zero_re]
      rw [integral_const_mul, integral_div, integral_sub D.G_int.norm hGre_int, hD_re_zero,
        sub_zero] at h12
      linarith
    exact le_antisymm hle1 hge1
  have hb_eq : b = (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹ :=
    eq_inv_of_mul_eq_one_left hb_mul_eq
  have hQ2_normG : ∀ u : ℝ, 2 * (G.Q_inf (u : ℂ)).re = D.normG u := fun u => by
    rw [hQ2_eq u, hb_eq, ShellHBData.normG, div_eq_inv_mul]
  have hQ2_pt : ∀ u : ℝ, Tendsto (fun k => Q2k k u) atTop (𝓝 (D.normG u)) := fun u => by
    simpa [hQ2_normG u] using hQ2_lim u
  have hQ2_l1_lim : Tendsto (fun k => ∫ u : ℝ, |Q2k k u - D.normG u|) atTop (𝓝 0) := by
    have hnorm_lim : Tendsto (fun k => ∫ u : ℝ, ‖Q2k k u‖) atTop (𝓝 (∫ u : ℝ, ‖D.normG u‖)) := by
      simp_rw [Real.norm_eq_abs, hQ2k_l1, D.normG_abs_integral]
      exact tendsto_const_nhds
    simpa [Real.norm_eq_abs] using tendsto_integral_norm_sub_of_tendsto_ae
      (Eventually.of_forall hQ2_int) D.normG_integrable (Eventually.of_forall hQ2_pt) hnorm_lim
  have hS_l1_lim : Tendsto (fun k =>
      shellMass (G.c (G.φ k)) (fun Δ => G.p (G.φ k) Δ + G.q (G.φ k) Δ) /
        shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ)) atTop (𝓝 0) := by
    have hmass_eq : ∀ k, shellMass (G.c (G.φ k)) (fun Δ => G.p (G.φ k) Δ + G.q (G.φ k) Δ) /
        shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) = ∫ u : ℝ, Sk k u := by
      intro k
      have habs : (fun u => |Sk k u|) = Sk k := funext fun u => abs_of_nonneg (hSk_nn k u)
      have heq : (fun u => |Sk k u|) = fun u =>
          |shellWindowProfile (G.c (G.φ k)) (fun Δ => G.p (G.φ k) Δ + G.q (G.φ k) Δ) u| /
            shellMass (G.c (G.φ k)) (fun Δ => 2 * G.q (G.φ k) Δ) := by
        ext u; rw [hSk_eq, abs_div, abs_of_pos (hf_pos k)]
      rw [← habs, heq, integral_div, integral_abs_shellWindowProfile (G.c_pos _)]
    simp_rw [hmass_eq]
    have htail_S : Tendsto (fun k => ∫ u in Ioi b₀, Sk k u) atTop (𝓝 0) := by
      have hdomS := integrableOn_airyEnv_Ici C₀ ν₀ 0 b₀ hC₀
      have h0 : ∫ u in Ioi b₀, (0 : ℝ) = 0 := by simp
      rw [← h0]
      refine tendsto_integral_of_dominated_convergence
        (fun u => C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (0 * u))
        (fun k => (hS_int k).aestronglyMeasurable.restrict)
        (hdomS.mono_set Ioi_subset_Ici_self) ?_ ?_
      · intro k
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
        have hbd := htail_env k u (mem_Ioi.mp hu).le
        rw [Real.norm_of_nonneg (hSk_nn k u), zero_mul, Real.exp_zero, mul_one]
        exact (le_abs_self _).trans ((abs_add_le _ _).trans hbd)
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
        simpa [S, hS_zero u] using hS_lim u
    have hmin_lim : Tendsto (fun k => ∫ u in Iic b₀, min (Sk k u) |D.normG u|) atTop (𝓝 0) := by
      have h0 : ∫ u in Iic b₀, (0 : ℝ) = 0 := by simp
      rw [← h0]
      refine tendsto_integral_of_dominated_convergence (fun u => |D.normG u|)
        (fun k => ((hS_int k).aestronglyMeasurable.inf D.normG_integrable.abs.aestronglyMeasurable).restrict)
        D.normG_integrable.abs.integrableOn ?_ ?_
      · intro k
        refine ae_restrict_of_forall_mem measurableSet_Iic fun u _ => ?_
        rw [Real.norm_of_nonneg (le_min (hSk_nn k u) (abs_nonneg _))]
        exact min_le_right _ _
      · refine ae_restrict_of_forall_mem measurableSet_Iic fun u _ => ?_
        have hS_eq : (G.P_inf (u : ℂ) + G.Q_inf (u : ℂ)).re = 0 := by simpa [S] using hS_zero u
        have hS_lim0 : Tendsto (fun k => Sk k u) atTop (𝓝 0) := hS_eq ▸ hS_lim u
        have hl : Tendsto (fun k => min (Sk k u) |D.normG u|) atTop (𝓝 (min 0 |D.normG u|)) :=
          hS_lim0.min tendsto_const_nhds
        simpa [min_eq_left (abs_nonneg (D.normG u))] using hl
    have hbound : ∀ᶠ k in atTop,
        0 ≤ ∫ u : ℝ, Sk k u ∧
        ∫ u : ℝ, Sk k u ≤ (∫ u in Iic b₀, min (Sk k u) |D.normG u|) +
          (∫ u : ℝ, |Q2k k u - D.normG u|) + ∫ u in Ioi b₀, Sk k u := by
      filter_upwards [hev_b₀] with k hk
      refine ⟨integral_nonneg (hSk_nn k), ?_⟩
      have hsp := integral_add_compl (measurableSet_Iic (a := b₀)) (hS_int k)
      rw [compl_Iic] at hsp
      have hle_Iic : ∫ u in Iic b₀, Sk k u ≤
          (∫ u in Iic b₀, min (Sk k u) |D.normG u|) + ∫ u : ℝ, |Q2k k u - D.normG u| := by
        have hpt_le : ∀ u ∈ Iic b₀, Sk k u ≤ min (Sk k u) |D.normG u| + |Q2k k u - D.normG u| := by
          intro u hu
          have hSQ : Sk k u ≤ Q2k k u := by
            have hH0 : Hk k u ≤ 0 := by
              rw [hHk_eq]
              exact div_nonpos_of_nonpos_of_nonneg
                (G.h_nonpos_tail (G.φ k) u ((mem_Iic.mp hu).trans hk)) (hf_pos k).le
            dsimp [Q2k, Sk, Hk] at hH0 ⊢; linarith
          rcases le_total (Sk k u) |D.normG u| with hsm | hlg
          · rw [min_eq_left hsm]; linarith [abs_nonneg (Q2k k u - D.normG u)]
          · rw [min_eq_right hlg]
            have h1 : Q2k k u ≤ |Q2k k u| := le_abs_self _
            have h2 : |Q2k k u| - |D.normG u| ≤ |Q2k k u - D.normG u| := abs_sub_abs_le_abs_sub _ _
            linarith
        have hmin_i : Integrable (fun u => min (Sk k u) |D.normG u|) :=
          D.normG_integrable.abs.mono' (AEStronglyMeasurable.inf
            (hS_int k).aestronglyMeasurable D.normG_integrable.abs.aestronglyMeasurable)
            (Eventually.of_forall fun u => by
              rw [Real.norm_of_nonneg (le_min (hSk_nn k u) (abs_nonneg _))]; exact min_le_right _ _)
        have hdiff_i : Integrable (fun u => |Q2k k u - D.normG u|) := by
          simpa only [Pi.sub_apply] using ((hQ2_int k).sub D.normG_integrable).abs
        have hm := setIntegral_mono_on (hS_int k).integrableOn (hmin_i.add hdiff_i).integrableOn
          measurableSet_Iic hpt_le
        dsimp only [Pi.add_apply] at hm
        rw [integral_add hmin_i.integrableOn hdiff_i.integrableOn] at hm
        have hIic_le : ∫ u in Iic b₀, |Q2k k u - D.normG u| ≤ ∫ u : ℝ, |Q2k k u - D.normG u| :=
          setIntegral_le_integral hdiff_i (Eventually.of_forall fun _ => abs_nonneg _)
        linarith
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using (hmin_lim.add hQ2_l1_lim).add htail_S)
      (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
  refine ⟨fun u => by simpa [Q2k, hQ2k_eq] using hQ2_pt u,
    by simpa [Q2k, hQ2k_eq] using hQ2_l1_lim,
    hS_l1_lim,
    fun y hy => ?_⟩
  have hLy := (one_profile_threshold_le_and_endpoint_iff D).1
  have hL0 : 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y :=
    ((one_profile_threshold_le_and_endpoint_iff D).2.mp (heq_tm ▸ hone)) y hy
  have hneg : airyLaplace (fun u => -(D.G (u : ℂ)).re) y =
      -airyLaplace (fun u => (D.G (u : ℂ)).re) y := by
    unfold airyLaplace; simp_rw [neg_mul]; rw [integral_neg, mul_neg]
  linarith

/-- **Conditional strict-gap step of Theorem `H.14` (`thm:ce-shell-gap`)**: for a single
`G : ShellGapPackage D`, if `∃ y > 0, ℒ_y(-G_N) < 0` (which holds whenever `Even D.S.card`
by `even_m_laplace_sign`), then `u_* < t_m` and the packaged convergent threshold satisfies
`lim_k (-u_thresh k / β₁) > -t_m / β₁`. (Full infimal `R_d^{CE}` quantification and
`o(c^{1/3})` shell offsets in `(eq:strict-gap)` remain external.) -/
theorem theorem_H14_strict_gap (D : ShellHBData) (G : ShellGapPackage D)
    (hneg : ∃ y : ℝ, 0 < y ∧ airyLaplace (fun u => -(D.G (u : ℂ)).re) y < 0) :
    G.u_ustar < D.tm ∧
    (-D.tm / shellBeta1 < -G.u_ustar / shellBeta1) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, -D.tm / shellBeta1 + δ ≤ -(G.u_thresh k) / shellBeta1 := by
  obtain ⟨_, _, _, hle, hcollapse⟩ := theorem_H14_subseq_bounds D G
  have hlt : G.u_ustar < D.tm := by
    refine lt_of_le_of_ne hle fun heq => ?_
    obtain ⟨_, _, _, hLle⟩ := hcollapse heq
    obtain ⟨y, hy, hyneg⟩ := hneg
    have hLy := hLle y hy
    have hLneg : airyLaplace (fun u => -(D.G (u : ℂ)).re) y =
        -airyLaplace (fun u => (D.G (u : ℂ)).re) y := by
      unfold airyLaplace; simp_rw [neg_mul]; rw [integral_neg, mul_neg]
    linarith
  have hs_gt : -D.tm / shellBeta1 < -G.u_ustar / shellBeta1 :=
    div_lt_div_of_pos_right (neg_lt_neg hlt) shellBeta1_pos
  let δ := (-G.u_ustar / shellBeta1 - -D.tm / shellBeta1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hs_tend : Tendsto (fun k => -(G.u_thresh k) / shellBeta1) atTop (𝓝 (-G.u_ustar / shellBeta1)) :=
    G.u_thresh_tendsto.neg.div_const shellBeta1
  have hev : ∀ᶠ k in atTop, -D.tm / shellBeta1 + δ ≤ -(G.u_thresh k) / shellBeta1 := by
    have hlt_lim : -D.tm / shellBeta1 + δ < -G.u_ustar / shellBeta1 := by dsimp [δ]; linarith
    exact (hs_tend.eventually (eventually_gt_nhds hlt_lim)).mono fun _ h => h.le
  exact ⟨hlt, hs_gt, δ, hδ, hev⟩


/-- info: 'FormalResearch.SignUncertainty.shell_reduction_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shell_reduction_pointwise

/-- info: 'FormalResearch.SignUncertainty.shell_reduction_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shell_reduction_lower

/-- info: 'FormalResearch.SignUncertainty.theorem_H14_subseq_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_H14_subseq_bounds

/-- info: 'FormalResearch.SignUncertainty.theorem_H14_strict_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_H14_strict_gap

end FormalResearch.SignUncertainty
