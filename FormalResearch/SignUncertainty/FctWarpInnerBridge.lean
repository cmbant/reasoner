/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpOuterIbp
public import FormalResearch.SignUncertainty.FctInnerConcrete
public import FormalResearch.SignUncertainty.FctInnerB2
public import FormalResearch.SignUncertainty.FctInnerJ0
public import FormalResearch.SignUncertainty.FctWarpFJClass

/-!
# Inner change-of-variables bridge for `fct:warp-asymp` (1)

Paper I (`constant_terms_five.tex`), Proposition FCT.5 (1), Step 2:
extends symbols supported inside `[0, 2.95 c^{1/12}] ⊂ [0, U_c]` by zero to `[0, ∞)`,
identifies their Abel limit `fctS` with the `Ioo 0 (fctUc c)` integral, proves the
diffeomorphism and CFU cubic normal form `c Φ̃(T(u); L₁, α) = -(û u + u³ / 12)`,
and bridges `fctWarpIntegrand`, `fctWarpIntegrandDerivAlpha`, `fctWarpIntegrandDerivL`
on the inner zone `(0, T(U_c))` to `fctS`.

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff
open FormalResearch.CohnElkies
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctPhiKill

namespace FormalResearch.SignUncertainty

noncomputable def warpTauStar : ℝ := (12 / π ^ 2) ^ (1 / 3 : ℝ)

noncomputable def warpC2Star : ℝ := (2 : ℝ) ^ (-(4 / 3 : ℝ)) * warpTauStar ^ 2

/-- Normalization constant `N₀ = 12 · 2^{1/3} c^{1/6} / (π² √τ_*)` of `(fct:I-asymp)`. -/
noncomputable def warpN0 (c : ℝ) : ℝ :=
  12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) / (π ^ 2 * Real.sqrt warpTauStar)

noncomputable def warpNu (K4 ε c L1 α : ℝ) : ℝ :=
  Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar)

noncomputable def warpC2 (K4 ε c L1 α : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(4 / 3 : ℝ)) * concreteInnerV K4 ε c L1 α 0 ^ 2

/-- Extension by `0` beyond `fctUc c`. -/
noncomputable def extUc (c : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  if u ≤ fctUc c then f u else 0

lemma extUc_eqOn (c : ℝ) (f : ℝ → ℂ) : EqOn (extUc c f) f (Icc 0 (fctUc c)) := by
  intro u hu; simp [extUc, hu.2]

lemma extUc_zero_of_gt {c u : ℝ} (f : ℝ → ℂ) (hu : fctUc c < u) : extUc c f u = 0 := by
  simp [extUc, not_le.mpr hu]

lemma extUc_mem_symCls {c : ℝ} {n : ℕ} {p B : ℝ} {f : ℝ → ℂ}
    (hc : 1 ≤ c) (hB : 0 ≤ B)
    (hf : FctSymClsOn (Icc 0 (fctUc c)) n p B f)
    (hzero : ∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c), f u = 0) :
    FctSymCls n p B (extUc c f) := by
  have hc0 : 0 < c := by linarith
  have hx12 : 0 < c ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hc0 _
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  have hDi : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  set ucut : ℝ := 2.95 * c ^ ((1 : ℝ) / 12)
  have hucut_pos : 0 < ucut := by positivity
  have hucut_lt : ucut < fctUc c := by
    dsimp only [ucut, fctUc]; linarith only [hx12]
  have hIco_eq : Ici (0 : ℝ) ∩ Ioo (-1 : ℝ) (fctUc c) = Ico (0 : ℝ) (fctUc c) := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioo, mem_Ico]
    exact ⟨fun ⟨hx0, _, hxc⟩ => ⟨hx0, hxc⟩, fun ⟨hx0, hxc⟩ => ⟨hx0, by linarith only [hx0], hxc⟩⟩
  have h0_oi : ∀ x ∈ Ioi ucut, extUc c f x = 0 := by
    intro x hx
    rcases le_or_gt x (fctUc c) with hxle | hxgt
    · simp only [extUc, hxle, ↓reduceIte]
      exact hzero x ⟨hx.out.le, hxle⟩
    · exact extUc_zero_of_gt f hxgt
  have hcd_oi : ContDiffOn ℝ n (extUc c f) (Ioi ucut) :=
    (contDiffOn_const (c := (0 : ℂ))).congr (fun x hx => h0_oi x hx)
  have hcd_loc : ∀ u ∈ Ici (0 : ℝ), ContDiffWithinAt ℝ n (extUc c f) (Ici 0) u := by
    intro u hu
    rcases lt_or_ge u (fctUc c) with hlt | hge
    · have hU1 : Ioo (-1 : ℝ) (fctUc c) ∈ 𝓝 u := isOpen_Ioo.mem_nhds ⟨by linarith only [hu.out], hlt⟩
      rw [← contDiffWithinAt_inter hU1, hIco_eq]
      have hf' : ContDiffWithinAt ℝ n f (Ico (0 : ℝ) (fctUc c)) u :=
        (hf.1.mono Ico_subset_Icc_self).contDiffWithinAt ⟨hu.out, hlt⟩
      exact hf'.congr (fun x hx => by simp [extUc, hx.2.le]) (by simp [extUc, hlt.le])
    · have hu_gt : ucut < u := lt_of_lt_of_le hucut_lt hge
      exact (hcd_oi.contDiffAt (isOpen_Ioi.mem_nhds hu_gt)).contDiffWithinAt
  have hcd : ContDiffOn ℝ n (extUc c f) (Ici 0) := fun u hu => hcd_loc u hu
  refine ⟨hcd, fun r hr u hu => ?_⟩
  rcases lt_or_ge u (fctUc c) with hlt | hge
  · have hDco : UniqueDiffOn ℝ (Ico (0 : ℝ) (fctUc c)) := uniqueDiffOn_Ico 0 (fctUc c)
    have hu_co : u ∈ Ico (0 : ℝ) (fctUc c) := ⟨hu.out, hlt⟩
    have hcon : iteratedFDerivWithin ℝ r (extUc c f) (Ico (0 : ℝ) (fctUc c)) u =
        iteratedFDerivWithin ℝ r f (Ico (0 : ℝ) (fctUc c)) u :=
      iteratedFDerivWithin_congr (fun x hx => by simp [extUc, hx.2.le]) hu_co r
    rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      ← iteratedFDerivWithin_subset Ico_subset_Ici_self hDco hDi (hcd.of_le (by exact_mod_cast hr)) hu_co,
      hcon,
      iteratedFDerivWithin_subset Ico_subset_Icc_self hDco hDu (hf.1.of_le (by exact_mod_cast hr)) hu_co,
      norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    exact hf.2 r hr u ⟨hu.out, hlt.le⟩
  · have hu_gt : ucut < u := lt_of_lt_of_le hucut_lt hge
    have hDoi : UniqueDiffOn ℝ (Ioi ucut) := isOpen_Ioi.uniqueDiffOn
    have hsub_oi : Ioi ucut ⊆ Ici (0 : ℝ) := fun x hx => le_of_lt (lt_trans hucut_pos hx)
    have hcon : iteratedFDerivWithin ℝ r (extUc c f) (Ioi ucut) u =
        iteratedFDerivWithin ℝ r (fun _ : ℝ => (0 : ℂ)) (Ioi ucut) u :=
      iteratedFDerivWithin_congr h0_oi hu_gt r
    have hzero_d : ‖iteratedFDerivWithin ℝ r (fun _ : ℝ => (0 : ℂ)) (Ioi ucut) u‖ = 0 := by
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp
      · rw [iteratedFDerivWithin_const_of_ne hr0.ne']; simp
    rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      ← iteratedFDerivWithin_subset hsub_oi hDoi hDi (hcd.of_le (by exact_mod_cast hr)) hu_gt,
      hcon, hzero_d]
    have h1u : 0 < 1 + u := by linarith only [hu.out]
    exact mul_nonneg hB (Real.rpow_pos_of_pos h1u _).le

lemma extUc_chi_symCls {c : ℝ} {n : ℕ} {p B C_χ : ℝ} {V : ℝ → ℝ} {f : ℝ → ℂ}
    (hc : 1 ≤ c) (hB : 0 ≤ B) (hCχ : 0 ≤ C_χ)
    (hχ_sym : FctSymClsOn (Icc 0 (fctUc c)) n 0 C_χ (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ)))
    (hχ_zero : ∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c), fctInnerChi outerChiIn c V u = 0)
    (hf : FctSymClsOn (Icc 0 (fctUc c)) n p B f) :
    FctSymCls n p (2 ^ n * C_χ * B) (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * f u)) := by
  have hc0 : 0 < c := by linarith
  have hDu := uniqueDiffOn_Icc (fctUc_pos hc0)
  have hprod := (hχ_sym.mul Icc_subset_Ici_self hDu hf).mono_p Icc_subset_Ici_self (by positivity)
    (by norm_num : (0 : ℝ) + p ≤ p)
  refine extUc_mem_symCls hc (by positivity) hprod fun u hu => ?_
  rw [hχ_zero u hu]; simp

noncomputable def chiExt (c : ℝ) (V : ℝ → ℝ) (u : ℝ) : ℂ :=
  extUc c (fun x => ((fctInnerChi outerChiIn c V x : ℝ) : ℂ)) u

lemma fctS_extUc_eq {c û : ℝ} {f : ℝ → ℂ} (hc : 0 < c)
    (hf_cont : ContinuousOn f (Icc 0 (fctUc c))) :
    FctSLimit û (extUc c f)
      (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
        ∫ u in Ioo (0 : ℝ) (fctUc c),
          ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) * f u) := by
  have hUc0 : 0 < fctUc c := fctUc_pos hc
  obtain ⟨M_f, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont
  have hMf_nn : 0 ≤ M_f := (norm_nonneg (f 0)).trans (hMf 0 ⟨le_rfl, hUc0.le⟩)
  let bound : ℝ → ℝ := fun u => M_f * u ^ (-(1 / 2 : ℝ))
  have h_int_rpow : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioo 0 (fctUc c)) := by
    have hioc : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioc 0 (fctUc c)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hUc0.le).mp (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    exact hioc.mono_set Ioo_subset_Ioc_self
  have hbound_int : IntegrableOn bound (Ioo 0 (fctUc c)) := h_int_rpow.const_mul M_f
  let F : ℝ → ℝ → ℂ := fun ε u =>
    ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * f u
  have hF_meas : ∀ ε : ℝ, AEStronglyMeasurable (F ε) (volume.restrict (Ioo 0 (fctUc c))) := by
    intro ε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    have hrpow : ContinuousOn (fun u : ℝ => ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Ioo 0 (fctUc c)) :=
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne')
    have hexp : Continuous (fun u : ℝ =>
        Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ))) := by
      fun_prop
    exact (hrpow.mul hexp.continuousOn).mul (hf_cont.mono Ioo_subset_Icc_self)
  have hF_bd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂(volume.restrict (Ioo 0 (fctUc c))), ‖F ε u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
    dsimp only [F, bound]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _),
      Complex.norm_exp]
    have hre : (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)).re = -(ε * u ^ 2) := by
      rw [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re]; ring
    have hexp_le : Real.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)).re ≤ 1 := by
      rw [hre]; exact Real.exp_le_one_iff.mpr (by nlinarith [hε, sq_nonneg u])
    calc u ^ (-(1 / 2 : ℝ)) * Real.exp _ * ‖f u‖
        ≤ u ^ (-(1 / 2 : ℝ)) * 1 * M_f :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp_le (Real.rpow_nonneg hu.1.le _))
            (hMf u (Ioo_subset_Icc_self hu)) (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hu.1.le _) zero_le_one)
      _ = M_f * u ^ (-(1 / 2 : ℝ)) := by ring
  have hF_lim : ∀ᵐ u ∂(volume.restrict (Ioo 0 (fctUc c))), Tendsto (fun ε => F ε u) (𝓝[>] 0) (𝓝 (F 0 u)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun u _ => ?_
    have hcont : Continuous (fun ε : ℝ => F ε u) := by dsimp only [F]; fun_prop
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim_int := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hF_meas) hF_bd hbound_int hF_lim
  unfold FctSLimit
  have heq_eps : ∀ ε : ℝ, fctSEps û ε (extUc c f) =
      Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * ∫ u in Ioo (0 : ℝ) (fctUc c), F ε u := by
    intro ε
    unfold fctSEps
    congr 1
    have hdiff_zero : ∀ u ∈ Ioi (0 : ℝ) \ Ioc 0 (fctUc c),
        ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * extUc c f u = 0 := by
      intro u hu
      have hgt : fctUc c < u := by
        rcases le_or_gt u (fctUc c) with hle | hgt
        · exact absurd ⟨hu.1, hle⟩ hu.2
        · exact hgt
      rw [extUc_zero_of_gt f hgt, mul_zero]
    have hsub_int : ∫ u in Ioi (0 : ℝ),
        ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * extUc c f u =
        ∫ u in Ioc 0 (fctUc c),
        ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * extUc c f u :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hdiff_zero
    rw [hsub_int, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    dsimp only [F]; rw [extUc_eqOn c f (Ioo_subset_Icc_self hu)]
  have hlim_tot : Tendsto (fun ε : ℝ => fctSEps û ε (extUc c f)) (𝓝[>] 0)
      (𝓝 (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * ∫ u in Ioo (0 : ℝ) (fctUc c), F 0 u)) :=
    (tendsto_const_nhds.mul hlim_int).congr fun ε => (heq_eps ε).symm
  simpa only [F, zero_mul, Complex.ofReal_zero, sub_zero] using hlim_tot

lemma warpTauStar_ge : (1.06 : ℝ) ≤ warpTauStar := by
  have h1 := fctB2_theta_bounds.1
  have h2 := fctB2_two_rpow_neg23_le
  have h2p : (0 : ℝ) < (2 : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have htp : 0 < warpTauStar := Real.rpow_pos_of_pos (by positivity) _
  change (0.6723 : ℝ) ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) * warpTauStar at h1
  nlinarith

lemma fctInnerT_deriv_and_image {K4 ε c L1 α : ℝ}
    (hc0 : 0 < c) (hcKV : pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 0.001)
    (hVjets : FctVJets pbKV c (concreteInnerV K4 ε c L1 α))
    (hqΩ : (concreteEll1 ε c L1, (1 : ℝ), α) ∈ (concreteBoxS K4 ε c).Ω)
    (hVeq : ∀ Y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L1 α Y =
      (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), Y)) :
    let V := concreteInnerV K4 ε c L1 α
    let T := fctInnerT c V
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    StrictMonoOn T (Icc 0 (fctUc c)) ∧
    T '' Ioo 0 (fctUc c) = Ioo 0 (T (fctUc c)) ∧
    (1.98 * c ^ (-(1 / 4 : ℝ)) ≤ T (fctUc c) ∧ T (fctUc c) < 2 * c ^ (-(1 / 4 : ℝ))) ∧
    ∀ u ∈ Ioo 0 (fctUc c),
      HasDerivAt T ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
        (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1))) u ∧
      0 < (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
        (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1)) := by
  intro V T S q
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hτ₁0 : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hY_mem : ∀ u ∈ Icc 0 (fctUc c), fctInnerY c u ∈ Icc (0 : ℝ) 3.5 := by
    intro u hu
    refine ⟨by unfold fctInnerY; have := hu.1; positivity, ?_⟩
    have h43 := fctB2_two_rpow_neg43_le
    have hx12 : 0 < c ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hc0 _
    have hc_pow : c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2 = 1 := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]
      norm_num
    have hu2 : u ^ 2 ≤ (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 :=
      pow_le_pow_left₀ hu.1 hu.2 2
    unfold fctInnerY
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
        ≤ 0.3969 * c ^ (-(1 / 6 : ℝ)) * (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := by gcongr
      _ = (0.3969 * 2.96 ^ 2) * (c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2) := by ring
      _ = 0.3969 * 2.96 ^ 2 := by rw [hc_pow, mul_one]
      _ ≤ 3.5 := by norm_num
  have hSV_cd : ContDiffOn ℝ 16 S.V (S.Ω ×ˢ Yint) := (S.V_jc (by norm_num : (4 : ℝ) ≤ 4)).1
  have hV_deriv : ∀ Y ∈ Ioo (0 : ℝ) 3.5, HasDerivAt V (fderiv ℝ S.V (q, Y) (0, 1)) Y ∧
      1.05 ≤ V Y ∧ |fderiv ℝ S.V (q, Y) (0, 1)| ≤ 0.001 := by
    intro Y hY
    have hY36 : Y ∈ Icc (0 : ℝ) 3.6 := ⟨hY.1.le, by linarith only [hY.2]⟩
    have hY_int : Y ∈ Yint := ⟨by linarith only [hY.1], by linarith only [hY.2]⟩
    have hO : IsOpen (S.Ω ×ˢ Yint) := S.hΩ.prod isOpen_Ioo
    have hS_at : DifferentiableAt ℝ S.V (q, Y) :=
      (hSV_cd.contDiffAt (hO.mem_nhds ⟨hqΩ, hY_int⟩)).differentiableAt (by norm_num)
    have hd_S : HasDerivAt (fun y => S.V (q, y)) (fderiv ℝ S.V (q, Y) (0, 1)) Y :=
      hS_at.hasFDerivAt.comp_hasDerivAt Y ((hasDerivAt_const Y q).prodMk (hasDerivAt_id Y))
    have hev : (fun y => S.V (q, y)) =ᶠ[𝓝 Y] V := by
      filter_upwards [isOpen_Ioo.mem_nhds hY] with y hy
      exact (hVeq y (Ioo_subset_Icc_self hy)).symm
    have hdV : HasDerivAt V (fderiv ℝ S.V (q, Y) (0, 1)) Y := hd_S.congr_of_eventuallyEq hev.symm
    have hVcd_pt : ContDiffAt ℝ 1 V Y := by
      have hcd := (hVjets.1.mono Ioo_subset_Icc_self).contDiffAt (isOpen_Ioo.mem_nhds ⟨hY.1, by linarith only [hY.2]⟩)
      exact hcd.of_le (by norm_num)
    have hdu : UniqueDiffOn ℝ (Icc (0 : ℝ) 3.6) := uniqueDiffOn_Icc (by norm_num)
    have hD_pt : deriv V Y = iteratedDerivWithin 1 V (Icc (0 : ℝ) 3.6) Y := by
      rw [← iteratedDeriv_one, ← iteratedDerivWithin_eq_iteratedDeriv hdu hVcd_pt hY36]
    have hV_bd : |V Y - warpTauStar| ≤ 0.001 := by
      have h0 := hVjets.2 0 (by norm_num) Y hY36
      rw [iteratedDerivWithin_zero] at h0
      exact h0.trans hcKV
    have hV'_bd : |fderiv ℝ S.V (q, Y) (0, 1)| ≤ 0.001 := by
      have e : V = fun z => (12 / π ^ 2) ^ (1 / 3 : ℝ) + (V z - (12 / π ^ 2) ^ (1 / 3 : ℝ)) := by
        ext z; ring
      have h1 : iteratedDerivWithin 1 V (Icc (0 : ℝ) 3.6) Y =
          iteratedDerivWithin 1 (fun z => V z - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc (0 : ℝ) 3.6) Y := by
        conv_lhs => rw [e]
        rw [iteratedDerivWithin_const_add (by norm_num : 0 < 1)]
      rw [← hdV.deriv, hD_pt, h1]
      exact (hVjets.2 1 (by norm_num) Y hY36).trans hcKV
    exact ⟨hdV, by linarith only [(abs_le.mp hV_bd).1, warpTauStar_ge], hV'_bd⟩
  have hT_deriv : ∀ u ∈ Ioo 0 (fctUc c),
      HasDerivAt T ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
        (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1))) u ∧
      0 < (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
        (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1)) := by
    intro u hu
    have hY_mem_u := hY_mem u (Ioo_subset_Icc_self hu)
    have hY_pos : 0 < fctInnerY c u := by unfold fctInnerY; have := hu.1; positivity
    have hY_lt : fctInnerY c u < 3.5 := by
      have h43 := fctB2_two_rpow_neg43_le
      have hc_pow : c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2 = 1 := by
        rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
      have hu2 : u ^ 2 < (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 :=
        pow_lt_pow_left₀ hu.2 hu.1.le (by norm_num)
      unfold fctInnerY
      calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
          < 0.3969 * c ^ (-(1 / 6 : ℝ)) * (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := by
            have : (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 ≤
                0.3969 * c ^ (-(1 / 6 : ℝ)) * u ^ 2 := by gcongr
            have hlt : 0.3969 * c ^ (-(1 / 6 : ℝ)) * u ^ 2 <
                0.3969 * c ^ (-(1 / 6 : ℝ)) * (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := by gcongr
            linarith
        _ = (0.3969 * 2.96 ^ 2) * (c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2) := by ring
        _ = 0.3969 * 2.96 ^ 2 := by rw [hc_pow, mul_one]
        _ ≤ 3.5 := by norm_num
    obtain ⟨hdV, hVlo, hV'bd⟩ := hV_deriv (fctInnerY c u) ⟨hY_pos, hY_lt⟩
    have hdY : HasDerivAt (fctInnerY c) ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (2 * u)) u := by
      unfold fctInnerY
      exact ((hasDerivAt_pow 2 u).const_mul _).congr_deriv (by ring)
    have hcompV : HasDerivAt (fun x => V (fctInnerY c x))
        (fderiv ℝ S.V (q, fctInnerY c u) (0, 1) * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (2 * u))) u :=
      hdV.comp u hdY
    have hlin : HasDerivAt (fun x : ℝ => (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * x)
        ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) u := by
      simpa using (hasDerivAt_id u).const_mul ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)))
    have hT_eq : T = fun x => ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * x) * V (fctInnerY c x) := rfl
    have hd_prod := hlin.mul hcompV
    have hsimp : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * V (fctInnerY c u) +
        (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u *
          (fderiv ℝ S.V (q, fctInnerY c u) (0, 1) *
            ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (2 * u))) =
        (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
          (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1)) := by
      unfold fctInnerY; ring
    have hdT : HasDerivAt T ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
        (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1))) u :=
      (hd_prod.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv hsimp
    have h2YV : |2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1)| ≤ 0.007 := by
      rw [abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_pos hY_pos]
      nlinarith only [hY_lt, (abs_le.mp hV'bd).1, (abs_le.mp hV'bd).2, hY_pos, abs_nonneg (fderiv ℝ S.V (q, fctInnerY c u) (0, 1)), hV'bd]
    have hpos_inner : 0 < V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1) := by
      linarith only [hVlo, (abs_le.mp h2YV).1]
    exact ⟨hdT, mul_pos (by positivity) hpos_inner⟩
  have hT_cont : ContinuousOn T (Icc 0 (fctUc c)) := by
    have hY_cont : Continuous (fctInnerY c) := by unfold fctInnerY; fun_prop
    have hV_comp : ContinuousOn (fun u => V (fctInnerY c u)) (Icc 0 (fctUc c)) :=
      hVjets.1.continuousOn.comp hY_cont.continuousOn fun u hu =>
        ⟨(hY_mem u hu).1, by linarith only [(hY_mem u hu).2]⟩
    exact ((continuous_const.mul continuous_id).continuousOn).mul hV_comp
  have hT_mono : StrictMonoOn T (Icc 0 (fctUc c)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 (fctUc c)) hT_cont fun u hu => ?_
    rw [interior_Icc] at hu
    rw [(hT_deriv u hu).1.deriv]
    exact (hT_deriv u hu).2
  have hT0 : T 0 = 0 := by dsimp only [T, fctInnerT]; ring
  have hT_img : T '' Ioo 0 (fctUc c) = Ioo 0 (T (fctUc c)) := by
    apply subset_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [← hT0]
      exact ⟨hT_mono ⟨le_rfl, hUc0.le⟩ (Ioo_subset_Icc_self hu) hu.1,
        hT_mono (Ioo_subset_Icc_self hu) ⟨hUc0.le, le_rfl⟩ hu.2⟩
    · intro τ hτ
      have hmem : τ ∈ Ioo (T 0) (T (fctUc c)) := by rwa [hT0]
      have hpre := intermediate_value_Ioo hUc0.le hT_cont hmem
      obtain ⟨u, hu, rfl⟩ := hpre
      exact ⟨u, hu, rfl⟩
  have hT_end : 1.98 * c ^ (-(1 / 4 : ℝ)) ≤ T (fctUc c) ∧ T (fctUc c) < 2 * c ^ (-(1 / 4 : ℝ)) := by
    have hYuc : fctInnerY c (fctUc c) ∈ Icc (0 : ℝ) 3.6 :=
      ⟨(hY_mem (fctUc c) ⟨hUc0.le, le_rfl⟩).1, by linarith only [(hY_mem (fctUc c) ⟨hUc0.le, le_rfl⟩).2]⟩
    have hVuc_bd : |V (fctInnerY c (fctUc c)) - warpTauStar| ≤ 0.001 := by
      have h0 := hVjets.2 0 (by norm_num) (fctInnerY c (fctUc c)) hYuc
      rw [iteratedDerivWithin_zero] at h0; exact h0.trans hcKV
    have hVuc_abs := abs_le.mp hVuc_bd
    have hratio := fctB2_inner_ratio hc0 V (fctUc c)
    have huc_x : fctUc c / c ^ ((1 : ℝ) / 12) = 2.96 := by
      dsimp only [fctUc]
      have hx0 : (c ^ ((1 : ℝ) / 12)) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
      field_simp [hx0]
    have hY_eq_uc : (2 : ℝ) ^ (-(4 / 3 : ℝ)) * (2.96 : ℝ) ^ 2 = fctInnerY c (fctUc c) := by
      unfold fctInnerY
      rw [← huc_x, div_pow]
      have hc12 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      rw [hc12, Real.rpow_neg hc0.le]; ring
    rw [huc_x, hY_eq_uc] at hratio
    change T (fctUc c) / c ^ (-(1 / 4 : ℝ)) = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * 2.96 * V (fctInnerY c (fctUc c)) at hratio
    have hθ := fctB2_theta_bounds
    have h223 := fctB2_two_rpow_neg23_le
    have h223_pos : 0 < (2 : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    change (0.6723 : ℝ) ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) * warpTauStar ∧ (2 : ℝ) ^ (-(2 / 3 : ℝ)) * warpTauStar ≤ 0.6724 at hθ
    have hrat_lo : 1.98 ≤ T (fctUc c) / c ^ (-(1 / 4 : ℝ)) := by
      rw [hratio]
      nlinarith only [hθ.1, h223, h223_pos, hVuc_abs.1]
    have hrat_hi : T (fctUc c) / c ^ (-(1 / 4 : ℝ)) < 2 := by
      rw [hratio]
      nlinarith only [hθ.2, h223, h223_pos, hVuc_abs.2]
    exact ⟨(le_div_iff₀ hτ₁0).mp hrat_lo, (div_lt_iff₀ hτ₁0).mp hrat_hi⟩
  exact ⟨hT_mono, hT_img, hT_end, hT_deriv⟩

lemma fctInnerT_phase_eq {K4 ε c L1 α u : ℝ}
    (hvalid : concreteBoxValid K4 ε c)
    (hp_dom : (L1, α) ∈ concretePhaseDom pbellMin ε c)
    (hKV : pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 0.001)
    (hVjets : FctVJets pbKV c (concreteInnerV K4 ε c L1 α))
    (hVeq : ∀ Y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L1 α Y =
      (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), Y))
    (hu : u ∈ Icc 0 (fctUc c))
    (hT_le : fctInnerT c (concreteInnerV K4 ε c L1 α) u ≤ 2 * c ^ (-(1 / 4 : ℝ))) :
    let S := concreteBoxS K4 ε c
    let û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
    c * concretePhiTilde K4 ε c (fctInnerT c (concreteInnerV K4 ε c L1 α) u) (L1, α) =
      -(û * u + u ^ 3 / 12) := by
  intro S û
  have hc0 : 0 < c := hvalid.2.2.1
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁0 : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  set V := concreteInnerV K4 ε c L1 α
  set τ := fctInnerT c V u
  set x := τ / τ₁
  set q := (concreteEll1 ε c L1, (1 : ℝ), α)
  set Y := fctInnerY c u
  obtain ⟨_, _, _, hSΩ, hSℓ, hSr, _, _, _, hdom_extra⟩ := concreteBox_spec hvalid
  have hphi_id := concreteBox_phi_id hvalid (lam := 1) (L1 := L1) (α := α) (x := x)
  have hqΩ : q ∈ S.Ω := by rw [hSΩ]; exact concreteEll1_mem_OmT hc0 pbellMin_pos.le hp_dom
  have hY35 : Y ∈ Icc (0 : ℝ) 3.5 := by
    refine ⟨by dsimp only [Y, fctInnerY]; have := hu.1; positivity, ?_⟩
    have h43 := fctB2_two_rpow_neg43_le
    have hx12 : 0 < c ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hc0 _
    have hc_pow : c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2 = 1 := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
    have hu2 : u ^ 2 ≤ (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
    dsimp only [Y, fctInnerY]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
        ≤ 0.3969 * c ^ (-(1 / 6 : ℝ)) * (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := by gcongr
      _ = (0.3969 * 2.96 ^ 2) * (c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2) := by ring
      _ = 0.3969 * 2.96 ^ 2 := by rw [hc_pow, mul_one]
      _ ≤ 3.5 := by norm_num
  have hY_int : Y ∈ Yint := ⟨by linarith only [hY35.1], by linarith only [hY35.2]⟩
  have hVY_eq : V Y = S.V (q, Y) := hVeq Y hY35
  have hVY_pos : 0 < V Y := by
    have h0 := hVjets.2 0 (by norm_num) Y ⟨hY35.1, by linarith only [hY35.2]⟩
    rw [iteratedDerivWithin_zero] at h0
    have htau := (abs_le.mp (h0.trans hKV)).1
    have hwg : (1.06 : ℝ) ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := warpTauStar_ge
    linarith only [htau, hwg]
  have hx0 : 0 ≤ x := div_nonneg (mul_nonneg (by have := hu.1; positivity) hVY_pos.le) hτ₁0.le
  have hτ24 : τ ≤ 2.4 * τ₁ := by linarith only [hT_le, hτ₁0]
  have hx24 : x ≤ 2.4 := (div_le_iff₀ hτ₁0).mpr hτ24
  have hx_eq : x = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u * V Y := by
    dsimp only [x, τ, fctInnerT]
    have hcc : c ^ (-(1 / 3 : ℝ)) / τ₁ = c ^ (-(1 / 12 : ℝ)) := by
      dsimp only [τ₁]; rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * V Y / τ₁
        = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ)) / τ₁) * u * V Y := by ring
      _ = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u * V Y := by rw [hcc]
  have hx2_eq : x ^ 2 = S.Z (q, Y) := by
    rw [← S.V_eq ⟨hqΩ, hY_int⟩, ← hVY_eq, hx_eq, mul_pow]
    have h2 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 = (2 : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hc2 : (c ^ (-(1 / 12 : ℝ))) ^ 2 = c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    dsimp only [Y, fctInnerY]
    rw [mul_pow, mul_pow, h2, hc2]
  have hx2_mem : x ^ 2 ∈ Ioo (-1 : ℝ) 6 := by rw [hx2_eq]; exact S.Z_mem ⟨hqΩ, hY_int⟩
  have hD_val : S.D (q, x ^ 2) = (V Y)⁻¹ := by
    rw [hx2_eq, hVY_eq]; exact (inv_inv _).symm
  have hS_id := S.hid (q := (q, x ^ 2)) ⟨hqΩ, hx2_mem⟩
  rw [hSℓ, hSr] at hS_id
  have hW_eq : x * S.D (q, x ^ 2) = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u := by
    rw [hD_val, hx_eq, mul_assoc, mul_inv_cancel₀ hVY_pos.ne', mul_one]
  have hτ_eq : τ₁ * x = τ := mul_div_cancel₀ τ hτ₁0.ne'
  have hphi_eq : concretePhiTilde K4 ε c τ (L1, α) =
      τ₁ ^ 3 * (S.A q * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u) -
        ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u) ^ 3 / 3) := by
    change concretePhiLambda K4 ε c 1 τ L1 α = _
    rw [← hτ_eq, ← hphi_id hx0 hx24]
    have hell : (L1 - ctTheta1 ε / c) / τ₁ ^ 2 = q.1 := by dsimp only [q]; unfold concreteEll1; rfl
    rw [hell] at *
    rw [show ((q.1, 1, α), x ^ 2) = (q, x ^ 2) from rfl, hS_id]
    have halg : x * (S.A q * S.D (q, x ^ 2) - x ^ 2 * S.D (q, x ^ 2) ^ 3 / 3) =
        S.A q * (x * S.D (q, x ^ 2)) - (x * S.D (q, x ^ 2)) ^ 3 / 3 := by ring
    dsimp only at hW_eq ⊢
    rw [halg, hW_eq]
  have hSA : S.A q = -û / (fctKappa c * τ₁ ^ 2) := by
    have hA := (hdom_extra (L1, α) hp_dom).2.2.1
    have hκ0 : fctKappa c ≠ 0 := (fctKappa_pos hc0).ne'
    have hτ20 : τ₁ ^ 2 ≠ 0 := (sq_pos_of_pos hτ₁0).ne'
    dsimp only [û]; rw [hA]; field_simp [hκ0, hτ20]; ring
  rw [hphi_eq, hSA]
  have h1 : c * (τ₁ ^ 3 * ((-û / (fctKappa c * τ₁ ^ 2)) *
      ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u))) = -(û * u) := by
    dsimp only [fctKappa, τ₁]
    have h2 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    have hc23 : c ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
    have hτ2 : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hτ3 : (c ^ (-(1 / 4 : ℝ))) ^ 3 = c ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [hτ2, hτ3]
    have hc_tot : c * c ^ (-(3 / 4 : ℝ)) * (c ^ (2 / 3 : ℝ))⁻¹ * (c ^ (-(1 / 2 : ℝ)))⁻¹ * c ^ (-(1 / 12 : ℝ)) = 1 := by
      rw [← Real.rpow_neg hc0.le, ← Real.rpow_neg hc0.le]
      conv_lhs => lhs; lhs; lhs; lhs; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
      norm_num
    have hmul : c * (c ^ (-(3 / 4 : ℝ)) * (-û / ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ))) *
        ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u))) =
        -(û * u) * (c * c ^ (-(3 / 4 : ℝ)) * (c ^ (2 / 3 : ℝ))⁻¹ * (c ^ (-(1 / 2 : ℝ)))⁻¹ * c ^ (-(1 / 12 : ℝ))) := by
      field_simp [h2, hc23, (Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))).ne']
    rw [hmul, hc_tot, mul_one]
  have h1' : c * (τ₁ ^ 3 * (-û / (fctKappa c * τ₁ ^ 2)) *
      ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u)) = -(û * u) := by
    rw [mul_assoc (τ₁ ^ 3)]; exact h1
  have h2 : c * (τ₁ ^ 3 * (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u) ^ 3 / 3)) = u ^ 3 / 12 := by
    have h23 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 3 = 1 / 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hc3 : (c ^ (-(1 / 12 : ℝ))) ^ 3 = c ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hτ3 : τ₁ ^ 3 = c ^ (-(3 / 4 : ℝ)) := by
      dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hc_tot : c * c ^ (-(3 / 4 : ℝ)) * c ^ (-(1 / 4 : ℝ)) = 1 := by
      conv_lhs => lhs; lhs; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    rw [mul_pow, mul_pow, h23, hc3, hτ3]
    calc c * (c ^ (-(3 / 4 : ℝ)) * (1 / 4 * c ^ (-(1 / 4 : ℝ)) * u ^ 3 / 3))
        = (c * c ^ (-(3 / 4 : ℝ)) * c ^ (-(1 / 4 : ℝ))) * (u ^ 3 / 12) := by ring
      _ = u ^ 3 / 12 := by rw [hc_tot, one_mul]
  have hfinal : c * (τ₁ ^ 3 * (-û / (fctKappa c * τ₁ ^ 2)) * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u) -
      τ₁ ^ 3 * (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)) * u) ^ 3 / 3)) = -(û * u + u ^ 3 / 12) := by
    rw [mul_sub, h1', h2]; ring
  rw [← hfinal]; ring

lemma fctInner_edge_jac_eq {K4 ε c L1 α u : ℝ}
    (hc0 : 0 < c) (hτ1_14 : c ^ (-(1 / 4 : ℝ)) ≤ 1 / 8)
    (hKV : pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 0.001)
    (hVjets : FctVJets pbKV c (concreteInnerV K4 ε c L1 α))
    (hVeq : ∀ Y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L1 α Y =
      (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), Y))
    (hu : u ∈ Ioo 0 (fctUc c))
    (hT_lt : fctInnerT c (concreteInnerV K4 ε c L1 α) u < 2 * c ^ (-(1 / 4 : ℝ))) :
    let V := concreteInnerV K4 ε c L1 α
    let T := fctInnerT c V
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    let T' := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
      (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1))
    warpN0 c * (π ^ 2 / 12) * Real.sqrt (uctMderiv (T u) / (2 * uctM (T u))) * T' =
      warpNu K4 ε c L1 α * u ^ (-(1 / 2 : ℝ)) *
        Jfun S.V fctH ((c ^ (-(1 / 4 : ℝ))) ^ 2) (q, fctInnerY c u) := by
  intro V T S q T'
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  set Y := fctInnerY c u
  have hY35 : Y ∈ Icc (0 : ℝ) 3.5 := by
    refine ⟨by dsimp only [Y, fctInnerY]; have := hu.1; positivity, ?_⟩
    have h43 := fctB2_two_rpow_neg43_le
    have hc_pow : c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2 = 1 := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
    have hu2 : u ^ 2 ≤ (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ hu.1.le hu.2.le 2
    dsimp only [Y, fctInnerY]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
        ≤ 0.3969 * c ^ (-(1 / 6 : ℝ)) * (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := by gcongr
      _ = (0.3969 * 2.96 ^ 2) * (c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2) := by ring
      _ = 0.3969 * 2.96 ^ 2 := by rw [hc_pow, mul_one]
      _ ≤ 3.5 := by norm_num
  have hVY_pos : 0 < V Y := by
    have h0 := hVjets.2 0 (by norm_num) Y ⟨hY35.1, by linarith only [hY35.2]⟩
    rw [iteratedDerivWithin_zero] at h0
    have htau := (abs_le.mp (h0.trans hKV)).1
    have hwg : (1.06 : ℝ) ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := warpTauStar_ge
    linarith only [htau, hwg]
  have hV0_pos : 0 < V 0 := by
    have h0 := hVjets.2 0 (by norm_num) 0 ⟨le_rfl, by norm_num⟩
    rw [iteratedDerivWithin_zero] at h0
    have htau := (abs_le.mp (h0.trans hKV)).1
    have hwg : (1.06 : ℝ) ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := warpTauStar_ge
    linarith only [htau, hwg]
  have hT_pos : 0 < T u := by
    dsimp only [T, fctInnerT]
    exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hc0 _)) hu.1) hVY_pos
  have hT_14 : T u < 1 / 4 := by linarith only [hT_lt, hτ1_14]
  rw [sqrt_uctMderiv_div_two_uctM hT_pos hT_14]
  have hT_eq : T u = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * V Y := rfl
  have hT_rpow : (T u) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) * u ^ (-(1 / 2 : ℝ)) * (V Y) ^ (-(1 / 2 : ℝ)) := by
    have h2p : 0 ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
    have hcp : 0 ≤ c ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
    rw [hT_eq, Real.mul_rpow (mul_nonneg (mul_nonneg h2p hcp) hu.1.le) hVY_pos.le,
      Real.mul_rpow (mul_nonneg h2p hcp) hu.1.le, Real.mul_rpow h2p hcp,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hc0.le]
    norm_num
  have hT_sq : (T u) ^ 2 = τ₁ ^ 2 * (Y * (S.V (q, Y)) ^ 2) := by
    rw [← hVeq Y hY35, hT_eq, mul_pow, mul_pow, mul_pow]
    have h2 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 = (2 : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hcτ : τ₁ ^ 2 * c ^ (-(1 / 6 : ℝ)) = (c ^ (-(1 / 3 : ℝ))) ^ 2 := by
      dsimp only [τ₁]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_mul hc0.le,
        ← Real.rpow_add hc0]
      norm_num
    dsimp only [Y, fctInnerY]
    rw [h2, ← hcτ]; ring
  have htauStar_pos : 0 < warpTauStar := by
    have : (1.06 : ℝ) ≤ warpTauStar := warpTauStar_ge; linarith
  have hNu_eq : warpNu K4 ε c L1 α = Real.sqrt (V 0) / Real.sqrt warpTauStar := by
    dsimp only [warpNu, V]; exact Real.sqrt_div hV0_pos.le warpTauStar
  have hS_V0 : S.V (q, 0) = V 0 := (hVeq 0 ⟨le_rfl, by norm_num⟩).symm
  have hS_VY : S.V (q, Y) = V Y := (hVeq Y hY35).symm
  have hV_half : (V Y) ^ (-(1 / 2 : ℝ)) * (V Y + 2 * Y * fderiv ℝ S.V (q, Y) (0, 1)) =
      Real.sqrt (V 0) * ((1 + 2 * (Y * fderiv ℝ S.V (q, Y) (0, 1)) * (S.V (q, Y))⁻¹) *
        (S.V (q, Y) * (S.V (q, 0))⁻¹) ^ (1 / 2 : ℝ)) := by
    rw [hS_V0, hS_VY, Real.mul_rpow hVY_pos.le (inv_nonneg.mpr hV0_pos.le),
      Real.inv_rpow hV0_pos.le, Real.sqrt_eq_rpow]
    have hV_mul_inv : V 0 ^ (1 / 2 : ℝ) * (V 0 ^ (1 / 2 : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hV0_pos _).ne'
    have hV_rpow : (V Y) ^ (-(1 / 2 : ℝ)) * V Y = (V Y) ^ (1 / 2 : ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one (V Y)]
      rw [← Real.rpow_add hVY_pos]; norm_num
    have hV_rpow2 : (V Y) ^ (-(1 / 2 : ℝ)) = (V Y) ^ (1 / 2 : ℝ) * (V Y)⁻¹ := by
      conv_rhs => rhs; rw [← Real.rpow_neg_one (V Y)]
      rw [← Real.rpow_add hVY_pos]; norm_num
    calc (V Y) ^ (-(1 / 2 : ℝ)) * (V Y + 2 * Y * fderiv ℝ S.V (q, Y) (0, 1))
        = (V Y) ^ (-(1 / 2 : ℝ)) * V Y + 2 * (Y * fderiv ℝ S.V (q, Y) (0, 1)) * (V Y) ^ (-(1 / 2 : ℝ)) := by ring
      _ = (V Y) ^ (1 / 2 : ℝ) + 2 * (Y * fderiv ℝ S.V (q, Y) (0, 1)) * ((V Y) ^ (1 / 2 : ℝ) * (V Y)⁻¹) := by
          rw [hV_rpow, hV_rpow2]
      _ = (V Y) ^ (1 / 2 : ℝ) * (1 + 2 * (Y * fderiv ℝ S.V (q, Y) (0, 1)) * (V Y)⁻¹) := by ring
      _ = (V 0 ^ (1 / 2 : ℝ) * (V 0 ^ (1 / 2 : ℝ))⁻¹) *
            ((V Y) ^ (1 / 2 : ℝ) * (1 + 2 * (Y * fderiv ℝ S.V (q, Y) (0, 1)) * (V Y)⁻¹)) := by rw [hV_mul_inv, one_mul]
      _ = V 0 ^ (1 / 2 : ℝ) * ((1 + 2 * (Y * fderiv ℝ S.V (q, Y) (0, 1)) * (V Y)⁻¹) *
            ((V Y) ^ (1 / 2 : ℝ) * (V 0 ^ (1 / 2 : ℝ))⁻¹)) := by ring
  have h2_tot : (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; norm_num
  have hc_tot : c ^ (1 / 6 : ℝ) * c ^ (1 / 6 : ℝ) * c ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
  rw [hT_rpow, hT_sq, hNu_eq]
  have hstep : warpN0 c * (π ^ 2 / 12) *
      ((2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) * u ^ (-(1 / 2 : ℝ)) * (V Y) ^ (-(1 / 2 : ℝ)) *
        fctH (τ₁ ^ 2 * (Y * S.V (q, Y) ^ 2))) * T' =
      ((12 / π ^ 2) * (π ^ 2 / 12)) * ((Real.sqrt warpTauStar)⁻¹) *
        ((2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ))) *
        (c ^ (1 / 6 : ℝ) * c ^ (1 / 6 : ℝ) * c ^ (-(1 / 3 : ℝ))) *
        u ^ (-(1 / 2 : ℝ)) * ((V Y) ^ (-(1 / 2 : ℝ)) * (V Y + 2 * Y * fderiv ℝ S.V (q, Y) (0, 1))) *
        fctH (τ₁ ^ 2 * (Y * S.V (q, Y) ^ 2)) := by
    dsimp only [warpN0, T', Y]; ring
  rw [hstep,
    show (12 : ℝ) / π ^ 2 * (π ^ 2 / 12) = 1 from by field_simp [Real.pi_ne_zero],
    h2_tot, hc_tot, one_mul, mul_one, mul_one, hV_half]
  dsimp only [Jfun, Y]; ring

lemma fctInner_split_integral {c : ℝ} {V : ℝ → ℝ} {T' : ℝ → ℝ} {g : ℝ → ℂ}
    (hc0 : 0 < c)
    (hT_mono : StrictMonoOn (fctInnerT c V) (Icc 0 (fctUc c)))
    (hT_img : fctInnerT c V '' Ioo 0 (fctUc c) = Ioo 0 (fctInnerT c V (fctUc c)))
    (hT_lo : 1.98 * c ^ (-(1 / 4 : ℝ)) ≤ fctInnerT c V (fctUc c))
    (hT_deriv : ∀ u ∈ Ioo 0 (fctUc c), HasDerivAt (fctInnerT c V) (T' u) u ∧ 0 < T' u) :
    ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) * g τ =
      ∫ u in Ioo (0 : ℝ) (fctUc c),
        ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * g (fctInnerT c V u) * ((T' u : ℝ) : ℂ) := by
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hT_pos : 0 < fctInnerT c V (fctUc c) := lt_of_lt_of_le (by positivity) hT_lo
  have h_sdiff_zero : ∀ τ ∈ Ioi (0 : ℝ) \ Ioc 0 (fctInnerT c V (fctUc c)),
      ((1 - outerChiOut c τ : ℝ) : ℂ) * g τ = 0 := by
    intro τ hτ
    have hge : fctInnerT c V (fctUc c) ≤ τ := by
      rcases le_or_gt τ (fctInnerT c V (fctUc c)) with hle | hgt
      · exact absurd ⟨hτ.1, hle⟩ hτ.2
      · exact hgt.le
    have h198 : 1.98 ≤ |τ / c ^ (-(1 / 4 : ℝ))| := by
      have hτ1 : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
      rw [abs_div, abs_of_pos hτ1, le_div_iff₀ hτ1, abs_of_pos hτ.1]
      exact hT_lo.trans hge
    have hchi1 : outerChiOut c τ = 1 := by
      unfold outerChiOut; rw [outerChiIn_cutoff.zero _ h198, sub_zero]
    rw [hchi1]; simp
  have hsub := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) measurableSet_Ioi
    Ioc_subset_Ioi_self h_sdiff_zero
  rw [hsub, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
  have hcongr : EqOn (fun τ => ((1 - outerChiOut c τ : ℝ) : ℂ) * g τ)
      (fun τ => ((outerChiIn (τ / c ^ (-(1 / 4 : ℝ))) : ℝ) : ℂ) * g τ)
      (Ioo 0 (fctInnerT c V (fctUc c))) := fun τ _ => by
    unfold outerChiOut; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← hT_img]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (hT_deriv u hu).1.hasDerivWithinAt)
    (hT_mono.mono Ioo_subset_Icc_self).injOn]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  rw [abs_of_pos (hT_deriv u hu).2, Complex.real_smul]
  dsimp only [fctInnerChi, fctTau1]
  ring

end FormalResearch.SignUncertainty
