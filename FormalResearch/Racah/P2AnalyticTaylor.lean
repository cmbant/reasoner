module

public import Mathlib

/-!
# Uniform Taylor remainder in one variable of a jointly smooth function (Weyl P2, WP1 / T1.3)

This is the generic analytic input behind the "uniform expansion" statements of the paper
(`thm:3jeven`, `thm:6jeven`, `thm:uniformedge`): if `G (z,t)` is jointly smooth on an open set
containing `K ×ˢ {0}` with `K` compact, then the Taylor polynomial of `t ↦ G (z,t)` at `t = 0`
approximates `G (z,t)` to order `|t|^R` uniformly in `z ∈ K`, with coefficients
`taylorCoeff (fun z t => G (z,t)) r z = ∂ₜʳ G (z,0) / r!` that are continuous in `z`
(analytic in `z` if `G` is analytic).

Generality: `E` is an arbitrary real normed space, `K ⊆ E` compact, `G : E × ℝ → ℝ` is
`ContDiffOn ℝ ∞` on an open set `U ⊇ K ×ˢ {0}`; the corollaries for global `ContDiff` and for
analytic `G` are stated too.

Method: the `t`-derivative `Dt H p = fderiv ℝ H p (0,1)` preserves joint smoothness on an open
set and `iteratedDeriv m (G (z,·)) t = (Dt^[m] G) (z,t)`, so the Lagrange-type bound
`taylor_mean_remainder_bound` has a constant given by the sup of the continuous function
`Dt^[n+1] G` on the compact set `K ×ˢ [0,ρ]`; negative `t` follows by reflecting `t ↦ -t`.
-/

@[expose] public section

namespace FormalResearch.Racah

open Set Filter Topology
open scoped ContDiff

/-- The Taylor coefficient `∂ₜʳ g(z,0) / r!` of `t ↦ g z t` at `t = 0`. -/
noncomputable def taylorCoeff {E : Type*} (g : E → ℝ → ℝ) (r : ℕ) (z : E) : ℝ :=
  iteratedDeriv r (g z) 0 / (r.factorial : ℝ)

section Dt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivative in the last variable. -/
noncomputable def Dt (H : E × ℝ → ℝ) (p : E × ℝ) : ℝ := fderiv ℝ H p (0, 1)

lemma contDiffOn_Dt {H : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (Dt H) U := by
  have h1 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ H p) U :=
    hH.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ H p (0, 1)) U :=
    h1.clm_apply contDiffOn_const
  exact h2

lemma contDiffOn_Dt_iterate {H : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (m : ℕ) : ContDiffOn ℝ ∞ (Dt^[m] H) U := by
  induction m with
  | zero => simpa using hH
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_Dt hU ih

/-- The slice `t ↦ G (z,t)` is smooth at `t` when `(z,t)` lies in the open set `U`. -/
lemma contDiffAt_slice {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {z : E} {t : ℝ} (hzt : (z, t) ∈ U) :
    ContDiffAt ℝ ∞ (fun s : ℝ => G (z, s)) t := by
  have h1 : ContDiffAt ℝ ∞ G (z, t) := hG.contDiffAt (hU.mem_nhds hzt)
  have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => ((z, s) : E × ℝ)) t :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  exact h1.comp t h2

/-- Iterated `t`-derivatives of a slice are the iterates of `Dt`. -/
lemma iteratedDeriv_slice_eq {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (z : E) (m : ℕ) :
    ∀ t : ℝ, (z, t) ∈ U → iteratedDeriv m (fun s : ℝ => G (z, s)) t = (Dt^[m] G) (z, t) := by
  induction m with
  | zero => intro t _; simp
  | succ m ih =>
    intro t ht
    have hopen : IsOpen {s : ℝ | (z, s) ∈ U} :=
      hU.preimage (continuous_const.prodMk continuous_id)
    have hev : iteratedDeriv m (fun s : ℝ => G (z, s)) =ᶠ[𝓝 t]
        fun s => (Dt^[m] G) (z, s) :=
      Filter.eventually_of_mem (hopen.mem_nhds ht) (fun s hs => ih s hs)
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hdiff : DifferentiableAt ℝ (Dt^[m] G) (z, t) :=
      ((contDiffOn_Dt_iterate hU hG m).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
    have hd : HasDerivAt (fun s : ℝ => ((z, s) : E × ℝ)) ((0 : E), (1 : ℝ)) t :=
      (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
    have := hdiff.hasFDerivAt.comp_hasDerivAt t hd
    rw [Function.iterate_succ_apply']
    exact this.deriv

/-- `taylorCoeff` as the value of an iterate of `Dt`. -/
lemma taylorCoeff_eq {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {z : E} (hz : (z, 0) ∈ U) (r : ℕ) :
    taylorCoeff (fun z t => G (z, t)) r z = (Dt^[r] G) (z, 0) / (r.factorial : ℝ) := by
  unfold taylorCoeff
  rw [iteratedDeriv_slice_eq hU hG z r 0 hz]

/-- The Taylor coefficients are continuous in `z` on `{z | (z,0) ∈ U}`. -/
theorem continuousOn_taylorCoeff {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (r : ℕ) :
    ContinuousOn (taylorCoeff (fun z t => G (z, t)) r) {z | (z, 0) ∈ U} := by
  have h1 : ContinuousOn (Dt^[r] G) U := (contDiffOn_Dt_iterate hU hG r).continuousOn
  have h2 : ContinuousOn (fun z : E => (Dt^[r] G) (z, 0)) {z | (z, 0) ∈ U} :=
    h1.comp (continuous_id.prodMk continuous_const).continuousOn (fun z hz => hz)
  have h3 := h2.div_const (r.factorial : ℝ)
  refine h3.congr (fun z hz => ?_)
  exact taylorCoeff_eq hU hG hz r

lemma analyticOnNhd_Dt_iterate {H : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hH : AnalyticOnNhd ℝ H U) (m : ℕ) : AnalyticOnNhd ℝ (Dt^[m] H) U := by
  induction m with
  | zero => simpa using hH
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have h1 := ih.fderiv_of_isOpen hU
    have h2 := (ContinuousLinearMap.apply ℝ ℝ ((0 : E), (1 : ℝ))).comp_analyticOnNhd h1
    exact h2

/-- If `G` is analytic on `U`, the Taylor coefficients are analytic in `z` where `(z,0) ∈ U`. -/
theorem analyticOnNhd_taylorCoeff {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : AnalyticOnNhd ℝ G U) (r : ℕ) :
    AnalyticOnNhd ℝ (taylorCoeff (fun z t => G (z, t)) r) {z | (z, 0) ∈ U} := by
  have hcd : ContDiffOn ℝ ∞ G U := hG.contDiffOn hU.uniqueDiffOn
  have h1 := analyticOnNhd_Dt_iterate hU hG r
  have h2 : AnalyticOnNhd ℝ (fun z : E => (Dt^[r] G) (z, 0)) {z | (z, 0) ∈ U} :=
    h1.comp (analyticOnNhd_id.prod analyticOnNhd_const) (fun z hz => hz)
  have h3 : AnalyticOnNhd ℝ (fun z : E => (Dt^[r] G) (z, 0) / (r.factorial : ℝ))
      {z | (z, 0) ∈ U} := h2.div_const
  exact h3.congr (hU.preimage (continuous_id.prodMk continuous_const)) (fun z hz => (taylorCoeff_eq hU hcd hz r).symm)

end Dt

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Tube lemma: a compact `K` with `K ×ˢ {0} ⊆ U` has a uniform `t`-thickening inside `U`. -/
lemma exists_tube {K : Set E} {U : Set (E × ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) : ∃ ρ : ℝ, 0 < ρ ∧ K ×ˢ Icc (-ρ) ρ ⊆ U := by
  obtain ⟨u, v, -, hv, hKu, h0, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hKU
  have h0v : (0 : ℝ) ∈ v := h0 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hv 0 h0v
  refine ⟨ε / 2, by positivity, ?_⟩
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  refine huv ⟨hKu hz, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  have := ht.1
  have := ht.2
  rw [abs_lt]
  constructor <;> linarith

/-- One-sided uniform Taylor bound with `R = n + 1`, for `t ∈ [0,ρ]`. -/
lemma taylor_uniform_nonneg {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) (n : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ z ∈ K, ∀ t ∈ Icc (0 : ℝ) ρ,
      |G (z, t) - ∑ r ∈ Finset.range (n + 1),
          taylorCoeff (fun z t => G (z, t)) r z * t ^ r| ≤ C * t ^ (n + 1) := by
  obtain ⟨ρ, hρ, htube⟩ := exists_tube hK hU hKU
  have hcpt : IsCompact (K ×ˢ Icc (0 : ℝ) ρ) := hK.prod isCompact_Icc
  have hsub : K ×ˢ Icc (0 : ℝ) ρ ⊆ U := fun p hp =>
    htube ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2⟩⟩
  have hcont : ContinuousOn (Dt^[n + 1] G) (K ×ˢ Icc (0 : ℝ) ρ) :=
    (contDiffOn_Dt_iterate hU hG (n + 1)).continuousOn.mono hsub
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hcont
  refine ⟨ρ, hρ, M / (n.factorial : ℝ), fun z hz t ht => ?_⟩
  set f : ℝ → ℝ := fun s => G (z, s) with hf
  have hzU : ∀ s ∈ Icc (0 : ℝ) ρ, (z, s) ∈ U := fun s hs => hsub ⟨hz, hs⟩
  have hfcd : ContDiffOn ℝ (n + 1 : ℕ) f (Icc 0 ρ) := fun s hs =>
    ((contDiffAt_slice hU hG (hzU s hs)).of_le (by exact_mod_cast le_top)).contDiffWithinAt
  have hC : ∀ y ∈ Icc (0 : ℝ) ρ, ‖iteratedDerivWithin (n + 1) f (Icc 0 ρ) y‖ ≤ M := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hρ)
      ((contDiffAt_slice hU hG (hzU y hy)).of_le (by exact_mod_cast le_top)) hy,
      iteratedDeriv_slice_eq hU hG z (n + 1) y (hzU y hy)]
    exact hM (z, y) ⟨hz, hy⟩
  have key := taylor_mean_remainder_bound hρ.le hfcd ht hC
  rw [taylor_within_apply] at key
  have hsum : ∑ k ∈ Finset.range (n + 1), (((k.factorial : ℝ)⁻¹ * (t - 0) ^ k) •
        iteratedDerivWithin k f (Icc 0 ρ) 0) =
      ∑ r ∈ Finset.range (n + 1), taylorCoeff (fun z t => G (z, t)) r z * t ^ r := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hρ)
      ((contDiffAt_slice hU hG (hzU 0 ⟨le_rfl, hρ.le⟩)).of_le (by exact_mod_cast le_top))
      ⟨le_rfl, hρ.le⟩]
    unfold taylorCoeff
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [hsum] at key
  rw [Real.norm_eq_abs] at key
  calc _ ≤ M * (t - 0) ^ (n + 1) / (n.factorial : ℝ) := key
    _ = M / (n.factorial : ℝ) * t ^ (n + 1) := by ring

/-- Reflection `t ↦ -t` of a jointly smooth function. -/
lemma reflect_contDiffOn {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) :
    IsOpen {p : E × ℝ | (p.1, -p.2) ∈ U} ∧
      ContDiffOn ℝ ∞ (fun p : E × ℝ => G (p.1, -p.2)) {p : E × ℝ | (p.1, -p.2) ∈ U} := by
  have hcd : ContDiff ℝ ∞ (fun p : E × ℝ => ((p.1, -p.2) : E × ℝ)) :=
    contDiff_fst.prodMk contDiff_snd.neg
  refine ⟨hU.preimage hcd.continuous, ?_⟩
  exact hG.comp hcd.contDiffOn (fun p hp => hp)

/-- **Uniform Taylor remainder** (`T1.3`).  If `G : E × ℝ → ℝ` is `C^∞` on an open set `U`
containing `K ×ˢ {0}` with `K` compact, then for every `R` there are `ρ > 0` and `C` with
`|G (z,t) - ∑_{r<R} taylorCoeff (fun z t => G (z,t)) r z * t^r| ≤ C |t|^R` for all `z ∈ K`,
`|t| ≤ ρ`. -/
theorem taylor_uniform {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) (R : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ z ∈ K, ∀ t : ℝ, |t| ≤ ρ →
      |G (z, t) - ∑ r ∈ Finset.range R, taylorCoeff (fun z t => G (z, t)) r z * t ^ r|
        ≤ C * |t| ^ R := by
  cases R with
  | zero =>
    obtain ⟨ρ, hρ, htube⟩ := exists_tube hK hU hKU
    have hcpt : IsCompact (K ×ˢ Icc (-ρ) ρ) := hK.prod isCompact_Icc
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (hG.continuousOn.mono htube)
    refine ⟨ρ, hρ, M, fun z hz t ht => ?_⟩
    have := hM (z, t) ⟨hz, abs_le.mp ht⟩
    simpa using this
  | succ n =>
    obtain ⟨ρ₁, hρ₁, C₁, h₁⟩ := taylor_uniform_nonneg hU hG hK hKU n
    obtain ⟨hU', hG'⟩ := reflect_contDiffOn hU hG
    have hKU' : K ×ˢ ({0} : Set ℝ) ⊆ {p : E × ℝ | (p.1, -p.2) ∈ U} := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      have : t = 0 := ht
      subst this
      simpa using hKU ⟨hz, rfl⟩
    obtain ⟨ρ₂, hρ₂, C₂, h₂⟩ := taylor_uniform_nonneg hU' hG' hK hKU' n
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, max C₁ C₂, fun z hz t ht => ?_⟩
    have hmax : 0 ≤ |t| ^ (n + 1) := by positivity
    have ht1 : |t| ≤ ρ₁ := ht.trans (min_le_left _ _)
    have ht2 : |t| ≤ ρ₂ := ht.trans (min_le_right _ _)
    rcases le_total 0 t with h0 | h0
    · have := h₁ z hz t ⟨h0, by rwa [abs_of_nonneg h0] at ht1⟩
      rw [abs_of_nonneg h0]
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have h0' : 0 ≤ -t := by linarith
      have habs : |t| = -t := abs_of_nonpos h0
      have := h₂ z hz (-t) ⟨h0', by rwa [habs] at ht2⟩
      have hcoef : ∀ r : ℕ, taylorCoeff (fun z t => G (z, -t)) r z =
          (-1) ^ r * taylorCoeff (fun z t => G (z, t)) r z := by
        intro r
        unfold taylorCoeff
        have := iteratedDeriv_comp_neg r (fun s : ℝ => G (z, s)) 0
        simp only [neg_zero, smul_eq_mul] at this
        rw [this]; ring
      simp only [hcoef, neg_neg] at this
      have hsum : ∑ r ∈ Finset.range (n + 1),
          (-1) ^ r * taylorCoeff (fun z t => G (z, t)) r z * (-t) ^ r =
          ∑ r ∈ Finset.range (n + 1), taylorCoeff (fun z t => G (z, t)) r z * t ^ r := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        have h : ((-1 : ℝ) ^ r) * ((-1 : ℝ) ^ r) = 1 := by rw [← mul_pow]; norm_num
        rw [neg_pow t r]
        linear_combination (taylorCoeff (fun z t => G (z, t)) r z * t ^ r) * h
      rw [hsum] at this
      rw [habs]
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by rw [← habs]; positivity))

/-- Global version: `G` is `C^∞` on all of `E × ℝ`. -/
theorem taylor_uniform_of_contDiff {G : E × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {K : Set E}
    (hK : IsCompact K) (R : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ z ∈ K, ∀ t : ℝ, |t| ≤ ρ →
      |G (z, t) - ∑ r ∈ Finset.range R, taylorCoeff (fun z t => G (z, t)) r z * t ^ r|
        ≤ C * |t| ^ R :=
  taylor_uniform isOpen_univ hG.contDiffOn hK (subset_univ _) R

/-- Version for `G` analytic on a neighbourhood of `K ×ˢ {0}`. -/
theorem taylor_uniform_of_analytic {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : AnalyticOnNhd ℝ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) (R : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ z ∈ K, ∀ t : ℝ, |t| ≤ ρ →
      |G (z, t) - ∑ r ∈ Finset.range R, taylorCoeff (fun z t => G (z, t)) r z * t ^ r|
        ≤ C * |t| ^ R :=
  taylor_uniform hU (hG.contDiffOn hU.uniqueDiffOn) hK hKU R

/-- The Taylor coefficients are continuous on `K` (the set where `(z,0) ∈ U`). -/
theorem continuousOn_taylorCoeff_of_subset {G : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) (r : ℕ) :
    ContinuousOn (taylorCoeff (fun z t => G (z, t)) r) K :=
  (continuousOn_taylorCoeff hU hG r).mono (fun _ hz => hKU ⟨hz, rfl⟩)

end Uniform

/-- info: 'FormalResearch.Racah.taylor_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taylor_uniform

/-- info: 'FormalResearch.Racah.analyticOnNhd_taylorCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOnNhd_taylorCoeff

/-- info: 'FormalResearch.Racah.continuousOn_taylorCoeff_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_taylorCoeff_of_subset

end FormalResearch.Racah
