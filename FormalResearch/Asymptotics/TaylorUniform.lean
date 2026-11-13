module

public import Mathlib

/-!
# Uniform Taylor remainder in one variable for a jointly smooth vector-valued function

If `G : E × ℝ → F` is jointly smooth on an open set containing `K ×ˢ {0}` with `K` compact, then the
Taylor polynomial of `t ↦ G (z,t)` at `t = 0` approximates `G (z,t)` to order `|t|^R` uniformly in
`z ∈ K`, with coefficients `taylorCoeff (fun z t => G (z,t)) r z = (r!)⁻¹ • ∂ₜʳ G (z,0)` that are
continuous in `z` (analytic in `z` if `G` is analytic).

This is the generic analytic input of `AnalyticGerm.lean`.  It is a generalisation, to values in an
arbitrary real normed space `F`, of `FormalResearch.Racah.taylor_uniform` (which is stated for
`F = ℝ` and kept unchanged); for `F = ℝ` the two `taylorCoeff`s agree (`Examples.lean`).

Method: the `t`-derivative `derivT H p = fderiv ℝ H p (0,1)` preserves joint smoothness on an open
set and `iteratedDeriv m (G (z,·)) t = (derivT^[m] G) (z,t)`, so the Lagrange-type bound
`taylor_mean_remainder_bound` has a constant given by the sup of the continuous function
`derivT^[n+1] G` on the compact set `K ×ˢ [0,ρ]`; negative `t` follows by reflecting `t ↦ -t`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace FormalResearch.Asymptotics

/-- The Taylor coefficient `(r!)⁻¹ • ∂ₜʳ g(z,0)` of `t ↦ g z t` at `t = 0`. -/
noncomputable def taylorCoeff {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → ℝ → F) (r : ℕ) (z : E) : F :=
  (r.factorial : ℝ)⁻¹ • iteratedDeriv r (g z) 0

section Derivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative in the last variable. -/
noncomputable def derivT (H : E × ℝ → F) (p : E × ℝ) : F := fderiv ℝ H p (0, 1)

lemma contDiffOn_derivT {H : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (derivT H) U := by
  have h1 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ H p) U :=
    hH.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const

lemma contDiffOn_derivT_iterate {H : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (m : ℕ) : ContDiffOn ℝ ∞ (derivT^[m] H) U := by
  induction m with
  | zero => simpa using hH
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_derivT hU ih

/-- The slice `t ↦ G (z,t)` is smooth at `t` when `(z,t)` lies in the open set `U`. -/
lemma contDiffAt_slice {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {z : E} {t : ℝ} (hzt : (z, t) ∈ U) :
    ContDiffAt ℝ ∞ (fun s : ℝ => G (z, s)) t := by
  have h1 : ContDiffAt ℝ ∞ G (z, t) := hG.contDiffAt (hU.mem_nhds hzt)
  have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => ((z, s) : E × ℝ)) t :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  exact h1.comp t h2

/-- Iterated `t`-derivatives of a slice are the iterates of `derivT`. -/
lemma iteratedDeriv_slice_eq {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (z : E) (m : ℕ) :
    ∀ t : ℝ, (z, t) ∈ U → iteratedDeriv m (fun s : ℝ => G (z, s)) t = (derivT^[m] G) (z, t) := by
  induction m with
  | zero => intro t _; simp
  | succ m ih =>
    intro t ht
    have hopen : IsOpen {s : ℝ | (z, s) ∈ U} :=
      hU.preimage (continuous_const.prodMk continuous_id)
    have hev : iteratedDeriv m (fun s : ℝ => G (z, s)) =ᶠ[𝓝 t]
        fun s => (derivT^[m] G) (z, s) :=
      Filter.eventually_of_mem (hopen.mem_nhds ht) (fun s hs => ih s hs)
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hdiff : DifferentiableAt ℝ (derivT^[m] G) (z, t) :=
      ((contDiffOn_derivT_iterate hU hG m).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
    have hd : HasDerivAt (fun s : ℝ => ((z, s) : E × ℝ)) ((0 : E), (1 : ℝ)) t :=
      (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
    have := hdiff.hasFDerivAt.comp_hasDerivAt t hd
    rw [Function.iterate_succ_apply']
    exact this.deriv

/-- `taylorCoeff` as the value of an iterate of `derivT`. -/
lemma taylorCoeff_eq {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {z : E} (hz : (z, 0) ∈ U) (r : ℕ) :
    taylorCoeff (fun z t => G (z, t)) r z = (r.factorial : ℝ)⁻¹ • (derivT^[r] G) (z, 0) := by
  unfold taylorCoeff
  rw [iteratedDeriv_slice_eq hU hG z r 0 hz]

/-- The Taylor coefficients are continuous in `z` on `{z | (z,0) ∈ U}`. -/
theorem continuousOn_taylorCoeff {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (r : ℕ) :
    ContinuousOn (taylorCoeff (fun z t => G (z, t)) r) {z | (z, 0) ∈ U} := by
  have h1 : ContinuousOn (derivT^[r] G) U := (contDiffOn_derivT_iterate hU hG r).continuousOn
  have h2 : ContinuousOn (fun z : E => (derivT^[r] G) (z, 0)) {z | (z, 0) ∈ U} :=
    h1.comp (continuous_id.prodMk continuous_const).continuousOn (fun z hz => hz)
  have h3 := h2.const_smul ((r.factorial : ℝ)⁻¹)
  refine h3.congr (fun z hz => ?_)
  exact taylorCoeff_eq hU hG hz r

lemma analyticOnNhd_derivT_iterate {H : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hH : AnalyticOnNhd ℝ H U) (m : ℕ) : AnalyticOnNhd ℝ (derivT^[m] H) U := by
  induction m with
  | zero => simpa using hH
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have h1 := ih.fderiv_of_isOpen hU
    exact (ContinuousLinearMap.apply ℝ F ((0 : E), (1 : ℝ))).comp_analyticOnNhd h1

/-- If `G` is analytic on `U`, the Taylor coefficients are analytic in `z` where `(z,0) ∈ U`. -/
theorem analyticOnNhd_taylorCoeff {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : AnalyticOnNhd ℝ G U) (r : ℕ) :
    AnalyticOnNhd ℝ (taylorCoeff (fun z t => G (z, t)) r) {z | (z, 0) ∈ U} := by
  have hcd : ContDiffOn ℝ ∞ G U := hG.contDiffOn hU.uniqueDiffOn
  have h1 := analyticOnNhd_derivT_iterate hU hG r
  have h2 : AnalyticOnNhd ℝ (fun z : E => (derivT^[r] G) (z, 0)) {z | (z, 0) ∈ U} :=
    h1.comp (analyticOnNhd_id.prod analyticOnNhd_const) (fun z hz => hz)
  have h3 : AnalyticOnNhd ℝ (fun z : E => (r.factorial : ℝ)⁻¹ • (derivT^[r] G) (z, 0))
      {z | (z, 0) ∈ U} := analyticOnNhd_const.smul h2
  exact h3.congr (hU.preimage (continuous_id.prodMk continuous_const))
    (fun z hz => (taylorCoeff_eq hU hcd hz r).symm)

end Derivative

section Uniform

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
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
lemma taylor_uniform_nonneg {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) (n : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ z ∈ K, ∀ t ∈ Icc (0 : ℝ) ρ,
      ‖G (z, t) - ∑ r ∈ Finset.range (n + 1),
          t ^ r • taylorCoeff (fun z t => G (z, t)) r z‖ ≤ C * t ^ (n + 1) := by
  obtain ⟨ρ, hρ, htube⟩ := exists_tube hK hU hKU
  have hcpt : IsCompact (K ×ˢ Icc (0 : ℝ) ρ) := hK.prod isCompact_Icc
  have hsub : K ×ˢ Icc (0 : ℝ) ρ ⊆ U := fun p hp =>
    htube ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2⟩⟩
  have hcont : ContinuousOn (derivT^[n + 1] G) (K ×ˢ Icc (0 : ℝ) ρ) :=
    (contDiffOn_derivT_iterate hU hG (n + 1)).continuousOn.mono hsub
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hcont
  refine ⟨ρ, hρ, M / (n.factorial : ℝ), fun z hz t ht => ?_⟩
  set f : ℝ → F := fun s => G (z, s) with hf
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
      ∑ r ∈ Finset.range (n + 1), t ^ r • taylorCoeff (fun z t => G (z, t)) r z := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hρ)
      ((contDiffAt_slice hU hG (hzU 0 ⟨le_rfl, hρ.le⟩)).of_le (by exact_mod_cast le_top))
      ⟨le_rfl, hρ.le⟩]
    unfold taylorCoeff
    simp only [sub_zero, mul_smul]
    rw [smul_comm]
  rw [hsum] at key
  calc _ ≤ M * (t - 0) ^ (n + 1) / (n.factorial : ℝ) := key
    _ = M / (n.factorial : ℝ) * t ^ (n + 1) := by ring

/-- Reflection `t ↦ -t` of a jointly smooth function. -/
lemma reflect_contDiffOn {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) :
    IsOpen {p : E × ℝ | (p.1, -p.2) ∈ U} ∧
      ContDiffOn ℝ ∞ (fun p : E × ℝ => G (p.1, -p.2)) {p : E × ℝ | (p.1, -p.2) ∈ U} := by
  have hcd : ContDiff ℝ ∞ (fun p : E × ℝ => ((p.1, -p.2) : E × ℝ)) :=
    contDiff_fst.prodMk contDiff_snd.neg
  refine ⟨hU.preimage hcd.continuous, ?_⟩
  exact hG.comp hcd.contDiffOn (fun p hp => hp)

/-- **Uniform Taylor remainder.**  If `G : E × ℝ → F` is `C^∞` on an open set `U` containing
`K ×ˢ {0}` with `K` compact, then for every `R` there are `ρ > 0` and `C` with
`‖G (z,t) - ∑_{r<R} t ^ r • taylorCoeff (fun z t => G (z,t)) r z‖ ≤ C |t|^R` for all `z ∈ K`,
`|t| ≤ ρ`. -/
theorem taylor_uniform {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) (R : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ z ∈ K, ∀ t : ℝ, |t| ≤ ρ →
      ‖G (z, t) - ∑ r ∈ Finset.range R, t ^ r • taylorCoeff (fun z t => G (z, t)) r z‖
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
          (-1 : ℝ) ^ r • taylorCoeff (fun z t => G (z, t)) r z := by
        intro r
        unfold taylorCoeff
        have := iteratedDeriv_comp_neg r (fun s : ℝ => G (z, s)) 0
        simp only [neg_zero] at this
        rw [this, smul_comm]
      simp only [hcoef, neg_neg, smul_smul] at this
      have hsum : ∑ r ∈ Finset.range (n + 1),
          ((-t) ^ r * (-1 : ℝ) ^ r) • taylorCoeff (fun z t => G (z, t)) r z =
          ∑ r ∈ Finset.range (n + 1), t ^ r • taylorCoeff (fun z t => G (z, t)) r z := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [← mul_pow, neg_mul_neg, mul_one]
      rw [hsum] at this
      rw [habs]
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by rw [← habs]; positivity))

end Uniform

/-- info: 'FormalResearch.Asymptotics.taylor_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taylor_uniform

/-- info: 'FormalResearch.Asymptotics.analyticOnNhd_taylorCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOnNhd_taylorCoeff

end FormalResearch.Asymptotics
