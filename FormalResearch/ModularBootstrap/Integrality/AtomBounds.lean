module

public import FormalResearch.ModularBootstrap.Integrality.ChebExplicit
public import FormalResearch.ModularBootstrap.Integrality.ShellInvDefs
public import FormalResearch.ModularBootstrap.Mixtures.WeightAxioms
public import FormalResearch.ModularBootstrap.Mixtures.O1
public import FormalResearch.ModularBootstrap.Mixtures.CrossingPort

/-!
# Analytical bounds & local cell moment-matching for `int:atom` (`INT-1`)

Supports `Integrality/Atom.lean` (`int:atom`, Theorem INT-1):
1. `SufficientMomentFloor`, `sufficientMomentFloor_cheb_explicit` (`W(M) = 8 (M + 1)^{5/2}` from
   `cheb_explicit`), and `integerMomentMatching_cell` (affine transport to `[B_mid - 1, B_mid + 1]`).
2. `rhoLowerCore` and `commonSource_cardyDensity_lower` (`int:rho-lower`): uniform Cardy density
   lower envelope `c_vac * rhoLowerCore w a t ≤ C.src.cardyDensity a t` for any `C : CommonSource`.
3. `commonSource_counting_bound` (`int:counting`): unconditional upper bound on `Z_0(1)` and
   `ν([T, R])` for any `SourceCrossingMeasure C.src a` supported on `[T, ∞)`.
4. `IntRepairSonineInput`: explicit repair & Sonine compression interface (`int:repair`,
   `int:sonine`) plus `rpow_weighted_taylor_le` and `rpow_half_mul_exp_neg_le_one`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Mixtures
open FormalResearch.ModularBootstrap.WeightAxioms

/-! ### Section 1: Abstract sufficient density floor & cell translation -/

/-- Abstract sufficient density floor on `[-1, 1]` for degree-`M` exact integer moment matching
of positive measures of integer total mass (`int:atom`: `W(M) > 1`). -/
def SufficientMomentFloor (W : ℕ → ℝ) : Prop :=
  (∀ M : ℕ, 1 < W M) ∧
  (∀ {M : ℕ}, 1 ≤ M → ∀ {μ : Measure ℝ} [IsFiniteMeasure μ],
    μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → ∀ {Ntot : ℕ}, μ Set.univ = Ntot →
      ENNReal.ofReal (W M) • volume.restrict (Set.Icc (-1 : ℝ) 1) ≤ μ →
        IntegerMomentMatching μ M)

/-- Concrete instance `W(M) = 8 (M + 1)^{5/2}` from `cheb_explicit` (`int:cheb-explicit`). -/
theorem sufficientMomentFloor_cheb_explicit :
    SufficientMomentFloor (fun M => 8 * ((M : ℝ) + 1) ^ 2 * Real.sqrt ((M : ℝ) + 1)) := by
  refine ⟨fun M => ?_, fun hM μ _ hsupp Ntot hN hfloor =>
    cheb_explicit hM hsupp hN le_rfl hfloor⟩
  have h1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith
  have hsq : (1 : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) := by
    rw [Real.le_sqrt zero_le_one (by linarith)]; linarith
  dsimp only
  nlinarith

/-- Translating an exact integer moment matching from `[-1, 1]` to a closed length-`2` cell
`Icc (B_mid - 1) (B_mid + 1)`. -/
lemma integerMomentMatching_cell {W : ℕ → ℝ} (hW : SufficientMomentFloor W)
    {M : ℕ} (hM : 1 ≤ M) (B_mid : ℝ) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsupp : μ (Set.Icc (B_mid - 1) (B_mid + 1))ᶜ = 0) {Ntot : ℕ} (hN : μ Set.univ = Ntot)
    (hfloor : ENNReal.ofReal (W M) • volume.restrict (Set.Icc (B_mid - 1) (B_mid + 1)) ≤ μ) :
    ∃ (κ : Type) (_ : Fintype κ) (t : κ → ℝ) (d : κ → ℕ),
      (∀ k, t k ∈ Set.Icc (B_mid - 1) (B_mid + 1)) ∧
      (∀ k, 1 ≤ d k) ∧
      (∀ P : ℝ[X], P.degree ≤ M → ∫ s, P.eval s ∂μ = ∑ k, (d k : ℝ) * P.eval (t k)) := by
  let shiftInv : ℝ → ℝ := fun s => s - B_mid
  have hm_inv : Measurable shiftInv := measurable_id.sub_const B_mid
  let μ0 : Measure ℝ := Measure.map shiftInv μ
  have hfin0 : IsFiniteMeasure μ0 := Measure.isFiniteMeasure_map μ shiftInv
  have hsupp0 : μ0 (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    rw [Measure.map_apply hm_inv measurableSet_Icc.compl]
    have hsub : shiftInv ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ ⊆ (Set.Icc (B_mid - 1) (B_mid + 1))ᶜ := by
      intro s hs hmem
      apply hs
      simp only [shiftInv, mem_Icc] at hmem ⊢
      constructor <;> linarith [hmem.1, hmem.2]
    exact measure_mono_null hsub hsupp
  have hN0 : μ0 Set.univ = Ntot := by
    rw [Measure.map_apply hm_inv MeasurableSet.univ, Set.preimage_univ, hN]
  have hfloor0 : ENNReal.ofReal (W M) • volume.restrict (Set.Icc (-1 : ℝ) 1) ≤ μ0 := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [smul_apply, smul_eq_mul, Measure.map_apply hm_inv hA, Measure.restrict_apply hA]
    have hmap_vol : volume (A ∩ Set.Icc (-1 : ℝ) 1) =
        volume (shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1)) := by
      have hpre : shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1) =
          (fun x => x + (-B_mid)) ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1) := by
        ext x; simp [shiftInv, sub_eq_add_neg]
      rw [hpre, (measurePreserving_add_right volume (-B_mid)).measure_preimage
        (hA.inter measurableSet_Icc).nullMeasurableSet]
    have hsub : shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1) ⊆
        (shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1) := by
      intro s ⟨hsA, hs1, hs2⟩
      exact ⟨hsA, by dsimp [shiftInv] at *; linarith, by dsimp [shiftInv] at *; linarith⟩
    have hle := Measure.le_iff.1 hfloor ((shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1))
      ((hm_inv hA).inter measurableSet_Icc)
    rw [smul_apply, smul_eq_mul,
      Measure.restrict_apply ((hm_inv hA).inter measurableSet_Icc)] at hle
    calc ENNReal.ofReal (W M) * volume (A ∩ Set.Icc (-1 : ℝ) 1)
        = ENNReal.ofReal (W M) * volume (shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1)) := by rw [hmap_vol]
      _ ≤ ENNReal.ofReal (W M) *
          volume (((shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1)) ∩
            Set.Icc (B_mid - 1) (B_mid + 1)) := by
          gcongr
          rw [Set.inter_assoc, Set.inter_self]
          exact hsub
      _ ≤ μ ((shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1)) := hle
      _ ≤ μ (shiftInv ⁻¹' A) := measure_mono inter_subset_left
  obtain ⟨κ, hfin, x, d, hx_mem, hd_pos, hmatch⟩ := @hW.2 M hM μ0 hfin0 hsupp0 Ntot hN0 hfloor0
  refine ⟨κ, hfin, fun k => B_mid + x k, d, fun k => ?_, hd_pos, fun P hP => ?_⟩
  · have hk := hx_mem k
    simp only [Set.mem_Icc] at hk ⊢
    constructor <;> linarith [hk.1, hk.2]
  · let Q : ℝ[X] := P.comp (Polynomial.X + Polynomial.C B_mid)
    have hQdeg : Q.degree ≤ M := by
      refine Polynomial.degree_le_natDegree.trans ?_
      have hnat_P : P.natDegree ≤ M := Polynomial.natDegree_le_of_degree_le hP
      have hnat_X : (Polynomial.X + Polynomial.C B_mid : ℝ[X]).natDegree ≤ 1 := by
        compute_degree!
      have hnat_Q : Q.natDegree ≤ M := by
        calc Q.natDegree ≤ P.natDegree * (Polynomial.X + Polynomial.C B_mid).natDegree :=
              Polynomial.natDegree_comp_le
          _ ≤ M * 1 := Nat.mul_le_mul hnat_P hnat_X
          _ = M := mul_one M
      exact_mod_cast hnat_Q
    have hQeq : ∀ s : ℝ, Q.eval (shiftInv s) = P.eval s := fun s => by
      dsimp [Q, shiftInv]
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      ring_nf
    have hQint : Integrable (fun y => Q.eval y) μ0 := by
      have hcQ : ContinuousOn (fun y => Q.eval y) (Set.Icc (-1 : ℝ) 1) :=
        Q.continuous.continuousOn
      rw [← Measure.restrict_eq_self_of_ae_mem
        (measure_eq_zero_iff_ae_notMem.1 hsupp0 |>.mono fun y hy => not_not.mp hy)]
      exact hcQ.integrableOn_Icc
    have hmap_int : ∫ y, Q.eval y ∂μ0 = ∫ s, P.eval s ∂μ := by
      rw [MeasureTheory.integral_map hm_inv.aemeasurable hQint.aestronglyMeasurable]
      exact integral_congr_ae (Eventually.of_forall hQeq)
    rw [← hmap_int, hmatch Q hQdeg]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [Q]
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring_nf

/-! ### Section 2: Uniform Cardy density lower bound (`int:rho-lower`) -/

/-- Asymptotic core `(t / a)^{(w-1)/2} (a t)^{-1/4} exp(4π √(a t))` of the Cardy density
at weight `w`. -/
noncomputable def rhoLowerCore (w : ℕ) (a t : ℝ) : ℝ :=
  (t / a) ^ (((w - 1 : ℕ) : ℝ) / 2) * (a * t) ^ (-(1 / 4 : ℝ)) *
    Real.exp (4 * π * Real.sqrt (a * t))

lemma rhoLowerCore_pos {w : ℕ} {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    0 < rhoLowerCore w a t := by
  unfold rhoLowerCore; positivity

lemma rhoLowerCore_mono {w : ℕ} (_hw : 1 ≤ w) {a : ℝ} (ha : 8 ≤ a)
    {t₁ t₂ : ℝ} (ht₁ : a / 8 ≤ t₁) (hle : t₁ ≤ t₂) :
    rhoLowerCore w a t₁ ≤ rhoLowerCore w a t₂ := by
  have ha_pos : 0 < a := by linarith
  have ht₁_pos : 0 < t₁ := by linarith
  have ht₂_pos : 0 < t₂ := ht₁_pos.trans_le hle
  have h1 : (t₁ / a) ^ (((w - 1 : ℕ) : ℝ) / 2) ≤ (t₂ / a) ^ (((w - 1 : ℕ) : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hle ha_pos.le) (by positivity)
  let g : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * Real.exp (4 * π * u)
  have hg_mono : StrictMonoOn g (Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
    · refine ContinuousOn.mul ?_ (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))
    · intro u hu
      rw [interior_Ici] at hu
      have hu_gt : 1 < u := mem_Ioi.mp hu
      have hu_pos : 0 < u := by linarith
      have hd1 : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
          ((-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ) - 1)) u :=
        Real.hasDerivAt_rpow_const (Or.inl hu_pos.ne')
      have hd2 : HasDerivAt (fun x : ℝ => Real.exp (4 * π * x)) (4 * π * Real.exp (4 * π * u)) u :=
        ((hasDerivAt_id u).const_mul (4 * π)).exp.congr_deriv (by simp; ring)
      have hdg : HasDerivAt g
          ((-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ) - 1) * Real.exp (4 * π * u) +
            u ^ (-(1 / 2 : ℝ)) * (4 * π * Real.exp (4 * π * u))) u :=
        hd1.mul hd2
      rw [hdg.deriv]
      have hpow_eq : u ^ (-(1 / 2 : ℝ) - 1) = u⁻¹ * u ^ (-(1 / 2 : ℝ)) := by
        rw [show -(1 / 2 : ℝ) - 1 = -1 + (-(1 / 2 : ℝ)) by ring,
          Real.rpow_add hu_pos, Real.rpow_neg_one]
      rw [hpow_eq]
      have hcomb : (-(1 / 2 : ℝ)) * (u⁻¹ * u ^ (-(1 / 2 : ℝ))) * Real.exp (4 * π * u) +
            u ^ (-(1 / 2 : ℝ)) * (4 * π * Real.exp (4 * π * u)) =
          (4 * π - 1 / (2 * u)) * u ^ (-(1 / 2 : ℝ)) * Real.exp (4 * π * u) := by
        field_simp [hu_pos.ne']
        ring
      rw [hcomb]
      have hcoeff : 0 < 4 * π - 1 / (2 * u) := by
        have h1u : 1 / (2 * u) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        linarith [Real.pi_gt_three]
      exact mul_pos (mul_pos hcoeff (Real.rpow_pos_of_pos hu_pos _)) (Real.exp_pos _)
  have hu₁ : 1 ≤ Real.sqrt (a * t₁) := by
    rw [Real.le_sqrt zero_le_one (by positivity)]
    nlinarith
  have hu_le : Real.sqrt (a * t₁) ≤ Real.sqrt (a * t₂) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle ha_pos.le)
  have hg_le : g (Real.sqrt (a * t₁)) ≤ g (Real.sqrt (a * t₂)) :=
    hg_mono.monotoneOn hu₁ (hu₁.trans hu_le) hu_le
  have hg_eq : ∀ t : ℝ, 0 < t →
      g (Real.sqrt (a * t)) = (a * t) ^ (-(1 / 4 : ℝ)) * Real.exp (4 * π * Real.sqrt (a * t)) := by
    intro t ht
    dsimp [g]
    have hpow : (Real.sqrt (a * t)) ^ (-(1 / 2 : ℝ)) = (a * t) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hpow]
  rw [hg_eq t₁ ht₁_pos, hg_eq t₂ ht₂_pos] at hg_le
  calc rhoLowerCore w a t₁
      = (t₁ / a) ^ (((w - 1 : ℕ) : ℝ) / 2) *
          ((a * t₁) ^ (-(1 / 4 : ℝ)) * Real.exp (4 * π * Real.sqrt (a * t₁))) := by
        unfold rhoLowerCore; ring
    _ ≤ (t₂ / a) ^ (((w - 1 : ℕ) : ℝ) / 2) *
          ((a * t₂) ^ (-(1 / 4 : ℝ)) * Real.exp (4 * π * Real.sqrt (a * t₂))) :=
        mul_le_mul h1 hg_le (by positivity) (by positivity)
    _ = rhoLowerCore w a t₂ := by
        unfold rhoLowerCore; ring

/-- **Uniform Cardy density lower bound (`int:rho-lower`)** for any `CommonSource`. -/
theorem commonSource_cardyDensity_lower (C : CommonSource) :
    ∃ c_vac a_star : ℝ, 0 < c_vac ∧ max C.a₀ 8 ≤ a_star ∧
      ∀ {a t : ℝ}, a_star ≤ a → a / 8 ≤ t →
        c_vac * rhoLowerCore C.src.w a t ≤ C.src.cardyDensity a t := by
  have hx0_pos : (0 : ℝ) < 1 / Real.sqrt 32 := by positivity
  obtain ⟨⟨Cx, n₀, hCx_nn, hasymp⟩, -, -, -, -⟩ := pmix_weight_b C hx0_pos
  obtain ⟨hnp0, hnp⟩ := nullPoly_exp_bounds C.F.prob hx0_pos
  set amp_lb : ℝ := C.F.d * C.F.prob.nullPoly (Real.exp (-4 * π * (1 / Real.sqrt 32)))
  have hamp_pos : 0 < amp_lb := mul_pos C.F.hd hnp0
  set a_star : ℝ := max (max C.a₀ 8) (max (n₀ / 12) (2 * Cx / (12 * amp_lb)))
  set c_vac : ℝ := (amp_lb / 2) / Real.sqrt 2
  have hc_pos : 0 < c_vac := by positivity
  refine ⟨c_vac, a_star, hc_pos, le_max_left _ _, fun {a t} ha ht => ?_⟩
  have ha8 : 8 ≤ a := (le_max_right _ _).trans ((le_max_left _ _).trans ha)
  have ha0 : C.a₀ ≤ a := (le_max_left _ _).trans ((le_max_left _ _).trans ha)
  have ha_pos : 0 < a := by linarith
  have ht_pos : 0 < t := by linarith
  set n : ℝ := 12 * a
  set x : ℝ := Real.sqrt (3 * t / n)
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hx_sq : x ^ 2 = 3 * t / n := Real.sq_sqrt (by positivity)
  have hx_ge : 1 / Real.sqrt 32 ≤ x := by
    dsimp [x, n]
    have h1 : 1 / 32 ≤ 3 * t / (12 * a) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    have h2 : Real.sqrt (1 / 32 : ℝ) ≤ Real.sqrt (3 * t / (12 * a)) := Real.sqrt_le_sqrt h1
    rwa [one_div, Real.sqrt_inv, ← one_div] at h2
  have hn_n0 : n₀ ≤ n := by
    have h1 : n₀ / 12 ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
    dsimp [n]; linarith
  have hcx_le : Cx / n ≤ amp_lb / 2 := by
    have h1 : 2 * Cx / (12 * amp_lb) ≤ a := (le_max_right _ _).trans ((le_max_right _ _).trans ha)
    have h12 : 0 < 12 * amp_lb := by positivity
    rw [div_le_iff₀ hn_pos]
    rw [div_le_iff₀ h12] at h1
    dsimp [n]
    nlinarith
  have hasym := hasymp hn_n0 hx_ge
  have hamp_x : amp_lb ≤ C.src.ampl x :=
    (mul_le_mul_of_nonneg_left (hnp hx_ge).1 C.F.hd.le).trans
      (ampl_lower C.F C.at_ (by positivity))
  have hV_eq : C.src.cardyV (n / 12) (n * x ^ 2 / 3) = C.src.cardyV a t := by
    have ha_eq : n / 12 = a := by dsimp [n]; ring
    have ht_eq : n * x ^ 2 / 3 = t := by
      rw [hx_sq]; field_simp [hn_pos.ne']
    rw [ha_eq, ht_eq]
  have hden_pos : 0 < (2 * x) ^ (C.src.w - 1) * besselAs (n * (2 * π * x / 3)) := by
    have hAs := besselAs_pos (by positivity : 0 < n * (2 * π * x / 3))
    positivity
  have hratio_lb : amp_lb / 2 ≤ C.src.cardyV a t /
      ((2 * x) ^ (C.src.w - 1) * besselAs (n * (2 * π * x / 3))) := by
    rw [← hV_eq]
    have h1 := (abs_sub_le_iff.mp hasym).2
    linarith
  have hV_lb : (amp_lb / 2) * ((2 * x) ^ (C.src.w - 1) * besselAs (n * (2 * π * x / 3))) ≤
      C.src.cardyV a t :=
    (le_div_iff₀ hden_pos).mp hratio_lb
  have h2x_eq : 2 * x = Real.sqrt (t / a) := by
    dsimp [x, n]
    have h1 : (2 : ℝ) = Real.sqrt 4 := by norm_num
    rw [h1, ← Real.sqrt_mul (by norm_num)]
    congr 1; field_simp [ha_pos.ne']; ring
  have harg_eq : n * (2 * π * x / 3) = 4 * π * Real.sqrt (a * t) := by
    dsimp [x, n]
    have h1 : (12 * a) * (2 * π * Real.sqrt (3 * t / (12 * a)) / 3) =
        4 * π * (2 * a * Real.sqrt (t / (4 * a))) := by
      have h312 : 3 * t / (12 * a) = t / (4 * a) := by ring
      rw [h312]; ring
    rw [h1]
    congr 1
    have h2 : 2 * a = Real.sqrt (4 * a ^ 2) := by
      rw [show 4 * a ^ 2 = (2 * a) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    rw [h2, ← Real.sqrt_mul (by positivity)]
    congr 1; field_simp [ha_pos.ne']
  have h2x_pow : (2 * x) ^ (C.src.w - 1) = (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) := by
    rw [h2x_eq, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have hAs_eq : besselAs (n * (2 * π * x / 3)) =
      (a * t) ^ (-(1 / 4 : ℝ)) * Real.exp (4 * π * Real.sqrt (a * t)) / (2 * π * Real.sqrt 2) := by
    rw [harg_eq]
    unfold besselAs
    have hrt : Real.sqrt (2 * π * (4 * π * Real.sqrt (a * t))) =
        2 * π * Real.sqrt 2 * (a * t) ^ (1 / 4 : ℝ) := by
      have h2π : (2 * π : ℝ) = Real.sqrt ((2 * π) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      have h_eq : Real.sqrt 2 * (a * t) ^ (1 / 4 : ℝ) = Real.sqrt (2 * Real.sqrt (a * t)) := by
        have hrt_sub : (a * t) ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt (a * t)) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          norm_num
        rw [hrt_sub, ← Real.sqrt_mul (by norm_num)]
      calc Real.sqrt (2 * π * (4 * π * Real.sqrt (a * t)))
          = Real.sqrt ((2 * π) ^ 2 * (2 * Real.sqrt (a * t))) := by congr 1; ring
        _ = Real.sqrt ((2 * π) ^ 2) * Real.sqrt (2 * Real.sqrt (a * t)) :=
            Real.sqrt_mul (by positivity) _
        _ = (2 * π) * (Real.sqrt 2 * (a * t) ^ (1 / 4 : ℝ)) := by rw [← h2π, h_eq]
        _ = 2 * π * Real.sqrt 2 * (a * t) ^ (1 / 4 : ℝ) := by ring
    rw [hrt, Real.rpow_neg (by positivity)]
    have hpi_ne : (2 * π : ℝ) ≠ 0 := by positivity
    have hrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
    have hat_ne : (a * t) ^ (1 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    field_simp [hpi_ne, hrt2_ne, hat_ne]
  have hdens_eq : C.src.cardyDensity a t = 2 * π * C.src.cardyV a t := rfl
  rw [hdens_eq]
  have hmul := mul_le_mul_of_nonneg_left hV_lb (by positivity : 0 ≤ 2 * π)
  rw [h2x_pow, hAs_eq] at hmul
  have hlhs : 2 * π * (amp_lb / 2 * ((t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) *
        ((a * t) ^ (-(1 / 4 : ℝ)) * Real.exp (4 * π * Real.sqrt (a * t)) /
          (2 * π * Real.sqrt 2)))) =
      c_vac * rhoLowerCore C.src.w a t := by
    dsimp [c_vac, rhoLowerCore]
    have hpi_ne : (2 * π : ℝ) ≠ 0 := by positivity
    field_simp [hpi_ne]
  linarith [hmul]

/-! ### Section 3: Unconditional counting bound (`int:counting`) -/

private lemma srcFun_abs_le {src : ShiftSource} {a : ℝ} (_hshift : src.ShiftLE a)
    {β : ℝ} (hβ : 0 < β) :
    |src.srcFun a β| ≤ src.tv * Real.exp (2 * π * a * β) := by
  unfold ShiftSource.srcFun ShiftSource.tv
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hj := src.hshift j
  have hle : a - src.shift j ≤ a := sub_le_self a hj
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hβ.le

/-- **Crossing counting bound (`int:counting`)**: unconditional upper bound on `Z_0(1)` and
`ν⁰([T, R])` for any `SourceCrossingMeasure C.src a` supported on `[T, ∞)` with `T ≥ max 1 w`. -/
theorem commonSource_counting_bound (C : CommonSource) {a T : ℝ}
    (ha : max C.a₀ (max 1 (C.src.w : ℝ)) ≤ a) (hT : max 1 (C.src.w : ℝ) ≤ T)
    (meas : SourceCrossingMeasure C.src a) (hsupp : meas.ν (Ici T)ᶜ = 0) :
    (∫ t in Ici T, Real.exp (-2 * π * t) ∂meas.ν ≤ C.src.tv * Real.exp (4 * π * a)) ∧
    (∀ R : ℝ, 1 ≤ R →
      meas.ν.real (Icc T R) ≤
        3 * C.src.tv * R ^ ((C.src.w : ℝ) / 2) * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * R))) := by
  have ha0 : C.a₀ ≤ a := (le_max_left _ _).trans ha
  have hshift : C.src.ShiftLE a := (C.at_ ha0).shift
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have ha_pos : 0 < a := by linarith
  have hw1 : 1 ≤ C.src.w := C.src.hw
  have hTw : (C.src.w : ℝ) ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hae_T : ∀ᵐ t ∂meas.ν, T ≤ t := by
    have hnot : ∀ᵐ t ∂meas.ν, t ∉ (Ici T)ᶜ := measure_eq_zero_iff_ae_notMem.1 hsupp
    filter_upwards [hnot] with t ht
    exact not_not.mp ht
  let Z : ℝ → ℝ := fun β => ∫ t in Ici T, Real.exp (-2 * π * β * t) ∂meas.ν
  have hint_IciT : ∀ {β : ℝ}, 0 < β →
      IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici T) meas.ν := fun {β} hβ =>
    (meas.finite_laplace hβ).mono_set (Ici_subset_Ici.2 (by linarith))
  have hZ_eq_Ici0 : ∀ {β : ℝ}, 0 < β →
      Z β = ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
    intro β _
    have hae_0 : ∀ᵐ t ∂meas.ν, t ∈ Ici (0 : ℝ) :=
      hae_T.mono fun t ht => show (0 : ℝ) ≤ t by linarith [ht, hT1]
    have hrestr1 : meas.ν.restrict (Ici T) = meas.ν :=
      Measure.restrict_eq_self_of_ae_mem hae_T
    have hrestr2 : meas.ν.restrict (Ici 0) = meas.ν :=
      Measure.restrict_eq_self_of_ae_mem hae_0
    dsimp [Z]
    rw [hrestr1, hrestr2]
  have hcross_Z : ∀ {β : ℝ}, 0 < β →
      Z β - β ^ (-(C.src.w : ℝ)) * Z β⁻¹ =
        β ^ (-(C.src.w : ℝ)) * C.src.srcFun a β⁻¹ - C.src.srcFun a β := by
    intro β hβ
    have hL1 := meas.finite_laplace hβ
    have hL2 := meas.finite_laplace (inv_pos.mpr hβ)
    have h2_eq : ∀ t : ℝ, Real.exp (-2 * π * t / β) = Real.exp (-2 * π * β⁻¹ * t) := fun t => by
      congr 1; ring
    have hZ_sub : ∫ t in Ici 0, thermalDiff C.src.w β t ∂meas.ν =
        Z β - β ^ (-(C.src.w : ℝ)) * Z β⁻¹ := by
      have htherm : (fun t => thermalDiff C.src.w β t) =
          fun t => Real.exp (-2 * π * β * t) -
            β ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
        ext t; unfold thermalDiff; rw [h2_eq t]
      rw [htherm, integral_sub hL1 (hL2.const_mul _), integral_const_mul,
        hZ_eq_Ici0 hβ, hZ_eq_Ici0 (inv_pos.mpr hβ)]
    have hR_sub : ∫ t in Ioi 0, thermalDiff C.src.w β t * C.src.cardyDensity a t =
        β ^ (-(C.src.w : ℝ)) * C.src.srcFun a β⁻¹ - C.src.srcFun a β := by
      have hc1 := C.src.cardyV_laplace a hβ
      have hc2 := C.src.cardyV_laplace a (inv_pos.mpr hβ)
      have hfun : (fun t => thermalDiff C.src.w β t * C.src.cardyDensity a t) =
          fun t => 2 * π * (C.src.cardyV a t * Real.exp (-2 * π * β * t)) -
            β ^ (-(C.src.w : ℝ)) * (2 * π * (C.src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t))) := by
        ext t
        unfold thermalDiff ShiftSource.cardyDensity
        rw [h2_eq t]; ring
      rw [hfun, integral_sub (hc1.1.const_mul _) ((hc2.1.const_mul _).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, hc1.2, hc2.2]
      have hpow_mul : β ^ (-(C.src.w : ℝ)) * (β⁻¹) ^ (-(C.src.w : ℝ)) = 1 := by
        rw [Real.inv_rpow hβ.le, ← Real.rpow_neg hβ.le, neg_neg, ← Real.rpow_add hβ,
          neg_add_cancel, Real.rpow_zero]
      rw [inv_inv, ← mul_assoc, hpow_mul, one_mul]
    rw [← hZ_sub, ← hR_sub]
    exact meas.crossing hβ
  have hZ_mono : ∀ {β₁ β₂ : ℝ}, 0 < β₁ → β₁ ≤ β₂ → Z β₂ ≤ Z β₁ := by
    intro β₁ β₂ hβ₁ hble
    refine setIntegral_mono_on (hint_IciT (hβ₁.trans_le hble)) (hint_IciT hβ₁)
      measurableSet_Ici fun t ht => ?_
    apply Real.exp_le_exp.mpr
    have ht0 : 0 ≤ t := by have : T ≤ t := ht; linarith [hT1]
    have hmul : 2 * π * β₁ * t ≤ 2 * π * β₂ * t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hble (by positivity)) ht0
    linarith
  have hZ_half_lb : Real.exp (π * T) * Z 1 ≤ Z (1 / 2) := by
    have hmul : ∀ᵐ t ∂meas.ν.restrict (Ici T),
        Real.exp (π * T) * Real.exp (-2 * π * 1 * t) ≤ Real.exp (-2 * π * (1 / 2) * t) := by
      rw [ae_restrict_iff' measurableSet_Ici]
      refine Eventually.of_forall fun t ht => ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htT : T ≤ t := ht
      nlinarith [Real.pi_pos]
    calc Real.exp (π * T) * Z 1
        = ∫ t in Ici T, Real.exp (π * T) * Real.exp (-2 * π * 1 * t) ∂meas.ν := by
          rw [← integral_const_mul]
      _ ≤ Z (1 / 2) := integral_mono_ae ((hint_IciT one_pos).const_mul _) (hint_IciT (by positivity)) hmul
  have hZ_two_ub : Z 2 ≤ Real.exp (-2 * π * T) * Z 1 := by
    have hmul : ∀ᵐ t ∂meas.ν.restrict (Ici T),
        Real.exp (-2 * π * 2 * t) ≤ Real.exp (-2 * π * T) * Real.exp (-2 * π * 1 * t) := by
      rw [ae_restrict_iff' measurableSet_Ici]
      refine Eventually.of_forall fun t ht => ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htT : T ≤ t := ht
      nlinarith [Real.pi_pos]
    calc Z 2 ≤ ∫ t in Ici T, Real.exp (-2 * π * T) * Real.exp (-2 * π * 1 * t) ∂meas.ν :=
          integral_mono_ae (hint_IciT two_pos) ((hint_IciT one_pos).const_mul _) hmul
      _ = Real.exp (-2 * π * T) * Z 1 := integral_const_mul _ _
  have hZ1_le : Z 1 ≤ C.src.tv * Real.exp (4 * π * a) := by
    have hcr := hcross_Z (β := 1 / 2) (by norm_num)
    have hinv2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    have hpow2 : (1 / 2 : ℝ) ^ (-(C.src.w : ℝ)) = (2 : ℝ) ^ (C.src.w : ℝ) := by
      rw [one_div, Real.inv_rpow zero_le_two, Real.rpow_neg zero_le_two, inv_inv]
    rw [hinv2, hpow2] at hcr
    have hv2 : |C.src.srcFun a 2| ≤ C.src.tv * Real.exp (4 * π * a) := by
      have h := srcFun_abs_le hshift (by norm_num : (0 : ℝ) < 2)
      rwa [show 2 * π * a * 2 = 4 * π * a by ring] at h
    have hvh : |C.src.srcFun a (1 / 2)| ≤ C.src.tv * Real.exp (π * a) := by
      have h := srcFun_abs_le hshift (by norm_num : (0 : ℝ) < 1 / 2)
      rwa [show 2 * π * a * (1 / 2) = π * a by ring] at h
    have hsum_v : (2 : ℝ) ^ (C.src.w : ℝ) * C.src.srcFun a 2 - C.src.srcFun a (1 / 2) ≤
        ((2 : ℝ) ^ (C.src.w : ℝ) + 1) * C.src.tv * Real.exp (4 * π * a) := by
      have hv2_ub := (abs_le.mp hv2).2
      have hvh_lb := (abs_le.mp hvh).1
      have hexp_le : Real.exp (π * a) ≤ Real.exp (4 * π * a) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have htv_nn : 0 ≤ C.src.tv := C.src.tv_nonneg
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (C.src.w : ℝ) by positivity]
    have hgap : (2 : ℝ) ^ (C.src.w : ℝ) + 1 ≤
        Real.exp (π * T) - (2 : ℝ) ^ (C.src.w : ℝ) * Real.exp (-2 * π * T) := by
      have h3w : 3 * (C.src.w : ℝ) ≤ π * T := by
        nlinarith [Real.pi_gt_three]
      have h8w : (8 : ℝ) ^ (C.src.w : ℝ) ≤ Real.exp (π * T) := by
        have h8_le : (8 : ℝ) ≤ Real.exp 3 := by
          have := Real.exp_one_gt_d9
          have h3 : (2.718 : ℝ) ^ 3 ≤ Real.exp 3 := by
            calc (2.718 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
                  pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 3
              _ = Real.exp ((3 : ℕ) * 1) := (Real.exp_nat_mul 1 3).symm
              _ = Real.exp 3 := by norm_num
          linarith [show (8 : ℝ) ≤ (2.718 : ℝ) ^ 3 by norm_num]
        calc (8 : ℝ) ^ (C.src.w : ℝ) ≤ (Real.exp 3) ^ (C.src.w : ℝ) :=
              Real.rpow_le_rpow (by positivity) h8_le (by positivity)
          _ = (Real.exp 3) ^ C.src.w := Real.rpow_natCast _ _
          _ = Real.exp ((C.src.w : ℝ) * 3) := (Real.exp_nat_mul 3 C.src.w).symm
          _ = Real.exp (3 * (C.src.w : ℝ)) := by ring_nf
          _ ≤ Real.exp (π * T) := Real.exp_le_exp.mpr h3w
      have he_neg : Real.exp (-2 * π * T) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
      have h2w_ge : (2 : ℝ) ≤ (2 : ℝ) ^ (C.src.w : ℝ) := by
        have : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (C.src.w : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hw1)
        simpa using this
      have h8_eq : (8 : ℝ) ^ (C.src.w : ℝ) = (2 : ℝ) ^ (C.src.w : ℝ) * (4 : ℝ) ^ (C.src.w : ℝ) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]; norm_num
      have h4_ge : (4 : ℝ) ≤ (4 : ℝ) ^ (C.src.w : ℝ) := by
        have : (4 : ℝ) ^ (1 : ℝ) ≤ (4 : ℝ) ^ (C.src.w : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hw1)
        simpa using this
      nlinarith
    have hZ1_nn : 0 ≤ Z 1 := setIntegral_nonneg measurableSet_Ici fun t _ => (Real.exp_pos _).le
    have hineq : (Real.exp (π * T) - (2 : ℝ) ^ (C.src.w : ℝ) * Real.exp (-2 * π * T)) * Z 1 ≤
        ((2 : ℝ) ^ (C.src.w : ℝ) + 1) * C.src.tv * Real.exp (4 * π * a) := by
      have hmul_ub : (2 : ℝ) ^ (C.src.w : ℝ) * Z 2 ≤
          (2 : ℝ) ^ (C.src.w : ℝ) * (Real.exp (-2 * π * T) * Z 1) :=
        mul_le_mul_of_nonneg_left hZ_two_ub (by positivity)
      calc (Real.exp (π * T) - (2 : ℝ) ^ (C.src.w : ℝ) * Real.exp (-2 * π * T)) * Z 1
          = Real.exp (π * T) * Z 1 - (2 : ℝ) ^ (C.src.w : ℝ) * (Real.exp (-2 * π * T) * Z 1) := by ring
        _ ≤ Z (1 / 2) - (2 : ℝ) ^ (C.src.w : ℝ) * Z 2 := sub_le_sub hZ_half_lb hmul_ub
        _ = (2 : ℝ) ^ (C.src.w : ℝ) * C.src.srcFun a 2 - C.src.srcFun a (1 / 2) := hcr
        _ ≤ ((2 : ℝ) ^ (C.src.w : ℝ) + 1) * C.src.tv * Real.exp (4 * π * a) := hsum_v
    have h2w1_pos : (0 : ℝ) < (2 : ℝ) ^ (C.src.w : ℝ) + 1 := by positivity
    have hineq2 : ((2 : ℝ) ^ (C.src.w : ℝ) + 1) * Z 1 ≤
        ((2 : ℝ) ^ (C.src.w : ℝ) + 1) * (C.src.tv * Real.exp (4 * π * a)) := by
      have hmul := mul_le_mul_of_nonneg_right hgap hZ1_nn
      linarith
    exact le_of_mul_le_mul_left hineq2 h2w1_pos
  refine ⟨by simpa [Z] using hZ1_le, fun R hR => ?_⟩
  by_cases hTR : R < T
  · have hemp : Icc T R = ∅ := Icc_eq_empty_of_lt hTR
    rw [hemp, measureReal_empty]
    have htv_nn : 0 ≤ C.src.tv := C.src.tv_nonneg
    positivity
  · have hle_TR : T ≤ R := not_lt.mp hTR
    set β : ℝ := min 1 (Real.sqrt (a / R))
    have hR_pos : 0 < R := by linarith
    have hβ_pos : 0 < β := lt_min one_pos (Real.sqrt_pos.mpr (div_pos ha_pos hR_pos))
    have hβ_le1 : β ≤ 1 := min_le_left _ _
    have h1_le_binv : 1 ≤ β⁻¹ := (one_le_inv₀ hβ_pos).mpr hβ_le1
    have hZinv_le : Z β⁻¹ ≤ Z 1 := hZ_mono one_pos h1_le_binv
    have hcr := hcross_Z hβ_pos
    have hZβ_le : Z β ≤ β ^ (-(C.src.w : ℝ)) * (Z 1 + |C.src.srcFun a β⁻¹|) + |C.src.srcFun a β| := by
      have h1 : Z β = β ^ (-(C.src.w : ℝ)) * Z β⁻¹ + β ^ (-(C.src.w : ℝ)) * C.src.srcFun a β⁻¹ -
          C.src.srcFun a β := by linarith
      have hpow_nn : 0 ≤ β ^ (-(C.src.w : ℝ)) := Real.rpow_nonneg hβ_pos.le _
      have hmul := mul_le_mul_of_nonneg_left (add_le_add hZinv_le (le_abs_self (C.src.srcFun a β⁻¹))) hpow_nn
      linarith [neg_le_abs (C.src.srcFun a β)]
    have hpow_ge1 : 1 ≤ β ^ (-(C.src.w : ℝ)) := by
      rw [Real.rpow_neg hβ_pos.le, one_le_inv₀ (Real.rpow_pos_of_pos hβ_pos _)]
      exact Real.rpow_le_one hβ_pos.le hβ_le1 (by positivity)
    have hsrc1 : |C.src.srcFun a β⁻¹| ≤ C.src.tv * Real.exp (2 * π * a / β) := by
      have h := srcFun_abs_le hshift (inv_pos.mpr hβ_pos)
      rwa [show 2 * π * a * β⁻¹ = 2 * π * a / β by rw [div_eq_mul_inv]] at h
    have hsrc2 : |C.src.srcFun a β| ≤ C.src.tv * Real.exp (2 * π * a * β) :=
      srcFun_abs_le hshift hβ_pos
    have hexp_1 : Real.exp (4 * π * a) ≤ Real.exp (4 * π * a + 2 * π * a / β) :=
      Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity))
    have hexp_2 : Real.exp (2 * π * a / β) ≤ Real.exp (4 * π * a + 2 * π * a / β) :=
      Real.exp_le_exp.mpr (le_add_of_nonneg_left (by positivity))
    have hexp_3 : Real.exp (2 * π * a * β) ≤ Real.exp (4 * π * a + 2 * π * a / β) := by
      apply Real.exp_le_exp.mpr
      have h1 : 2 * π * a * β ≤ 2 * π * a := by
        simpa using mul_le_mul_of_nonneg_left hβ_le1 (by positivity)
      have h2 : 0 ≤ 2 * π * a / β := by positivity
      have h3 : 0 ≤ 2 * π * a := by positivity
      linarith
    have hZβ_ub : Z β ≤ β ^ (-(C.src.w : ℝ)) * (3 * C.src.tv * Real.exp (4 * π * a + 2 * π * a / β)) := by
      have hpow_nn : 0 ≤ β ^ (-(C.src.w : ℝ)) := Real.rpow_nonneg hβ_pos.le _
      have htv_nn : 0 ≤ C.src.tv := C.src.tv_nonneg
      have hsum1 : Z 1 + |C.src.srcFun a β⁻¹| ≤ 2 * C.src.tv * Real.exp (4 * π * a + 2 * π * a / β) := by
        have h1 : Z 1 ≤ C.src.tv * Real.exp (4 * π * a + 2 * π * a / β) :=
          hZ1_le.trans (mul_le_mul_of_nonneg_left hexp_1 htv_nn)
        have h2 : |C.src.srcFun a β⁻¹| ≤ C.src.tv * Real.exp (4 * π * a + 2 * π * a / β) :=
          hsrc1.trans (mul_le_mul_of_nonneg_left hexp_2 htv_nn)
        linarith
      have h3 : |C.src.srcFun a β| ≤ β ^ (-(C.src.w : ℝ)) * (C.src.tv * Real.exp (4 * π * a + 2 * π * a / β)) := by
        have h3a : |C.src.srcFun a β| ≤ C.src.tv * Real.exp (4 * π * a + 2 * π * a / β) :=
          hsrc2.trans (mul_le_mul_of_nonneg_left hexp_3 htv_nn)
        calc |C.src.srcFun a β| ≤ 1 * (C.src.tv * Real.exp (4 * π * a + 2 * π * a / β)) := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_right hpow_ge1 (by positivity)
      calc Z β ≤ β ^ (-(C.src.w : ℝ)) * (Z 1 + |C.src.srcFun a β⁻¹|) + |C.src.srcFun a β| := hZβ_le
        _ ≤ β ^ (-(C.src.w : ℝ)) * (2 * C.src.tv * Real.exp (4 * π * a + 2 * π * a / β)) +
              β ^ (-(C.src.w : ℝ)) * (C.src.tv * Real.exp (4 * π * a + 2 * π * a / β)) :=
            add_le_add (mul_le_mul_of_nonneg_left hsum1 hpow_nn) h3
        _ = _ := by ring
    have hmarkov : Real.exp (-2 * π * β * R) * meas.ν.real (Icc T R) ≤ Z β := by
      have hIcc_fin : meas.ν (Icc T R) < ∞ := by
        have hexp_pos : 0 < Real.exp (-2 * π * R) := Real.exp_pos _
        have hle_m : ENNReal.ofReal (Real.exp (-2 * π * R)) * meas.ν (Icc T R) ≤
            ∫⁻ t in Ici T, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
          calc ENNReal.ofReal (Real.exp (-2 * π * R)) * meas.ν (Icc T R)
              = ∫⁻ _ in Icc T R, ENNReal.ofReal (Real.exp (-2 * π * R)) ∂meas.ν := by
                rw [setLIntegral_const]
            _ ≤ ∫⁻ t in Icc T R, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
                refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
                exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.2]))
            _ ≤ ∫⁻ t in Ici T, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν :=
                lintegral_mono_set Set.Icc_subset_Ici_self
        have hlt := lt_of_le_of_lt hle_m (hint_IciT one_pos).lintegral_lt_top
        exact (ENNReal.mul_lt_top_iff.mp hlt).elim (fun h => h.2)
          (fun h => h.elim (fun h0 => absurd h0 (ENNReal.ofReal_pos.mpr hexp_pos).ne')
            (fun h0 => by simp [h0]))
      have h1 : IntegrableOn (fun _ => Real.exp (-2 * π * β * R)) (Icc T R) meas.ν :=
        integrableOn_const hIcc_fin.ne
      have h2 : IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Icc T R) meas.ν :=
        (hint_IciT hβ_pos).mono_set Set.Icc_subset_Ici_self
      calc Real.exp (-2 * π * β * R) * meas.ν.real (Icc T R)
          = ∫ _ in Icc T R, Real.exp (-2 * π * β * R) ∂meas.ν := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ ∫ t in Icc T R, Real.exp (-2 * π * β * t) ∂meas.ν := by
            refine setIntegral_mono_on h1 h2 measurableSet_Icc fun t ht => ?_
            have htR : t ≤ R := ht.2
            exact Real.exp_le_exp.mpr (by
              have hle : 2 * π * β * t ≤ 2 * π * β * R :=
                mul_le_mul_of_nonneg_left htR (by positivity)
              linarith)
        _ ≤ Z β := by
            refine setIntegral_mono_set (hint_IciT hβ_pos) ?_
              (Eventually.of_forall fun _ ht => Set.Icc_subset_Ici_self ht)
            exact Eventually.of_forall fun t => (Real.exp_pos _).le
    have hmeas_ub : meas.ν.real (Icc T R) ≤
        Real.exp (2 * π * β * R) *
          (β ^ (-(C.src.w : ℝ)) * (3 * C.src.tv * Real.exp (4 * π * a + 2 * π * a / β))) := by
      have h1 := mul_le_mul_of_nonneg_left (hmarkov.trans hZβ_ub) (Real.exp_pos (2 * π * β * R)).le
      have hcan : Real.exp (2 * π * β * R) * Real.exp (-2 * π * β * R) = 1 := by
        rw [← Real.exp_add]; simp
      rwa [← mul_assoc, hcan, one_mul] at h1
    have hβ_pow : β ^ (-(C.src.w : ℝ)) ≤ R ^ ((C.src.w : ℝ) / 2) := by
      by_cases haR : a ≤ R
      · have hβeq : β = Real.sqrt (a / R) := min_eq_right (Real.sqrt_le_one.mpr ((div_le_one hR_pos).mpr haR))
        rw [hβeq, Real.rpow_neg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        have heq_w : (1 / 2 : ℝ) * (C.src.w : ℝ) = (C.src.w : ℝ) / 2 := by ring
        rw [heq_w, ← Real.inv_rpow (by positivity), inv_div]
        exact Real.rpow_le_rpow (by positivity) (div_le_self hR_pos.le ha1) (by positivity)
      · have hRa : R < a := not_le.mp haR
        have hβeq : β = 1 := min_eq_left ((Real.le_sqrt zero_le_one (by positivity)).mpr
          (by rw [one_pow, le_div_iff₀ hR_pos]; linarith))
        rw [hβeq, Real.one_rpow]
        exact Real.one_le_rpow hR (by positivity)
    have hexp_sum : 2 * π * β * R + (4 * π * a + 2 * π * a / β) ≤
        6 * π * a + 4 * π * Real.sqrt (a * R) := by
      by_cases haR : a ≤ R
      · have hβeq : β = Real.sqrt (a / R) := min_eq_right (Real.sqrt_le_one.mpr ((div_le_one hR_pos).mpr haR))
        rw [hβeq]
        have h1 : Real.sqrt (a / R) * R = Real.sqrt (a * R) := by
          have hRrt : R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hR_pos.le).symm
          nth_rw 2 [hRrt]
          rw [← Real.sqrt_mul (by positivity)]
          congr 1; field_simp [hR_pos.ne']
        have h2 : a / Real.sqrt (a / R) = Real.sqrt (a * R) := by
          have hart : a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha_pos.le).symm
          nth_rw 1 [hart]
          rw [← Real.sqrt_div (by positivity)]
          congr 1; field_simp [ha_pos.ne']
        have hsum : 2 * π * Real.sqrt (a / R) * R + (4 * π * a + 2 * π * a / Real.sqrt (a / R)) =
            4 * π * a + 4 * π * Real.sqrt (a * R) := by
          calc 2 * π * Real.sqrt (a / R) * R + (4 * π * a + 2 * π * a / Real.sqrt (a / R))
              = 2 * π * (Real.sqrt (a / R) * R) + 4 * π * a + 2 * π * (a / Real.sqrt (a / R)) := by ring
            _ = 4 * π * a + 4 * π * Real.sqrt (a * R) := by rw [h1, h2]; ring
        rw [hsum]
        have h2pia : 0 ≤ 2 * π * a := by positivity
        linarith
      · have hRa : R < a := not_le.mp haR
        have hβeq : β = 1 := min_eq_left ((Real.le_sqrt zero_le_one (by positivity)).mpr
          (by rw [one_pow, le_div_iff₀ hR_pos]; linarith))
        rw [hβeq, mul_one, div_one]
        have hR_le : R ≤ Real.sqrt (a * R) := by
          rw [Real.le_sqrt hR_pos.le (by positivity), sq]
          exact mul_le_mul_of_nonneg_right hRa.le hR_pos.le
        have h2R_le : 2 * π * R ≤ 4 * π * Real.sqrt (a * R) := by
          have h1 : 2 * π * R ≤ 2 * π * Real.sqrt (a * R) :=
            mul_le_mul_of_nonneg_left hR_le (by positivity)
          have h2 : 0 ≤ 2 * π * Real.sqrt (a * R) := by positivity
          linarith
        linarith
    calc meas.ν.real (Icc T R)
        ≤ Real.exp (2 * π * β * R) *
            (β ^ (-(C.src.w : ℝ)) * (3 * C.src.tv * Real.exp (4 * π * a + 2 * π * a / β))) := hmeas_ub
      _ = β ^ (-(C.src.w : ℝ)) * (3 * C.src.tv *
            (Real.exp (2 * π * β * R) * Real.exp (4 * π * a + 2 * π * a / β))) := by ring
      _ = β ^ (-(C.src.w : ℝ)) * (3 * C.src.tv * Real.exp (2 * π * β * R + (4 * π * a + 2 * π * a / β))) := by
          rw [← Real.exp_add]
      _ ≤ R ^ ((C.src.w : ℝ) / 2) * (3 * C.src.tv * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * R))) := by
          have hexp_le := Real.exp_le_exp.mpr hexp_sum
          have htv_nn : 0 ≤ C.src.tv := C.src.tv_nonneg
          exact mul_le_mul hβ_pow (mul_le_mul_of_nonneg_left hexp_le (by positivity))
            (by positivity) (by positivity)
      _ = 3 * C.src.tv * R ^ ((C.src.w : ℝ) / 2) * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * R)) := by
          ring

/-! ### Section 4: Repair & Sonine input (`int:repair`, `int:sonine`) -/

/-- Operator-theoretic & Hankel repair input for `int:atom` (`int:repair` and `int:sonine`
from `integrality.tex`, whose polynomial Taylor step `hankelDual_bound` and projection identity
`repair_identity_*` are already proved in `Integrality/RepairTaylor.lean` and
`Integrality/RepairIdentity.lean`, while Weber's identity and `int:sonine` remain open). -/
structure IntRepairSonineInput (w : ℕ) where
  C_son : ℝ
  hC_son_nn : 0 ≤ C_son
  repair : ∀ {B₀ B : ℝ}, 0 < B₀ → B₀ < B → ∀ (M : ℕ)
    {σ μ : Measure ℝ} [IsFiniteMeasure σ] [IsFiniteMeasure μ],
    σ (Icc B₀ B)ᶜ = 0 → μ (Icc B₀ B)ᶜ = 0 →
    (∀ P : ℝ[X], P.degree ≤ M → ∫ s, P.eval s ∂σ = ∫ s, P.eval s ∂μ) →
    ∃ r : ℝ → ℝ, ContinuousOn r (Ioi B) ∧
      (∀ {β : ℝ}, 0 < β →
        IntegrableOn (fun t => Real.exp (-2 * π * β * t) * |r t|) (Ioi B) ∧
        (∫ s, thermalDiff w β s ∂σ - ∫ s, thermalDiff w β s ∂μ +
          ∫ t in Ioi B, thermalDiff w β t * r t = 0)) ∧
      (∀ {t : ℝ}, B < t →
        let h := (B - B₀) / 2
        let m : ℕ := M + 1
        |r t| ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
          (min 1 ((2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
            C_son * Real.exp (C_son * (B + w)) *
              (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m))

lemma rpow_weighted_taylor_le {P : ℝ} (hP : 0 < P) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-2 * π * x) * (2 * π * Real.exp 1 * x / ((m : ℝ) * Real.sqrt P)) ^ m ≤
      P ^ (-(m : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp; positivity
  · have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have hsqP_pos : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
    let u : ℝ := 2 * π * x / m
    have hu_nn : 0 ≤ u := by positivity
    have heu : Real.exp 1 * u ≤ Real.exp u := by
      have h1 : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
      calc Real.exp 1 * u ≤ Real.exp 1 * Real.exp (u - 1) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le
        _ = Real.exp u := by rw [← Real.exp_add]; congr 1; ring
    have heu_pow : (Real.exp 1 * u) ^ m ≤ Real.exp (2 * π * x) := by
      calc (Real.exp 1 * u) ^ m ≤ (Real.exp u) ^ m := pow_le_pow_left₀ (by positivity) heu m
        _ = Real.exp (m * u) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (2 * π * x) := by
            dsimp [u]; field_simp [hm_pos.ne']
    have hfac_eq : 2 * π * Real.exp 1 * x / ((m : ℝ) * Real.sqrt P) =
        (Real.exp 1 * u) / Real.sqrt P := by
      dsimp [u]; ring
    rw [hfac_eq, div_pow]
    have hcan : Real.exp (-2 * π * x) * Real.exp (2 * π * x) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-2 * π * x) * ((Real.exp 1 * u) ^ m / Real.sqrt P ^ m)
        ≤ Real.exp (-2 * π * x) * (Real.exp (2 * π * x) / Real.sqrt P ^ m) := by
          gcongr
      _ = (Real.exp (-2 * π * x) * Real.exp (2 * π * x)) * (Real.sqrt P ^ m)⁻¹ := by ring
      _ = (Real.sqrt P ^ m)⁻¹ := by rw [hcan, one_mul]
      _ = P ^ (-(m : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ m, ← Real.rpow_mul hP.le,
            ← Real.rpow_neg hP.le]
          congr 1; ring

lemma rpow_half_mul_exp_neg_le_one {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x * Real.exp (-2 * π * x) ≤ 1 := by
  have h1 : Real.sqrt x ≤ 1 + x := by
    have hsq : Real.sqrt x ^ 2 ≤ (1 + x) ^ 2 := by
      rw [Real.sq_sqrt hx]; nlinarith
    exact le_of_sq_le_sq hsq (by positivity)
  have h2 : 1 + x ≤ Real.exp (2 * π * x) := by
    have := Real.add_one_le_exp (2 * π * x)
    nlinarith [Real.pi_gt_three]
  calc Real.sqrt x * Real.exp (-2 * π * x)
      ≤ Real.exp (2 * π * x) * Real.exp (-2 * π * x) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end FormalResearch.ModularBootstrap.Integrality

