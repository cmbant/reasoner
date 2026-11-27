module

public import FormalResearch.ModularBootstrap.Integrality.ChebExplicit
public import FormalResearch.ModularBootstrap.Integrality.ShellInvCells
public import FormalResearch.ModularBootstrap.Integrality.IntClosed
public import FormalResearch.ModularBootstrap.Mixtures.WeightAxioms
public import FormalResearch.ModularBootstrap.Mixtures.O1
public import FormalResearch.ModularBootstrap.Mixtures.CrossingPort

/-!
# Cell-by-cell atomisation of a reserved crossing measure (`int:atom`, Theorem INT-1)

`CFT/modular_bootstrap/paper/integrality.tex`, Theorem INT-1 (`int:atom`):
given a positive crossing measure carrying a uniform multiple `δ ρ` of the Cardy density
`ρ = 2π V` on `[T, ∞)` (`T ≥ a'/8`) and polynomial moment orders `M_k ≥ K H_k / log P_k`
satisfying `(δ / 8) inf_{s ≥ B_{k-1}} ρ(s) ≥ W(M_k)`, produces a locally finite
integer-degeneracy crossing spectrum `ν_ℤ` (`IsIntegerCounting ν_ℤ`) at the same gap `T`.

Contents:
1. Abstract sufficient density floor `SufficientMomentFloor W` and its concrete instantiation
   `sufficientMomentFloor_cheb_explicit` for `W(M) = 8 (M + 1)^{5/2}` (`cheb_explicit`), with
   affine translation from `[-1, 1]` to any closed length-`2` cell `[B_mid - 1, B_mid + 1]`.
2. Unconditional uniform Cardy density lower bound `commonSource_cardyDensity_lower`
   (`int:rho-lower`) for any `C : CommonSource` (covering `(H_w)`, `(H_{w,mix})`, and dominated
   atomic sources `(H_{w,λ})`), with monotone lower envelope on `[a/8, ∞)`.
3. Unconditional crossing counting bound `commonSource_counting_bound` (`int:counting`).
4. Explicit repair & Sonine compression interface `IntRepairSonineInput w` (encapsulating the
   remaining inputs of `int:repair` and `int:sonine`: Weber's crossing identity and the
   exponential Sonine inverse bound `2π B ‖A_{B,w}^{-1}‖ ≤ C exp(C B)`).
5. `int_atom_common` (any `C : CommonSource` and abstract floor `W`),
   `int_atom_cheb_explicit` (instantiated with `W(M) = 8 (M + 1)^{5/2}`), and
   `int_atom_fixedWeight` (for `(H_w)`, `AdmissibleCrossingMeasure prob (c̃ / 12)`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Finset Polynomial
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Mixtures

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
  haveI : IsFiniteMeasure μ0 := Measure.isFiniteMeasure_map μ shiftInv
  have hsupp0 : μ0 (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    rw [Measure.map_apply hm_inv measurableSet_Icc.compl]
    have hsub : shiftInv ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ ⊆ (Set.Icc (B_mid - 1) (B_mid + 1))ᶜ := by
      intro s hs hmem
      apply hs
      simp only [shiftInv, mem_Icc] at hmem ⊢
      constructor <;> linarith
    exact measure_mono_null hsub hsupp
  have hN0 : μ0 Set.univ = Ntot := by
    rw [Measure.map_apply hm_inv MeasurableSet.univ, preimage_univ, hN]
  have hfloor0 : ENNReal.ofReal (W M) • volume.restrict (Set.Icc (-1 : ℝ) 1) ≤ μ0 := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm_inv hA,
      Measure.restrict_apply hA]
    have hmap_vol : volume (A ∩ Set.Icc (-1 : ℝ) 1) =
        volume (shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1)) := by
      have hpre : shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1) =
          (fun x => x - B_mid) ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1) := rfl
      rw [hpre, Real.volume_preimage_sub_right]
    have hsub : shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1) ⊆
        (shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1) := by
      intro s ⟨hsA, hs1, hs2⟩
      exact ⟨hsA, by dsimp [shiftInv] at *; linarith, by dsimp [shiftInv] at *; linarith⟩
    have hle := Measure.le_iff.1 hfloor ((shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1))
      ((hm_inv hA).inter measurableSet_Icc)
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply ((hm_inv hA).inter measurableSet_Icc)] at hle
    calc ENNReal.ofReal (W M) * volume (A ∩ Set.Icc (-1 : ℝ) 1)
        = ENNReal.ofReal (W M) * volume (shiftInv ⁻¹' (A ∩ Set.Icc (-1 : ℝ) 1)) := by rw [hmap_vol]
      _ ≤ ENNReal.ofReal (W M) *
          volume (((shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1)) ∩
            Set.Icc (B_mid - 1) (B_mid + 1)) := by
          gcongr
          rw [inter_assoc, inter_self]
          exact hsub
      _ ≤ μ ((shiftInv ⁻¹' A) ∩ Set.Icc (B_mid - 1) (B_mid + 1)) := hle
      _ ≤ μ (shiftInv ⁻¹' A) := measure_mono inter_subset_left
  obtain ⟨κ, hfin, x, d, hx_mem, hd_pos, hmatch⟩ := hW.2 hM hsupp0 hN0 hfloor0
  refine ⟨κ, hfin, fun k => B_mid + x k, d, fun k => ?_, hd_pos, fun P hP => ?_⟩
  · have hk := hx_mem k
    simp only [mem_Icc] at hk ⊢
    constructor <;> linarith
  · let Q : ℝ[X] := P.comp (Polynomial.X + Polynomial.C B_mid)
    have hQdeg : Q.degree ≤ M := (Polynomial.degree_comp_le).trans (by
      have hdeg1 : (Polynomial.X + Polynomial.C B_mid : ℝ[X]).degree ≤ 1 := by
        compute_degree!
      rcases eq_or_ne P 0 with rfl | hP0
      · simp
      · calc P.degree * (Polynomial.X + Polynomial.C B_mid).degree
            ≤ P.degree * 1 :=
              mul_le_mul_of_nonneg_left hdeg1 (by simp [Polynomial.degree_eq_natDegree hP0])
          _ = P.degree := mul_one _
          _ ≤ M := hP)
    have hQeq : ∀ s : ℝ, Q.eval (shiftInv s) = P.eval s := fun s => by
      dsimp [Q, shiftInv]
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      ring_nf
    have hQint : Integrable (fun y => Q.eval y) μ0 := by
      have hcQ : ContinuousOn (fun y => Q.eval y) (Set.Icc (-1 : ℝ) 1) :=
        Q.continuous.continuousOn
      rw [← Measure.restrict_eq_self_of_ae_mem
        (measure_eq_zero_iff_ae_notMem.1 hsupp0 |>.mono fun y hy => not_not.mp hy)]
      exact isCompact_Icc.integrableOn_of_continuousOn hcQ
    have hmap_int : ∫ y, Q.eval y ∂μ0 = ∫ s, P.eval s ∂μ := by
      rw [MeasureTheory.integral_map hm_inv.aemeasurable hQint.aestronglyMeasurable]
      exact integral_congr_ae (Eventually.of_forall hQeq)
    rw [← hmap_int, hmatch Q hQdeg]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [Q]
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring_nf

/-! ### Section 2: Uniform Cardy density lower bound (`int:rho-lower`) -/

private noncomputable def rhoLowerCore (w : ℕ) (a t : ℝ) : ℝ :=
  (t / a) ^ (((w - 1 : ℕ) : ℝ) / 2) * (a * t) ^ (-(1 / 4 : ℝ)) *
    Real.exp (4 * π * Real.sqrt (a * t))

private lemma rhoLowerCore_pos {w : ℕ} {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    0 < rhoLowerCore w a t := by
  unfold rhoLowerCore; positivity

private lemma rhoLowerCore_mono {w : ℕ} (hw : 1 ≤ w) {a : ℝ} (ha : 8 ≤ a)
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
      exact continuousOn_id.rpow_const fun x hx => Or.inl (by linarith [mem_Ici.mp hx])
    · intro u hu
      rw [interior_Ici] at hu
      have hu_gt : 1 < u := mem_Ioi.mp hu
      have hu_pos : 0 < u := by linarith
      have hd1 : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
          ((-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ) - 1)) u :=
        Real.hasDerivAt_rpow_const (Or.inl hu_pos.ne')
      have hd2 : HasDerivAt (fun x : ℝ => Real.exp (4 * π * x)) (4 * π * Real.exp (4 * π * u)) u := by
        simpa [Function.comp_def] using
          ((hasDerivAt_id u).const_mul (4 * π)).exp.congr_deriv (by ring)
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
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hg_eq t₁ ht₁_pos, hg_eq t₂ ht₂_pos] at hg_le
  unfold rhoLowerCore
  exact mul_le_mul h1 hg_le (by positivity) (by positivity)

/-- **Uniform Cardy density lower bound (`int:rho-lower`)** for any `CommonSource`. -/
theorem commonSource_cardyDensity_lower (C : CommonSource) :
    ∃ c_vac a_star : ℝ, 0 < c_vac ∧ max C.a₀ 8 ≤ a_star ∧
      ∀ {a t : ℝ}, a_star ≤ a → a / 8 ≤ t →
        c_vac * rhoLowerCore C.src.w a t ≤ C.src.cardyDensity a t := by
  have hx0_pos : (0 : ℝ) < 1 / Real.sqrt 32 := by positivity
  obtain ⟨⟨Cx, n₀, hCx_nn, hasymp⟩, -, -, -, -⟩ := pmix_weight_b C hx0_pos
  obtain ⟨_, hnp⟩ := nullPoly_exp_bounds C.F.prob hx0_pos
  set amp_lb : ℝ := C.F.d * C.F.prob.nullPoly (Real.exp (-4 * π * (1 / Real.sqrt 32)))
  have hamp_pos : 0 < amp_lb := mul_pos C.F.hd (hnp le_rfl).1
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
        rw [← Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
        congr 1
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [mul_assoc, h_eq, h2π, ← Real.sqrt_mul (by positivity)]
      congr 1; ring
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

private lemma srcFun_abs_le {src : ShiftSource} {a : ℝ} (hshift : src.ShiftLE a)
    {β : ℝ} (hβ : 0 < β) :
    |src.srcFun a β| ≤ src.tv * Real.exp (2 * π * a * β) := by
  unfold ShiftSource.srcFun ShiftSource.tv
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hj := src.hshift j
  nlinarith [Real.pi_pos]

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
      IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici T) meas.ν := fun hβ =>
    (meas.finite_laplace hβ).mono_set (Ici_subset_Ici.2 (by linarith))
  have hZ_eq_Ici0 : ∀ {β : ℝ}, 0 < β →
      Z β = ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
    intro β _
    have hae_0 : ∀ᵐ t ∂meas.ν, t ∈ Ici (0 : ℝ) := hae_T.mono fun t ht => by linarith
    dsimp [Z]
    rw [Measure.restrict_eq_self_of_ae_mem hae_T, Measure.restrict_eq_self_of_ae_mem hae_0]
  have hcross_Z : ∀ {β : ℝ}, 0 < β →
      Z β - β ^ (-(C.src.w : ℝ)) * Z β⁻¹ =
        β ^ (-(C.src.w : ℝ)) * C.src.srcFun a β⁻¹ - C.src.srcFun a β := by
    intro β hβ
    have hL1 := meas.finite_laplace hβ
    have hL2 := meas.finite_laplace (inv_pos.mpr hβ)
    have h2_eq : (fun t => Real.exp (-2 * π * t / β)) =
        fun t => Real.exp (-2 * π * β⁻¹ * t) := by
      ext t; simp [div_eq_mul_inv, mul_comm, mul_assoc]
    have hZ_sub : ∫ t in Ici 0, thermalDiff C.src.w β t ∂meas.ν =
        Z β - β ^ (-(C.src.w : ℝ)) * Z β⁻¹ := by
      have htherm : (fun t => thermalDiff C.src.w β t) =
          fun t => Real.exp (-2 * π * β * t) -
            β ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
        ext t; unfold thermalDiff; rw [h2_eq]
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
        rw [h2_eq]; ring
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
      measurableSet_Ici fun t _ => ?_
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, show 0 ≤ t by linarith [mem_Ici.mp (by assumption : t ∈ Ici T)]]
  have hZ_half_lb : Real.exp (π * T) * Z 1 ≤ Z (1 / 2) := by
    have hmul : (fun t => Real.exp (π * T) * Real.exp (-2 * π * 1 * t)) ≤ᵐ[meas.ν.restrict (Ici T)]
        (fun t => Real.exp (-2 * π * (1 / 2) * t)) := by
      rw [ae_restrict_iff' measurableSet_Ici]
      refine Eventually.of_forall fun t ht => ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htT : T ≤ t := mem_Ici.mp ht
      nlinarith [Real.pi_pos]
    calc Real.exp (π * T) * Z 1
        = ∫ t in Ici T, Real.exp (π * T) * Real.exp (-2 * π * 1 * t) ∂meas.ν := by
          rw [← integral_const_mul]
      _ ≤ Z (1 / 2) := integral_mono_ae ((hint_IciT one_pos).const_mul _) (hint_IciT (by positivity)) hmul
  have hZ_two_ub : Z 2 ≤ Real.exp (-2 * π * T) * Z 1 := by
    have hmul : (fun t => Real.exp (-2 * π * 2 * t)) ≤ᵐ[meas.ν.restrict (Ici T)]
        (fun t => Real.exp (-2 * π * T) * Real.exp (-2 * π * 1 * t)) := by
      rw [ae_restrict_iff' measurableSet_Ici]
      refine Eventually.of_forall fun t ht => ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htT : T ≤ t := mem_Ici.mp ht
      nlinarith [Real.pi_pos]
    calc Z 2 ≤ ∫ t in Ici T, Real.exp (-2 * π * T) * Real.exp (-2 * π * 1 * t) ∂meas.ν :=
          integral_mono_ae (hint_IciT two_pos) ((hint_IciT one_pos).const_mul _) hmul
      _ = Real.exp (-2 * π * T) * Z 1 := integral_const_mul _ _
  have hZ1_le : Z 1 ≤ C.src.tv * Real.exp (4 * π * a) := by
    have hcr := hcross_Z (β := 1 / 2) (by norm_num)
    have hinv2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    have hpow2 : (1 / 2 : ℝ) ^ (-(C.src.w : ℝ)) = (2 : ℝ) ^ (C.src.w : ℝ) := by
      rw [one_div, Real.inv_rpow zero_le_two, neg_neg]
    rw [hinv2, hpow2] at hcr
    have hv2 : |C.src.srcFun a 2| ≤ C.src.tv * Real.exp (4 * π * a) := by
      simpa [mul_assoc, show 2 * π * a * 2 = 4 * π * a by ring] using
        srcFun_abs_le hshift (by norm_num : (0 : ℝ) < 2)
    have hvh : |C.src.srcFun a (1 / 2)| ≤ C.src.tv * Real.exp (π * a) := by
      simpa [show 2 * π * a * (1 / 2) = π * a by ring] using
        srcFun_abs_le hshift (by norm_num : (0 : ℝ) < 1 / 2)
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
            rw [← Real.exp_nat_mul]; simp only [Nat.cast_ofNat, mul_one]
            exact pow_le_pow_left₀ (by norm_num) (by linarith) 3
          linarith [show (8 : ℝ) ≤ (2.718 : ℝ) ^ 3 by norm_num]
        calc (8 : ℝ) ^ (C.src.w : ℝ) ≤ (Real.exp 3) ^ (C.src.w : ℝ) :=
              Real.rpow_le_rpow (by positivity) h8_le (by positivity)
          _ = Real.exp (3 * (C.src.w : ℝ)) := by rw [← Real.exp_nat_mul]; norm_cast; rw [mul_comm]
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
      have := hZ_half_lb
      have := hZ_two_ub
      linarith
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
    positivity [C.src.tv_nonneg]
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
      have hv1 := (abs_le.mp (le_abs_self (C.src.srcFun a β⁻¹))).2
      have hv2 := (abs_le.mp (le_abs_self (-C.src.srcFun a β))).2
      have := mul_le_mul_of_nonneg_left (add_le_add hZinv_le (le_abs_self _)) hpow_nn
      linarith [neg_le_abs (C.src.srcFun a β)]
    have hpow_ge1 : 1 ≤ β ^ (-(C.src.w : ℝ)) := by
      rw [Real.rpow_neg hβ_pos.le, one_le_inv₀ (Real.rpow_pos_of_pos hβ_pos _)]
      exact Real.rpow_le_one hβ_pos.le hβ_le1 (by positivity)
    have hsrc1 : |C.src.srcFun a β⁻¹| ≤ C.src.tv * Real.exp (2 * π * a / β) := by
      have := srcFun_abs_le hshift (inv_pos.mpr hβ_pos)
      rwa [show 2 * π * a * β⁻¹ = 2 * π * a / β by rw [div_eq_mul_inv]] at this
    have hsrc2 : |C.src.srcFun a β| ≤ C.src.tv * Real.exp (2 * π * a * β) :=
      srcFun_abs_le hshift hβ_pos
    have hexp_1 : Real.exp (4 * π * a) ≤ Real.exp (4 * π * a + 2 * π * a / β) :=
      Real.exp_le_exp.mpr (by have : 0 ≤ 2 * π * a / β := by positivity; linarith)
    have hexp_2 : Real.exp (2 * π * a / β) ≤ Real.exp (4 * π * a + 2 * π * a / β) :=
      Real.exp_le_exp.mpr (by have : 0 ≤ 4 * π * a := by positivity; linarith)
    have hexp_3 : Real.exp (2 * π * a * β) ≤ Real.exp (4 * π * a + 2 * π * a / β) := by
      apply Real.exp_le_exp.mpr
      have h1 : 2 * π * a * β ≤ 2 * π * a * 1 := mul_le_mul_of_nonneg_left hβ_le1 (by positivity)
      have h2 : 0 ≤ 2 * π * a / β := by positivity
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
                refine setLIntegral_mono_ae measurableSet_Icc (Eventually.of_forall fun t ht => ?_)
                exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.2]))
            _ ≤ ∫⁻ t in Ici T, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν :=
                lintegral_mono_set Icc_subset_Ici_self
        have hlt := lt_of_le_of_lt hle_m (hint_IciT one_pos).lintegral_lt_top
        exact (ENNReal.mul_lt_top_iff.mp hlt).elim (fun h => absurd h (ENNReal.ofReal_pos.mpr hexp_pos).ne') id
      have h1 : IntegrableOn (fun _ => Real.exp (-2 * π * β * R)) (Icc T R) meas.ν :=
        integrableOn_const hIcc_fin.ne
      have h2 : IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Icc T R) meas.ν :=
        (hint_IciT hβ_pos).mono_set Icc_subset_Ici_self
      calc Real.exp (-2 * π * β * R) * meas.ν.real (Icc T R)
          = ∫ _ in Icc T R, Real.exp (-2 * π * β * R) ∂meas.ν := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ ∫ t in Icc T R, Real.exp (-2 * π * β * t) ∂meas.ν := by
            refine setIntegral_mono_on h1 h2 measurableSet_Icc fun t ht => ?_
            exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hβ_pos, ht.2])
        _ ≤ Z β := by
            refine setIntegral_mono_set (hint_IciT hβ_pos) ?_ Icc_subset_Ici_self.eventuallyLE
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
      · have hβeq : β = Real.sqrt (a / R) := min_eq_right (Real.sqrt_le_one.mpr (div_le_one hR_pos |>.mpr haR))
        rw [hβeq, Real.rpow_neg (Real.sqrt_nonneg _), inv_eq_one_div, Real.sqrt_eq_rpow,
          ← Real.rpow_mul (by positivity)]
        have hr1 : ((1 : ℝ) / (a / R) ^ ((C.src.w : ℝ) / 2)) = (R / a) ^ ((C.src.w : ℝ) / 2) := by
          rw [← Real.inv_rpow (by positivity), inv_div]
        have heq_w : (1 / 2 : ℝ) * (C.src.w : ℝ) = (C.src.w : ℝ) / 2 := by ring
        rw [heq_w, hr1]
        exact Real.rpow_le_rpow (by positivity) (div_le_self hR_pos.le ha1) (by positivity)
      · have hRa : R < a := not_le.mp haR
        have hβeq : β = 1 := min_eq_left ((Real.le_sqrt zero_le_one (by positivity)).mpr (by rw [one_pow, le_div_iff₀ hR_pos]; linarith))
        rw [hβeq, Real.one_rpow]
        exact Real.one_le_rpow hR (by positivity)
    have hexp_sum : 2 * π * β * R + (4 * π * a + 2 * π * a / β) ≤
        6 * π * a + 4 * π * Real.sqrt (a * R) := by
      by_cases haR : a ≤ R
      · have hβeq : β = Real.sqrt (a / R) := min_eq_right (Real.sqrt_le_one.mpr (div_le_one hR_pos |>.mpr haR))
        rw [hβeq]
        have h1 : Real.sqrt (a / R) * R = Real.sqrt (a * R) := by
          have hRrt : R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hR_pos.le).symm
          nth_rw 2 [hRrt]
          rw [← Real.sqrt_mul (by positivity)]
          congr 1; field_simp [hR_pos.ne']
        have h2 : a / Real.sqrt (a / R) = Real.sqrt (a * R) := by
          have hart : a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha_pos.le).symm
          nth_rw 1 [hart]
          rw [← Real.sqrt_div (by positivity), div_div_eq_mul_div, div_self ha_pos.ne', one_mul]
          congr 1; ring
        have hsum : 2 * π * Real.sqrt (a / R) * R + (4 * π * a + 2 * π * a / Real.sqrt (a / R)) =
            4 * π * a + 4 * π * Real.sqrt (a * R) := by
          calc 2 * π * Real.sqrt (a / R) * R + (4 * π * a + 2 * π * a / Real.sqrt (a / R))
              = 2 * π * (Real.sqrt (a / R) * R) + 4 * π * a + 2 * π * (a / Real.sqrt (a / R)) := by ring
            _ = 4 * π * a + 4 * π * Real.sqrt (a * R) := by rw [h1, h2]; ring
        rw [hsum]
        linarith [Real.pi_pos]
      · have hRa : R < a := not_le.mp haR
        have hβeq : β = 1 := min_eq_left ((Real.le_sqrt zero_le_one (by positivity)).mpr (by rw [one_pow, le_div_iff₀ hR_pos]; linarith))
        rw [hβeq]
        have hR_le : R ≤ Real.sqrt (a * R) := by
          rw [Real.le_sqrt hR_pos.le (by positivity)]
          nlinarith
        nlinarith [Real.pi_pos]
    calc meas.ν.real (Icc T R)
        ≤ Real.exp (2 * π * β * R) *
            (β ^ (-(C.src.w : ℝ)) * (3 * C.src.tv * Real.exp (4 * π * a + 2 * π * a / β))) := hmeas_ub
      _ = β ^ (-(C.src.w : ℝ)) * (3 * C.src.tv * Real.exp (2 * π * β * R + (4 * π * a + 2 * π * a / β))) := by
          rw [Real.exp_add]; ring
      _ ≤ R ^ ((C.src.w : ℝ) / 2) * (3 * C.src.tv * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * R))) := by
          have hexp_le := Real.exp_le_exp.mpr hexp_sum
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

/-! ### Section 5: Theorem INT-1 (`int:atom`) -/

private lemma rpow_weighted_taylor_le {P : ℝ} (hP : 0 < P) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
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
        _ = Real.exp (m * u) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ = Real.exp (2 * π * x) := by
            congr 1; dsimp [u]; field_simp [hm_pos.ne']
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

private lemma rpow_half_mul_exp_neg_le_one {x : ℝ} (hx : 0 ≤ x) :
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

/-- **Theorem INT-1 (`int:atom`)** for any `CommonSource` (covering `(H_w)`, `(H_{w,mix})`,
and dominated atomic sources) and any abstract sufficient density floor `W`. -/
theorem int_atom_common (C : CommonSource) {W : ℕ → ℝ} (hW : SufficientMomentFloor W)
    (repair : IntRepairSonineInput C.src.w) :
    ∃ K a₁ : ℝ, 0 < K ∧ max C.a₀ 24 ≤ a₁ ∧
      ∀ {a T δ : ℝ}, a₁ ≤ a → a / 8 ≤ T → 0 < δ → δ ≤ 1 →
        ∀ (meas : SourceCrossingMeasure C.src a), meas.ν (Ici T)ᶜ = 0 →
        (ENNReal.ofReal δ •
          (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T) ≤
            meas.ν) →
        ∀ (M : ℕ → ℕ), (∀ k, 1 ≤ M k) →
          (∀ k : ℕ, 1 ≤ k →
            let B_prev := T + ((k - 1 : ℕ) : ℝ)
            let B_next := T + ((k + 1 : ℕ) : ℝ)
            let H_k := a + B_next + Real.log (1 / δ) + (C.src.w : ℝ)
            let P_k := a * B_prev
            K * H_k / Real.log P_k ≤ (M k : ℝ)) →
          (∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, T + ((k - 1 : ℕ) : ℝ) ≤ s →
            W (M k) ≤ (δ / 8) * C.src.cardyDensity a s) →
          ∃ measZ : SourceCrossingMeasure C.src a,
            measZ.ν (Ici T)ᶜ = 0 ∧ IsIntegerCounting measZ.ν := by
  obtain ⟨c_vac, a_star, hc_vac_pos, ha_star_ge, hrho_lb⟩ := commonSource_cardyDensity_lower C
  have hw1 : 1 ≤ C.src.w := C.src.hw
  let wR : ℝ := (C.src.w : ℝ)
  let c0 : ℝ := max (1 : ℝ) (wR / 2)
  have hc0_ge1 : 1 ≤ c0 := le_max_left _ _
  let C_w_fac : ℝ := (8 : ℝ) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2)
  let C_count_fac : ℝ := 3 * max C.src.tv 1 * c0 ^ (wR / 2)
  let C_const : ℝ := 2 * π * (9 / 4 * C_count_fac) * C_w_fac * (1 + repair.C_son) / c_vac
  let C_exp : ℝ := 9 * π + repair.C_son + 1
  let K : ℝ := 2 * (C_exp + 2)
  let a₁ : ℝ := max (max C.a₀ 24) (max (max a_star (8 * max 1 wR)) (Real.log (max C_const 1) + 1))
  have hK_pos : 0 < K := by dsimp [K, C_exp]; have := repair.hC_son_nn; positivity
  refine ⟨K, a₁, hK_pos, le_max_left _ _, fun {a T δ} ha hT hδ0 hδ1 meas hsupp hres M hM1 hM_ord hM_fl => ?_⟩
  have ha0 : C.a₀ ≤ a := (le_max_left _ _).trans ((le_max_left _ _).trans ha)
  have ha24 : 24 ≤ a := (le_max_right _ _).trans ((le_max_left _ _).trans ha)
  have ha_star : a_star ≤ a := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ha))
  have ha8w : 8 * max 1 wR ≤ a := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ha))
  have ha_const : Real.log (max C_const 1) + 1 ≤ a := (le_max_right _ _).trans ((le_max_right _ _).trans ha)
  have ha8 : 8 ≤ a := by linarith
  have ha_pos : 0 < a := by linarith
  have hT_max : max 1 wR ≤ T := by
    have : 8 * max 1 wR ≤ 8 * T := by linarith
    linarith
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT_max
  have hTw : wR ≤ T := (le_max_right _ _).trans hT_max
  have ha_ge_c0 : max C.a₀ (max 1 wR) ≤ a :=
    max_le ha0 (max_le (by linarith) (by have := le_max_right 1 wR; linarith))
  have hcount := commonSource_counting_bound C ha_ge_c0 hT_max meas hsupp
  let X := Set.Ici T
  have hEmb : MeasurableEmbedding (Subtype.val : X → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  have hT_pos : 0 < T := by linarith
  have hV_nonneg_Ici : ∀ t ∈ Ici T, 0 ≤ C.src.cardyDensity a t := fun t ht => by
    unfold ShiftSource.cardyDensity
    exact mul_nonneg (by positivity) ((C.at_ ha0).nonneg_V (by linarith [mem_Ici.mp ht]))
  have hm_dens : Measurable (fun t : ℝ => ENNReal.ofReal (C.src.cardyDensity a t)) :=
    ((C.src.continuous_cardyV a).const_mul (2 * π)).measurable.ennreal_ofReal
  let ρ_real : Measure ℝ :=
    (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T)
  have hρ_real_eq : ρ_real =
      (volume.restrict (Ici T)).withDensity (fun t => ENNReal.ofReal (C.src.cardyDensity a t)) := by
    dsimp [ρ_real]; rw [Measure.restrict_withDensity measurableSet_Ici]
  have hρ_real_int : ∀ {β : ℝ}, 0 < β →
      Integrable (fun t => Real.exp (-2 * π * β * t)) ρ_real := by
    intro β hβ
    have hc := (C.src.cardyV_laplace a hβ).1
    have hdens_int : Integrable (fun t => Real.exp (-2 * π * β * t) * C.src.cardyDensity a t)
        (volume.restrict (Ici T)) := by
      refine ((hc.const_mul (2 * π)).mono_set (Ici_subset_Ioi.2 hT_pos)).congr_fun ?_
        measurableSet_Ici
      intro t _
      unfold ShiftSource.cardyDensity; ring
    rw [hρ_real_eq, integrable_withDensity_iff_integrable_smul' hm_dens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hdens_int.congr ?_
    rw [ae_restrict_iff' measurableSet_Ici]
    refine Eventually.of_forall fun t ht => ?_
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hV_nonneg_Ici t ht)]
    ring
  let ν0_sub : Measure X := Measure.comap Subtype.val meas.ν
  let ρ_sub : Measure X := Measure.comap Subtype.val ρ_real
  have hν0_map : Measure.map Subtype.val ν0_sub = meas.ν := by
    dsimp [ν0_sub]
    rw [hEmb.map_comap meas.ν, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem
      (measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono fun t ht => not_not.mp ht)
  have hρ_map : Measure.map Subtype.val ρ_sub = ρ_real := by
    dsimp [ρ_sub]
    rw [hEmb.map_comap ρ_real, Subtype.range_coe]
    exact Measure.restrict_eq_self (Ici T)
  let RPos := {β : ℝ // 0 < β}
  let S : ShellSetup X :=
    { Ω := fun k => {x : X | (x : ℝ) < T + (k : ℝ)}
      I := RPos
      Γ := RPos
      K := fun β x => thermalDiff C.src.w β.1 x.1
      c := fun β => ∫ t in Ioi 0, thermalDiff C.src.w β.1 t * C.src.cardyDensity a t
      e := fun γ x => Real.exp (-2 * π * γ.1 * x.1)
      ρ := ρ_sub
      ν0 := ν0_sub
      δ := δ
      γ' := id
      C := fun γ => Real.exp (4 * π * γ.1)
      Ω_open := fun k => isOpen_lt continuous_subtype_val continuous_const
      Ω_mono := fun k₁ k₂ hk x hx => lt_of_lt_of_le hx (by have : (k₁ : ℝ) ≤ k₂ := by exact_mod_cast hk; linarith)
      Ω_zero := by ext x; simp [X, mem_Ici]; linarith [x.2]
      Ω_cover := by
        ext x; simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
        obtain ⟨k, hk⟩ := exists_nat_gt ((x : ℝ) - T)
        exact ⟨k, by linarith⟩
      K_cont := fun β => by unfold thermalDiff; fun_prop
      e_cont := fun γ => by fun_prop
      e_pos := fun γ x => Real.exp_pos _
      K_dom := fun β => by
        classical
        let βinv : RPos := ⟨β.1⁻¹, inv_pos.mpr β.2⟩
        let s : Finset RPos := {β, βinv}
        let coef : RPos → ℝ := fun γ => if γ = β then 1 else if γ = βinv then β.1 ^ (-(C.src.w : ℝ)) else 0
        refine ⟨s, coef, fun γ => ?_, fun x => ?_⟩
        · dsimp [coef]; split_ifs <;> positivity
        · have htherm : |thermalDiff C.src.w β.1 x.1| ≤
              Real.exp (-2 * π * β.1 * x.1) + β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * x.1) := by
            unfold thermalDiff
            have h1 := abs_sub (Real.exp (-2 * π * β.1 * x.1))
              (β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * x.1 / β.1))
            rwa [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg (Real.rpow_nonneg β.2.le _),
              abs_of_pos (Real.exp_pos _), show 2 * π * x.1 / β.1 = 2 * π * β.1⁻¹ * x.1 by
                rw [div_eq_mul_inv]; ring] at h1
          by_cases heq : β = βinv
          · have hβ1 : β.1 = 1 := by
              have hinv : β.1 = β.1⁻¹ := congrArg Subtype.val heq
              nlinarith [mul_inv_cancel₀ β.2.ne']
            have hs_eq : s = {β} := by dsimp [s]; rw [← heq, Finset.pair_eq_singleton]
            rw [hs_eq, Finset.sum_singleton]
            dsimp [coef]; simp only [↓reduceIte, one_mul, hβ1, Real.one_rpow, inv_one] at htherm ⊢
            linarith
          · have hs_eq : ∑ γ ∈ s, coef γ * Real.exp (-2 * π * γ.1 * x.1) =
                coef β * Real.exp (-2 * π * β.1 * x.1) +
                  coef βinv * Real.exp (-2 * π * βinv.1 * x.1) := Finset.sum_pair heq
            rw [hs_eq]
            dsimp [coef]
            simp only [↓reduceIte, Ne.symm heq, one_mul]
            exact htherm
      δ_pos := hδ0
      δ_le := hδ1
      ρ_int := fun γ => by
        have hm : Measurable (Subtype.val : X → ℝ) := measurable_subtype_coe
        have hc : Continuous (fun t : ℝ => Real.exp (-2 * π * γ.1 * t)) := by fun_prop
        rw [← integrable_map_measure (hc.comp measurable_id).aestronglyMeasurable hm.aemeasurable,
          hρ_map]
        exact hρ_real_int γ.2
      ν0_int := fun γ => by
        have hm : Measurable (Subtype.val : X → ℝ) := measurable_subtype_coe
        have hc : Continuous (fun t : ℝ => Real.exp (-2 * π * γ.1 * t)) := by fun_prop
        rw [← integrable_map_measure (hc.comp measurable_id).aestronglyMeasurable hm.aemeasurable,
          hν0_map]
        have hae_0 : ∀ᵐ t ∂meas.ν, t ∈ Ici (0 : ℝ) := by
          have := measure_eq_zero_iff_ae_notMem.1 hsupp
          filter_upwards [this] with t ht
          exact le_trans (by linarith) (not_not.mp ht)
        simpa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae_0] using meas.finite_laplace γ.2
      ν0_K := fun β => by
        have hm : Measurable (Subtype.val : X → ℝ) := measurable_subtype_coe
        have hc : Continuous (fun t : ℝ => thermalDiff C.src.w β.1 t) := by
          unfold thermalDiff; fun_prop
        have hint_ν : Integrable (fun t : ℝ => thermalDiff C.src.w β.1 t) meas.ν := by
          have hae_0 : ∀ᵐ t ∂meas.ν, t ∈ Ici (0 : ℝ) := by
            have := measure_eq_zero_iff_ae_notMem.1 hsupp
            filter_upwards [this] with t ht
            exact le_trans (by linarith) (not_not.mp ht)
          have h1 := meas.finite_laplace β.2
          have h2 := meas.finite_laplace (inv_pos.mpr β.2)
          rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae_0] at h1 h2
          unfold thermalDiff
          have h2' : Integrable (fun t => Real.exp (-2 * π * t / β.1)) meas.ν := by
            convert h2 using 1; ext t; simp [div_eq_mul_inv, mul_comm, mul_assoc]
          exact h1.sub (h2'.const_mul _)
        have hmap_int : ∫ x : X, thermalDiff C.src.w β.1 x.1 ∂ν0_sub =
            ∫ t : ℝ, thermalDiff C.src.w β.1 t ∂meas.ν := by
          rw [← hν0_map, integral_map hm.aemeasurable hc.aestronglyMeasurable]
        have hae_0 : ∀ᵐ t ∂meas.ν, t ∈ Ici (0 : ℝ) := by
          have := measure_eq_zero_iff_ae_notMem.1 hsupp
          filter_upwards [this] with t ht
          exact le_trans (by linarith) (not_not.mp ht)
        rw [hmap_int, ← Measure.restrict_eq_self_of_ae_mem hae_0]
        exact meas.crossing β.2
      reserve_le := by
        refine Measure.le_iff.2 fun A hA => ?_
        have hA_val : MeasurableSet (Subtype.val '' A) := hEmb.measurableSet_image.2 hA
        have h1 : ρ_sub A = ρ_real (Subtype.val '' A) := by
          rw [← hρ_map, Measure.map_apply hEmb.measurable hA_val]
          congr 1; exact (Subtype.val_injective.preimage_image A).symm
        have h2 : ν0_sub A = meas.ν (Subtype.val '' A) := by
          rw [← hν0_map, Measure.map_apply hEmb.measurable hA_val]
          congr 1; exact (Subtype.val_injective.preimage_image A).symm
        rw [Measure.smul_apply, smul_eq_mul, h1, h2]
        have hle := Measure.le_iff.1 hres (Subtype.val '' A) hA_val
        simpa [ρ_real, Measure.smul_apply, smul_eq_mul] using hle
      C_nonneg := fun γ => (Real.exp_pos _).le }
  have hν0_fin : ∀ R : ℝ, S.ν0 {x : X | (x : ℝ) ≤ R} < ∞ := fun R => by
    by_cases hTR : R < T
    · have hemp : {x : X | (x : ℝ) ≤ R} = ∅ := by
        ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; linarith [x.2]
      rw [hemp, measure_empty]; exact ENNReal.coe_lt_top
    · have hle_TR : T ≤ R := not_lt.mp hTR
      have hm : MeasurableSet (Icc T R) := measurableSet_Icc
      have hmeas_eq : S.ν0 {x : X | (x : ℝ) ≤ R} = meas.ν (Icc T R) := by
        change ν0_sub {x : X | (x : ℝ) ≤ R} = _
        rw [← hν0_map, Measure.map_apply hEmb.measurable hm]
        congr 1; ext x; simp [x.2]
      rw [hmeas_eq]
      have hexp_pos : 0 < Real.exp (-2 * π * R) := Real.exp_pos _
      have hle_exp : ENNReal.ofReal (Real.exp (-2 * π * R)) * meas.ν (Icc T R) ≤
          ∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
        calc ENNReal.ofReal (Real.exp (-2 * π * R)) * meas.ν (Icc T R)
            = ∫⁻ _ in Icc T R, ENNReal.ofReal (Real.exp (-2 * π * R)) ∂meas.ν := by
              rw [setLIntegral_const]
          _ ≤ ∫⁻ t in Icc T R, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
              refine setLIntegral_mono_ae measurableSet_Icc (Eventually.of_forall fun t ht => ?_)
              exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.2]))
          _ ≤ ∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν :=
              lintegral_mono_set (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 (by linarith)))
      have hlt := lt_of_le_of_lt hle_exp (meas.finite_laplace one_pos).lintegral_lt_top
      exact (ENNReal.mul_lt_top_iff.mp hlt).elim (fun h => absurd h (ENNReal.ofReal_pos.mpr hexp_pos).ne') id
  haveI : SigmaFinite S.ν0 := by
    refine ⟨⟨{
      set := fun k => {x : X | (x : ℝ) ≤ T + (k : ℝ)}
      set_mem := fun _ => trivial
      finite := fun k => hν0_fin (T + (k : ℝ))
      spanning := by
        ext x; simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
        obtain ⟨k, hk⟩ := exists_nat_gt ((x : ℝ) - T)
        exact ⟨k, by linarith⟩
    }⟩⟩
  have hρ_sub_fin : ∀ R : ℝ, S.ρ {x : X | (x : ℝ) ≤ R} < ∞ := fun R => by
    have h1 := Measure.le_iff.1 S.reserve_le {x : X | (x : ℝ) ≤ R}
      (measurableSet_le continuous_subtype_val.measurable measurable_const)
    rw [Measure.smul_apply, smul_eq_mul] at h1
    have hlt := lt_of_le_of_lt h1 (hν0_fin R)
    exact (ENNReal.mul_lt_top_iff.mp hlt).elim (fun h => absurd h (ENNReal.ofReal_pos.mpr hδ0).ne') id
  have hcells : ∀ (j : ℕ) (Sg lam : Measure X), S.Inv j Sg lam →
      ∃ (ι : Type) (_ : Fintype ι) (U : ι → Set X) (μ σ Rp Rm : ι → Measure X),
        S.CellStep j lam U μ σ Rp Rm := by
    intro j Sg lam hInv
    let k : ℕ := j + 1
    have hk1 : 1 ≤ k := Nat.succ_pos j
    let B₀ : ℝ := T + (j : ℝ)
    let B_mid : ℝ := T + ((j + 1 : ℕ) : ℝ)
    let B : ℝ := T + ((j + 2 : ℕ) : ℝ)
    have hB0_pos : 0 < B₀ := by dsimp [B₀]; positivity
    have hB_mid_eq : B_mid = B₀ + 1 := by dsimp [B_mid, B₀]; push_cast; ring
    have hB_eq : B = B_mid + 1 := by dsimp [B, B_mid]; push_cast; ring
    have hB0_lt_B : B₀ < B := by linarith
    have hB0_ge_T : T ≤ B₀ := by dsimp [B₀]; linarith
    have hB_ge1 : 1 ≤ B := by dsimp [B]; linarith
    let Mk : ℕ := M k
    have hMk1 : 1 ≤ Mk := hM1 k
    have hMk_fl : ∀ s : ℝ, B₀ ≤ s → W Mk ≤ (δ / 8) * C.src.cardyDensity a s := fun s hs => by
      have hs' : T + ((k - 1 : ℕ) : ℝ) ≤ s := by simpa [k, B₀] using hs
      exact hM_fl k hk1 s hs'
    let U₀ : Set X := {x : X | B₀ ≤ (x : ℝ) ∧ (x : ℝ) ≤ B}
    have hcell_closed : IsClosed U₀ :=
      (isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)
    have hU0_meas : MeasurableSet U₀ := hcell_closed.measurableSet
    have hcell_sub : U₀ ⊆ closure (S.Ω (j + 2)) \ S.Ω j := by
      intro x ⟨hx1, hx2⟩
      refine ⟨?_, fun hxΩ => ?_⟩
      · rcases eq_or_lt_of_le hx2 with hxeq | hxlt
        · rw [mem_closure_iff_seq_limit]
          let seq : ℕ → X := fun n => ⟨max T (B - 1 / ((n : ℝ) + 1)), le_max_left _ _⟩
          refine ⟨seq, fun n => ?_, ?_⟩
          · dsimp [S, seq]
            have hT_lt : T < B := by dsimp [B]; linarith
            rw [max_lt_iff]
            exact ⟨hT_lt, by dsimp [B]; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]⟩
          · rw [Subtype.tendsto_iff]
            have hsub_tend : Tendsto (fun n : ℕ => B - 1 / ((n : ℝ) + 1)) atTop (𝓝 B) := by
              simpa using tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
            have hev : ∀ᶠ n in atTop, T ≤ B - 1 / ((n : ℝ) + 1) := by
              have hT_lt : T < B := by dsimp [B]; linarith
              filter_upwards [hsub_tend.eventually (lt_mem_nhds hT_lt)] with n hn
              exact hn.le
            have hmax : (fun n : ℕ => (seq n : ℝ)) =ᶠ[atTop] fun n : ℕ => B - 1 / ((n : ℝ) + 1) :=
              hev.mono fun n hn => max_eq_right hn
            rw [hxeq]
            exact hsub_tend.congr' hmax.symm
        · exact subset_closure (by simpa [S, B] using hxlt)
      · exact not_lt_of_ge hx1 (by simpa [S, B₀] using hxΩ)
    have hsh_meas : ∀ i : ℕ, MeasurableSet (S.shell i) := fun i =>
      (S.Ω_open (i + 1)).measurableSet.diff (S.Ω_open i).measurableSet
    have hshj_eq : S.shell j = {x : X | B₀ ≤ (x : ℝ) ∧ (x : ℝ) < B_mid} := by
      ext x; simp [ShellSetup.shell, S, B₀, B_mid, not_lt]
    have hshj1_eq : S.shell (j + 1) = {x : X | B_mid ≤ (x : ℝ) ∧ (x : ℝ) < B} := by
      ext x; simp [ShellSetup.shell, S, B_mid, B, not_lt]
    have hsh_union_sub : S.shell j ∪ S.shell (j + 1) ⊆ U₀ := by
      intro x hx
      rcases hx with h | h
      · rw [hshj_eq] at h; exact ⟨h.1, le_of_lt (h.2.trans (by linarith))⟩
      · rw [hshj1_eq] at h; exact ⟨le_trans (by linarith) h.1, h.2.le⟩
    have hsh_disj : Disjoint (S.shell j) (S.shell (j + 1)) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      rw [hshj_eq] at h1; rw [hshj1_eq] at h2
      linarith
    have hU0_fin_ν0 : S.ν0 {x : X | (x : ℝ) ≤ B} < ∞ := hν0_fin B
    have hU0_fin_ρ : S.ρ {x : X | (x : ℝ) ≤ B} < ∞ := hρ_sub_fin B
    have hcm_add : ∀ a₁ a₂ : ℝ, 0 ≤ a₁ → 0 ≤ a₂ → S.cm (a₁ + a₂) = S.cm a₁ + S.cm a₂ := by
      intro a₁ a₂ ha₁ ha₂
      ext A hA
      simp only [ShellSetup.cm, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      have hmul : (a₁ + a₂) * S.δ = a₁ * S.δ + a₂ * S.δ := by ring
      rw [hmul, ENNReal.ofReal_add (mul_nonneg ha₁ S.δ_pos.le) (mul_nonneg ha₂ S.δ_pos.le), add_mul]
    have hcm_mono : ∀ {a₁ a₂ : ℝ}, a₁ ≤ a₂ → S.cm a₁ ≤ S.cm a₂ := fun h => by
      refine Measure.le_iff.2 fun A _ => ?_
      simp only [ShellSetup.cm, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h S.δ_pos.le)) _
    have hlam_sh1 : S.LEOn (S.shell (j + 1)) (S.cm (cE j)) lam := fun A hA hAs =>
      hInv.2.2.2.2.1 A hA (hAs.trans fun x hx hxΩ => hx.2 hxΩ)
    have hlam_Ω2_le : lam (S.Ω (j + 2)) ≤ ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := by
      have h1 := hInv.2.2.1
      have h2 := Measure.le_iff.1 h1 (S.Ω (j + 2)) (S.Ω_open (j + 2)).measurableSet
      have hcm_th : S.cm (theta j) (S.Ω (j + 2)) ≤ ENNReal.ofReal (1 / 8) * S.ν0 (S.Ω (j + 2)) := by
        have hth_le : theta j ≤ 1 / 8 := by unfold theta; linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 3) by positivity]
        calc S.cm (theta j) (S.Ω (j + 2))
            ≤ S.cm (1 / 8) (S.Ω (j + 2)) := Measure.le_iff.1 (hcm_mono hth_le) _ _
          _ = ENNReal.ofReal (1 / 8) * (ENNReal.ofReal S.δ * S.ρ (S.Ω (j + 2))) := by
              simp only [ShellSetup.cm, Measure.smul_apply, smul_eq_mul]
              rw [mul_comm (1 / 8) S.δ, ENNReal.ofReal_mul S.δ_pos.le, mul_assoc, mul_comm (ENNReal.ofReal S.δ)]
          _ ≤ ENNReal.ofReal (1 / 8) * S.ν0 (S.Ω (j + 2)) := by
              gcongr
              simpa [Measure.smul_apply, smul_eq_mul] using
                Measure.le_iff.1 S.reserve_le (S.Ω (j + 2)) (S.Ω_open (j + 2)).measurableSet
      calc lam (S.Ω (j + 2)) ≤ S.ν0 (S.Ω (j + 2)) + S.cm (theta j) (S.Ω (j + 2)) := h2
        _ ≤ 1 * S.ν0 (S.Ω (j + 2)) + ENNReal.ofReal (1 / 8) * S.ν0 (S.Ω (j + 2)) := by
            rw [one_mul]; gcongr
        _ = ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := by
            rw [← add_mul]
            congr 1
            rw [show (9 / 8 : ℝ) = 1 + 1 / 8 by norm_num, ENNReal.ofReal_add zero_le_one (by norm_num),
              ENNReal.ofReal_one]
    have hlam_sh_fin : ∀ {A : Set X}, A ⊆ S.Ω (j + 2) → lam A < ∞ := fun hA => by
      have hm_sub : S.Ω (j + 2) ⊆ {x : X | (x : ℝ) ≤ B} := fun x hx => by
        dsimp [S, B] at hx; exact hx.le
      calc lam A ≤ lam (S.Ω (j + 2)) := measure_mono hA
        _ ≤ ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := hlam_Ω2_le
        _ ≤ ENNReal.ofReal (9 / 8) * S.ν0 {x : X | (x : ℝ) ≤ B} := by gcongr; exact hm_sub
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU0_fin_ν0
    let lam0 : Measure X := lam.restrict (S.shell j)
    let lam1 : Measure X := lam.restrict (S.shell (j + 1))
    let R1 : Measure X := (S.cm (5 / 8)).restrict (S.shell (j + 1))
    haveI : IsFiniteMeasure lam0 := ⟨by
      simpa [lam0] using hlam_sh_fin (fun _ hx => (Nat.le_succ _ |> fun h =>
        S.Ω_mono (Nat.le_succ _) hx.1))⟩
    haveI : IsFiniteMeasure lam1 := ⟨by
      simpa [lam1] using hlam_sh_fin (fun _ hx => hx.1)⟩
    haveI : IsFiniteMeasure R1 := ⟨by
      have hm_sub : S.shell (j + 1) ⊆ {x : X | (x : ℝ) ≤ B} := fun x hx => by
        have : x ∈ S.Ω (j + 2) := hx.1
        dsimp [S, B] at this; exact this.le
      calc R1 univ = S.cm (5 / 8) (S.shell (j + 1)) := by simp [R1]
        _ ≤ S.cm (5 / 8) {x : X | (x : ℝ) ≤ B} := measure_mono hm_sub
        _ < ∞ := by
            simp only [ShellSetup.cm, Measure.smul_apply, smul_eq_mul]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU0_fin_ρ⟩
    have hR1_le : R1 ≤ lam1 := Measure.le_iff.2 fun A hA => by
      simp only [R1, lam1, Measure.restrict_apply hA]
      have h58_cE : 5 / 8 ≤ cE j := by unfold cE; linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 3) by positivity]
      calc S.cm (5 / 8) (A ∩ S.shell (j + 1))
          ≤ S.cm (cE j) (A ∩ S.shell (j + 1)) := Measure.le_iff.1 (hcm_mono h58_cE) _ _
        _ ≤ lam (A ∩ S.shell (j + 1)) :=
            hlam_sh1 (A ∩ S.shell (j + 1)) (hA.inter (hsh_meas (j + 1))) inter_subset_right
    let rem : Measure X := lam1 - R1
    have hrem_add : rem + R1 = lam1 := Measure.sub_add_cancel_of_le hR1_le
    have hrem_ge : (S.cm (1 / 4)).restrict (S.shell (j + 1)) ≤ rem := by
      refine Measure.le_iff.2 fun A hA => ?_
      rw [Measure.sub_apply hA hR1_le]
      refine ENNReal.le_tsub_of_add_le_right ?_
      simp only [R1, lam1, Measure.restrict_apply hA]
      have hsum_cm : S.cm (1 / 4) (A ∩ S.shell (j + 1)) + S.cm (5 / 8) (A ∩ S.shell (j + 1)) =
          S.cm (7 / 8) (A ∩ S.shell (j + 1)) := by
        rw [← Measure.add_apply, ← hcm_add (1 / 4) (5 / 8) (by norm_num) (by norm_num)]
        congr 1; norm_num
      rw [hsum_cm]
      have h78_cE : 7 / 8 ≤ cE j := by unfold cE; linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 3) by positivity]
      calc S.cm (7 / 8) (A ∩ S.shell (j + 1))
          ≤ S.cm (cE j) (A ∩ S.shell (j + 1)) := Measure.le_iff.1 (hcm_mono h78_cE) _ _
        _ ≤ lam (A ∩ S.shell (j + 1)) :=
            hlam_sh1 (A ∩ S.shell (j + 1)) (hA.inter (hsh_meas (j + 1))) inter_subset_right
    have hvol_sh1 : ENNReal.ofReal (W Mk) • volume.restrict (Ico B_mid B) ≤
        ENNReal.ofReal (1 / 8 * δ) • (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ico B_mid B) := by
      refine Measure.le_iff.2 fun A hA => ?_
      rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        Measure.restrict_apply hA, Measure.restrict_apply hA, withDensity_apply _ (hA.inter measurableSet_Ico)]
      calc ENNReal.ofReal (W Mk) * volume (A ∩ Ico B_mid B)
          = ∫⁻ _ in A ∩ Ico B_mid B, ENNReal.ofReal (W Mk) ∂volume := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ t in A ∩ Ico B_mid B, ENNReal.ofReal ((δ / 8) * C.src.cardyDensity a t) ∂volume := by
            refine setLIntegral_mono_ae (hA.inter measurableSet_Ico) (Eventually.of_forall fun t ht => ?_)
            exact ENNReal.ofReal_le_ofReal (hMk_fl t (by linarith [ht.2.1]))
        _ = ENNReal.ofReal (1 / 8 * δ) *
              ∫⁻ t in A ∩ Ico B_mid B, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
            have heq : (fun t : ℝ => ENNReal.ofReal ((δ / 8) * C.src.cardyDensity a t)) =
                fun t => ENNReal.ofReal (1 / 8 * δ) * ENNReal.ofReal (C.src.cardyDensity a t) := by
              ext t
              rw [show (δ / 8) * C.src.cardyDensity a t = (1 / 8 * δ) * C.src.cardyDensity a t by ring,
                ENNReal.ofReal_mul (by positivity)]
            rw [heq, lintegral_const_mul _ hm_dens]
    have hρ_sh1_eq : Measure.map Subtype.val (S.ρ.restrict (S.shell (j + 1))) =
        ρ_real.restrict (Ico B_mid B) := by
      have himg : Subtype.val ⁻¹' Ico B_mid B = S.shell (j + 1) := by
        ext x; simp [hshj1_eq]
      calc Measure.map Subtype.val (S.ρ.restrict (S.shell (j + 1)))
          = Measure.map Subtype.val (S.ρ.restrict (Subtype.val ⁻¹' Ico B_mid B)) := by rw [himg]
        _ = (Measure.map Subtype.val S.ρ).restrict (Ico B_mid B) :=
            (hEmb.map_restrict_preimage S.ρ (Ico B_mid B)).symm
        _ = ρ_real.restrict (Ico B_mid B) := by rw [hρ_map]
    have hR1_mass_gt : 5 < (R1 univ).toReal := by
      have hge_W : ENNReal.ofReal (W Mk) ≤ ENNReal.ofReal (1 / 8 * δ) * S.ρ (S.shell (j + 1)) := by
        have hvol_1 : volume (Ico B_mid B) = 1 := by
          rw [Real.volume_Ico, hB_eq, add_sub_cancel_left, ENNReal.ofReal_one]
        have h1 := Measure.le_iff.1 hvol_sh1 univ MeasurableSet.univ
        rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
          Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ,
          univ_inter, hvol_1, mul_one] at h1
        have hr_eq : (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)) (Ico B_mid B) =
            S.ρ (S.shell (j + 1)) := by
          have himg : Subtype.val '' S.shell (j + 1) = Ico B_mid B := by
            ext t; simp [hshj1_eq]; constructor
            · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩; exact ⟨hx1, hx2⟩
            · rintro ⟨ht1, ht2⟩; exact ⟨⟨t, by linarith⟩, ⟨ht1, ht2⟩, rfl⟩
          have h2 : S.ρ (S.shell (j + 1)) = ρ_real (Ico B_mid B) := by
            change ρ_sub (S.shell (j + 1)) = _
            rw [← hρ_map, Measure.map_apply hEmb.measurable (hsh_meas (j + 1) |> fun hm => by
              rw [← himg]; exact hEmb.measurableSet_image.2 hm)]
            congr 1; exact (Subtype.val_injective.preimage_image _).symm
          rw [h2]
          dsimp [ρ_real]
          rw [Measure.restrict_apply measurableSet_Ico]
          congr 1; ext t; simp only [mem_inter_iff, mem_Ico, mem_Ici, and_iff_left_iff_imp]
          intro ⟨ht1, _⟩; linarith
        simpa [hr_eq] using h1
      have hR1_eq : R1 univ = 5 * (ENNReal.ofReal (1 / 8 * δ) * S.ρ (S.shell (j + 1))) := by
        simp only [R1, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          ShellSetup.cm, Measure.smul_apply, smul_eq_mul]
        rw [show (5 / 8 : ℝ) * S.δ = 5 * (1 / 8 * S.δ) by ring,
          ENNReal.ofReal_mul (by norm_num), mul_assoc]
        norm_num
      have h5W : ENNReal.ofReal (5 * W Mk) ≤ R1 univ := by
        rw [hR1_eq, ENNReal.ofReal_mul (by norm_num)]
        gcongr
        norm_num
      have hlt_top : R1 univ ≠ ∞ := measure_ne_top R1 univ
      have htoReal := ENNReal.toReal_mono hlt_top h5W
      rw [ENNReal.toReal_ofReal (by linarith [hW.1 Mk])] at htoReal
      linarith [hW.1 Mk]
    let L_lo : ℝ := ((lam0 + rem) univ).toReal
    let Ntot : ℕ := Nat.ceil L_lo
    let α : ℝ := ((Ntot : ℝ) - L_lo) / (R1 univ).toReal
    have hR1_pos_real : 0 < (R1 univ).toReal := by linarith
    have hα0 : 0 ≤ α := div_nonneg (sub_nonneg.mpr (Nat.le_ceil L_lo)) hR1_pos_real.le
    have hα1 : α ≤ 1 := by
      have hceil_lt : (Ntot : ℝ) - L_lo < 1 := by
        by_cases hL : L_lo ≤ 0
        · have hN0 : Ntot = 0 := Nat.ceil_eq_zero.mpr hL
          have hL_nn : 0 ≤ L_lo := ENNReal.toReal_nonneg
          have hL0 : L_lo = 0 := le_antisymm hL hL_nn
          simp [hN0, hL0]
        · exact (Nat.ceil_lt_add_one (not_le.mp hL).le).trans_le (by linarith) |> by
            intro h; linarith
      rw [div_le_one hR1_pos_real]
      linarith
    let μ₀ : Measure X := lam0 + rem + ENNReal.ofReal α • R1
    haveI : IsFiniteMeasure rem := isFiniteMeasure_of_le lam1 Measure.sub_le
    haveI : IsFiniteMeasure μ₀ := by
      dsimp [μ₀]
      infer_instance
    have hμ₀_univ : μ₀ univ = Ntot := by
      have hL_fin : (lam0 + rem) univ ≠ ∞ := measure_ne_top _ _
      have hR1_fin : R1 univ ≠ ∞ := measure_ne_top _ _
      have hsum_toReal : (μ₀ univ).toReal = (Ntot : ℝ) := by
        dsimp [μ₀]
        simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
        rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
          (ENNReal.mul_ne_top ENNReal.ofReal_lt_top.ne hR1_fin),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal hα0]
        change L_lo + α * (R1 univ).toReal = (Ntot : ℝ)
        dsimp [α]
        field_simp [hR1_pos_real.ne']
        ring
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ₀ univ), hsum_toReal]
      simp
    have hμ₀_supp : μ₀ (U₀ ∩ (S.shell j ∪ S.shell (j + 1)))ᶜ = 0 := by
      have heq_inter : U₀ ∩ (S.shell j ∪ S.shell (j + 1)) = S.shell j ∪ S.shell (j + 1) :=
        inter_eq_right.mpr hsh_union_sub
      rw [heq_inter]
      have hsub_compl : (S.shell j ∪ S.shell (j + 1))ᶜ ⊆ (S.shell j)ᶜ ∩ (S.shell (j + 1))ᶜ := by
        intro x hx; simp only [mem_compl_iff, mem_union, not_or] at hx; exact hx
      dsimp [μ₀]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      have h1 : lam0 (S.shell j ∪ S.shell (j + 1))ᶜ = 0 := by
        dsimp [lam0]
        rw [Measure.restrict_apply (MeasurableSet.compl ((hsh_meas j).union (hsh_meas (j + 1))))]
        have : (S.shell j ∪ S.shell (j + 1))ᶜ ∩ S.shell j = ∅ := by
          ext x; simp; tauto
        rw [this, measure_empty]
      have h2 : rem (S.shell j ∪ S.shell (j + 1))ᶜ = 0 := by
        refine le_antisymm ?_ (zero_le _)
        calc rem (S.shell j ∪ S.shell (j + 1))ᶜ
            ≤ lam1 (S.shell j ∪ S.shell (j + 1))ᶜ := Measure.le_iff.1 Measure.sub_le _ _
          _ = 0 := by
              dsimp [lam1]
              rw [Measure.restrict_apply (MeasurableSet.compl ((hsh_meas j).union (hsh_meas (j + 1))))]
              have : (S.shell j ∪ S.shell (j + 1))ᶜ ∩ S.shell (j + 1) = ∅ := by
                ext x; simp; tauto
              rw [this, measure_empty]
      have h3 : R1 (S.shell j ∪ S.shell (j + 1))ᶜ = 0 := by
        dsimp [R1]
        rw [Measure.restrict_apply (MeasurableSet.compl ((hsh_meas j).union (hsh_meas (j + 1))))]
        have : (S.shell j ∪ S.shell (j + 1))ᶜ ∩ S.shell (j + 1) = ∅ := by
          ext x; simp; tauto
        rw [this, measure_empty]
      rw [h1, h2, h3, add_zero, zero_add, mul_zero]
    have hμ₀_le_lam : μ₀ ≤ lam := by
      refine Measure.le_iff.2 fun A hA => ?_
      have hstep : μ₀ A ≤ lam0 A + lam1 A := by
        dsimp [μ₀]
        simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
        have hsmul : ENNReal.ofReal α * R1 A ≤ R1 A := by
          calc ENNReal.ofReal α * R1 A ≤ 1 * R1 A :=
                mul_le_mul_right' (ENNReal.ofReal_le_one.mpr hα1) _
            _ = R1 A := one_mul _
        calc lam0 A + rem A + ENNReal.ofReal α * R1 A
            ≤ lam0 A + (rem A + R1 A) := by rw [add_assoc]; exact add_le_add_left hsmul _
          _ = lam0 A + lam1 A := by rw [← Measure.add_apply, hrem_add]
      calc μ₀ A ≤ lam0 A + lam1 A := hstep
        _ = lam (A ∩ S.shell j) + lam (A ∩ S.shell (j + 1)) := by
            simp only [lam0, lam1, Measure.restrict_apply hA]
        _ = lam ((A ∩ S.shell j) ∪ (A ∩ S.shell (j + 1))) := by
            rw [measure_union (hsh_disj.mono inter_subset_right inter_subset_right)
              (hA.inter (hsh_meas (j + 1)))]
        _ ≤ lam A := measure_mono (union_subset inter_subset_left inter_subset_left)
    have hshell_vanish : S.LEOn (S.shell j) lam μ₀ := fun A hA hAs => by
      have hlam0_eq : lam A = lam0 A := by
        dsimp [lam0]; rw [Measure.restrict_apply hA, inter_eq_left.mpr hAs]
      dsimp [μ₀]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      linarith [zero_le (rem A + ENNReal.ofReal α * R1 A)] |> fun _ => by
        rw [hlam0_eq, add_assoc]
        exact le_self_add
    have hshell_reserve : S.LEOn (S.shell (j + 1)) (μ₀ + S.cm (5 / 8)) lam := fun A hA hAs => by
      have hlam1_eq : lam A = lam1 A := by
        dsimp [lam1]; rw [Measure.restrict_apply hA, inter_eq_left.mpr hAs]
      have hR1_eq : R1 A = S.cm (5 / 8) A := by
        dsimp [R1]; rw [Measure.restrict_apply hA, inter_eq_left.mpr hAs]
      rw [hlam1_eq, ← hrem_add, Measure.add_apply, hR1_eq]
      dsimp [μ₀]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [add_assoc (lam0 A), add_comm (lam0 A), add_assoc]
      exact add_le_add_left le_self_add _
    let μ₀_real : Measure ℝ := Measure.map Subtype.val μ₀
    haveI : IsFiniteMeasure μ₀_real := Measure.isFiniteMeasure_map μ₀ Subtype.val
    have hμ₀_real_supp : μ₀_real (Icc B₀ B)ᶜ = 0 := by
      rw [Measure.map_apply hEmb.measurable measurableSet_Icc.compl]
      refine measure_mono_null (fun x hx => ?_) hμ₀_supp
      intro ⟨hx1, _⟩
      exact hx hx1
    have hμ₀_real_univ : μ₀_real univ = Ntot := by
      rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, preimage_univ, hμ₀_univ]
    have hfloor_μ0 : ENNReal.ofReal (W Mk) • volume.restrict (Icc B₀ B) ≤ μ₀_real := by
      have hvol_B : volume.restrict (Icc B₀ B) = volume.restrict (Ico B₀ B) := by
        ext A hA
        have hdiff : A ∩ Icc B₀ B = (A ∩ Ico B₀ B) ∪ (A ∩ {B}) := by
          ext t; simp only [mem_inter_iff, mem_union, mem_Icc, mem_Ico, mem_singleton_iff]
          constructor
          · rintro ⟨htA, ht1, ht2⟩
            rcases eq_or_lt_of_le ht2 with rfl | hlt
            · exact Or.inr ⟨htA, rfl⟩
            · exact Or.inl ⟨htA, ht1, hlt⟩
          · rintro (⟨htA, ht1, ht2⟩ | ⟨htA, rfl⟩)
            · exact ⟨htA, ht1, ht2.le⟩
            · exact ⟨htA, hB0_lt_B.le, le_rfl⟩
        rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hdiff]
        exact measure_union_null (measure_mono_null inter_subset_right Real.volume_singleton)
      have hshj_ge : (S.cm (1 / 8)).restrict (S.shell j) ≤ lam0 := by
        refine Measure.le_iff.2 fun A hA => ?_
        simp only [lam0, Measure.restrict_apply hA]
        calc S.cm (1 / 8) (A ∩ S.shell j)
            ≤ S.cm (5 / 8) (A ∩ S.shell j) := Measure.le_iff.1 (hcm_mono (by norm_num)) _ _
          _ ≤ lam (A ∩ S.shell j) :=
              hInv.2.2.2.1 (A ∩ S.shell j) (hA.inter (hsh_meas j)) inter_subset_right
      have hshj1_ge : (S.cm (1 / 8)).restrict (S.shell (j + 1)) ≤ rem := by
        refine le_trans ?_ hrem_ge
        refine Measure.le_iff.2 fun A hA => ?_
        simp only [Measure.restrict_apply hA]
        exact Measure.le_iff.1 (hcm_mono (by norm_num)) _ _
      have hcm_le_μ0 : (S.cm (1 / 8)).restrict (S.shell j ∪ S.shell (j + 1)) ≤ μ₀ := by
        refine Measure.le_iff.2 fun A hA => ?_
        rw [Measure.restrict_apply hA,
          show A ∩ (S.shell j ∪ S.shell (j + 1)) = (A ∩ S.shell j) ∪ (A ∩ S.shell (j + 1)) by
            ext x; simp; tauto,
          measure_union (hsh_disj.mono inter_subset_right inter_subset_right)
            (hA.inter (hsh_meas (j + 1)))]
        dsimp [μ₀]
        simp only [Measure.add_apply]
        calc S.cm (1 / 8) (A ∩ S.shell j) + S.cm (1 / 8) (A ∩ S.shell (j + 1))
            ≤ lam0 A + rem A := by
              refine add_le_add ?_ ?_
              · simpa [Measure.restrict_apply hA] using
                  Measure.le_iff.1 hshj_ge A hA
              · simpa [Measure.restrict_apply hA] using
                  Measure.le_iff.1 hshj1_ge A hA
          _ ≤ lam0 A + rem A + (ENNReal.ofReal α • R1) A := le_self_add
      have hcm_map_eq : Measure.map Subtype.val ((S.cm (1 / 8)).restrict (S.shell j ∪ S.shell (j + 1))) =
          (ENNReal.ofReal (1 / 8 * S.δ) • ρ_real).restrict (Ico B₀ B) := by
        have hpre : Subtype.val ⁻¹' Ico B₀ B = S.shell j ∪ S.shell (j + 1) := by
          ext x
          simp only [mem_preimage, mem_Ico, mem_union, hshj_eq, hshj1_eq, mem_ofPred_eq]
          constructor
          · intro ⟨hx1, hx2⟩
            rcases lt_or_ge (x : ℝ) B_mid with h | h
            · exact Or.inl ⟨hx1, h⟩
            · exact Or.inr ⟨h, hx2⟩
          · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
            · exact ⟨hx1, hx2.trans (by linarith)⟩
            · exact ⟨le_trans (by linarith) hx1, hx2⟩
        rw [← hpre, ← hEmb.map_restrict_preimage]
        ext A hA
        simp only [Measure.restrict_apply hA, Measure.map_apply hEmb.measurable (hA.inter measurableSet_Ico),
          ShellSetup.cm, Measure.smul_apply, smul_eq_mul, ← hρ_map,
          Measure.map_apply hEmb.measurable (hA.inter measurableSet_Ico)]
      have hfloor_Ico : ENNReal.ofReal (W Mk) • volume.restrict (Ico B₀ B) ≤
          (ENNReal.ofReal (1 / 8 * S.δ) • ρ_real).restrict (Ico B₀ B) := by
        refine Measure.le_iff.2 fun A hA => ?_
        rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.restrict_apply hA,
          Measure.smul_apply, smul_eq_mul, smul_eq_mul]
        dsimp [ρ_real]
        rw [Measure.restrict_apply (hA.inter measurableSet_Ico),
          withDensity_apply _ ((hA.inter measurableSet_Ico).inter measurableSet_Ici)]
        calc ENNReal.ofReal (W Mk) * volume (A ∩ Ico B₀ B)
            = ∫⁻ _ in A ∩ Ico B₀ B, ENNReal.ofReal (W Mk) ∂volume := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ t in A ∩ Ico B₀ B, ENNReal.ofReal ((δ / 8) * C.src.cardyDensity a t) ∂volume := by
              refine setLIntegral_mono_ae (hA.inter measurableSet_Ico) (Eventually.of_forall fun t ht => ?_)
              exact ENNReal.ofReal_le_ofReal (hMk_fl t ht.2.1)
          _ = ENNReal.ofReal (1 / 8 * S.δ) *
                ∫⁻ t in A ∩ Ico B₀ B ∩ Ici T, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
              have hint_eq : A ∩ Ico B₀ B ∩ Ici T = A ∩ Ico B₀ B :=
                inter_eq_left.mpr (inter_subset_right.trans fun t ht => le_trans hB0_ge_T ht.1)
              rw [hint_eq]
              have heq : (fun t : ℝ => ENNReal.ofReal ((δ / 8) * C.src.cardyDensity a t)) =
                  fun t => ENNReal.ofReal (1 / 8 * S.δ) * ENNReal.ofReal (C.src.cardyDensity a t) := by
                ext t
                have hdeq : S.δ = δ := rfl
                rw [hdeq, show (δ / 8) * C.src.cardyDensity a t = (1 / 8 * δ) * C.src.cardyDensity a t by ring,
                  ENNReal.ofReal_mul (by positivity)]
              rw [heq, lintegral_const_mul _ hm_dens]
      rw [hvol_B]
      refine hfloor_Ico.trans ?_
      rw [← hcm_map_eq]
      exact Measure.map_mono hcm_le_μ0 hEmb.measurable
    have hfloor_cell : ENNReal.ofReal (W Mk) • volume.restrict (Icc (B_mid - 1) (B_mid + 1)) ≤ μ₀_real := by
      have h1 : B_mid - 1 = B₀ := by linarith
      have h2 : B_mid + 1 = B := by linarith
      rwa [h1, h2]
    have hμ₀_supp_mid : μ₀_real (Icc (B_mid - 1) (B_mid + 1))ᶜ = 0 := by
      have h1 : B_mid - 1 = B₀ := by linarith
      have h2 : B_mid + 1 = B := by linarith
      rwa [h1, h2]
    obtain ⟨κ, hκ_fin, t_at, d_at, ht_mem, hd_pos, hmatch⟩ :=
      integerMomentMatching_cell hW hMk1 B_mid hμ₀_supp_mid hμ₀_real_univ hfloor_cell
    have ht_mem' : ∀ q : κ, t_at q ∈ Icc B₀ B := fun q => by
      have := ht_mem q; rwa [show B_mid - 1 = B₀ by linarith, show B_mid + 1 = B by linarith] at this
    let σ₀ : Measure X := ∑ q : κ, (d_at q : ℝ≥0∞) • Measure.dirac ⟨t_at q, le_trans hB0_ge_T (ht_mem' q).1⟩
    let σ₀_real : Measure ℝ := Measure.map Subtype.val σ₀
    haveI : IsFiniteMeasure σ₀ := by dsimp [σ₀]; infer_instance
    haveI : IsFiniteMeasure σ₀_real := Measure.isFiniteMeasure_map σ₀ Subtype.val
    have hσ₀_atomic : S.IsIntAtomicOn U₀ σ₀ :=
      ⟨κ, hκ_fin, fun q => ⟨t_at q, le_trans hB0_ge_T (ht_mem' q).1⟩, d_at,
        fun q => ⟨hd_pos q, ht_mem' q⟩, rfl⟩
    have hσ₀_real_eq : σ₀_real = ∑ q : κ, (d_at q : ℝ≥0∞) • Measure.dirac (t_at q) := by
      dsimp [σ₀_real, σ₀]
      ext A hA
      simp only [Measure.map_apply hEmb.measurable hA, Measure.finset_sum_apply,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (hEmb.measurable hA),
        Measure.dirac_apply' _ hA, mem_preimage]
    have hσ₀_real_supp : σ₀_real (Icc B₀ B)ᶜ = 0 := by
      rw [hσ₀_real_eq]
      simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply' _ measurableSet_Icc.compl, mem_compl_iff]
      exact Finset.sum_eq_zero fun q _ => by simp [ht_mem' q]
    have hσ₀_real_mom : ∀ P : ℝ[X], P.degree ≤ Mk →
        ∫ s, P.eval s ∂σ₀_real = ∫ s, P.eval s ∂μ₀_real := by
      intro P hP
      have hmatchP := hmatch P hP
      have hLHS : ∫ s, P.eval s ∂σ₀_real = ∑ q : κ, (d_at q : ℝ) * P.eval (t_at q) := by
        rw [hσ₀_real_eq, integral_finset_sum_measure]
        · refine Finset.sum_congr rfl fun q _ => ?_
          rw [integral_smul_measure, integral_dirac, ENNReal.toReal_natCast, smul_eq_mul]
        · intro q _
          exact ((integrable_dirac' P.continuous.stronglyMeasurable (by simp)).smul_measure (by simp))
      rw [hLHS, hmatchP]
    have hσ₀_mass_eq : σ₀ U₀ = μ₀ U₀ := by
      have h1 : (∑ q : κ, (d_at q : ℝ)) = (Ntot : ℝ) := by
        have hP1 := hσ₀_real_mom (Polynomial.C 1) (by simp)
        have hLHS1 : ∫ s, (Polynomial.C (1 : ℝ)).eval s ∂σ₀_real = ∑ q : κ, (d_at q : ℝ) := by
          rw [hσ₀_real_eq, integral_finset_sum_measure]
          · refine Finset.sum_congr rfl fun q _ => ?_
            simp [integral_smul_measure]
          · intro q _
            exact (integrable_dirac' continuous_const.stronglyMeasurable (by simp)).smul_measure (by simp)
        have hRHS1 : ∫ s, (Polynomial.C (1 : ℝ)).eval s ∂μ₀_real = (Ntot : ℝ) := by
          simp [hμ₀_real_univ]
        linarith
      have hsum_nat : (∑ q : κ, d_at q) = Ntot := by exact_mod_cast h1
      have hσ_U0 : σ₀ U₀ = (∑ q : κ, d_at q : ℕ) := by
        dsimp [σ₀]
        simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' _ hU0_meas, Nat.cast_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        have hq : (⟨t_at q, le_trans hB0_ge_T (ht_mem' q).1⟩ : X) ∈ U₀ := ht_mem' q
        simp [hq]
      have hμ_U0 : μ₀ U₀ = Ntot := by
        have hsub_u : μ₀ U₀ = μ₀ univ := by
          refine le_antisymm (measure_mono (subset_univ _)) ?_
          calc μ₀ univ = μ₀ U₀ + μ₀ U₀ᶜ := (measure_add_measure_compl hU0_meas).symm
            _ = μ₀ U₀ + 0 := by
                congr 1
                refine measure_mono_null (fun x hx => fun hx' => hx hx'.1) hμ₀_supp
            _ = μ₀ U₀ := add_zero _
        rw [hsub_u, hμ₀_univ]
      rw [hσ_U0, hμ_U0, hsum_nat]
    obtain ⟨r, hr_cont, hr_cross, hr_bd⟩ :=
      repair.repair hB0_pos hB0_lt_B Mk hσ₀_real_supp hμ₀_real_supp hσ₀_real_mom
    have hσ_univ_le : σ₀_real.real univ ≤ 9 / 8 * meas.ν.real (Icc T B) := by
      have hσ_eq_μ : σ₀_real univ = μ₀_real univ := by
        have h1 : σ₀_real univ = σ₀ U₀ := by
          rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, preimage_univ]
          have hcomp : σ₀ U₀ᶜ = 0 := by
            dsimp [σ₀]
            simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
              Measure.dirac_apply' _ hU0_meas.compl, mem_compl_iff]
            exact Finset.sum_eq_zero fun q _ => by simp [ht_mem' q]
          rw [← measure_add_measure_compl hU0_meas, hcomp, add_zero]
        rw [h1, hσ₀_mass_eq, ← hμ₀_univ, hμ₀_real_univ]
      have hμ_le_Ω : μ₀ univ ≤ lam (S.Ω (j + 2)) := by
        have hsub_sh : S.shell j ∪ S.shell (j + 1) ⊆ S.Ω (j + 2) := fun x hx => by
          rcases hx with h | h
          · exact S.Ω_mono (Nat.le_succ _) h.1
          · exact h.1
        have hcomp : μ₀ (S.Ω (j + 2))ᶜ = 0 := by
          refine measure_mono_null (fun x hx => fun hmem => hx (hsub_sh hmem.2)) hμ₀_supp
        calc μ₀ univ = μ₀ (S.Ω (j + 2)) + μ₀ (S.Ω (j + 2))ᶜ :=
              (measure_add_measure_compl (S.Ω_open (j + 2)).measurableSet).symm
          _ = μ₀ (S.Ω (j + 2)) := by rw [hcomp, add_zero]
          _ ≤ lam (S.Ω (j + 2)) := Measure.le_iff.1 hμ₀_le_lam _ (S.Ω_open (j + 2)).measurableSet
      have hν_le : S.ν0 (S.Ω (j + 2)) ≤ meas.ν (Icc T B) := by
        have hm_sub : S.Ω (j + 2) ⊆ {x : X | (x : ℝ) ≤ B} := fun x hx => by
          dsimp [S, B] at hx; exact hx.le
        have hmeas_eq : S.ν0 {x : X | (x : ℝ) ≤ B} = meas.ν (Icc T B) := by
          change ν0_sub {x : X | (x : ℝ) ≤ B} = _
          rw [← hν0_map, Measure.map_apply hEmb.measurable measurableSet_Icc]
          congr 1; ext x; simp [x.2]
        rw [← hmeas_eq]
        exact measure_mono hm_sub
      have hfin_νB : meas.ν (Icc T B) ≠ ∞ := by
        have hmeas_eq : S.ν0 {x : X | (x : ℝ) ≤ B} = meas.ν (Icc T B) := by
          change ν0_sub {x : X | (x : ℝ) ≤ B} = _
          rw [← hν0_map, Measure.map_apply hEmb.measurable measurableSet_Icc]
          congr 1; ext x; simp [x.2]
        rw [← hmeas_eq]; exact (hν0_fin B).ne
      have hcomb : σ₀_real univ ≤ ENNReal.ofReal (9 / 8) * meas.ν (Icc T B) := by
        calc σ₀_real univ = μ₀_real univ := hσ_eq_μ
          _ = μ₀ univ := by rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, preimage_univ]
          _ ≤ lam (S.Ω (j + 2)) := hμ_le_Ω
          _ ≤ ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := hlam_Ω2_le
          _ ≤ ENNReal.ofReal (9 / 8) * meas.ν (Icc T B) := by gcongr
      have htoReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_lt_top.ne hfin_νB) hcomb
      simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 9 / 8)] using htoReal
    have hμ_univ_le : μ₀_real.real univ ≤ 9 / 8 * meas.ν.real (Icc T B) := by
      have h1 : σ₀_real univ = μ₀_real univ := by
        rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, preimage_univ,
          Measure.map_apply hEmb.measurable MeasurableSet.univ, preimage_univ]
        have hcomp : σ₀ U₀ᶜ = 0 := by
          dsimp [σ₀]
          simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
            Measure.dirac_apply' _ hU0_meas.compl, mem_compl_iff]
          exact Finset.sum_eq_zero fun q _ => by simp [ht_mem' q]
        rw [← measure_add_measure_compl hU0_meas, hcomp, add_zero, hσ₀_mass_eq, ← hμ₀_univ]
      simpa [Measure.real, h1] using hσ_univ_le
    let r_X : X → ℝ := fun x => r x.1
    have hr_cont_X : ContinuousOn r_X {x : X | B < (x : ℝ)} :=
      hr_cont.comp continuous_subtype_val.continuousOn fun x hx => hx
    have hr_meas : Measurable (fun t : ℝ => if B < t then |r t| else 0) := by
      have hm_on : Measurable (Set.indicator (Ioi B) (fun t => |r t|)) :=
        (measurableOn_Ioi_iff_measurable).mp hr_cont.norm.measurableOn
      convert hm_on using 1
      ext t; simp [Set.indicator]
    let Rp₀_real : Measure ℝ := (volume.withDensity fun t => ENNReal.ofReal (max (r t) 0)).restrict (Ioi B)
    let Rm₀_real : Measure ℝ := (volume.withDensity fun t => ENNReal.ofReal (max (-r t) 0)).restrict (Ioi B)
    let Rp₀ : Measure X := Measure.comap Subtype.val Rp₀_real
    let Rm₀ : Measure X := Measure.comap Subtype.val Rm₀_real
    have hIoiB_sub : Ioi B ⊆ Subtype.val '' (univ : Set X) := by
      rw [Subtype.range_coe]; exact Ioi_subset_Ici hB0_ge_T.le |> fun h =>
        (Ioi_subset_Ici hB0_lt_B.le).trans (Ici_subset_Ici.2 hB0_ge_T)
    have hRp_map : Measure.map Subtype.val Rp₀ = Rp₀_real := by
      dsimp [Rp₀]
      rw [hEmb.map_comap, Subtype.range_coe]
      exact Measure.restrict_eq_self_of_ae_mem (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t ht => show T ≤ t by linarith [mem_Ioi.mp ht])
    have hRm_map : Measure.map Subtype.val Rm₀ = Rm₀_real := by
      dsimp [Rm₀]
      rw [hEmb.map_comap, Subtype.range_coe]
      exact Measure.restrict_eq_self_of_ae_mem (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t ht => show T ≤ t by linarith [mem_Ioi.mp ht])
    have hRp_null : Rp₀ (S.Ω (j + 2)) = 0 := by
      have hm : MeasurableSet (Subtype.val '' S.Ω (j + 2)) :=
        hEmb.measurableSet_image.2 (S.Ω_open (j + 2)).measurableSet
      have h1 : Rp₀ (S.Ω (j + 2)) = Rp₀_real (Subtype.val '' S.Ω (j + 2)) := by
        rw [← hRp_map, Measure.map_apply hEmb.measurable hm]
        congr 1; exact (Subtype.val_injective.preimage_image _).symm
      rw [h1]
      dsimp [Rp₀_real]
      rw [Measure.restrict_apply hm]
      have hemp : Subtype.val '' S.Ω (j + 2) ∩ Ioi B = ∅ := by
        ext t; rintro ⟨⟨x, hx, rfl⟩, ht⟩; dsimp [S, B] at hx; linarith [mem_Ioi.mp ht]
      rw [hemp, measure_empty]
    have hRm_null : Rm₀ (S.Ω (j + 2)) = 0 := by
      have hm : MeasurableSet (Subtype.val '' S.Ω (j + 2)) :=
        hEmb.measurableSet_image.2 (S.Ω_open (j + 2)).measurableSet
      have h1 : Rm₀ (S.Ω (j + 2)) = Rm₀_real (Subtype.val '' S.Ω (j + 2)) := by
        rw [← hRm_map, Measure.map_apply hEmb.measurable hm]
        congr 1; exact (Subtype.val_injective.preimage_image _).symm
      rw [h1]
      dsimp [Rm₀_real]
      rw [Measure.restrict_apply hm]
      have hemp : Subtype.val '' S.Ω (j + 2) ∩ Ioi B = ∅ := by
        ext t; rintro ⟨⟨x, hx, rfl⟩, ht⟩; dsimp [S, B] at hx; linarith [mem_Ioi.mp ht]
      rw [hemp, measure_empty]
    have hr_abs_le : ∀ {t : ℝ}, B < t →
        |r t| ≤ (1 / 2 : ℝ) ^ (j + 4) * S.δ * C.src.cardyDensity a t := by
      intro t ht
      have hB_prev_eq : T + ((k - 1 : ℕ) : ℝ) = B₀ := by dsimp [k, B₀]; simp
      have hB_next_eq : T + ((k + 1 : ℕ) : ℝ) = B := by dsimp [k, B]
      have hHk_pos : 0 < a + B + Real.log (1 / δ) + wR := by
        have hlog_nn : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
        positivity
      set H_k : ℝ := a + B + Real.log (1 / δ) + wR
      set P_k : ℝ := a * B₀
      have hPk_ge : 72 ≤ P_k := by
        have hB0_ge3 : 3 ≤ B₀ := by linarith
        nlinarith
      have hPk_pos : 0 < P_k := by linarith
      have hlogPk_pos : 0 < Real.log P_k := Real.log_pos (by linarith)
      have hM_ineq := hM_ord k hk1
      dsimp at hM_ineq
      rw [hB_prev_eq, hB_next_eq] at hM_ineq
      change K * H_k / Real.log P_k ≤ (Mk : ℝ) at hM_ineq
      let m : ℕ := Mk + 1
      have hm_ge : K * H_k / Real.log P_k ≤ (m : ℝ) := hM_ineq.trans (by exact_mod_cast Nat.le_succ Mk)
      have hKm : (C_exp + 2) * H_k ≤ ((m : ℝ) / 2) * Real.log P_k := by
        have h1 := (div_le_iff₀ hlogPk_pos).mp hm_ge
        dsimp [K] at h1
        linarith
      have hPk_rpow_le : P_k ^ (-(m : ℝ) / 2) ≤ Real.exp (-(C_exp + 2) * H_k) := by
        rw [Real.rpow_def_of_pos hPk_pos]
        apply Real.exp_le_exp.mpr
        have hneg : -(m : ℝ) / 2 * Real.log P_k = -(((m : ℝ) / 2) * Real.log P_k) := by ring
        rw [show Real.log P_k * (-(m : ℝ) / 2) = -(m : ℝ) / 2 * Real.log P_k by ring, hneg]
        linarith
      have hrt_tail := hr_bd ht
      dsimp at hrt_tail
      have hh_eq : (B - B₀) / 2 = 1 := by linarith
      rw [hh_eq, mul_one] at hrt_tail
      have hcount_B := hcount.2 B hB_ge1
      have hsum_meas : σ₀_real.real univ + μ₀_real.real univ ≤
          (9 / 4 : ℝ) * (3 * C.src.tv * B ^ (wR / 2) * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * B))) := by
        linarith [hσ_univ_le, hμ_univ_le, hcount_B]
      have hBw_le : B ^ (wR / 2) ≤ c0 ^ (wR / 2) * Real.exp B := by
        have hc0_pos : 0 < c0 := by positivity
        have hB_pos : 0 < B := by linarith
        have hlog_le : Real.log B ≤ Real.log c0 + B / c0 := by
          have h1 : Real.log (B / c0) ≤ B / c0 - 1 := Real.log_le_sub_one_of_pos (div_pos hB_pos hc0_pos)
          rw [Real.log_div hB_pos.ne' hc0_pos.ne'] at h1
          linarith
        have hmul_log : (wR / 2) * Real.log B ≤ (wR / 2) * Real.log c0 + B := by
          have hw_le_c0 : wR / 2 ≤ c0 := le_max_right _ _
          have hdiv_le : (wR / 2) * (B / c0) ≤ B := by
            rw [mul_div_assoc', div_le_iff₀ hc0_pos]
            exact mul_le_mul_of_nonneg_right hw_le_c0 hB_pos.le
          have h2 := mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ wR / 2)
          linarith
        rw [Real.rpow_def_of_pos hB_pos, Real.rpow_def_of_pos hc0_pos, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      have h4sqrt_le : 4 * π * Real.sqrt (a * B) ≤ 2 * π * a + 2 * π * B := by
        have h1 : 2 * Real.sqrt (a * B) ≤ a + B := two_mul_le_add_sq (Real.sqrt a) (Real.sqrt B) |> fun h => by
          simpa [Real.sqrt_mul ha_pos.le, Real.sq_sqrt ha_pos.le, Real.sq_sqrt (show 0 ≤ B by linarith)] using h
        nlinarith [Real.pi_pos]
      have h2sqrt_le : 2 * π * Real.sqrt (a * B) ≤ π * a + π * B := by linarith
      have hsum_meas2 : σ₀_real.real univ + μ₀_real.real univ ≤
          (9 / 4 : ℝ) * C_count_fac * Real.exp (8 * π * a + (2 * π + 1) * B) := by
        have htv_le : C.src.tv ≤ max C.src.tv 1 := le_max_left _ _
        calc σ₀_real.real univ + μ₀_real.real univ
            ≤ (9 / 4 : ℝ) * (3 * C.src.tv * B ^ (wR / 2) * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * B))) := hsum_meas
          _ ≤ (9 / 4 : ℝ) * (3 * max C.src.tv 1 * (c0 ^ (wR / 2) * Real.exp B) *
                Real.exp (6 * π * a + (2 * π * a + 2 * π * B))) := by
              gcongr
              · exact C.src.tv_nonneg
              · exact Real.exp_le_exp.mpr (by linarith)
          _ = (9 / 4 : ℝ) * C_count_fac * Real.exp (8 * π * a + (2 * π + 1) * B) := by
              dsimp [C_count_fac]
              rw [← Real.exp_add]
              ring_nf
      have ht_B0_le : (t / B₀) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) ≤
          C_w_fac * (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) := by
        have hle_div : t / B₀ ≤ 8 * (t / a) := by
          have ha_le_8B0 : a ≤ 8 * B₀ := by linarith
          rw [div_le_iff₀ hB0_pos, show 8 * (t / a) * B₀ = t * (8 * B₀ / a) by ring]
          exact le_mul_of_one_le_right (by linarith) ((one_le_div ha_pos).mpr ha_le_8B0)
        calc (t / B₀) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2)
            ≤ (8 * (t / a)) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) :=
              Real.rpow_le_rpow (by positivity) hle_div (by positivity)
          _ = C_w_fac * (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) := by
              dsimp [C_w_fac]
              exact Real.mul_rpow (by norm_num) (by positivity)
      let x_t : ℝ := Real.sqrt (a * t)
      let x_B : ℝ := Real.sqrt (a * B)
      have hx_t_nn : 0 ≤ x_t := Real.sqrt_nonneg _
      have hx_B_nn : 0 ≤ x_B := Real.sqrt_nonneg _
      have hterm1_eq : 2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀) =
          2 * π * Real.exp 1 * x_t / ((m : ℝ) * Real.sqrt P_k) := by
        dsimp [x_t, P_k]
        rw [Real.sqrt_mul ha_pos.le t, Real.sqrt_mul ha_pos.le B₀]
        have hsqa_ne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
        field_simp [hsqa_ne]
      have hterm2_eq : 2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀) =
          2 * π * Real.exp 1 * x_B / ((m : ℝ) * Real.sqrt P_k) := by
        dsimp [x_B, P_k]
        rw [Real.sqrt_mul ha_pos.le B, Real.sqrt_mul ha_pos.le B₀]
        have hsqa_ne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
        field_simp [hsqa_ne]
      have hquarter_exp : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-2 * π * x_t) ≤ 1 := by
        have hsq : Real.sqrt x_t = (a * t) ^ (1 / 4 : ℝ) := by
          dsimp [x_t]
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          norm_num
        rw [← hsq]
        exact rpow_half_mul_exp_neg_le_one hx_t_nn
      have hterm1_bound : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
          min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) ≤
          P_k ^ (-(m : ℝ) / 2) := by
        calc (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
              min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m)
            ≤ (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
                (2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m := by
              gcongr; exact min_le_right _ _
          _ = ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-2 * π * x_t)) *
                (Real.exp (-2 * π * x_t) * (2 * π * Real.exp 1 * x_t / ((m : ℝ) * Real.sqrt P_k)) ^ m) := by
              rw [hterm1_eq, ← Real.exp_add]
              have hexp4 : -2 * π * x_t + -2 * π * x_t = -4 * π * x_t := by ring
              rw [hexp4]; ring
          _ ≤ 1 * P_k ^ (-(m : ℝ) / 2) := by
              exact mul_le_mul hquarter_exp (rpow_weighted_taylor_le hPk_pos m hx_t_nn)
                (by positivity) zero_le_one
          _ = P_k ^ (-(m : ℝ) / 2) := one_mul _
      have hterm2_bound : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
          (repair.C_son * Real.exp (repair.C_son * (B + wR)) *
            (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) ≤
          repair.C_son * Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR) *
            P_k ^ (-(m : ℝ) / 2) := by
        have hqt4 : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) ≤ 1 := by
          have hexp_le : Real.exp (-2 * π * x_t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
          calc (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t)
              = ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-2 * π * x_t)) * Real.exp (-2 * π * x_t) := by
                rw [← Real.exp_add, show -2 * π * x_t + -2 * π * x_t = -4 * π * x_t by ring]; ring
            _ ≤ 1 * 1 := mul_le_mul hquarter_exp hexp_le (Real.exp_pos _).le zero_le_one
            _ = 1 := one_mul 1
        have hB_wt := rpow_weighted_taylor_le hPk_pos m hx_B_nn
        have hzB_le : (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m ≤
            Real.exp (2 * π * x_B) * P_k ^ (-(m : ℝ) / 2) := by
          rw [hterm2_eq]
          have h1 := mul_le_mul_of_nonneg_left hB_wt (Real.exp_pos (2 * π * x_B)).le
          have hcan : Real.exp (2 * π * x_B) * Real.exp (-2 * π * x_B) = 1 := by rw [← Real.exp_add]; simp
          rwa [← mul_assoc, hcan, one_mul] at h1
        have hC_nn : 0 ≤ repair.C_son := repair.hC_son_nn
        calc (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
              (repair.C_son * Real.exp (repair.C_son * (B + wR)) *
                (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)
            ≤ 1 * (repair.C_son * Real.exp (repair.C_son * (B + wR)) *
                (Real.exp (2 * π * x_B) * P_k ^ (-(m : ℝ) / 2))) := by
              gcongr
          _ = repair.C_son * (Real.exp (repair.C_son * (B + wR)) * Real.exp (2 * π * x_B)) *
                P_k ^ (-(m : ℝ) / 2) := by ring
          _ ≤ repair.C_son * Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR) *
                P_k ^ (-(m : ℝ) / 2) := by
              gcongr
              rw [← Real.exp_add]
              exact Real.exp_le_exp.mpr (by dsimp [x_B] at h2sqrt_le; linarith)
      have hrho_eq : (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) =
          rhoLowerCore C.src.w a t * ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t)) := by
        unfold rhoLowerCore
        have h1 : (a * t) ^ (-(1 / 4 : ℝ)) * (a * t) ^ (1 / 4 : ℝ) = 1 := by
          rw [← Real.rpow_add (by positivity : 0 < a * t)]; simp
        have h2 : Real.exp (4 * π * x_t) * Real.exp (-4 * π * x_t) = 1 := by
          rw [← Real.exp_add]; simp
        dsimp [x_t]
        calc (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2)
            = (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) *
                ((a * t) ^ (-(1 / 4 : ℝ)) * (a * t) ^ (1 / 4 : ℝ)) *
                (Real.exp (4 * π * Real.sqrt (a * t)) * Real.exp (-4 * π * Real.sqrt (a * t))) := by
              rw [h1, h2, mul_one, mul_one]
          _ = _ := by ring
      have hexp_pos1 : Real.exp (8 * π * a + (2 * π + 1) * B) ≤ Real.exp (C_exp * H_k) := by
        apply Real.exp_le_exp.mpr
        have hlog_nn : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
        dsimp [C_exp, H_k]
        nlinarith [Real.pi_pos, repair.hC_son_nn, hB0_ge_T]
      have hexp_pos2 : Real.exp (8 * π * a + (2 * π + 1) * B) *
          Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR) ≤ Real.exp (C_exp * H_k) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hlog_nn : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
        dsimp [C_exp, H_k]
        nlinarith [Real.pi_pos, repair.hC_son_nn, hB0_ge_T]
      have hbrace :
          Real.exp (8 * π * a + (2 * π + 1) * B) *
            ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
              (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
                repair.C_son * Real.exp (repair.C_son * (B + wR)) *
                  (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)) ≤
          (1 + repair.C_son) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) := by
        have hdist : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
              (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
                repair.C_son * Real.exp (repair.C_son * (B + wR)) *
                  (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) ≤
            (1 + repair.C_son * Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR)) *
              P_k ^ (-(m : ℝ) / 2) := by
          rw [mul_add]
          linarith [hterm1_bound, hterm2_bound]
        have he1_nn : 0 ≤ Real.exp (8 * π * a + (2 * π + 1) * B) := (Real.exp_pos _).le
        have h1 : Real.exp (8 * π * a + (2 * π + 1) * B) *
              (1 + repair.C_son * Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR)) ≤
            (1 + repair.C_son) * Real.exp (C_exp * H_k) := by
          rw [mul_add, mul_one]
          have hC_nn : 0 ≤ repair.C_son := repair.hC_son_nn
          calc Real.exp (8 * π * a + (2 * π + 1) * B) +
                repair.C_son * (Real.exp (8 * π * a + (2 * π + 1) * B) *
                  Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR))
              ≤ Real.exp (C_exp * H_k) + repair.C_son * Real.exp (C_exp * H_k) := by gcongr
            _ = (1 + repair.C_son) * Real.exp (C_exp * H_k) := by ring
        calc Real.exp (8 * π * a + (2 * π + 1) * B) * _
            ≤ Real.exp (8 * π * a + (2 * π + 1) * B) *
                ((1 + repair.C_son * Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR)) *
                  P_k ^ (-(m : ℝ) / 2)) := mul_le_mul_of_nonneg_left hdist he1_nn
          _ = (Real.exp (8 * π * a + (2 * π + 1) * B) *
                (1 + repair.C_son * Real.exp (π * a + (π + repair.C_son) * B + repair.C_son * wR))) *
                P_k ^ (-(m : ℝ) / 2) := by ring
          _ ≤ (1 + repair.C_son) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
      have hC_const_exp : C_const * Real.exp (-H_k) ≤ 1 := by
        have hlog_nn : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
        have hC_le : C_const ≤ Real.exp a := by
          have h1 : C_const ≤ max C_const 1 := le_max_left _ _
          have h2 : max C_const 1 = Real.exp (Real.log (max C_const 1)) :=
            (Real.exp_log (lt_max_of_lt_right one_pos)).symm
          have h3 : Real.exp (Real.log (max C_const 1)) ≤ Real.exp a :=
            Real.exp_le_exp.mpr (by linarith)
          exact h1.trans (h2 ▸ h3)
        have ha_H : a ≤ H_k := by dsimp [H_k]; linarith
        calc C_const * Real.exp (-H_k) ≤ Real.exp a * Real.exp (-a) := by
              exact mul_le_mul hC_le (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
          _ = 1 := by rw [← Real.exp_add]; simp
      have hexp_tail : Real.exp (-H_k) ≤ (1 / 2 : ℝ) ^ (j + 4) * δ := by
        have hlog_eq : Real.exp (-Real.log (1 / δ)) = δ := by
          rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hδ0), one_div_inv]
        have hsum_ge : ((j + 4 : ℕ) : ℝ) ≤ a + B + wR := by
          push_cast; dsimp [B]; linarith
        have hexp_neg1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
          have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) h2e
        have hexp_pow : Real.exp (-((j + 4 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ (j + 4) := by
          rw [show -((j + 4 : ℕ) : ℝ) = ((j + 4 : ℕ) : ℝ) * (-1) by ring, Real.exp_nat_mul]
          exact pow_le_pow_left₀ (Real.exp_pos _).le hexp_neg1 _
        calc Real.exp (-H_k) = Real.exp (-(a + B + wR)) * Real.exp (-Real.log (1 / δ)) := by
              dsimp [H_k]; rw [← Real.exp_add]; congr 1; ring
          _ = Real.exp (-(a + B + wR)) * δ := by rw [hlog_eq]
          _ ≤ Real.exp (-((j + 4 : ℕ) : ℝ)) * δ := by
              gcongr; linarith
          _ ≤ (1 / 2 : ℝ) ^ (j + 4) * δ := by gcongr
      have hrho_cd : c_vac * rhoLowerCore C.src.w a t ≤ C.src.cardyDensity a t :=
        hrho_lb ha_star (by linarith)
      have hcomb_exp : Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) ≤ Real.exp (-H_k) * Real.exp (-H_k) := by
        calc Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2)
            ≤ Real.exp (C_exp * H_k) * Real.exp (-(C_exp + 2) * H_k) := by gcongr
          _ = Real.exp (-H_k) * Real.exp (-H_k) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc |r t| ≤ 2 * π * (σ₀_real.real univ + μ₀_real.real univ) * (t / B₀) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) *
              (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
                repair.C_son * Real.exp (repair.C_son * (B + wR)) *
                  (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) := hrt_tail
        _ ≤ 2 * π * ((9 / 4 : ℝ) * C_count_fac * Real.exp (8 * π * a + (2 * π + 1) * B)) *
              (C_w_fac * (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2)) *
              (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
                repair.C_son * Real.exp (repair.C_son * (B + wR)) *
                  (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) := by
            gcongr
            exact add_nonneg (le_min zero_le_one (by positivity)) (mul_nonneg (mul_nonneg repair.hC_son_nn (Real.exp_pos _).le) (by positivity))
        _ = (2 * π * (9 / 4 * C_count_fac) * C_w_fac * rhoLowerCore C.src.w a t) *
              (Real.exp (8 * π * a + (2 * π + 1) * B) *
                ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
                  (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
                    repair.C_son * Real.exp (repair.C_son * (B + wR)) *
                      (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m))) := by
            rw [hrho_eq]; ring
        _ ≤ (2 * π * (9 / 4 * C_count_fac) * C_w_fac * rhoLowerCore C.src.w a t) *
              ((1 + repair.C_son) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2)) := by
            gcongr; exact mul_nonneg (by positivity) (rhoLowerCore_pos ha_pos (by linarith)).le
        _ = (C_const * (Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2))) * (c_vac * rhoLowerCore C.src.w a t) := by
            dsimp [C_const]; field_simp [hc_vac_pos.ne']
        _ ≤ (C_const * (Real.exp (-H_k) * Real.exp (-H_k))) * C.src.cardyDensity a t := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hcomb_exp (by dsimp [C_const]; have := repair.hC_son_nn; positivity))
              hrho_cd (mul_nonneg hc_vac_pos.le (rhoLowerCore_pos ha_pos (by linarith)).le) (by positivity)
        _ = (C_const * Real.exp (-H_k)) * Real.exp (-H_k) * C.src.cardyDensity a t := by ring
        _ ≤ (1 : ℝ) * ((1 / 2 : ℝ) ^ (j + 4) * δ) * C.src.cardyDensity a t := by
            refine mul_le_mul (mul_le_mul hC_const_exp hexp_tail (Real.exp_pos _).le zero_le_one)
              le_rfl (hV_nonneg_Ici t (by linarith)) (by positivity)
        _ = (1 / 2 : ℝ) ^ (j + 4) * S.δ * C.src.cardyDensity a t := by
            change (1 : ℝ) * ((1 / 2 : ℝ) ^ (j + 4) * S.δ) * C.src.cardyDensity a t = _; ring
    have hR_le : Rp₀ + Rm₀ ≤ S.cm ((1 / 2 : ℝ) ^ (j + 4)) := by
      have hreal_le : Rp₀_real + Rm₀_real ≤
          (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) • ρ_real) := by
        refine Measure.le_iff.2 fun A hA => ?_
        have hm_pos_p : Measurable (fun t : ℝ => ENNReal.ofReal (max (r t) 0)) :=
          ((measurableOn_Ioi_iff_measurable).mp hr_cont.measurableOn).max measurable_const |>.ennreal_ofReal
        have hm_pos_m : Measurable (fun t : ℝ => ENNReal.ofReal (max (-r t) 0)) :=
          ((measurableOn_Ioi_iff_measurable).mp hr_cont.neg.measurableOn).max measurable_const |>.ennreal_ofReal
        have hr_max_sum : ∀ t : ℝ, max (r t) 0 + max (-r t) 0 = |r t| := fun t => by
          rcases le_total 0 (r t) with h | h <;> simp [max_eq_left, max_eq_right, abs_of_nonneg, abs_of_nonpos, h] <;> linarith
        dsimp [Rp₀_real, Rm₀_real, ρ_real]
        simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
          withDensity_apply _ (hA.inter measurableSet_Ioi)]
        rw [← lintegral_add_left hm_pos_p]
        have hlin : ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal (max (r t) 0) + ENNReal.ofReal (max (-r t) 0) ∂volume =
            ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal |r t| ∂volume := by
          refine setLIntegral_congr_fun (hA.inter measurableSet_Ioi) (Eventually.of_forall fun t _ => ?_)
          rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), hr_max_sum]
        rw [hlin, withDensity_apply _ (hA.inter measurableSet_Ici)]
        calc ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal |r t| ∂volume
            ≤ ∫⁻ t in A ∩ Ioi B,
                ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ * C.src.cardyDensity a t) ∂volume := by
              refine setLIntegral_mono_ae (hA.inter measurableSet_Ioi) (Eventually.of_forall fun t ht => ?_)
              exact ENNReal.ofReal_le_ofReal (hr_abs_le (mem_Ioi.mp ht.2))
          _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) *
                ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
              have heq : (fun t => ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ * C.src.cardyDensity a t)) =
                  fun t => ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) * ENNReal.ofReal (C.src.cardyDensity a t) := by
                ext t; exact ENNReal.ofReal_mul (by positivity)
              rw [heq, lintegral_const_mul _ hm_dens]
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) *
                ∫⁻ t in A ∩ Ici T, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
              gcongr
              exact lintegral_mono_set (inter_subset_inter_right A fun t ht => by linarith [mem_Ioi.mp ht])
      refine Measure.le_iff.2 fun A hA => ?_
      have hA_val : MeasurableSet (Subtype.val '' A) := hEmb.measurableSet_image.2 hA
      have h1 : (Rp₀ + Rm₀) A = (Rp₀_real + Rm₀_real) (Subtype.val '' A) := by
        simp only [Measure.add_apply]
        have hp : Rp₀ A = Rp₀_real (Subtype.val '' A) := by
          rw [← hRp_map, Measure.map_apply hEmb.measurable hA_val]; congr 1
          exact (Subtype.val_injective.preimage_image A).symm
        have hm : Rm₀ A = Rm₀_real (Subtype.val '' A) := by
          rw [← hRm_map, Measure.map_apply hEmb.measurable hA_val]; congr 1
          exact (Subtype.val_injective.preimage_image A).symm
        rw [hp, hm]
      have h2 : S.cm ((1 / 2 : ℝ) ^ (j + 4)) A =
          (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) • ρ_real) (Subtype.val '' A) := by
        simp only [ShellSetup.cm, Measure.smul_apply, smul_eq_mul]
        congr 1; change ρ_sub A = _
        rw [← hρ_map, Measure.map_apply hEmb.measurable hA_val]; congr 1
        exact (Subtype.val_injective.preimage_image A).symm
      rw [h1, h2]
      exact Measure.le_iff.1 hreal_le (Subtype.val '' A) hA_val
    have hbal : ∀ β : RPos,
        ∫ x, S.K β x ∂σ₀ + ∫ x, S.K β x ∂Rp₀ =
          ∫ x, S.K β x ∂μ₀ + ∫ x, S.K β x ∂Rm₀ := fun β => by
      have hcK : Continuous (fun t : ℝ => thermalDiff C.src.w β.1 t) := by
        unfold thermalDiff; fun_prop
      have hK_bd : ∀ {t : ℝ}, B < t → |thermalDiff C.src.w β.1 t| ≤
          Real.exp (-2 * π * β.1 * t) + β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * t) := by
        intro t _
        unfold thermalDiff
        have h1 := abs_sub (Real.exp (-2 * π * β.1 * t)) (β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * t / β.1))
        rwa [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg (Real.rpow_nonneg β.2.le _),
          abs_of_pos (Real.exp_pos _), show 2 * π * t / β.1 = 2 * π * β.1⁻¹ * t by
            rw [div_eq_mul_inv]; ring] at h1
      have hr_int1 := (hr_cross β.2).1
      have hr_int2 := (hr_cross (inv_pos.mpr β.2)).1
      have hK_r_int : IntegrableOn (fun t => thermalDiff C.src.w β.1 t * r t) (Ioi B) := by
        have hdom : IntegrableOn (fun t =>
            Real.exp (-2 * π * β.1 * t) * |r t| +
              β.1 ^ (-(C.src.w : ℝ)) * (Real.exp (-2 * π * β.1⁻¹ * t) * |r t|)) (Ioi B) :=
          hr_int1.add (hr_int2.const_mul _)
        refine hdom.mono' (hcK.aestronglyMeasurable.mul
          ((hr_cont.aestronglyMeasurable measurableSet_Ioi).mono_measure Measure.restrict_le_self |> fun _ =>
            hr_cont.continuousOn.aestronglyMeasurable measurableSet_Ioi)) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun t ht => ?_
        rw [Real.norm_eq_abs, abs_mul]
        calc |thermalDiff C.src.w β.1 t| * |r t|
            ≤ (Real.exp (-2 * π * β.1 * t) + β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * t)) * |r t| :=
              mul_le_mul_of_nonneg_right (hK_bd ht) (abs_nonneg _)
          _ = Real.exp (-2 * π * β.1 * t) * |r t| +
                β.1 ^ (-(C.src.w : ℝ)) * (Real.exp (-2 * π * β.1⁻¹ * t) * |r t|) := by ring
      have hp_int_real : Integrable (fun t => thermalDiff C.src.w β.1 t) Rp₀_real := by
        dsimp [Rp₀_real]
        rw [Measure.restrict_withDensity measurableSet_Ioi,
          integrable_withDensity_iff_integrable_smul'
            ((((measurableOn_Ioi_iff_measurable).mp hr_cont.measurableOn).max measurable_const).ennreal_ofReal)
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        refine hK_r_int.abs.mono' ?_ ?_
        · exact (hcK.aestronglyMeasurable.smul_left _).mono_measure le_rfl |> fun _ =>
            (hcK.aestronglyMeasurable.mul
              (( hr_cont.aestronglyMeasurable measurableSet_Ioi |> fun _ =>
                (hr_cont.max continuousOn_const).aestronglyMeasurable measurableSet_Ioi)))
        · rw [ae_restrict_iff' measurableSet_Ioi]
          refine Eventually.of_forall fun t _ => ?_
          rw [smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _), Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (le_max_right _ _)]
          gcongr; exact le_abs_self _ |> fun _ => max_le (le_abs_self _) (abs_nonneg _)
      have hm_int_real : Integrable (fun t => thermalDiff C.src.w β.1 t) Rm₀_real := by
        dsimp [Rm₀_real]
        rw [Measure.restrict_withDensity measurableSet_Ioi,
          integrable_withDensity_iff_integrable_smul'
            ((((measurableOn_Ioi_iff_measurable).mp hr_cont.neg.measurableOn).max measurable_const).ennreal_ofReal)
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        refine hK_r_int.abs.mono' ?_ ?_
        · exact (hcK.aestronglyMeasurable.mul
              (hr_cont.neg.max continuousOn_const |>.aestronglyMeasurable measurableSet_Ioi))
        · rw [ae_restrict_iff' measurableSet_Ioi]
          refine Eventually.of_forall fun t _ => ?_
          rw [smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _), Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (le_max_right _ _)]
          gcongr; exact max_le (neg_le_abs _) (abs_nonneg _)
      have hRp_int_eq : ∫ x, S.K β x ∂Rp₀ =
          ∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (r t) 0 := by
        have h1 : ∫ x, S.K β x ∂Rp₀ = ∫ t, thermalDiff C.src.w β.1 t ∂Rp₀_real := by
          rw [← hRp_map, integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]
          rfl
        rw [h1]
        dsimp [Rp₀_real]
        rw [Measure.restrict_withDensity measurableSet_Ioi,
          integral_withDensity_eq_integral_toReal_smul
            ((((measurableOn_Ioi_iff_measurable).mp hr_cont.measurableOn).max measurable_const).ennreal_ofReal)
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _), mul_comm]
      have hRm_int_eq : ∫ x, S.K β x ∂Rm₀ =
          ∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (-r t) 0 := by
        have h1 : ∫ x, S.K β x ∂Rm₀ = ∫ t, thermalDiff C.src.w β.1 t ∂Rm₀_real := by
          rw [← hRm_map, integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]
          rfl
        rw [h1]
        dsimp [Rm₀_real]
        rw [Measure.restrict_withDensity measurableSet_Ioi,
          integral_withDensity_eq_integral_toReal_smul
            ((((measurableOn_Ioi_iff_measurable).mp hr_cont.neg.measurableOn).max measurable_const).ennreal_ofReal)
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _), mul_comm]
      have hσ_eq : ∫ x, S.K β x ∂σ₀ = ∫ s, thermalDiff C.src.w β.1 s ∂σ₀_real := by
        dsimp [σ₀_real]
        rw [integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]; rfl
      have hμ_eq : ∫ x, S.K β x ∂μ₀ = ∫ s, thermalDiff C.src.w β.1 s ∂μ₀_real := by
        dsimp [μ₀_real]
        rw [integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]; rfl
      have hrp_int : IntegrableOn (fun t => thermalDiff C.src.w β.1 t * max (r t) 0) (Ioi B) := by
        dsimp [Rp₀_real] at hp_int_real
        rw [Measure.restrict_withDensity measurableSet_Ioi,
          integrable_withDensity_iff_integrable_smul'
            ((((measurableOn_Ioi_iff_measurable).mp hr_cont.measurableOn).max measurable_const).ennreal_ofReal)
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hp_int_real
        refine hp_int_real.congr ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t _ => by
          rw [smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _), mul_comm]
      have hrm_int : IntegrableOn (fun t => thermalDiff C.src.w β.1 t * max (-r t) 0) (Ioi B) := by
        dsimp [Rm₀_real] at hm_int_real
        rw [Measure.restrict_withDensity measurableSet_Ioi,
          integrable_withDensity_iff_integrable_smul'
            ((((measurableOn_Ioi_iff_measurable).mp hr_cont.neg.measurableOn).max measurable_const).ennreal_ofReal)
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hm_int_real
        refine hm_int_real.congr ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t _ => by
          rw [smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _), mul_comm]
      have hsub_r : ∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (r t) 0 -
            ∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (-r t) 0 =
          ∫ t in Ioi B, thermalDiff C.src.w β.1 t * r t := by
        rw [← integral_sub hrp_int hrm_int]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rcases le_total 0 (r t) with h | h <;>
          simp [max_eq_left, max_eq_right, h] <;> ring
      rw [hσ_eq, hμ_eq, hRp_int_eq, hRm_int_eq]
      linarith [(hr_cross β.2).2]
    refine ⟨Unit, inferInstance, fun _ => U₀, fun _ => μ₀, fun _ => σ₀, fun _ => Rp₀, fun _ => Rm₀, ?_⟩
    exact
      { cell_closed := fun _ => hcell_closed
        cell_sub := fun _ => hcell_sub
        sigma_atomic := fun _ => hσ₀_atomic
        mu_supp := fun _ => hμ₀_supp
        mass := fun _ => hσ₀_mass_eq
        mu_le := by simpa using hμ₀_le_lam
        shell_vanish := fun A hA hAs => by simpa using hshell_vanish A hA hAs
        shell_reserve := fun A hA hAs => by simpa using hshell_reserve A hA hAs
        Rp_null := fun _ => hRp_null
        Rm_null := fun _ => hRm_null
        R_le := by simpa using hR_le
        balance := fun _ β => hbal β
        comparison := fun _ γ x hx y hy => by
          dsimp [S]
          have hx_ge : B₀ ≤ x.1 := hx.1
          have hy_le : y.1 ≤ B := hy.2
          have hexp_le : Real.exp (-2 * π * γ.1 * x.1) ≤ Real.exp (4 * π * γ.1) * Real.exp (-2 * π * γ.1 * y.1) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hdiff : y.1 - x.1 ≤ 2 := by linarith
            nlinarith [Real.pi_pos, γ.2]
          exact hexp_le }
  obtain ⟨σ, hσ_atom, hσ_compact, _, hσ_e_int, hσ_K⟩ := S.shell_inv hcells
  let νℤ : Measure ℝ := Measure.map Subtype.val (Measure.sum σ)
  have hνℤ_supp : νℤ (Ici T)ᶜ = 0 := by
    rw [Measure.map_apply hEmb.measurable measurableSet_Ici.compl]
    have hemp : Subtype.val ⁻¹' (Ici T)ᶜ = ∅ := by
      ext x; simp [x.2]
    rw [hemp, measure_empty]
  have hνℤ_laplace : ∀ {β : ℝ}, 0 < β →
      IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici 0) νℤ := fun {β} hβ => by
    have hae_0 : ∀ᵐ t ∂νℤ, t ∈ Ici (0 : ℝ) := by
      have := measure_eq_zero_iff_ae_notMem.1 hνℤ_supp
      filter_upwards [this] with t ht
      exact le_trans (by linarith) (not_not.mp ht)
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae_0]
    have hcont_e : Continuous (fun t : ℝ => Real.exp (-2 * π * β * t)) := by fun_prop
    exact (integrable_map_measure hcont_e.aestronglyMeasurable hEmb.measurable.aemeasurable).2
      (hσ_e_int ⟨β, hβ⟩)
  have hνℤ_cross : ∀ {β : ℝ}, 0 < β →
      ∫ t in Ici 0, thermalDiff C.src.w β t ∂νℤ =
        ∫ t in Ioi 0, thermalDiff C.src.w β t * C.src.cardyDensity a t := fun {β} hβ => by
    have hae_0 : ∀ᵐ t ∂νℤ, t ∈ Ici (0 : ℝ) := by
      have := measure_eq_zero_iff_ae_notMem.1 hνℤ_supp
      filter_upwards [this] with t ht
      exact le_trans (by linarith) (not_not.mp ht)
    rw [Measure.restrict_eq_self_of_ae_mem hae_0]
    have hcont_K : Continuous (fun t : ℝ => thermalDiff C.src.w β t) := by unfold thermalDiff; fun_prop
    rw [integral_map hEmb.measurable.aemeasurable hcont_K.aestronglyMeasurable]
    exact hσ_K ⟨β, hβ⟩
  let measZ : SourceCrossingMeasure C.src a :=
    { ν := νℤ
      supp_nonneg := by
        have hsub : Iio (0 : ℝ) ⊆ (Ici T)ᶜ := fun t ht => by
          simp only [mem_compl_iff, mem_Ici, not_le]; linarith [mem_Iio.mp ht]
        exact measure_mono_null hsub hνℤ_supp
      finite_laplace := hνℤ_laplace
      crossing := hνℤ_cross }
  refine ⟨measZ, hνℤ_supp, ?_⟩
  classical
  have hσ_unpack : ∀ j : ℕ, ∃ (ι : Type) (_ : Fintype ι) (x : ι → X) (d : ι → ℕ),
      (∀ i, 1 ≤ d i ∧ x i ∈ closure (S.Ω (j + 2)) \ S.Ω j) ∧
      σ j = ∑ i, (d i : ℝ≥0∞) • Measure.dirac (x i) := hσ_atom
  choose ι_s hfin_s x_s d_s hxd_s hσ_eq_s using hσ_unpack
  letI := hfin_s
  let S_set : Set ℝ := ⋃ j : ℕ, Set.range (fun i : ι_s j => (x_s j i : ℝ))
  have hx_bounds : ∀ (j : ℕ) (i : ι_s j), T + (j : ℝ) ≤ (x_s j i : ℝ) := fun j i => by
    have hnot := (hxd_s j i).2.2
    simpa [S, not_lt] using hnot
  let d_tot : ℝ → ℕ := fun y =>
    ∑ j ∈ Finset.range (Nat.floor (max 0 (y - T)) + 1),
      ∑ i : ι_s j, if (x_s j i : ℝ) = y then d_s j i else 0
  have hd_pos : ∀ y ∈ S_set, 1 ≤ d_tot y := by
    intro y hy
    rcases mem_iUnion.1 hy with ⟨j₀, i₀, rfl⟩
    have hj_lt : j₀ < Nat.floor (max 0 ((x_s j₀ i₀ : ℝ) - T)) + 1 := by
      have hge := hx_bounds j₀ i₀
      have hj_le : j₀ ≤ Nat.floor (max 0 ((x_s j₀ i₀ : ℝ) - T)) :=
        Nat.le_floor (le_max_of_le_right (by linarith))
      exact Nat.lt_succ_of_le hj_le
    refine le_trans (hxd_s j₀ i₀).1 ?_
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj_lt))
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀))
    simp
  have hS_loc_fin : ∀ K : Set ℝ, IsCompact K → (S_set ∩ K).Finite := by
    intro K hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp
    · obtain ⟨R, hR⟩ := hK.bddAbove
      let N := Nat.floor (max 0 (R - T)) + 1
      have hsub : S_set ∩ K ⊆ ⋃ j ∈ Finset.range N, Set.range (fun i : ι_s j => (x_s j i : ℝ)) := by
        rintro y ⟨hyS, hyK⟩
        rcases mem_iUnion.1 hyS with ⟨j, i, rfl⟩
        have hleR : (x_s j i : ℝ) ≤ R := hR hyK
        have hj_le : j ≤ Nat.floor (max 0 (R - T)) :=
          Nat.le_floor (le_max_of_le_right (by linarith [hx_bounds j i]))
        exact mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le)) ⟨i, rfl⟩
      exact (Finset.finite_toSet (Finset.range N)).biUnion
        (fun j _ => Set.finite_range _) |>.subset hsub
  refine ⟨S_set, d_tot, hS_loc_fin, hd_pos, ?_⟩
  ext A hA
  change νℤ A = (Measure.sum fun y : S_set => (d_tot y : ℝ≥0∞) • Measure.dirac (y : ℝ)) A
  have hν_A : νℤ A = ∑' p : (j : ℕ) × ι_s j,
      if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0 := by
    rw [Measure.map_apply hEmb.measurable hA, Measure.sum_apply _ (hEmb.measurable hA)]
    rw [ENNReal.tsum_sigma']
    refine tsum_congr fun j => ?_
    rw [hσ_eq_s j]
    simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (hEmb.measurable hA), mem_preimage, Set.indicator_apply]
    rw [← tsum_fintype]
    refine tsum_congr fun i => ?_
    split_ifs <;> simp
  have hsum_A : (Measure.sum fun y : S_set => (d_tot y : ℝ≥0∞) • Measure.dirac (y : ℝ)) A =
      ∑' y : S_set, if (y : ℝ) ∈ A then (d_tot y : ℝ≥0∞) else 0 := by
    rw [Measure.sum_apply _ hA]
    refine tsum_congr fun y => ?_
    simp [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  rw [hν_A, hsum_A]
  let f_map : ((j : ℕ) × ι_s j) → S_set := fun p =>
    ⟨(x_s p.1 p.2 : ℝ), mem_iUnion.mpr ⟨p.1, p.2, rfl⟩⟩
  rw [← ENNReal.tsum_fiberwise (fun p : (j : ℕ) × ι_s j =>
      if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0) f_map]
  refine tsum_congr fun y => ?_
  have hfib_eq : ∑' (p : {p : (j : ℕ) × ι_s j // f_map p = y}),
        (if (x_s p.1.1 p.1.2 : ℝ) ∈ A then (d_s p.1.1 p.1.2 : ℝ≥0∞) else 0) =
      if (y : ℝ) ∈ A then (d_tot y : ℝ≥0∞) else 0 := by
    let N := Nat.floor (max 0 ((y : ℝ) - T)) + 1
    let g : ((j : ℕ) × ι_s j) → ℝ≥0∞ := fun p =>
      if f_map p = y then (if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0) else 0
    have hfib_g : (∑' p : {p : (j : ℕ) × ι_s j // f_map p = y},
          (if (x_s p.1.1 p.1.2 : ℝ) ∈ A then (d_s p.1.1 p.1.2 : ℝ≥0∞) else 0)) =
        ∑' p : (j : ℕ) × ι_s j, g p := by
      have := (Equiv.tsum_subtype (fun p : (j : ℕ) × ι_s j => f_map p = y)
        (fun p => if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0))
      simpa [g, Set.indicator_apply] using this
    rw [hfib_g, ENNReal.tsum_sigma']
    have hvan : ∀ j : ℕ, j ∉ Finset.range N → (∑' i : ι_s j, g ⟨j, i⟩) = 0 := by
      intro j hj
      refine ENNReal.tsum_eq_zero.2 fun i => ?_
      dsimp [g, f_map]
      split_ifs with hfeq
      · have heq_y : (x_s j i : ℝ) = (y : ℝ) := congrArg Subtype.val hfeq
        have hj_le : j ≤ Nat.floor (max 0 ((y : ℝ) - T)) :=
          Nat.le_floor (le_max_of_le_right (by linarith [hx_bounds j i]))
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le)) hj
      · rfl
    rw [tsum_eq_sum hvan]
    have hsum_d : (∑ j ∈ Finset.range N, ∑' i : ι_s j, g ⟨j, i⟩) =
        if (y : ℝ) ∈ A then (d_tot y : ℝ≥0∞) else 0 := by
      split_ifs with hyA
      · simp only [d_tot, N, Nat.cast_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [tsum_fintype]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp [g, f_map]
        have hiff : f_map ⟨j, i⟩ = y ↔ (x_s j i : ℝ) = (y : ℝ) := Subtype.ext_iff
        rw [hiff]
        split_ifs with heq
        · simp [heq, hyA]
        · simp
      · refine Finset.sum_eq_zero fun j _ => ?_
        refine ENNReal.tsum_eq_zero.2 fun i => ?_
        dsimp [g, f_map]
        split_ifs with hfeq hmem
        · exact absurd (congrArg Subtype.val hfeq ▸ hmem) hyA
        · rfl
        · rfl
    exact hsum_d
  exact hfib_eq

/-- **Theorem INT-1 (`int:atom`)**, concrete Chebyshev instantiation with
`W(M) = 8 (M + 1)^{5/2}` (`cheb_explicit`). -/
theorem int_atom_cheb_explicit (C : CommonSource) (repair : IntRepairSonineInput C.src.w) :
    ∃ K a₁ : ℝ, 0 < K ∧ max C.a₀ 24 ≤ a₁ ∧
      ∀ {a T δ : ℝ}, a₁ ≤ a → a / 8 ≤ T → 0 < δ → δ ≤ 1 →
        ∀ (meas : SourceCrossingMeasure C.src a), meas.ν (Ici T)ᶜ = 0 →
        (ENNReal.ofReal δ •
          (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T) ≤
            meas.ν) →
        ∀ (M : ℕ → ℕ), (∀ k, 1 ≤ M k) →
          (∀ k : ℕ, 1 ≤ k →
            let B_prev := T + ((k - 1 : ℕ) : ℝ)
            let B_next := T + ((k + 1 : ℕ) : ℝ)
            let H_k := a + B_next + Real.log (1 / δ) + (C.src.w : ℝ)
            let P_k := a * B_prev
            K * H_k / Real.log P_k ≤ (M k : ℝ)) →
          (∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, T + ((k - 1 : ℕ) : ℝ) ≤ s →
            8 * ((M k : ℝ) + 1) ^ 2 * Real.sqrt ((M k : ℝ) + 1) ≤
              (δ / 8) * C.src.cardyDensity a s) →
          ∃ measZ : SourceCrossingMeasure C.src a,
            measZ.ν (Ici T)ᶜ = 0 ∧ IsIntegerCounting measZ.ν :=
  int_atom_common C sufficientMomentFloor_cheb_explicit repair

/-- **Theorem INT-1 (`int:atom`)**, fixed-weight `(H_w)` specialisation (`AdmissibleCrossingMeasure prob a`). -/
theorem int_atom_fixedWeight (prob : FixedWeightProblem) (repair : IntRepairSonineInput prob.w) :
    ∃ K a₁ : ℝ, 0 < K ∧ max (max prob.totalShift 1) 24 ≤ a₁ ∧
      ∀ {a T δ : ℝ}, a₁ ≤ a → a / 8 ≤ T → 0 < δ → δ ≤ 1 →
        ∀ (meas : AdmissibleCrossingMeasure prob a), meas.ν (Ici T)ᶜ = 0 →
        (ENNReal.ofReal δ •
          (volume.withDensity fun t => ENNReal.ofReal (prob.cardyDensity a t)).restrict (Ici T) ≤
            meas.ν) →
        ∀ (M : ℕ → ℕ), (∀ k, 1 ≤ M k) →
          (∀ k : ℕ, 1 ≤ k →
            let B_prev := T + ((k - 1 : ℕ) : ℝ)
            let B_next := T + ((k + 1 : ℕ) : ℝ)
            let H_k := a + B_next + Real.log (1 / δ) + (prob.w : ℝ)
            let P_k := a * B_prev
            K * H_k / Real.log P_k ≤ (M k : ℝ)) →
          (∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, T + ((k - 1 : ℕ) : ℝ) ≤ s →
            8 * ((M k : ℝ) + 1) ^ 2 * Real.sqrt ((M k : ℝ) + 1) ≤
              (δ / 8) * prob.cardyDensity a s) →
          ∃ measZ : AdmissibleCrossingMeasure prob a,
            measZ.ν (Ici T)ᶜ = 0 ∧ IsIntegerCounting measZ.ν := by
  have hshift : ∀ {a : ℝ}, max prob.totalShift 1 ≤ a → (ShiftSource.ofProblem prob).ShiftLE a :=
    fun {a} ha => (ofProblem_shiftLE_iff prob).2 ((le_max_left _ _).trans ha)
  let F : FloorData (ShiftSource.ofProblem prob) := ⟨prob.m, prob.μ, prob.hμ, 1, one_pos⟩
  let C : CommonSource :=
    { src := ShiftSource.ofProblem prob
      F := F
      a₀ := max prob.totalShift 1
      at_ := fun {a} ha =>
        { pos := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ha)
          shift := hshift ha
          prob_shift := (le_max_left _ _).trans ha
          floor := fun _ _ => by rw [one_mul] } }
  obtain ⟨K, a₁, hK, ha₁, hmain⟩ := int_atom_cheb_explicit C repair
  refine ⟨K, a₁, hK, ha₁, fun {a T δ} ha hT hδ0 hδ1 meas hsupp hres M hM1 hM_ord hM_fl => ?_⟩
  let smeas : SourceCrossingMeasure C.src a :=
    { ν := meas.ν
      supp_nonneg := meas.supp_nonneg
      finite_laplace := meas.finite_laplace
      crossing := fun {β} hβ => by simpa [C] using meas.crossing hβ }
  obtain ⟨smeasZ, hsZ_supp, hsZ_cnt⟩ :=
    hmain ha hT hδ0 hδ1 smeas hsupp hres M hM1 hM_ord hM_fl
  exact ⟨⟨smeasZ.ν, smeasZ.supp_nonneg, smeasZ.finite_laplace,
    fun {β} hβ => by simpa [C] using smeasZ.crossing hβ⟩, hsZ_supp, hsZ_cnt⟩

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_atom_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_atom_common

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_atom_cheb_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_atom_cheb_explicit

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_atom_fixedWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_atom_fixedWeight

end FormalResearch.ModularBootstrap.Integrality


