module

public import FormalResearch.ModularBootstrap.Integrality.AtomCell
public import FormalResearch.ModularBootstrap.Integrality.IntClosed
public import FormalResearch.ModularBootstrap.Mixtures.WeightAxioms

/-!
# Cell-by-cell atomisation of a reserved crossing measure (`int:atom`, Theorem INT-1)

`CFT/modular_bootstrap/paper/integrality.tex`, Theorem INT-1 (`int:atom`):
given a positive crossing measure carrying a uniform multiple `δ ρ` of the Cardy density
`ρ = 2π V` on `[T, ∞)` (`T ≥ a'/8`) and polynomial moment orders `M_k ≥ K H_k / log P_k`
satisfying `(δ / 8) inf_{s ≥ B_{k-1}} ρ(s) ≥ W(M_k)`, produces a locally finite
integer-degeneracy crossing spectrum `ν_ℤ` (`IsIntegerCounting ν_ℤ`) at the same gap `T`.

The supporting infrastructure lives in:
* `Integrality.AtomBounds` (`SufficientMomentFloor`, `sufficientMomentFloor_cheb_explicit`,
  `commonSource_cardyDensity_lower`, `commonSource_counting_bound`),
* `Integrality.RepairHankel` (`sonineRepairConst`, `hankel_repair`),
* `Integrality.AtomCell` (`atomShellSetup`, `atom_cell_step`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Finset Polynomial
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Mixtures

/-- **Theorem INT-1 (`int:atom`)** for any `CommonSource` (covering `(H_w)`, `(H_{w,mix})`,
and dominated atomic sources) and any abstract sufficient density floor `W`. -/
theorem int_atom_common (C : CommonSource) {W : ℕ → ℝ} (hW : SufficientMomentFloor W) :
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
  let wR : ℝ := (C.src.w : ℝ)
  let c0 : ℝ := max (1 : ℝ) (wR / 2)
  let C_w_fac : ℝ := (8 : ℝ) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2)
  let C_count_fac : ℝ := 3 * max C.src.tv 1 * c0 ^ (wR / 2)
  let C_const : ℝ := 2 * π * (9 / 4 * C_count_fac) * C_w_fac * (1 + sonineRepairConst) / c_vac
  let C_exp : ℝ := 9 * π + sonineRepairConst + 1
  let K : ℝ := 2 * (C_exp + 2)
  let a₁ : ℝ := max (max C.a₀ 24) (max (max a_star (8 * max 1 wR)) (Real.log (max C_const 1) + 1))
  have hK_pos : 0 < K := by dsimp [K, C_exp]; have := sonineRepairConst_nonneg; positivity
  refine ⟨K, a₁, hK_pos, le_max_left _ _, fun {a T δ} ha hT hδ0 hδ1 meas hsupp hres M hM1 hM_ord hM_fl => ?_⟩
  have ha0 : C.a₀ ≤ a := (le_max_left _ _).trans ((le_max_left _ _).trans ha)
  have ha24 : 24 ≤ a := (le_max_right _ _).trans ((le_max_left _ _).trans ha)
  have ha_star : a_star ≤ a := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ha))
  have ha8w : 8 * max 1 wR ≤ a := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ha))
  have ha_const : Real.log (max C_const 1) + 1 ≤ a := (le_max_right _ _).trans ((le_max_right _ _).trans ha)
  have ha_pos : 0 < a := by linarith
  have hT_max : max 1 wR ≤ T := by
    have : 8 * max 1 wR ≤ 8 * T := by linarith
    linarith
  have ha_ge_c0 : max C.a₀ (max 1 wR) ≤ a :=
    max_le ha0 (max_le (by linarith) (by have := le_max_right 1 wR; linarith))
  have hcount := commonSource_counting_bound C ha_ge_c0 hT_max meas hsupp
  let X := Set.Ici T
  have hEmb : MeasurableEmbedding (Subtype.val : X → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  have hT_pos : 0 < T := by linarith
  let S := atomShellSetup C ha0 hT_pos hδ0 hδ1 meas hsupp hres
  have hsig : SigmaFinite S.ν0 := atomShellSetup_sigmaFinite C ha0 hT_pos hδ0 hδ1 meas hsupp hres
  have hcells : ∀ (j : ℕ) (Sg lam : Measure X), S.Inv j Sg lam →
      ∃ (ι : Type) (_ : Fintype ι) (U : ι → Set X) (μ σ Rp Rm : ι → Measure X),
        S.CellStep j lam U μ σ Rp Rm := fun j Sg lam hInv =>
    atom_cell_step C hW hc_vac_pos ha0 ha24 hT hδ0 hδ1
      (fun {t'} ht' => hrho_lb ha_star ht') meas hsupp hres hcount.2 ha_const M hM1 hM_ord hM_fl
      j Sg lam hInv
  obtain ⟨σ, hσ_atom, _, _, hσ_e_int, hσ_K⟩ := @ShellSetup.shell_inv _ _ _ _ S hsig hcells
  let νℤ : Measure ℝ := Measure.map Subtype.val (Measure.sum σ)
  have hνℤ_supp : νℤ (Ici T)ᶜ = 0 := by
    rw [Measure.map_apply hEmb.measurable measurableSet_Ici.compl]
    have hemp : (Subtype.val : X → ℝ) ⁻¹' (Ici T)ᶜ = ∅ :=
      Set.ext fun x => ⟨fun hx => hx x.2, False.elim⟩
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
          simp only [Set.mem_compl_iff, Set.mem_Ici, not_le]; linarith [Set.mem_Iio.mp ht]
        exact measure_mono_null hsub hνℤ_supp
      finite_laplace := hνℤ_laplace
      crossing := hνℤ_cross }
  refine ⟨measZ, hνℤ_supp, ?_⟩
  classical
  have hσ_unpack : ∀ j : ℕ, ∃ (ι : Type) (_ : Fintype ι) (x : ι → X) (d : ι → ℕ),
      (∀ i, 1 ≤ d i ∧ x i ∈ closure (S.Ω (j + 2)) \ S.Ω j) ∧
      σ j = ∑ i, (d i : ℝ≥0∞) • Measure.dirac (x i) := hσ_atom
  choose ι_s hfin_s x_s d_s hxd_s hσ_eq_s using hσ_unpack
  let := hfin_s
  let S_set : Set ℝ := ⋃ j : ℕ, Set.range (fun i : ι_s j => (x_s j i : ℝ))
  have hx_bounds : ∀ (j : ℕ) (i : ι_s j), T + (j : ℝ) ≤ (x_s j i : ℝ) := fun j i => by
    have hnot := (hxd_s j i).2.2
    simpa [S, atomShellSetup, not_lt] using hnot
  let d_tot : ℝ → ℕ := fun y =>
    ∑ j ∈ Finset.range (Nat.floor (max 0 (y - T)) + 1),
      ∑ i : ι_s j, if (x_s j i : ℝ) = y then d_s j i else 0
  have hd_pos : ∀ y ∈ S_set, 1 ≤ d_tot y := by
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨j₀, i₀, rfl⟩
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
    rcases K.eq_empty_or_nonempty with rfl | _
    · simp
    · obtain ⟨R, hR⟩ := hK.bddAbove
      let N := Nat.floor (max 0 (R - T)) + 1
      have hsub : S_set ∩ K ⊆ ⋃ j ∈ Finset.range N, Set.range (fun i : ι_s j => (x_s j i : ℝ)) := by
        rintro y ⟨hyS, hyK⟩
        rcases Set.mem_iUnion.1 hyS with ⟨j, i, rfl⟩
        have hleR : (x_s j i : ℝ) ≤ R := hR hyK
        have hj_le : j ≤ Nat.floor (max 0 (R - T)) :=
          Nat.le_floor (le_max_of_le_right (by linarith [hx_bounds j i]))
        exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le)) ⟨i, rfl⟩
      exact (Finset.finite_toSet (Finset.range N)).biUnion
        (fun _ _ => Set.finite_range _) |>.subset hsub
  refine ⟨S_set, d_tot, hS_loc_fin, hd_pos, ?_⟩
  ext A hA
  change νℤ A = (Measure.sum fun y : S_set => (d_tot y : ℝ≥0∞) • Measure.dirac (y : ℝ)) A
  have hν_A : νℤ A = ∑' p : (j : ℕ) × ι_s j,
      if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0 := by
    rw [Measure.map_apply hEmb.measurable hA, Measure.sum_apply _ (hEmb.measurable hA)]
    rw [tsum_sigma']
    refine tsum_congr fun j => ?_
    rw [hσ_eq_s j]
    simp only [sum_apply, smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (hEmb.measurable hA), Set.mem_preimage, Set.indicator_apply]
    calc (∑ x, (d_s j x : ℝ≥0∞) * (if (x_s j x : ℝ) ∈ A then 1 else 0))
        = ∑ i, (if (x_s j i : ℝ) ∈ A then (d_s j i : ℝ≥0∞) else 0) :=
          Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
      _ = ∑' i, (if (x_s j i : ℝ) ∈ A then (d_s j i : ℝ≥0∞) else 0) := (tsum_fintype _).symm
  have hsum_A : (Measure.sum fun y : S_set => (d_tot y : ℝ≥0∞) • Measure.dirac (y : ℝ)) A =
      ∑' y : S_set, if (y : ℝ) ∈ A then (d_tot y : ℝ≥0∞) else 0 := by
    rw [Measure.sum_apply _ hA]
    refine tsum_congr fun y => ?_
    simp [smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA, Set.indicator_apply]
  rw [hν_A, hsum_A]
  let f_map : ((j : ℕ) × ι_s j) → S_set := fun p =>
    ⟨(x_s p.1 p.2 : ℝ), Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩⟩
  rw [← tsum_fiberwise (fun p : (j : ℕ) × ι_s j =>
      if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0) f_map]
  refine tsum_congr fun y => ?_
  let N := Nat.floor (max 0 ((y : ℝ) - T)) + 1
  let g : ((j : ℕ) × ι_s j) → ℝ≥0∞ := fun p =>
    if f_map p = y then (if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0) else 0
  have hfib_g : (∑' p : f_map ⁻¹' {y},
        (if (x_s p.1.1 p.1.2 : ℝ) ∈ A then (d_s p.1.1 p.1.2 : ℝ≥0∞) else 0)) =
      ∑' p : (j : ℕ) × ι_s j, g p := by
    have := (tsum_subtype (f_map ⁻¹' {y})
      (fun p => if (x_s p.1 p.2 : ℝ) ∈ A then (d_s p.1 p.2 : ℝ≥0∞) else 0))
    simpa [g, Set.indicator_apply] using this
  rw [hfib_g, tsum_sigma']
  have hvan : ∀ j : ℕ, j ∉ Finset.range N → (∑' i : ι_s j, g ⟨j, i⟩) = 0 := by
    intro j hj
    refine tsum_eq_zero_iff.2 fun i => ?_
    dsimp only [g]
    by_cases hfeq : f_map ⟨j, i⟩ = y
    · have heq_y : (x_s j i : ℝ) = (y : ℝ) := congrArg Subtype.val hfeq
      have hj_le : j ≤ Nat.floor (max 0 ((y : ℝ) - T)) :=
        Nat.le_floor (le_max_of_le_right (by linarith [hx_bounds j i]))
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le)) hj
    · simp [hfeq]
  rw [tsum_eq_sum hvan]
  split_ifs with hyA
  · simp only [d_tot, N, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [g]
    have hiff : f_map ⟨j, i⟩ = y ↔ (x_s j i : ℝ) = (y : ℝ) := Subtype.ext_iff
    simp only [hiff]
    by_cases heq : (x_s j i : ℝ) = (y : ℝ)
    · simp [heq, hyA]
    · simp [heq]
  · refine Finset.sum_eq_zero fun j _ => ?_
    refine tsum_eq_zero_iff.2 fun i => ?_
    dsimp only [g]
    by_cases hfeq : f_map ⟨j, i⟩ = y
    · have heq_y : (x_s j i : ℝ) = (y : ℝ) := congrArg Subtype.val hfeq
      simp [hfeq, heq_y, hyA]
    · simp [hfeq]

/-- **Theorem INT-1 (`int:atom`)**, concrete Chebyshev instantiation with
`W(M) = 8 (M + 1)^{5/2}` (`cheb_explicit`). -/
theorem int_atom_cheb_explicit (C : CommonSource) :
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
  int_atom_common C sufficientMomentFloor_cheb_explicit

/-- **Theorem INT-1 (`int:atom`)**, fixed-weight `(H_w)` specialisation (`AdmissibleCrossingMeasure prob a`). -/
theorem int_atom_fixedWeight (prob : FixedWeightProblem) :
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
          floor := fun _ _ => by dsimp [F]; rw [one_mul]; exact le_refl _ } }
  obtain ⟨K, a₁, hK, ha₁, hmain⟩ := int_atom_cheb_explicit C
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
