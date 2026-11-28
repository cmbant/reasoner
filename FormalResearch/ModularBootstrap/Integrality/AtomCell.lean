module

public import FormalResearch.ModularBootstrap.Integrality.AtomBounds
public import FormalResearch.ModularBootstrap.Integrality.RepairHankel
public import FormalResearch.ModularBootstrap.Integrality.ShellInvCells

/-!
# Shell setup and single-cell step for `int:atom` (`INT-1`)

Constructs the `ShellSetup (Set.Ici T)` instance (`atomShellSetup`) and proves the single-cell
hypothesis `atom_cell_step : S.CellStep j lam U μ σ Rp Rm` for every stage `j` satisfying
`S.Inv j Sg lam`, together with `SigmaFinite S.ν0` (`atomShellSetup_sigmaFinite`), consumed by
`Integrality/Atom.lean`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Mixtures

section CellHelpers

noncomputable def atomRhoReal (C : CommonSource) (a T : ℝ) : Measure ℝ :=
  (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T)

lemma atomRhoReal_eq (C : CommonSource) (a T : ℝ) :
    atomRhoReal C a T =
      (volume.restrict (Ici T)).withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t) := by
  ext A hA
  dsimp [atomRhoReal]
  rw [Measure.restrict_apply hA, withDensity_apply _ (hA.inter measurableSet_Ici),
    withDensity_apply _ hA, Measure.restrict_restrict hA, Set.inter_comm]

private lemma atomRhoReal_integrable (C : CommonSource) {a T : ℝ} (ha0 : C.a₀ ≤ a) (hT : 0 < T)
    {β : ℝ} (hβ : 0 < β) :
    Integrable (fun t => Real.exp (-2 * π * β * t)) (atomRhoReal C a T) := by
  have hV_nonneg_Ici : ∀ t ∈ Ici T, 0 ≤ C.src.cardyDensity a t := fun t ht => by
    unfold ShiftSource.cardyDensity
    exact mul_nonneg (by positivity) ((C.at_ ha0).nonneg_V (by linarith [Set.mem_Ici.mp ht]))
  have hm_dens : Measurable (fun t : ℝ => ENNReal.ofReal (C.src.cardyDensity a t)) :=
    ((C.src.continuous_cardyV a).const_mul (2 * π)).measurable.ennreal_ofReal
  have hc : IntegrableOn (fun t => C.src.cardyV a t * Real.exp (-2 * π * β * t)) (Ioi 0) :=
    (C.src.cardyV_laplace a hβ).1
  have hc_mul : IntegrableOn (fun t => 2 * π * (C.src.cardyV a t * Real.exp (-2 * π * β * t))) (Ioi 0) :=
    hc.const_mul (2 * π)
  have hdens_sub : IntegrableOn (fun t => 2 * π * (C.src.cardyV a t * Real.exp (-2 * π * β * t))) (Ici T) :=
    hc_mul.mono_set (Ici_subset_Ioi.2 hT)
  have hdens_int : Integrable (fun t => Real.exp (-2 * π * β * t) * C.src.cardyDensity a t)
      (volume.restrict (Ici T)) := by
    refine hdens_sub.congr_fun (fun t _ => ?_) measurableSet_Ici
    unfold ShiftSource.cardyDensity; ring
  rw [atomRhoReal_eq, integrable_withDensity_iff_integrable_smul' hm_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine hdens_int.congr ((ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun t ht => ?_))
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hV_nonneg_Ici t ht)]
  ring

/-- Canonical `ShellSetup (Set.Ici T)` for `int_atom_common`. -/
noncomputable def atomShellSetup (C : CommonSource) {a T δ : ℝ}
    (ha0 : C.a₀ ≤ a) (hT : 0 < T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (meas : SourceCrossingMeasure C.src a) (hsupp : meas.ν (Ici T)ᶜ = 0)
    (hres : ENNReal.ofReal δ •
      (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T) ≤
        meas.ν) :
    ShellSetup (Set.Ici T) :=
  let X := Set.Ici T
  let RPos := {β : ℝ // 0 < β}
  let hEmb : MeasurableEmbedding (Subtype.val : X → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  let ν0_sub : Measure X := Measure.comap Subtype.val meas.ν
  let ρ_sub : Measure X := Measure.comap Subtype.val (atomRhoReal C a T)
  have hν0_map : Measure.map Subtype.val ν0_sub = meas.ν := by
    dsimp [ν0_sub]
    rw [hEmb.map_comap meas.ν, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem
      (measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono fun _ ht => not_not.mp ht)
  have hρ_map : Measure.map Subtype.val ρ_sub = atomRhoReal C a T := by
    dsimp [ρ_sub]
    rw [hEmb.map_comap (atomRhoReal C a T), Subtype.range_coe]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    dsimp [atomRhoReal]
    rw [ae_restrict_iff' measurableSet_Ici]
    exact Eventually.of_forall fun _ ht => ht
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
    Ω_open := fun _ => isOpen_lt continuous_subtype_val continuous_const
    Ω_mono := fun k₁ k₂ hk x hx => by
      have hx' : (x : ℝ) < T + (k₁ : ℝ) := hx
      have hcast : (k₁ : ℝ) ≤ k₂ := by exact_mod_cast hk
      change (x : ℝ) < T + (k₂ : ℝ)
      linarith
    Ω_zero := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false, Nat.cast_zero, add_zero]
      exact not_lt_of_ge x.2
    Ω_cover := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨k, hk⟩ := exists_nat_gt ((x : ℝ) - T)
      refine ⟨k, ?_⟩
      change (x : ℝ) < T + (k : ℝ)
      linarith
    K_cont := fun β => by unfold thermalDiff; fun_prop
    e_cont := fun γ => by fun_prop
    e_pos := fun _ _ => Real.exp_pos _
    K_dom := fun β => by
      classical
      let βinv : RPos := ⟨β.1⁻¹, inv_pos.mpr β.2⟩
      let s : Finset RPos := {β, βinv}
      let coef : RPos → ℝ := fun γ => if γ = β then 1 else if γ = βinv then β.1 ^ (-(C.src.w : ℝ)) else 0
      refine ⟨s, coef, fun γ => ?_, fun x => ?_⟩
      · have hβp : 0 < β.1 := β.2
        dsimp [coef]; split_ifs <;> positivity
      · have htherm : |thermalDiff C.src.w β.1 x.1| ≤
            Real.exp (-2 * π * β.1 * x.1) + β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * x.1) := by
          unfold thermalDiff
          have h2eq : Real.exp (-2 * π * x.1 / β.1) = Real.exp (-2 * π * β.1⁻¹ * x.1) := by
            congr 1; ring
          rw [h2eq]
          calc |Real.exp (-2 * π * β.1 * x.1) - β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * x.1)|
              ≤ |Real.exp (-2 * π * β.1 * x.1)| + |β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * x.1)| :=
                abs_sub _ _
            _ = Real.exp (-2 * π * β.1 * x.1) + β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * x.1) := by
                rw [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg (Real.rpow_nonneg β.2.le _),
                  abs_of_pos (Real.exp_pos _)]
        by_cases heq : β = βinv
        · have hβ1 : β.1 = 1 := by
            have hinv : β.1 = β.1⁻¹ := congrArg Subtype.val heq
            have hsq : β.1 * β.1 = 1 := by
              calc β.1 * β.1 = β.1 * β.1⁻¹ := by nth_rw 2 [hinv]
                _ = 1 := mul_inv_cancel₀ β.2.ne'
            have hpos : 0 < β.1 := β.2
            nlinarith
          have hs_eq : s = {β} := by dsimp [s]; rw [← heq, Finset.pair_eq_singleton]
          rw [hs_eq, Finset.sum_singleton]
          dsimp [coef]
          simp only [↓reduceIte, one_mul]
          unfold thermalDiff
          rw [hβ1, Real.one_rpow, one_mul, div_one, mul_one, sub_self, abs_zero]
          exact (Real.exp_pos _).le
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
      have heq : (fun x : X => Real.exp (-2 * π * γ.1 * x.1)) =
          (fun t : ℝ => Real.exp (-2 * π * γ.1 * t)) ∘ Subtype.val := rfl
      rw [heq, ← integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable, hρ_map]
      exact atomRhoReal_integrable C ha0 hT γ.2
    ν0_int := fun γ => by
      have hm : Measurable (Subtype.val : X → ℝ) := measurable_subtype_coe
      have hc : Continuous (fun t : ℝ => Real.exp (-2 * π * γ.1 * t)) := by fun_prop
      have heq : (fun x : X => Real.exp (-2 * π * γ.1 * x.1)) =
          (fun t : ℝ => Real.exp (-2 * π * γ.1 * t)) ∘ Subtype.val := rfl
      rw [heq, ← integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable, hν0_map]
      have hae_0 : ∀ᵐ t ∂meas.ν, t ∈ Ici (0 : ℝ) := by
        have := measure_eq_zero_iff_ae_notMem.1 hsupp
        filter_upwards [this] with t ht
        exact show 0 ≤ t by linarith [show T ≤ t from not_not.mp ht]
      simpa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae_0] using meas.finite_laplace γ.2
    ν0_K := fun β => by
      have hm : Measurable (Subtype.val : X → ℝ) := measurable_subtype_coe
      have hc : Continuous (fun t : ℝ => thermalDiff C.src.w β.1 t) := by
        unfold thermalDiff; fun_prop
      have hmap_int : ∫ x : X, thermalDiff C.src.w β.1 x.1 ∂ν0_sub =
          ∫ t : ℝ, thermalDiff C.src.w β.1 t ∂meas.ν := by
        rw [← hν0_map, integral_map hm.aemeasurable hc.aestronglyMeasurable]
      have hae_0 : ∀ᵐ t ∂meas.ν, t ∈ Ici (0 : ℝ) := by
        have := measure_eq_zero_iff_ae_notMem.1 hsupp
        filter_upwards [this] with t ht
        exact show 0 ≤ t by linarith [show T ≤ t from not_not.mp ht]
      rw [hmap_int, ← Measure.restrict_eq_self_of_ae_mem hae_0]
      exact meas.crossing β.2
    reserve_le := by
      refine Measure.le_iff.2 fun A hA => ?_
      have hA_val : MeasurableSet (Subtype.val '' A) := hEmb.measurableSet_image.2 hA
      have h1 : ρ_sub A = atomRhoReal C a T (Subtype.val '' A) := by
        rw [← hρ_map, Measure.map_apply hEmb.measurable hA_val]
        congr 1; exact (Subtype.val_injective.preimage_image A).symm
      have h2 : ν0_sub A = meas.ν (Subtype.val '' A) := by
        rw [← hν0_map, Measure.map_apply hEmb.measurable hA_val]
        congr 1; exact (Subtype.val_injective.preimage_image A).symm
      rw [smul_apply, smul_eq_mul, h1, h2]
      have hle := Measure.le_iff.1 hres (Subtype.val '' A) hA_val
      simpa [atomRhoReal, smul_apply, smul_eq_mul] using hle
    C_nonneg := fun _ => (Real.exp_pos _).le }

lemma atomShellSetup_nu0_fin (C : CommonSource) {a T δ : ℝ}
    (ha0 : C.a₀ ≤ a) (hT : 0 < T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (meas : SourceCrossingMeasure C.src a) (hsupp : meas.ν (Ici T)ᶜ = 0)
    (hres : ENNReal.ofReal δ •
      (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T) ≤
        meas.ν) (R : ℝ) :
    (atomShellSetup C ha0 hT hδ0 hδ1 meas hsupp hres).ν0 {x : Set.Ici T | (x : ℝ) ≤ R} < ∞ := by
  let S := atomShellSetup C ha0 hT hδ0 hδ1 meas hsupp hres
  let hEmb : MeasurableEmbedding (Subtype.val : Set.Ici T → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  have hν0_map : Measure.map Subtype.val S.ν0 = meas.ν := by
    dsimp [S, atomShellSetup]
    rw [hEmb.map_comap meas.ν, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem
      (measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono fun _ ht => not_not.mp ht)
  by_cases hTR : R < T
  · have hemp : {x : Set.Ici T | (x : ℝ) ≤ R} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hxT : T ≤ (x : ℝ) := x.2
      linarith
    change S.ν0 {x : Set.Ici T | (x : ℝ) ≤ R} < ∞
    rw [hemp, measure_empty]; exact ENNReal.coe_lt_top
  · have hle_TR : T ≤ R := not_lt.mp hTR
    have hm : MeasurableSet (Icc T R) := measurableSet_Icc
    have hmeas_eq : S.ν0 {x : Set.Ici T | (x : ℝ) ≤ R} = meas.ν (Icc T R) := by
      rw [← hν0_map, Measure.map_apply hEmb.measurable hm]
      congr 1; ext x; exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    change S.ν0 {x : Set.Ici T | (x : ℝ) ≤ R} < ∞
    rw [hmeas_eq]
    have hexp_pos : 0 < Real.exp (-2 * π * R) := Real.exp_pos _
    have hle_exp : ENNReal.ofReal (Real.exp (-2 * π * R)) * meas.ν (Icc T R) ≤
        ∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
      calc ENNReal.ofReal (Real.exp (-2 * π * R)) * meas.ν (Icc T R)
          = ∫⁻ _ in Icc T R, ENNReal.ofReal (Real.exp (-2 * π * R)) ∂meas.ν := by
            rw [setLIntegral_const]
        _ ≤ ∫⁻ t in Icc T R, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν := by
            refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.2]))
        _ ≤ ∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν :=
            lintegral_mono_set (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 (by linarith)))
    have hlt := lt_of_le_of_lt hle_exp (meas.finite_laplace one_pos).lintegral_lt_top
    exact (ENNReal.mul_lt_top_iff.mp hlt).elim (fun h => h.2)
      (fun h => h.elim (fun h0 => absurd h0 (ENNReal.ofReal_pos.mpr hexp_pos).ne')
        (fun h0 => by simp [h0]))

lemma atomShellSetup_sigmaFinite (C : CommonSource) {a T δ : ℝ}
    (ha0 : C.a₀ ≤ a) (hT : 0 < T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (meas : SourceCrossingMeasure C.src a) (hsupp : meas.ν (Ici T)ᶜ = 0)
    (hres : ENNReal.ofReal δ •
      (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T) ≤
        meas.ν) :
    SigmaFinite (atomShellSetup C ha0 hT hδ0 hδ1 meas hsupp hres).ν0 := by
  refine ⟨⟨{
    set := fun k => {x : Set.Ici T | (x : ℝ) ≤ T + (k : ℝ)}
    set_mem := fun _ => trivial
    finite := fun k => atomShellSetup_nu0_fin C ha0 hT hδ0 hδ1 meas hsupp hres (T + (k : ℝ))
    spanning := by
      ext x; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      obtain ⟨k, hk⟩ := exists_nat_gt ((x : ℝ) - T)
      exact ⟨k, by linarith⟩
  }⟩⟩

private lemma exp_neg_one_le_half : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h2e

private lemma exp_add_two_sub (c h : ℝ) :
    Real.exp (c * h) * Real.exp (-(c + 2) * h) = Real.exp (-h) * Real.exp (-h) := by
  rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

private lemma atom_tail_finish {r_val c_vac rho V δ C_count_fac C_w_fac C_const C_son C_exp H_k P_k
      sumMeas powB0 powA tailSum expB rhoFac : ℝ} {m j : ℕ}
    (hc_vac_pos : 0 < c_vac) (hδ0 : 0 < δ) (hC_son_nn : 0 ≤ C_son)
    (hV_nn : 0 ≤ V) (hrho_pos : 0 < rho)
    (hCc_nn : 0 ≤ C_count_fac) (hCw_nn : 0 ≤ C_w_fac) (htail_nn : 0 ≤ tailSum)
    (hpowB0_nn : 0 ≤ powB0) (hexpB_nn : 0 ≤ expB)
    (hrho_cd : c_vac * rho ≤ V)
    (hCconst_eq : C_const = 2 * π * (9 / 4 * C_count_fac) * C_w_fac * (1 + C_son) / c_vac)
    (hC_const_exp : C_const * Real.exp (-H_k) ≤ 1)
    (hexp_tail : Real.exp (-H_k) ≤ (1 / 2 : ℝ) ^ (j + 4) * δ)
    (hcomb_exp : Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) ≤ Real.exp (-H_k) * Real.exp (-H_k))
    (hbrace : expB * (rhoFac * tailSum) ≤ (1 + C_son) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2))
    (hrt_tail : |r_val| ≤ 2 * π * sumMeas * powB0 * tailSum)
    (hsum_meas2 : sumMeas ≤ (9 / 4 : ℝ) * C_count_fac * expB)
    (ht_B0_le : powB0 ≤ C_w_fac * powA)
    (hrho_eq : powA = rho * rhoFac) :
    |r_val| ≤ (1 / 2 : ℝ) ^ (j + 4) * δ * V := by
  have hpi_nn : 0 ≤ 2 * π := by positivity
  have hCconst_nn : 0 ≤ C_const := by rw [hCconst_eq]; positivity
  calc |r_val| ≤ 2 * π * sumMeas * powB0 * tailSum := hrt_tail
    _ ≤ 2 * π * ((9 / 4 : ℝ) * C_count_fac * expB) * (C_w_fac * powA) * tailSum := by
        gcongr
    _ = (2 * π * (9 / 4 * C_count_fac) * C_w_fac * rho) * (expB * (rhoFac * tailSum)) := by
        rw [hrho_eq]; ring
    _ ≤ (2 * π * (9 / 4 * C_count_fac) * C_w_fac * rho) *
          ((1 + C_son) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2)) := by
        gcongr
    _ = (C_const * (Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2))) * (c_vac * rho) := by
        rw [hCconst_eq]; field_simp [hc_vac_pos.ne']
    _ ≤ (C_const * (Real.exp (-H_k) * Real.exp (-H_k))) * V := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hcomb_exp hCconst_nn)
          hrho_cd (mul_nonneg hc_vac_pos.le hrho_pos.le) (by positivity)
    _ = (C_const * Real.exp (-H_k)) * Real.exp (-H_k) * V := by rw [← mul_assoc C_const]
    _ ≤ (1 : ℝ) * ((1 / 2 : ℝ) ^ (j + 4) * δ) * V := by
        refine mul_le_mul (mul_le_mul hC_const_exp hexp_tail (Real.exp_pos _).le zero_le_one)
          le_rfl hV_nn (by positivity)
    _ = (1 / 2 : ℝ) ^ (j + 4) * δ * V := by rw [one_mul]

private lemma atom_tail_brace {a t B B₀ wR C_son C_exp H_k P_k δ : ℝ} {m : ℕ}
    (ha_pos : 0 < a) (ht_pos : 0 < t) (hB0_pos : 0 < B₀) (hPk_pos : 0 < P_k)
    (hP_eq : P_k = a * B₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hB_nn : 0 ≤ B) (hwR_nn : 0 ≤ wR) (hC_son_nn : 0 ≤ C_son)
    (hCexp_eq : C_exp = 9 * π + C_son + 1)
    (hHk_eq : H_k = a + B + Real.log (1 / δ) + wR)
    (h2sqrt_le : 2 * π * Real.sqrt (a * B) ≤ π * a + π * B) :
    Real.exp (8 * π * a + (2 * π + 1) * B) *
      ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t)) *
        (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
          C_son * Real.exp (C_son * (B + wR)) *
            (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)) ≤
    (1 + C_son) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) := by
  let x_t : ℝ := Real.sqrt (a * t)
  let x_B : ℝ := Real.sqrt (a * B)
  have hx_t_nn : 0 ≤ x_t := Real.sqrt_nonneg _
  have hx_B_nn : 0 ≤ x_B := Real.sqrt_nonneg _
  have hterm1_eq : 2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀) =
      2 * π * Real.exp 1 * x_t / ((m : ℝ) * Real.sqrt P_k) := by
    dsimp [x_t]
    rw [hP_eq, Real.sqrt_mul ha_pos.le t, Real.sqrt_mul ha_pos.le B₀]
    have hsqa_ne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
    field_simp [hsqa_ne]
  have hterm2_eq : 2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀) =
      2 * π * Real.exp 1 * x_B / ((m : ℝ) * Real.sqrt P_k) := by
    dsimp [x_B]
    rw [hP_eq, Real.sqrt_mul ha_pos.le B, Real.sqrt_mul ha_pos.le B₀]
    have hsqa_ne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
    field_simp [hsqa_ne]
  have hat_nn : 0 ≤ a * t := mul_nonneg ha_pos.le ht_pos.le
  have hquarter_exp : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-2 * π * x_t) ≤ 1 := by
    have hsq : Real.sqrt x_t = (a * t) ^ (1 / 4 : ℝ) := by
      dsimp [x_t]
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hat_nn]
      norm_num
    rw [← hsq]
    exact rpow_half_mul_exp_neg_le_one hx_t_nn
  have hterm1_bound : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
      min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) ≤
      P_k ^ (-(m : ℝ) / 2) := by
    have hpref_nn : 0 ≤ (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) :=
      mul_nonneg (Real.rpow_nonneg hat_nn _) (Real.exp_pos _).le
    have hexp4 : Real.exp (-4 * π * x_t) = Real.exp (-2 * π * x_t) * Real.exp (-2 * π * x_t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
          min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m)
        ≤ (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
            (2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hpref_nn
      _ = ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-2 * π * x_t)) *
            (Real.exp (-2 * π * x_t) * (2 * π * Real.exp 1 * x_t / ((m : ℝ) * Real.sqrt P_k)) ^ m) := by
          rw [hterm1_eq, hexp4]; ring
      _ ≤ 1 * P_k ^ (-(m : ℝ) / 2) :=
          mul_le_mul hquarter_exp (rpow_weighted_taylor_le hPk_pos m hx_t_nn) (by positivity) zero_le_one
      _ = P_k ^ (-(m : ℝ) / 2) := one_mul _
  have hterm2_bound : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
      (C_son * Real.exp (C_son * (B + wR)) *
        (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) ≤
      C_son * Real.exp (π * a + (π + C_son) * B + C_son * wR) *
        P_k ^ (-(m : ℝ) / 2) := by
    have hqt4 : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) ≤ 1 := by
      have h2pi_x : 0 ≤ 2 * π * x_t := mul_nonneg (by positivity) hx_t_nn
      have hexp_le : Real.exp (-2 * π * x_t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t)
          = ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-2 * π * x_t)) * Real.exp (-2 * π * x_t) := by
            have h2exp : Real.exp (-4 * π * x_t) = Real.exp (-2 * π * x_t) * Real.exp (-2 * π * x_t) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [h2exp, mul_assoc]; ring
        _ ≤ 1 * 1 := mul_le_mul hquarter_exp hexp_le (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    have hB_wt := rpow_weighted_taylor_le hPk_pos m hx_B_nn
    have hzB_le : (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m ≤
        Real.exp (2 * π * x_B) * P_k ^ (-(m : ℝ) / 2) := by
      rw [hterm2_eq]
      have h1 := mul_le_mul_of_nonneg_left hB_wt (Real.exp_pos (2 * π * x_B)).le
      have hcan : Real.exp (2 * π * x_B) * Real.exp (-2 * π * x_B) = 1 := by rw [← Real.exp_add]; simp
      rwa [← mul_assoc, hcan, one_mul] at h1
    calc (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
          (C_son * Real.exp (C_son * (B + wR)) *
            (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)
        ≤ 1 * (C_son * Real.exp (C_son * (B + wR)) *
            (Real.exp (2 * π * x_B) * P_k ^ (-(m : ℝ) / 2))) := by
          gcongr
      _ = C_son * (Real.exp (C_son * (B + wR)) * Real.exp (2 * π * x_B)) *
            P_k ^ (-(m : ℝ) / 2) := by ring
      _ ≤ C_son * Real.exp (π * a + (π + C_son) * B + C_son * wR) *
            P_k ^ (-(m : ℝ) / 2) := by
          gcongr
          rw [← Real.exp_add]
          have hxB_sum : 2 * π * x_B ≤ π * a + π * B := h2sqrt_le
          exact Real.exp_le_exp.mpr (by linarith)
  have hexp_pos1 : Real.exp (8 * π * a + (2 * π + 1) * B) ≤ Real.exp (C_exp * H_k) := by
    apply Real.exp_le_exp.mpr
    have hlog_nn : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
    have hCexp_nn : 0 ≤ C_exp := by rw [hCexp_eq]; positivity
    have h8 : 8 * π * a ≤ C_exp * a :=
      mul_le_mul_of_nonneg_right (by rw [hCexp_eq]; linarith [Real.pi_pos]) ha_pos.le
    have h2 : (2 * π + 1) * B ≤ C_exp * B :=
      mul_le_mul_of_nonneg_right (by rw [hCexp_eq]; linarith [Real.pi_pos]) hB_nn
    have hl : 0 ≤ C_exp * Real.log (1 / δ) := mul_nonneg hCexp_nn hlog_nn
    have hw : 0 ≤ C_exp * wR := mul_nonneg hCexp_nn hwR_nn
    have hsum : C_exp * H_k = C_exp * a + C_exp * B + C_exp * Real.log (1 / δ) + C_exp * wR := by
      rw [hHk_eq]; ring
    linarith
  have hexp_pos2 : Real.exp (8 * π * a + (2 * π + 1) * B) *
      Real.exp (π * a + (π + C_son) * B + C_son * wR) ≤ Real.exp (C_exp * H_k) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog_nn : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
    have hCexp_nn : 0 ≤ C_exp := by rw [hCexp_eq]; positivity
    have h9 : 9 * π * a ≤ C_exp * a :=
      mul_le_mul_of_nonneg_right (by rw [hCexp_eq]; linarith) ha_pos.le
    have h3 : (3 * π + 1 + C_son) * B ≤ C_exp * B :=
      mul_le_mul_of_nonneg_right (by rw [hCexp_eq]; linarith [Real.pi_pos]) hB_nn
    have hw : C_son * wR ≤ C_exp * wR :=
      mul_le_mul_of_nonneg_right (by rw [hCexp_eq]; linarith [Real.pi_pos]) hwR_nn
    have hl : 0 ≤ C_exp * Real.log (1 / δ) := mul_nonneg hCexp_nn hlog_nn
    have hcomb : (8 * π * a + (2 * π + 1) * B) + (π * a + (π + C_son) * B + C_son * wR) =
        9 * π * a + (3 * π + 1 + C_son) * B + C_son * wR := by ring
    have hsum : C_exp * H_k = C_exp * a + C_exp * B + C_exp * Real.log (1 / δ) + C_exp * wR := by
      rw [hHk_eq]; ring
    linarith
  have hdist : (a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
        (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
          C_son * Real.exp (C_son * (B + wR)) *
            (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) ≤
      (1 + C_son * Real.exp (π * a + (π + C_son) * B + C_son * wR)) *
        P_k ^ (-(m : ℝ) / 2) := by
    rw [mul_add, add_mul, one_mul]
    exact add_le_add hterm1_bound hterm2_bound
  have he1_nn : 0 ≤ Real.exp (8 * π * a + (2 * π + 1) * B) := (Real.exp_pos _).le
  have h1 : Real.exp (8 * π * a + (2 * π + 1) * B) *
        (1 + C_son * Real.exp (π * a + (π + C_son) * B + C_son * wR)) ≤
      (1 + C_son) * Real.exp (C_exp * H_k) := by
    rw [mul_add, mul_one]
    calc Real.exp (8 * π * a + (2 * π + 1) * B) +
          Real.exp (8 * π * a + (2 * π + 1) * B) *
            (C_son * Real.exp (π * a + (π + C_son) * B + C_son * wR))
        = Real.exp (8 * π * a + (2 * π + 1) * B) +
          C_son * (Real.exp (8 * π * a + (2 * π + 1) * B) *
            Real.exp (π * a + (π + C_son) * B + C_son * wR)) := by ring
      _ ≤ Real.exp (C_exp * H_k) + C_son * Real.exp (C_exp * H_k) := by gcongr
      _ = (1 + C_son) * Real.exp (C_exp * H_k) := by ring
  calc Real.exp (8 * π * a + (2 * π + 1) * B) * _
      ≤ Real.exp (8 * π * a + (2 * π + 1) * B) *
          ((1 + C_son * Real.exp (π * a + (π + C_son) * B + C_son * wR)) *
            P_k ^ (-(m : ℝ) / 2)) := mul_le_mul_of_nonneg_left hdist he1_nn
    _ = (Real.exp (8 * π * a + (2 * π + 1) * B) *
          (1 + C_son * Real.exp (π * a + (π + C_son) * B + C_son * wR))) *
          P_k ^ (-(m : ℝ) / 2) := by ring
    _ ≤ (1 + C_son) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

private lemma atom_tail_r_bound (C : CommonSource)
    {c_vac : ℝ} (hc_vac_pos : 0 < c_vac)
    {a T δ : ℝ} (ha24 : 24 ≤ a)
    (hrho_lb : ∀ {t : ℝ}, a / 8 ≤ t → c_vac * rhoLowerCore C.src.w a t ≤ C.src.cardyDensity a t)
    (hT : a / 8 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (meas : SourceCrossingMeasure C.src a)
    (hcount_fn : ∀ R : ℝ, 1 ≤ R →
      meas.ν.real (Icc T R) ≤
        3 * C.src.tv * R ^ ((C.src.w : ℝ) / 2) * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * R)))
    {j : ℕ} {Mk : ℕ}
    (ha_const : Real.log (max (2 * π * (9 / 4 * (3 * max C.src.tv 1 *
        (max (1 : ℝ) ((C.src.w : ℝ) / 2)) ^ ((C.src.w : ℝ) / 2))) *
      (8 : ℝ) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) * (1 + sonineRepairConst) / c_vac) 1) + 1 ≤ a)
    (hM_ord : (2 * ((9 * π + sonineRepairConst + 1) + 2)) *
        (a + (T + ((j + 2 : ℕ) : ℝ)) + Real.log (1 / δ) + (C.src.w : ℝ)) /
      Real.log (a * (T + (j : ℝ))) ≤ (Mk : ℝ))
    {σ₀_real μ₀_real : Measure ℝ}
    (hσ_univ_le : σ₀_real.real univ ≤ 9 / 8 * meas.ν.real (Icc T (T + ((j + 2 : ℕ) : ℝ))))
    (hμ_univ_le : μ₀_real.real univ ≤ 9 / 8 * meas.ν.real (Icc T (T + ((j + 2 : ℕ) : ℝ))))
    {r : ℝ → ℝ}
    (hr_bd : ∀ {t : ℝ}, T + ((j + 2 : ℕ) : ℝ) < t →
      let B₀ := T + (j : ℝ)
      let B := T + ((j + 2 : ℕ) : ℝ)
      let h := (B - B₀) / 2
      let m : ℕ := Mk + 1
      |r t| ≤ 2 * π * (σ₀_real.real univ + μ₀_real.real univ) * (t / B₀) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) *
        (min 1 ((2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
          sonineRepairConst * Real.exp (sonineRepairConst * (B + (C.src.w : ℝ))) *
            (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m))
    {t : ℝ} (ht : T + ((j + 2 : ℕ) : ℝ) < t) :
    |r t| ≤ (1 / 2 : ℝ) ^ (j + 4) * δ * C.src.cardyDensity a t := by
  let wR : ℝ := (C.src.w : ℝ)
  let c0 : ℝ := max (1 : ℝ) (wR / 2)
  let C_w_fac : ℝ := (8 : ℝ) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2)
  let C_count_fac : ℝ := 3 * max C.src.tv 1 * c0 ^ (wR / 2)
  let C_const : ℝ := 2 * π * (9 / 4 * C_count_fac) * C_w_fac * (1 + sonineRepairConst) / c_vac
  let C_exp : ℝ := 9 * π + sonineRepairConst + 1
  let K : ℝ := 2 * (C_exp + 2)
  let B₀ : ℝ := T + (j : ℝ)
  let B : ℝ := T + ((j + 2 : ℕ) : ℝ)
  have ha_pos : 0 < a := by linarith
  have hB0_ge_T : T ≤ B₀ := by dsimp [B₀]; linarith
  have hB0_pos : 0 < B₀ := by linarith
  have hB_ge1 : 1 ≤ B := by dsimp [B]; linarith
  have hw1 : 1 ≤ C.src.w := C.src.hw
  have hV_nn : 0 ≤ C.src.cardyDensity a t := by
    have hj_nn : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by positivity
    exact le_trans (mul_nonneg hc_vac_pos.le (rhoLowerCore_pos ha_pos (by linarith)).le)
      (hrho_lb (by linarith))
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
  let m : ℕ := Mk + 1
  have hm_ge : K * H_k / Real.log P_k ≤ (m : ℝ) := hM_ord.trans (by exact_mod_cast Nat.le_succ Mk)
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
  have hh_eq : (B - B₀) / 2 = 1 := by dsimp [B, B₀]; push_cast; ring
  rw [hh_eq, mul_one] at hrt_tail
  have hcount_B := hcount_fn B hB_ge1
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
      have hw_div : (wR / 2) / c0 ≤ 1 := (div_le_one hc0_pos).mpr hw_le_c0
      have hdiv_le : (wR / 2) * (B / c0) ≤ B := by
        calc (wR / 2) * (B / c0) = ((wR / 2) / c0) * B := by ring
          _ ≤ 1 * B := mul_le_mul_of_nonneg_right hw_div hB_pos.le
          _ = B := one_mul B
      have h2 := mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ wR / 2)
      linarith
    rw [Real.rpow_def_of_pos hB_pos, Real.rpow_def_of_pos hc0_pos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h4sqrt_le : 4 * π * Real.sqrt (a * B) ≤ 2 * π * a + 2 * π * B := by
    have h1 : 2 * Real.sqrt (a * B) ≤ a + B := by
      have h0 := two_mul_le_add_sq (Real.sqrt a) (Real.sqrt B)
      rw [Real.sq_sqrt ha_pos.le, Real.sq_sqrt (show 0 ≤ B by linarith),
        mul_assoc, ← Real.sqrt_mul ha_pos.le B] at h0
      exact h0
    nlinarith [Real.pi_pos]
  have h2sqrt_le : 2 * π * Real.sqrt (a * B) ≤ π * a + π * B := by linarith
  have hsum_meas2 : σ₀_real.real univ + μ₀_real.real univ ≤
      (9 / 4 : ℝ) * C_count_fac * Real.exp (8 * π * a + (2 * π + 1) * B) := by
    have htv_le : C.src.tv ≤ max C.src.tv 1 := le_max_left _ _
    have hexp_le : Real.exp (6 * π * a + 4 * π * Real.sqrt (a * B)) ≤
        Real.exp (6 * π * a + (2 * π * a + 2 * π * B)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc σ₀_real.real univ + μ₀_real.real univ
        ≤ (9 / 4 : ℝ) * (3 * C.src.tv * B ^ (wR / 2) * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * B))) := hsum_meas
      _ ≤ (9 / 4 : ℝ) * (3 * max C.src.tv 1 * (c0 ^ (wR / 2) * Real.exp B) *
            Real.exp (6 * π * a + (2 * π * a + 2 * π * B))) := by
          gcongr
      _ = (9 / 4 : ℝ) * C_count_fac * (Real.exp B * Real.exp (6 * π * a + (2 * π * a + 2 * π * B))) := by
          dsimp [C_count_fac]; ring
      _ = (9 / 4 : ℝ) * C_count_fac * Real.exp (8 * π * a + (2 * π + 1) * B) := by
          rw [← Real.exp_add]; congr 2; ring
  have ht_pos : 0 < t := by
    have hj2_nn : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by positivity
    linarith
  have ht_B0_le : (t / B₀) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) ≤
      C_w_fac * (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) := by
    have hle_div : t / B₀ ≤ 8 * (t / a) := by
      have ha_le_8B0 : a ≤ 8 * B₀ := by linarith
      rw [div_le_iff₀ hB0_pos, show 8 * (t / a) * B₀ = t * (8 * B₀ / a) by ring]
      exact le_mul_of_one_le_right ht_pos.le ((one_le_div ha_pos).mpr ha_le_8B0)
    have hta_nn : 0 ≤ t / a := div_nonneg ht_pos.le ha_pos.le
    calc (t / B₀) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2)
        ≤ (8 * (t / a)) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) :=
          Real.rpow_le_rpow (div_nonneg ht_pos.le hB0_pos.le) hle_div (by positivity)
      _ = C_w_fac * (t / a) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) := by
          dsimp [C_w_fac]
          exact Real.mul_rpow (by norm_num) hta_nn
  let x_t : ℝ := Real.sqrt (a * t)
  have hat_nn : 0 ≤ a * t := mul_nonneg ha_pos.le ht_pos.le
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
  have hB_nn : 0 ≤ B := by dsimp [B]; positivity
  have hwR_nn : 0 ≤ wR := Nat.cast_nonneg _
  have hbrace :
      Real.exp (8 * π * a + (2 * π + 1) * B) *
        ((a * t) ^ (1 / 4 : ℝ) * Real.exp (-4 * π * x_t) *
          (min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
            sonineRepairConst * Real.exp (sonineRepairConst * (B + wR)) *
              (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)) ≤
      (1 + sonineRepairConst) * Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) :=
    atom_tail_brace ha_pos ht_pos hB0_pos hPk_pos rfl hδ0 hδ1 hB_nn hwR_nn sonineRepairConst_nonneg
      rfl rfl h2sqrt_le
  have hC_const_exp : C_const * Real.exp (-H_k) ≤ 1 := by
    have hlog_nn : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
    have hC_le : C_const ≤ Real.exp a := by
      have h1 : C_const ≤ max C_const 1 := le_max_left _ _
      have h2 : max C_const 1 = Real.exp (Real.log (max C_const 1)) :=
        (Real.exp_log (lt_max_of_lt_right one_pos)).symm
      have h3 : Real.exp (Real.log (max C_const 1)) ≤ Real.exp a :=
        Real.exp_le_exp.mpr (by linarith)
      exact h1.trans (h2 ▸ h3)
    have hB_nn : 0 ≤ B := by dsimp [B]; positivity
    have hwR_nn : 0 ≤ wR := by positivity
    have ha_H : a ≤ H_k := by
      have h1 : a ≤ a + B := le_add_of_nonneg_right hB_nn
      have h2 : a + B ≤ a + B + Real.log (1 / δ) := le_add_of_nonneg_right hlog_nn
      have h3 : a + B + Real.log (1 / δ) ≤ H_k := le_add_of_nonneg_right hwR_nn
      exact h1.trans (h2.trans h3)
    calc C_const * Real.exp (-H_k) ≤ Real.exp a * Real.exp (-a) :=
          mul_le_mul hC_le (Real.exp_le_exp.mpr (neg_le_neg ha_H))
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hexp_tail : Real.exp (-H_k) ≤ (1 / 2 : ℝ) ^ (j + 4) * δ := by
    have hlog_eq : Real.exp (-Real.log (1 / δ)) = δ := by
      rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hδ0), one_div, inv_inv]
    have hsum_ge : ((j + 4 : ℕ) : ℝ) ≤ a + B + wR := by
      have ha4 : (4 : ℝ) ≤ a := le_trans (by norm_num : (4 : ℝ) ≤ 24) ha24
      have hjB : (j : ℝ) ≤ B := by
        have hT_nn : 0 ≤ T :=
          le_trans (div_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 24) ha24) (by norm_num)) hT
        have hj2_ge : (j : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right j 2
        dsimp [B]; exact le_add_of_nonneg_of_le hT_nn hj2_ge
      have hcast : ((j + 4 : ℕ) : ℝ) = (j : ℝ) + 4 := by
        rw [Nat.cast_add]; norm_num
      have hwR_nn : 0 ≤ wR := Nat.cast_nonneg _
      calc ((j + 4 : ℕ) : ℝ) = (j : ℝ) + 4 := hcast
        _ ≤ B + 4 := by gcongr
        _ ≤ B + a := by gcongr
        _ = a + B := add_comm B a
        _ ≤ a + B + wR := le_add_of_nonneg_right hwR_nn
    have hexp_pow : Real.exp (-((j + 4 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ (j + 4) := by
      rw [show -((j + 4 : ℕ) : ℝ) = ((j + 4 : ℕ) : ℝ) * (-1) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_half _
    calc Real.exp (-H_k) = Real.exp (-(a + B + wR)) * Real.exp (-Real.log (1 / δ)) := by
          dsimp [H_k]; rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (-(a + B + wR)) * δ := by rw [hlog_eq]
      _ ≤ Real.exp (-((j + 4 : ℕ) : ℝ)) * δ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsum_ge)) hδ0.le
      _ ≤ (1 / 2 : ℝ) ^ (j + 4) * δ :=
          mul_le_mul_of_nonneg_right hexp_pow hδ0.le
  have ha8_le_t : a / 8 ≤ t :=
    le_trans hT (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg (j + 2))) ht.le)
  have hrho_cd : c_vac * rhoLowerCore C.src.w a t ≤ C.src.cardyDensity a t :=
    hrho_lb ha8_le_t
  have hrho_pos : 0 < rhoLowerCore C.src.w a t := rhoLowerCore_pos ha_pos ht_pos
  have hcomb_exp : Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2) ≤ Real.exp (-H_k) * Real.exp (-H_k) := by
    calc Real.exp (C_exp * H_k) * P_k ^ (-(m : ℝ) / 2)
        ≤ Real.exp (C_exp * H_k) * Real.exp (-(C_exp + 2) * H_k) := by gcongr
      _ = Real.exp (-H_k) * Real.exp (-H_k) := exp_add_two_sub C_exp H_k
  have hCc_nn : 0 ≤ C_count_fac :=
    mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_right _ _)))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hCw_nn : 0 ≤ C_w_fac := Real.rpow_nonneg (by norm_num) _
  have hpowB0_nn : 0 ≤ (t / B₀) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) :=
    Real.rpow_nonneg (div_nonneg ht_pos.le hB0_pos.le) _
  have hexpB_nn : 0 ≤ Real.exp (8 * π * a + (2 * π + 1) * B) := (Real.exp_pos _).le
  have hden_nn : 0 ≤ (m : ℝ) * Real.sqrt B₀ := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have ht1_nn : 0 ≤ (2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m :=
    pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Real.exp_pos _).le) (Real.sqrt_nonneg _)) hden_nn) _
  have ht2_nn : 0 ≤ (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m :=
    pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Real.exp_pos _).le) (Real.sqrt_nonneg _)) hden_nn) _
  have htail_nn : 0 ≤
      min 1 ((2 * π * Real.exp 1 * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
        sonineRepairConst * Real.exp (sonineRepairConst * (B + wR)) *
          (2 * π * Real.exp 1 * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m :=
    add_nonneg (le_min zero_le_one ht1_nn)
      (mul_nonneg (mul_nonneg sonineRepairConst_nonneg (Real.exp_pos _).le) ht2_nn)
  exact atom_tail_finish hc_vac_pos hδ0 sonineRepairConst_nonneg hV_nn hrho_pos hCc_nn hCw_nn htail_nn
    hpowB0_nn hexpB_nn hrho_cd rfl hC_const_exp hexp_tail hcomb_exp hbrace hrt_tail hsum_meas2
    ht_B0_le hrho_eq

end CellHelpers

/-- Single-cell step builder `CellStep` for `atomShellSetup`. -/
lemma atom_cell_step (C : CommonSource) {W : ℕ → ℝ} (hW : SufficientMomentFloor W)
    {c_vac : ℝ} (hc_vac_pos : 0 < c_vac)
    {a T δ : ℝ} (ha0 : C.a₀ ≤ a) (ha24 : 24 ≤ a) (hT : a / 8 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hrho_lb : ∀ {t : ℝ}, a / 8 ≤ t → c_vac * rhoLowerCore C.src.w a t ≤ C.src.cardyDensity a t)
    (meas : SourceCrossingMeasure C.src a) (hsupp : meas.ν (Ici T)ᶜ = 0)
    (hres : ENNReal.ofReal δ •
      (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ici T) ≤
        meas.ν)
    (hcount_fn : ∀ R : ℝ, 1 ≤ R →
      meas.ν.real (Icc T R) ≤
        3 * C.src.tv * R ^ ((C.src.w : ℝ) / 2) * Real.exp (6 * π * a + 4 * π * Real.sqrt (a * R)))
    (ha_const : Real.log (max (2 * π * (9 / 4 * (3 * max C.src.tv 1 *
        (max (1 : ℝ) ((C.src.w : ℝ) / 2)) ^ ((C.src.w : ℝ) / 2))) *
      (8 : ℝ) ^ (((C.src.w - 1 : ℕ) : ℝ) / 2) * (1 + sonineRepairConst) / c_vac) 1) + 1 ≤ a)
    (M : ℕ → ℕ) (hM1 : ∀ k, 1 ≤ M k)
    (hM_ord : ∀ k : ℕ, 1 ≤ k →
      (2 * ((9 * π + sonineRepairConst + 1) + 2)) *
        (a + (T + ((k + 1 : ℕ) : ℝ)) + Real.log (1 / δ) + (C.src.w : ℝ)) /
      Real.log (a * (T + ((k - 1 : ℕ) : ℝ))) ≤ (M k : ℝ))
    (hM_fl : ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, T + ((k - 1 : ℕ) : ℝ) ≤ s →
      W (M k) ≤ (δ / 8) * C.src.cardyDensity a s)
    (j : ℕ) (Sg lam : Measure (Set.Ici T))
    (hInv : (atomShellSetup C ha0 (by linarith) hδ0 hδ1 meas hsupp hres).Inv j Sg lam) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Set (Set.Ici T)) (μ σ Rp Rm : ι → Measure (Set.Ici T)),
      (atomShellSetup C ha0 (by linarith) hδ0 hδ1 meas hsupp hres).CellStep j lam U μ σ Rp Rm := by
  have hT_pos : 0 < T := by linarith
  let S := atomShellSetup C ha0 hT_pos hδ0 hδ1 meas hsupp hres
  let X := Set.Ici T
  let RPos := {β : ℝ // 0 < β}
  let hEmb : MeasurableEmbedding (Subtype.val : X → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  have hν0_map : Measure.map Subtype.val S.ν0 = meas.ν := by
    dsimp [S, atomShellSetup]
    rw [hEmb.map_comap meas.ν, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem
      (measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono fun _ ht => not_not.mp ht)
  have hρ_map : Measure.map Subtype.val S.ρ = atomRhoReal C a T := by
    dsimp [S, atomShellSetup]
    rw [hEmb.map_comap (atomRhoReal C a T), Subtype.range_coe]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    dsimp [atomRhoReal]
    rw [ae_restrict_iff' measurableSet_Ici]
    exact Eventually.of_forall fun _ ht => ht
  have hm_dens : Measurable (fun t : ℝ => ENNReal.ofReal (C.src.cardyDensity a t)) :=
    ((C.src.continuous_cardyV a).const_mul (2 * π)).measurable.ennreal_ofReal
  have hν0_fin := fun R => atomShellSetup_nu0_fin C ha0 hT_pos hδ0 hδ1 meas hsupp hres R
  have hρ_sub_fin : ∀ R : ℝ, S.ρ {x : X | (x : ℝ) ≤ R} < ∞ := fun R => by
    have h1 := Measure.le_iff.1 S.reserve_le {x : X | (x : ℝ) ≤ R}
      (measurableSet_le continuous_subtype_val.measurable measurable_const)
    rw [smul_apply, smul_eq_mul] at h1
    have hlt := lt_of_le_of_lt h1 (hν0_fin R)
    exact (ENNReal.mul_lt_top_iff.mp hlt).elim (fun h => h.2)
      (fun h => h.elim (fun h0 => absurd h0 (ENNReal.ofReal_pos.mpr hδ0).ne')
        (fun h0 => by simp [h0]))
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
        · change max T (B - 1 / ((n : ℝ) + 1)) < T + ((j + 2 : ℕ) : ℝ)
          have hj2_nn : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by positivity
          have hT_lt : T < B := by dsimp [B]; linarith
          rw [max_lt_iff]
          exact ⟨by dsimp [B] at hT_lt; exact hT_lt,
            by dsimp [B]; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]⟩
        · rw [tendsto_subtype_rng]
          have hsub_tend : Tendsto (fun n : ℕ => B - 1 / ((n : ℝ) + 1)) atTop (𝓝 B) := by
            have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
              tendsto_one_div_add_atTop_nhds_zero_nat
            have h1 : Tendsto (fun n : ℕ => B - 1 / ((n : ℝ) + 1)) atTop (𝓝 (B - 0)) :=
              tendsto_const_nhds.sub h0
            simpa only [sub_zero] using h1
          have hev : ∀ᶠ n : ℕ in atTop, T ≤ B - 1 / ((n : ℝ) + 1) := by
            have hj2_nn : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by positivity
            have hT_lt : T < B := by dsimp [B]; linarith
            filter_upwards [hsub_tend.eventually (lt_mem_nhds hT_lt)] with n hn
            exact hn.le
          have hmax : (fun n : ℕ => (seq n : ℝ)) =ᶠ[atTop] fun n : ℕ => B - 1 / ((n : ℝ) + 1) :=
            hev.mono fun n hn => max_eq_right hn
          rw [hxeq]
          exact hsub_tend.congr' hmax.symm
      · exact subset_closure (show (x : ℝ) < T + ((j + 2 : ℕ) : ℝ) by dsimp [B] at hxlt; exact hxlt)
    · have hxlt : (x : ℝ) < T + (j : ℝ) := hxΩ
      dsimp [B₀] at hx1
      linarith
  have hsh_meas : ∀ i : ℕ, MeasurableSet (S.shell i) := fun i =>
    (S.Ω_open (i + 1)).measurableSet.diff (S.Ω_open i).measurableSet
  have hshj_eq : S.shell j = {x : X | B₀ ≤ (x : ℝ) ∧ (x : ℝ) < B_mid} := by
    ext x
    dsimp only [ShellSetup.shell, S, atomShellSetup, B₀, B_mid]
    push_cast
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hshj1_eq : S.shell (j + 1) = {x : X | B_mid ≤ (x : ℝ) ∧ (x : ℝ) < B} := by
    ext x
    dsimp only [ShellSetup.shell, S, atomShellSetup, B_mid, B]
    push_cast
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hsh_union_sub : S.shell j ∪ S.shell (j + 1) ⊆ U₀ := by
    intro x hx
    rcases hx with h | h
    · rw [hshj_eq] at h; exact ⟨h.1, le_of_lt (h.2.trans (by linarith))⟩
    · rw [hshj1_eq] at h; exact ⟨le_trans (by linarith) h.1, h.2.le⟩
  have hsh_disj : Disjoint (S.shell j) (S.shell (j + 1)) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    rw [hshj_eq] at h1; rw [hshj1_eq] at h2
    have hlt := lt_of_lt_of_le h1.2 h2.1
    linarith [lt_irrefl B_mid]
  have hU0_fin_ν0 : S.ν0 {x : X | (x : ℝ) ≤ B} < ∞ := hν0_fin B
  have hU0_fin_ρ : S.ρ {x : X | (x : ℝ) ≤ B} < ∞ := hρ_sub_fin B
  have hcm_add : ∀ a₁ a₂ : ℝ, 0 ≤ a₁ → 0 ≤ a₂ → S.cm (a₁ + a₂) = S.cm a₁ + S.cm a₂ := by
    intro a₁ a₂ ha₁ ha₂
    ext A hA
    simp only [ShellSetup.cm, add_apply, smul_apply, smul_eq_mul]
    have hmul : (a₁ + a₂) * S.δ = a₁ * S.δ + a₂ * S.δ := by ring
    rw [hmul, ENNReal.ofReal_add (mul_nonneg ha₁ S.δ_pos.le) (mul_nonneg ha₂ S.δ_pos.le), add_mul]
  have hcm_mono : ∀ {a₁ a₂ : ℝ}, a₁ ≤ a₂ → S.cm a₁ ≤ S.cm a₂ := fun h => by
    refine Measure.le_iff.2 fun A _ => ?_
    simp only [ShellSetup.cm, smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h S.δ_pos.le)) zero_le
  have hlam_sh1 : ShellSetup.LEOn (S.shell (j + 1)) (S.cm (cE j)) lam := fun A hA hAs =>
    hInv.2.2.2.2.1 A hA (hAs.trans fun _ hx hxΩ => hx.2 hxΩ)
  have hlam_Ω2_le : lam (S.Ω (j + 2)) ≤ ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := by
    have h1 := hInv.2.2.1
    have h2 := Measure.le_iff.1 h1 (S.Ω (j + 2)) (S.Ω_open (j + 2)).measurableSet
    have hcm_th : S.cm (theta j) (S.Ω (j + 2)) ≤ ENNReal.ofReal (1 / 8) * S.ν0 (S.Ω (j + 2)) := by
      have hth_le : theta j ≤ 1 / 8 := by unfold theta; linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 3) by positivity]
      calc S.cm (theta j) (S.Ω (j + 2))
          ≤ S.cm (1 / 8) (S.Ω (j + 2)) := Measure.le_iff.1 (hcm_mono hth_le) _ (S.Ω_open (j + 2)).measurableSet
        _ = ENNReal.ofReal (1 / 8) * (ENNReal.ofReal S.δ * S.ρ (S.Ω (j + 2))) := by
            simp only [ShellSetup.cm, smul_apply, smul_eq_mul]
            rw [ENNReal.ofReal_mul (by norm_num), mul_assoc]
        _ ≤ ENNReal.ofReal (1 / 8) * S.ν0 (S.Ω (j + 2)) := by
            gcongr
            simpa [smul_apply, smul_eq_mul] using
              Measure.le_iff.1 S.reserve_le (S.Ω (j + 2)) (S.Ω_open (j + 2)).measurableSet
    calc lam (S.Ω (j + 2)) ≤ S.ν0 (S.Ω (j + 2)) + S.cm (theta j) (S.Ω (j + 2)) := h2
      _ ≤ 1 * S.ν0 (S.Ω (j + 2)) + ENNReal.ofReal (1 / 8) * S.ν0 (S.Ω (j + 2)) := by
          rw [one_mul]; gcongr
      _ = ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := by
          rw [← add_mul]
          congr 1
          rw [show (9 / 8 : ℝ) = 1 + 1 / 8 by norm_num, ENNReal.ofReal_add zero_le_one (by norm_num),
            ENNReal.ofReal_one]
  have hlam_sh_fin : ∀ {A : Set X}, A ⊆ S.Ω (j + 2) → lam A < ∞ := fun {A} hA => by
    have hm_sub : S.Ω (j + 2) ⊆ {x : X | (x : ℝ) ≤ B} := fun x hx => by
      have hxlt : (x : ℝ) < B := by simpa [S, atomShellSetup, B] using hx
      exact hxlt.le
    calc lam A ≤ lam (S.Ω (j + 2)) := measure_mono hA
      _ ≤ ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := hlam_Ω2_le
      _ ≤ ENNReal.ofReal (9 / 8) * S.ν0 {x : X | (x : ℝ) ≤ B} := by gcongr
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU0_fin_ν0
  let lam0 : Measure X := lam.restrict (S.shell j)
  let lam1 : Measure X := lam.restrict (S.shell (j + 1))
  let Reserve1 : Measure X := (S.cm (5 / 8)).restrict (S.shell (j + 1))
  let R1 : Measure X := (S.cm (1 / 8)).restrict (S.shell (j + 1))
  have hfin_lam0 : IsFiniteMeasure lam0 := ⟨by
    simpa [lam0] using hlam_sh_fin (show S.shell j ⊆ S.Ω (j + 2) from fun _ hx => S.Ω_mono (Nat.le_succ _) hx.1)⟩
  have hfin_lam1 : IsFiniteMeasure lam1 := ⟨by
    simpa [lam1] using hlam_sh_fin (show S.shell (j + 1) ⊆ S.Ω (j + 2) from fun _ hx => hx.1)⟩
  have hfin_Res1 : IsFiniteMeasure Reserve1 := ⟨by
    have hm_sub : S.shell (j + 1) ⊆ {x : X | (x : ℝ) ≤ B} := fun x hx => by
      rw [hshj1_eq] at hx; exact hx.2.le
    calc Reserve1 univ = S.cm (5 / 8) (S.shell (j + 1)) := by simp [Reserve1]
      _ ≤ S.cm (5 / 8) {x : X | (x : ℝ) ≤ B} := measure_mono hm_sub
      _ < ∞ := by
          simp only [ShellSetup.cm, smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU0_fin_ρ⟩
  have hfin_R1 : IsFiniteMeasure R1 := ⟨by
    have hm_sub : S.shell (j + 1) ⊆ {x : X | (x : ℝ) ≤ B} := fun x hx => by
      rw [hshj1_eq] at hx; exact hx.2.le
    calc R1 univ = S.cm (1 / 8) (S.shell (j + 1)) := by simp [R1]
      _ ≤ S.cm (1 / 8) {x : X | (x : ℝ) ≤ B} := measure_mono hm_sub
      _ < ∞ := by
          simp only [ShellSetup.cm, smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU0_fin_ρ⟩
  have hRes_R1_le : Reserve1 + R1 ≤ lam1 := Measure.le_iff.2 fun A hA => by
    simp only [Reserve1, R1, lam1, add_apply, Measure.restrict_apply hA]
    have hsum_cm : S.cm (5 / 8) (A ∩ S.shell (j + 1)) + S.cm (1 / 8) (A ∩ S.shell (j + 1)) =
        S.cm (3 / 4) (A ∩ S.shell (j + 1)) := by
      rw [← add_apply, ← hcm_add (5 / 8) (1 / 8) (by norm_num) (by norm_num)]
      congr 1; norm_num
    rw [hsum_cm]
    have h34_cE : 3 / 4 ≤ cE j := by unfold cE; linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 3) by positivity]
    calc S.cm (3 / 4) (A ∩ S.shell (j + 1))
        ≤ S.cm (cE j) (A ∩ S.shell (j + 1)) :=
          Measure.le_iff.1 (hcm_mono h34_cE) _ (hA.inter (hsh_meas (j + 1)))
      _ ≤ lam (A ∩ S.shell (j + 1)) :=
          hlam_sh1 (A ∩ S.shell (j + 1)) (hA.inter (hsh_meas (j + 1))) inter_subset_right
  let rem : Measure X := lam1 - (Reserve1 + R1)
  have hrem_add : rem + (Reserve1 + R1) = lam1 := Measure.sub_add_cancel_of_le hRes_R1_le
  have hrem_ge : (S.cm (1 / 8)).restrict (S.shell (j + 1)) ≤ rem := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [Measure.sub_apply hA hRes_R1_le]
    have hle : (S.cm (1 / 8)).restrict (S.shell (j + 1)) A + (Reserve1 + R1) A ≤ lam1 A := by
      simp only [Reserve1, R1, lam1, add_apply, Measure.restrict_apply hA]
      have h18_58 : S.cm (1 / 8) (A ∩ S.shell (j + 1)) +
          (S.cm (5 / 8) (A ∩ S.shell (j + 1)) + S.cm (1 / 8) (A ∩ S.shell (j + 1))) =
          S.cm (7 / 8) (A ∩ S.shell (j + 1)) := by
        rw [← add_apply, ← hcm_add (5 / 8) (1 / 8) (by norm_num) (by norm_num),
          ← add_apply, ← hcm_add (1 / 8) (5 / 8 + 1 / 8) (by norm_num) (by norm_num)]
        congr 1; norm_num
      rw [h18_58]
      have h78_cE : 7 / 8 ≤ cE j := by unfold cE; linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 3) by positivity]
      calc S.cm (7 / 8) (A ∩ S.shell (j + 1))
          ≤ S.cm (cE j) (A ∩ S.shell (j + 1)) :=
            Measure.le_iff.1 (hcm_mono h78_cE) _ (hA.inter (hsh_meas (j + 1)))
        _ ≤ lam (A ∩ S.shell (j + 1)) :=
            hlam_sh1 (A ∩ S.shell (j + 1)) (hA.inter (hsh_meas (j + 1))) inter_subset_right
    have hfin_RR : (Reserve1 + R1) A ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨measure_ne_top Reserve1 A, measure_ne_top R1 A⟩
    calc (S.cm (1 / 8)).restrict (S.shell (j + 1)) A
        = (S.cm (1 / 8)).restrict (S.shell (j + 1)) A + (Reserve1 + R1) A - (Reserve1 + R1) A :=
          (ENNReal.add_sub_cancel_right hfin_RR).symm
      _ ≤ lam1 A - (Reserve1 + R1) A := tsub_le_tsub_right hle _
  have hvol_sh1 : ENNReal.ofReal (W Mk) • volume.restrict (Ico B_mid B) ≤
      ENNReal.ofReal (1 / 8 * δ) • (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)).restrict (Ico B_mid B) := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.restrict_apply hA, Measure.restrict_apply hA, withDensity_apply _ (hA.inter measurableSet_Ico)]
    calc ENNReal.ofReal (W Mk) * volume (A ∩ Ico B_mid B)
        = ∫⁻ _ in A ∩ Ico B_mid B, ENNReal.ofReal (W Mk) ∂volume := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ t in A ∩ Ico B_mid B, ENNReal.ofReal ((δ / 8) * C.src.cardyDensity a t) ∂volume := by
          refine setLIntegral_mono' (hA.inter measurableSet_Ico) fun t ht => ?_
          exact ENNReal.ofReal_le_ofReal (hMk_fl t (by linarith [ht.2.1]))
      _ = ENNReal.ofReal (1 / 8 * δ) *
            ∫⁻ t in A ∩ Ico B_mid B, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
          have heq : (fun t : ℝ => ENNReal.ofReal ((δ / 8) * C.src.cardyDensity a t)) =
              fun t => ENNReal.ofReal (1 / 8 * δ) * ENNReal.ofReal (C.src.cardyDensity a t) := by
            ext t
            rw [show (δ / 8) * C.src.cardyDensity a t = (1 / 8 * δ) * C.src.cardyDensity a t by ring,
              ENNReal.ofReal_mul (by positivity)]
          rw [heq, lintegral_const_mul _ hm_dens]
  have hR1_mass_gt : 1 < (R1 univ).toReal := by
    have hge_W : ENNReal.ofReal (W Mk) ≤ ENNReal.ofReal (1 / 8 * δ) * S.ρ (S.shell (j + 1)) := by
      have hvol_1 : volume (Ico B_mid B) = 1 := by
        rw [Real.volume_Ico, hB_eq, add_sub_cancel_left, ENNReal.ofReal_one]
      have h1 := Measure.le_iff.1 hvol_sh1 univ MeasurableSet.univ
      rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
        Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, hvol_1, mul_one] at h1
      have hpre1 : Subtype.val ⁻¹' Ico B_mid B = S.shell (j + 1) := by
        ext x; rw [hshj1_eq]; rfl
      have hinter1 : Ico B_mid B ∩ Ici T = Ico B_mid B := Set.inter_eq_left.mpr fun t ht => by
        change T ≤ t
        have ht1 : B_mid ≤ t := ht.1
        have hj1_nn : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by positivity
        dsimp [B_mid] at ht1; linarith
      have hr_eq : (volume.withDensity fun t => ENNReal.ofReal (C.src.cardyDensity a t)) (Ico B_mid B) =
          S.ρ (S.shell (j + 1)) := by
        have h2 : S.ρ (S.shell (j + 1)) = atomRhoReal C a T (Ico B_mid B) := by
          rw [← hρ_map, Measure.map_apply hEmb.measurable measurableSet_Ico, hpre1]
        rw [h2]
        dsimp [atomRhoReal]
        rw [Measure.restrict_apply measurableSet_Ico, hinter1]
      simpa [hr_eq] using h1
    have hR1_eq : R1 univ = ENNReal.ofReal (1 / 8 * δ) * S.ρ (S.shell (j + 1)) := by
      simp only [R1, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        ShellSetup.cm, smul_apply, smul_eq_mul]
      rfl
    have hW_R1 : ENNReal.ofReal (W Mk) ≤ R1 univ := hR1_eq ▸ hge_W
    have hlt_top : R1 univ ≠ ∞ := measure_ne_top R1 univ
    have htoReal := ENNReal.toReal_mono hlt_top hW_R1
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
      · have := Nat.ceil_lt_add_one (not_le.mp hL).le
        linarith
    rw [div_le_one hR1_pos_real]
    linarith
  let μ₀ : Measure X := lam0 + rem + ENNReal.ofReal α • R1
  have hfin_rem : IsFiniteMeasure rem := ⟨by
    calc rem univ ≤ lam1 univ := by rw [Measure.sub_apply MeasurableSet.univ hRes_R1_le]; exact tsub_le_self
      _ < ∞ := hfin_lam1.measure_univ_lt_top⟩
  have hfin_μ0 : IsFiniteMeasure μ₀ := ⟨by
    dsimp [μ₀]
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hfin_lam0.measure_univ_lt_top, hfin_rem.measure_univ_lt_top⟩,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin_R1.measure_univ_lt_top⟩⟩
  have hμ₀_univ : μ₀ univ = Ntot := by
    have hR1_fin : R1 univ ≠ ∞ := hfin_R1.measure_univ_lt_top.ne
    have hsum_toReal : (μ₀ univ).toReal = (Ntot : ℝ) := by
      dsimp [μ₀]
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨hfin_lam0.measure_univ_lt_top.ne, hfin_rem.measure_univ_lt_top.ne⟩)
        (ENNReal.mul_ne_top ENNReal.ofReal_lt_top.ne hR1_fin),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hα0]
      change L_lo + α * (R1 univ).toReal = (Ntot : ℝ)
      dsimp [α]
      field_simp [hR1_pos_real.ne']
      ring
    rw [← ENNReal.ofReal_toReal hfin_μ0.measure_univ_lt_top.ne, hsum_toReal]
    simp
  have hμ₀_supp : μ₀ (U₀ ∩ (S.shell j ∪ S.shell (j + 1)))ᶜ = 0 := by
    have heq_inter : U₀ ∩ (S.shell j ∪ S.shell (j + 1)) = S.shell j ∪ S.shell (j + 1) :=
      Set.inter_eq_right.mpr hsh_union_sub
    rw [heq_inter]
    dsimp [μ₀]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have h1 : lam0 (S.shell j ∪ S.shell (j + 1))ᶜ = 0 := by
      dsimp [lam0]
      rw [Measure.restrict_apply (MeasurableSet.compl ((hsh_meas j).union (hsh_meas (j + 1))))]
      have : (S.shell j ∪ S.shell (j + 1))ᶜ ∩ S.shell j = ∅ :=
        Set.ext fun _ => ⟨fun ⟨h1, h2⟩ => h1 (Or.inl h2), False.elim⟩
      rw [this, measure_empty]
    have h2 : rem (S.shell j ∪ S.shell (j + 1))ᶜ = 0 := by
      refine le_antisymm ?_ zero_le
      have hsub_le : rem (S.shell j ∪ S.shell (j + 1))ᶜ ≤ lam1 (S.shell j ∪ S.shell (j + 1))ᶜ := by
        rw [Measure.sub_apply (MeasurableSet.compl ((hsh_meas j).union (hsh_meas (j + 1)))) hRes_R1_le]
        exact tsub_le_self
      calc rem (S.shell j ∪ S.shell (j + 1))ᶜ
          ≤ lam1 (S.shell j ∪ S.shell (j + 1))ᶜ := hsub_le
        _ = 0 := by
            dsimp [lam1]
            rw [Measure.restrict_apply (MeasurableSet.compl ((hsh_meas j).union (hsh_meas (j + 1))))]
            have : (S.shell j ∪ S.shell (j + 1))ᶜ ∩ S.shell (j + 1) = ∅ :=
              Set.ext fun _ => ⟨fun ⟨h1, h2⟩ => h1 (Or.inr h2), False.elim⟩
            rw [this, measure_empty]
    have h3 : R1 (S.shell j ∪ S.shell (j + 1))ᶜ = 0 := by
      dsimp [R1]
      rw [Measure.restrict_apply (MeasurableSet.compl ((hsh_meas j).union (hsh_meas (j + 1))))]
      have : (S.shell j ∪ S.shell (j + 1))ᶜ ∩ S.shell (j + 1) = ∅ :=
        Set.ext fun _ => ⟨fun ⟨h1, h2⟩ => h1 (Or.inr h2), False.elim⟩
      rw [this, measure_empty]
    rw [h1, h2, h3, add_zero, zero_add, mul_zero]
  have hμ₀_le_lam : μ₀ ≤ lam := by
    refine Measure.le_iff.2 fun A hA => ?_
    have hstep : μ₀ A ≤ lam0 A + lam1 A := by
      dsimp [μ₀]
      simp only [add_apply, smul_apply, smul_eq_mul]
      have hsmul : ENNReal.ofReal α * R1 A ≤ R1 A := by
        calc ENNReal.ofReal α * R1 A ≤ 1 * R1 A :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr hα1) zero_le
          _ = R1 A := one_mul _
      calc lam0 A + rem A + ENNReal.ofReal α * R1 A
          = lam0 A + (rem A + ENNReal.ofReal α * R1 A) := add_assoc _ _ _
        _ ≤ lam0 A + (rem A + (Reserve1 A + R1 A)) := by
            gcongr
            exact hsmul.trans le_add_self
        _ = lam0 A + lam1 A := by
            rw [← add_apply, ← add_apply, hrem_add]
    calc μ₀ A ≤ lam0 A + lam1 A := hstep
      _ = lam (A ∩ S.shell j) + lam (A ∩ S.shell (j + 1)) := by
          simp only [lam0, lam1, Measure.restrict_apply hA]
      _ = lam ((A ∩ S.shell j) ∪ (A ∩ S.shell (j + 1))) := by
          rw [measure_union (hsh_disj.mono inter_subset_right inter_subset_right)
            (hA.inter (hsh_meas (j + 1)))]
      _ ≤ lam A := measure_mono (union_subset inter_subset_left inter_subset_left)
  have hshell_vanish : ShellSetup.LEOn (S.shell j) lam μ₀ := fun A hA hAs => by
    have hlam0_eq : lam A = lam0 A := by
      dsimp [lam0]; rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hAs]
    dsimp [μ₀]
    simp only [add_apply]
    rw [hlam0_eq, add_assoc]
    exact le_self_add
  have hshell_reserve : ShellSetup.LEOn (S.shell (j + 1)) (μ₀ + S.cm (5 / 8)) lam := fun A hA hAs => by
    have hlam0_zero : lam0 A = 0 := by
      dsimp [lam0]
      have hinter_empty : A ∩ S.shell j = ∅ :=
        Set.disjoint_iff_inter_eq_empty.1 (Set.disjoint_of_subset_left hAs hsh_disj.symm)
      rw [Measure.restrict_apply hA, hinter_empty, measure_empty]
    have hlam1_eq : lam A = lam1 A := by
      dsimp [lam1]; rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hAs]
    have hRes1_eq : S.cm (5 / 8) A = Reserve1 A := by
      dsimp [Reserve1]; rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hAs]
    have hsmul : ENNReal.ofReal α * R1 A ≤ R1 A := by
      calc ENNReal.ofReal α * R1 A ≤ 1 * R1 A :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr hα1) zero_le
        _ = R1 A := one_mul _
    have hrem_addA : rem A + (Reserve1 A + R1 A) = lam1 A := by
      rw [← add_apply, ← add_apply, hrem_add]
    dsimp [μ₀]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hlam0_zero, zero_add, hlam1_eq, ← hrem_addA, hRes1_eq]
    calc rem A + ENNReal.ofReal α * R1 A + Reserve1 A
        = rem A + (Reserve1 A + ENNReal.ofReal α * R1 A) := by ring
      _ ≤ rem A + (Reserve1 A + R1 A) := by gcongr
  let μ₀_real : Measure ℝ := Measure.map Subtype.val μ₀
  have hfin_μ0_real : IsFiniteMeasure μ₀_real := Measure.isFiniteMeasure_map μ₀ Subtype.val
  have hμ₀_real_supp : μ₀_real (Icc B₀ B)ᶜ = 0 := by
    rw [Measure.map_apply hEmb.measurable measurableSet_Icc.compl]
    refine measure_mono_null (fun x hx => ?_) hμ₀_supp
    intro ⟨hx1, _⟩
    exact hx hx1
  have hμ₀_real_univ : μ₀_real univ = Ntot := by
    rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, Set.preimage_univ, hμ₀_univ]
  have hfloor_μ0 : ENNReal.ofReal (W Mk) • volume.restrict (Icc B₀ B) ≤ μ₀_real := by
    have hvol_B : volume.restrict (Icc B₀ B) = volume.restrict (Ico B₀ B) := by
      ext A hA
      have hdiff : A ∩ Icc B₀ B = (A ∩ Ico B₀ B) ∪ (A ∩ {B}) := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_Icc, Set.mem_Ico, Set.mem_singleton_iff]
        constructor
        · rintro ⟨htA, ht1, ht2⟩
          rcases eq_or_lt_of_le ht2 with rfl | hlt
          · exact Or.inr ⟨htA, rfl⟩
          · exact Or.inl ⟨htA, ht1, hlt⟩
        · rintro (⟨htA, ht1, ht2⟩ | ⟨htA, rfl⟩)
          · exact ⟨htA, ht1, ht2.le⟩
          · exact ⟨htA, hB0_lt_B.le, le_rfl⟩
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hdiff]
      exact le_antisymm
        (calc volume ((A ∩ Ico B₀ B) ∪ (A ∩ {B}))
            ≤ volume (A ∩ Ico B₀ B) + volume (A ∩ {B}) := measure_union_le _ _
          _ = volume (A ∩ Ico B₀ B) + 0 := by
              rw [measure_mono_null inter_subset_right Real.volume_singleton]
          _ = volume (A ∩ Ico B₀ B) := add_zero _)
        (measure_mono subset_union_left)
    have hshj_ge : (S.cm (1 / 8)).restrict (S.shell j) ≤ lam0 := by
      refine Measure.le_iff.2 fun A hA => ?_
      simp only [lam0, Measure.restrict_apply hA]
      calc S.cm (1 / 8) (A ∩ S.shell j)
          ≤ S.cm (5 / 8) (A ∩ S.shell j) :=
            Measure.le_iff.1 (hcm_mono (by norm_num)) _ (hA.inter (hsh_meas j))
        _ ≤ lam (A ∩ S.shell j) :=
            hInv.2.2.2.1 (A ∩ S.shell j) (hA.inter (hsh_meas j)) inter_subset_right
    have hshj1_ge : (S.cm (1 / 8)).restrict (S.shell (j + 1)) ≤ rem := by
      refine le_trans ?_ hrem_ge
      refine Measure.le_iff.2 fun A hA => ?_
      simp only [Measure.restrict_apply hA]
      exact Measure.le_iff.1 (hcm_mono (by norm_num)) _ (hA.inter (hsh_meas (j + 1)))
    have hcm_le_μ0 : (S.cm (1 / 8)).restrict (S.shell j ∪ S.shell (j + 1)) ≤ μ₀ := by
      refine Measure.le_iff.2 fun A hA => ?_
      rw [Measure.restrict_apply hA,
        show A ∩ (S.shell j ∪ S.shell (j + 1)) = (A ∩ S.shell j) ∪ (A ∩ S.shell (j + 1)) by
          ext x; simp; tauto,
        measure_union (hsh_disj.mono inter_subset_right inter_subset_right)
          (hA.inter (hsh_meas (j + 1)))]
      dsimp [μ₀]
      simp only [add_apply]
      calc S.cm (1 / 8) (A ∩ S.shell j) + S.cm (1 / 8) (A ∩ S.shell (j + 1))
          ≤ lam0 A + rem A := by
            refine add_le_add ?_ ?_
            · simpa [Measure.restrict_apply hA] using Measure.le_iff.1 hshj_ge A hA
            · simpa [Measure.restrict_apply hA] using Measure.le_iff.1 hshj1_ge A hA
        _ ≤ lam0 A + rem A + (ENNReal.ofReal α • R1) A := le_self_add
    have hcm_map_eq : Measure.map Subtype.val ((S.cm (1 / 8)).restrict (S.shell j ∪ S.shell (j + 1))) =
        (ENNReal.ofReal (1 / 8 * S.δ) • atomRhoReal C a T).restrict (Ico B₀ B) := by
      have hpre : Subtype.val ⁻¹' Ico B₀ B = S.shell j ∪ S.shell (j + 1) := by
        ext x
        rw [Set.mem_preimage, Set.mem_Ico, Set.mem_union, hshj_eq, hshj1_eq]
        change (B₀ ≤ (x : ℝ) ∧ (x : ℝ) < B) ↔
          (B₀ ≤ (x : ℝ) ∧ (x : ℝ) < B_mid) ∨ (B_mid ≤ (x : ℝ) ∧ (x : ℝ) < B)
        constructor
        · intro ⟨hx1, hx2⟩
          rcases lt_or_ge (x : ℝ) B_mid with h | h
          · exact Or.inl ⟨hx1, h⟩
          · exact Or.inr ⟨h, hx2⟩
        · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
          · exact ⟨hx1, hx2.trans (by linarith)⟩
          · exact ⟨le_trans (by linarith) hx1, hx2⟩
      rw [← hpre]
      ext A hA
      rw [Measure.map_apply hEmb.measurable hA, Measure.restrict_apply (hEmb.measurable hA),
        Measure.restrict_apply hA, smul_apply, smul_eq_mul]
      simp only [ShellSetup.cm, smul_apply, smul_eq_mul]
      rw [← hρ_map, Measure.map_apply hEmb.measurable (hA.inter measurableSet_Ico), Set.preimage_inter]
    have hfloor_Ico : ENNReal.ofReal (W Mk) • volume.restrict (Ico B₀ B) ≤
        (ENNReal.ofReal (1 / 8 * S.δ) • atomRhoReal C a T).restrict (Ico B₀ B) := by
      refine Measure.le_iff.2 fun A hA => ?_
      rw [smul_apply, Measure.restrict_apply hA, Measure.restrict_apply hA, smul_apply, smul_eq_mul, smul_eq_mul]
      dsimp [atomRhoReal]
      rw [Measure.restrict_apply (hA.inter measurableSet_Ico),
        withDensity_apply _ ((hA.inter measurableSet_Ico).inter measurableSet_Ici)]
      calc ENNReal.ofReal (W Mk) * volume (A ∩ Ico B₀ B)
          = ∫⁻ _ in A ∩ Ico B₀ B, ENNReal.ofReal (W Mk) ∂volume := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ t in A ∩ Ico B₀ B, ENNReal.ofReal ((δ / 8) * C.src.cardyDensity a t) ∂volume := by
            refine setLIntegral_mono' (hA.inter measurableSet_Ico) fun t ht => ?_
            exact ENNReal.ofReal_le_ofReal (hMk_fl t ht.2.1)
        _ = ENNReal.ofReal (1 / 8 * S.δ) *
              ∫⁻ t in A ∩ Ico B₀ B ∩ Ici T, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
            have hint_eq : A ∩ Ico B₀ B ∩ Ici T = A ∩ Ico B₀ B :=
              Set.inter_eq_left.mpr (inter_subset_right.trans fun t ht => le_trans hB0_ge_T ht.1)
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
  have hfin_σ0 : IsFiniteMeasure σ₀ := ⟨by
    dsimp [σ₀]
    simp only [sum_apply, smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, mul_one]
    exact ENNReal.sum_lt_top.2 fun q _ => ENNReal.natCast_lt_top _⟩
  have hfin_σ0_real : IsFiniteMeasure σ₀_real := Measure.isFiniteMeasure_map σ₀ Subtype.val
  have hσ₀_atomic : ShellSetup.IsIntAtomicOn U₀ σ₀ :=
    ⟨κ, hκ_fin, fun q => ⟨t_at q, le_trans hB0_ge_T (ht_mem' q).1⟩, d_at,
      fun q => ⟨hd_pos q, ht_mem' q⟩, rfl⟩
  have hσ₀_real_eq : σ₀_real = ∑ q : κ, (d_at q : ℝ≥0∞) • Measure.dirac (t_at q) := by
    dsimp [σ₀_real, σ₀]
    ext A hA
    rw [Measure.map_apply hEmb.measurable hA]
    simp only [sum_apply, smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (hEmb.measurable hA), Measure.dirac_apply' _ hA]
    refine Finset.sum_congr rfl fun q _ => ?_
    rfl
  have hσ₀_real_supp : σ₀_real (Icc B₀ B)ᶜ = 0 := by
    rw [hσ₀_real_eq]
    simp only [sum_apply, smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Icc.compl]
    exact Finset.sum_eq_zero fun q _ => by simp [ht_mem' q]
  have hσ₀_real_mom : ∀ P : ℝ[X], P.degree ≤ Mk →
      ∫ s, P.eval s ∂σ₀_real = ∫ s, P.eval s ∂μ₀_real := by
    intro P hP
    have hmatchP := hmatch P hP
    have hLHS : ∫ s, P.eval s ∂σ₀_real = ∑ q : κ, (d_at q : ℝ) * P.eval (t_at q) := by
      rw [hσ₀_real_eq, integral_finsetSum_measure]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [integral_smul_measure, integral_dirac, ENNReal.toReal_natCast, smul_eq_mul]
      · intro q _
        exact (integrable_dirac' P.continuous.stronglyMeasurable
          (by simp)).smul_measure (ENNReal.natCast_ne_top _)
    rw [hLHS, hmatchP]
  have hμ₀_Uc : μ₀ U₀ᶜ = 0 :=
    measure_mono_null (show U₀ᶜ ⊆ (U₀ ∩ (S.shell j ∪ S.shell (j + 1)))ᶜ from fun _ hx hx' => hx hx'.1)
      hμ₀_supp
  have hμ₀_U0_univ : μ₀ U₀ = μ₀ univ := by
    calc μ₀ U₀ = μ₀ U₀ + 0 := (add_zero _).symm
      _ = μ₀ U₀ + μ₀ U₀ᶜ := by rw [hμ₀_Uc]
      _ = μ₀ univ := measure_add_measure_compl hU0_meas
  have hσ₀_mass_eq : σ₀ U₀ = μ₀ U₀ := by
    have h1 : (∑ q : κ, (d_at q : ℝ)) = (Ntot : ℝ) := by
      have hmatch1 := hmatch (Polynomial.C 1) (by simp)
      simp only [Polynomial.eval_C, mul_one, integral_const, smul_eq_mul,
        Measure.real_def, hμ₀_real_univ, ENNReal.toReal_natCast] at hmatch1
      exact hmatch1.symm
    have hsum_nat : (∑ q : κ, d_at q) = Ntot := by exact_mod_cast h1
    have hσ_U0 : σ₀ U₀ = (∑ q : κ, d_at q : ℕ) := by
      dsimp [σ₀]
      simp only [sum_apply, smul_apply, smul_eq_mul, Measure.dirac_apply' _ hU0_meas, Nat.cast_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hq : (⟨t_at q, le_trans hB0_ge_T (ht_mem' q).1⟩ : X) ∈ U₀ := ht_mem' q
      simp [hq]
    have hμ_U0 : μ₀ U₀ = Ntot := by rw [hμ₀_U0_univ, hμ₀_univ]
    rw [hσ_U0, hμ_U0, hsum_nat]
  obtain ⟨r, hr_cont, hr_cross, hr_bd⟩ :=
    hankel_repair C.src.hw hB0_pos hB0_lt_B Mk hσ₀_real_supp hμ₀_real_supp hσ₀_real_mom
  have hσ_univ_le : σ₀_real.real univ ≤ 9 / 8 * meas.ν.real (Icc T B) := by
    have hσ_eq_μ : σ₀_real univ = μ₀_real univ := by
      have h1 : σ₀_real univ = σ₀ U₀ := by
        rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, Set.preimage_univ]
        have hcomp : σ₀ U₀ᶜ = 0 := by
          dsimp [σ₀]
          simp only [sum_apply, smul_apply, smul_eq_mul, Measure.dirac_apply' _ hU0_meas.compl]
          exact Finset.sum_eq_zero fun q _ => by
            have hq : (⟨t_at q, le_trans hB0_ge_T (ht_mem' q).1⟩ : X) ∉ U₀ᶜ := fun h => h (ht_mem' q)
            simp [hq]
        rw [← measure_add_measure_compl hU0_meas, hcomp, add_zero]
      rw [h1, hσ₀_mass_eq, hμ₀_U0_univ]
      rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, Set.preimage_univ]
    have hμ_le_Ω : μ₀ univ ≤ lam (S.Ω (j + 2)) := by
      have hsub_sh : S.shell j ∪ S.shell (j + 1) ⊆ S.Ω (j + 2) := fun x hx => by
        rcases hx with h | h
        · exact S.Ω_mono (Nat.le_succ _) h.1
        · exact h.1
      have hcomp : μ₀ (S.Ω (j + 2))ᶜ = 0 := by
        refine measure_mono_null (fun _ hx => fun hmem => hx (hsub_sh hmem.2)) hμ₀_supp
      calc μ₀ univ = μ₀ (S.Ω (j + 2)) + μ₀ (S.Ω (j + 2))ᶜ :=
            (measure_add_measure_compl (S.Ω_open (j + 2)).measurableSet).symm
        _ = μ₀ (S.Ω (j + 2)) := by rw [hcomp, add_zero]
        _ ≤ lam (S.Ω (j + 2)) := Measure.le_iff.1 hμ₀_le_lam _ (S.Ω_open (j + 2)).measurableSet
    have hν_le : S.ν0 (S.Ω (j + 2)) ≤ meas.ν (Icc T B) := by
      have hm_sub : S.Ω (j + 2) ⊆ {x : X | (x : ℝ) ≤ B} := fun x hx => by
        have hxlt : (x : ℝ) < B := by simpa [S, atomShellSetup, B] using hx
        exact hxlt.le
      have hmeas_eq : S.ν0 {x : X | (x : ℝ) ≤ B} = meas.ν (Icc T B) := by
        rw [← hν0_map, Measure.map_apply hEmb.measurable measurableSet_Icc]
        congr 1; ext x; exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      rw [← hmeas_eq]
      exact measure_mono hm_sub
    have hfin_νB : meas.ν (Icc T B) ≠ ∞ := by
      have hmeas_eq : S.ν0 {x : X | (x : ℝ) ≤ B} = meas.ν (Icc T B) := by
        rw [← hν0_map, Measure.map_apply hEmb.measurable measurableSet_Icc]
        congr 1; ext x; exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      rw [← hmeas_eq]; exact (hν0_fin B).ne
    have hcomb : σ₀_real univ ≤ ENNReal.ofReal (9 / 8) * meas.ν (Icc T B) := by
      calc σ₀_real univ = μ₀_real univ := hσ_eq_μ
        _ = μ₀ univ := by rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, Set.preimage_univ]
        _ ≤ lam (S.Ω (j + 2)) := hμ_le_Ω
        _ ≤ ENNReal.ofReal (9 / 8) * S.ν0 (S.Ω (j + 2)) := hlam_Ω2_le
        _ ≤ ENNReal.ofReal (9 / 8) * meas.ν (Icc T B) := by gcongr
    have htoReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_lt_top.ne hfin_νB) hcomb
    simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 9 / 8)] using htoReal
  have hμ_univ_le : μ₀_real.real univ ≤ 9 / 8 * meas.ν.real (Icc T B) := by
    have h1 : σ₀_real univ = μ₀_real univ := by
      rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, Set.preimage_univ,
        Measure.map_apply hEmb.measurable MeasurableSet.univ, Set.preimage_univ]
      have hcomp : σ₀ U₀ᶜ = 0 := by
        dsimp [σ₀]
        simp only [sum_apply, smul_apply, smul_eq_mul, Measure.dirac_apply' _ hU0_meas.compl]
        exact Finset.sum_eq_zero fun q _ => by
          have hq : (⟨t_at q, le_trans hB0_ge_T (ht_mem' q).1⟩ : X) ∉ U₀ᶜ := fun h => h (ht_mem' q)
          simp [hq]
      rw [← measure_add_measure_compl hU0_meas, hcomp, add_zero, hσ₀_mass_eq, hμ₀_U0_univ]
    simpa [Measure.real, h1] using hσ_univ_le
  let r_pos : ℝ → ℝ := (Ioi B).piecewise (fun s => max (r s) 0) (fun _ => 0)
  let r_neg : ℝ → ℝ := (Ioi B).piecewise (fun s => max (-r s) 0) (fun _ => 0)
  have hr_pos_cont : ContinuousOn (fun s => max (r s) 0) (Ioi B) :=
    (continuous_id.max continuous_const).comp_continuousOn hr_cont
  have hr_neg_cont : ContinuousOn (fun s => max (-r s) 0) (Ioi B) :=
    (continuous_id.max continuous_const).comp_continuousOn hr_cont.neg
  have hr_pos_meas : Measurable (fun t : ℝ => ENNReal.ofReal (r_pos t)) :=
    (ContinuousOn.measurable_piecewise hr_pos_cont continuousOn_const measurableSet_Ioi).ennreal_ofReal
  have hr_neg_meas : Measurable (fun t : ℝ => ENNReal.ofReal (r_neg t)) :=
    (ContinuousOn.measurable_piecewise hr_neg_cont continuousOn_const measurableSet_Ioi).ennreal_ofReal
  have hr_pos_eq : ∀ {t : ℝ}, B < t → r_pos t = max (r t) 0 := fun {t} ht => by
    simp only [r_pos, Set.piecewise, Set.mem_Ioi, ht, ↓reduceIte]
  have hr_neg_eq : ∀ {t : ℝ}, B < t → r_neg t = max (-r t) 0 := fun {t} ht => by
    simp only [r_neg, Set.piecewise, Set.mem_Ioi, ht, ↓reduceIte]
  let Rp₀_real : Measure ℝ := (volume.withDensity fun t => ENNReal.ofReal (r_pos t)).restrict (Ioi B)
  let Rm₀_real : Measure ℝ := (volume.withDensity fun t => ENNReal.ofReal (r_neg t)).restrict (Ioi B)
  let Rp₀ : Measure X := Measure.comap Subtype.val Rp₀_real
  let Rm₀ : Measure X := Measure.comap Subtype.val Rm₀_real
  have hRp_map : Measure.map Subtype.val Rp₀ = Rp₀_real := by
    dsimp [Rp₀]
    rw [hEmb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun t ht => show T ≤ t by linarith [Set.mem_Ioi.mp ht])
  have hRm_map : Measure.map Subtype.val Rm₀ = Rm₀_real := by
    dsimp [Rm₀]
    rw [hEmb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun t ht => show T ≤ t by linarith [Set.mem_Ioi.mp ht])
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
      ext t
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨x, hx, rfl⟩, ht⟩
      have hxlt : (x : ℝ) < B := by simpa [S, atomShellSetup, B] using hx
      linarith
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
      ext t
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨x, hx, rfl⟩, ht⟩
      have hxlt : (x : ℝ) < B := by simpa [S, atomShellSetup, B] using hx
      linarith
    rw [hemp, measure_empty]
  have hr_abs_le : ∀ {t : ℝ}, B < t →
      |r t| ≤ (1 / 2 : ℝ) ^ (j + 4) * S.δ * C.src.cardyDensity a t := fun {t} ht => by
    have hMk_ord : (2 * ((9 * π + sonineRepairConst + 1) + 2)) *
        (a + (T + ((j + 2 : ℕ) : ℝ)) + Real.log (1 / δ) + (C.src.w : ℝ)) /
        Real.log (a * (T + (j : ℝ))) ≤ (Mk : ℝ) := by
      have hk_prev : ((k - 1 : ℕ) : ℝ) = (j : ℝ) := rfl
      have hk_next : ((k + 1 : ℕ) : ℝ) = ((j + 2 : ℕ) : ℝ) := rfl
      have h0 := hM_ord k hk1
      rwa [hk_prev, hk_next] at h0
    exact atom_tail_r_bound C hc_vac_pos ha24 hrho_lb hT hδ0 hδ1 meas hcount_fn ha_const
      hMk_ord hσ_univ_le hμ_univ_le hr_bd ht
  have hR_le : Rp₀ + Rm₀ ≤ S.cm ((1 / 2 : ℝ) ^ (j + 4)) := by
    have hreal_le : Rp₀_real + Rm₀_real ≤
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) • atomRhoReal C a T) := by
      refine Measure.le_iff.2 fun A hA => ?_
      have hr_max_sum : ∀ t : ℝ, max (r t) 0 + max (-r t) 0 = |r t| := fun t => by
        rcases le_total 0 (r t) with h | h
        · simp [h, abs_of_nonneg h]
        · simp [h, abs_of_nonpos h]
      dsimp [Rp₀_real, Rm₀_real, atomRhoReal]
      simp only [add_apply, smul_apply, smul_eq_mul, Measure.restrict_apply hA,
        withDensity_apply _ (hA.inter measurableSet_Ioi)]
      rw [← lintegral_add_left hr_pos_meas]
      have hlin : ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal (r_pos t) + ENNReal.ofReal (r_neg t) ∂volume =
          ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal |r t| ∂volume := by
        refine setLIntegral_congr_fun (hA.inter measurableSet_Ioi) fun t ht => ?_
        have hBt : B < t := ht.2
        rw [hr_pos_eq hBt, hr_neg_eq hBt, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
          hr_max_sum]
      rw [hlin, withDensity_apply _ (hA.inter measurableSet_Ici)]
      calc ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal |r t| ∂volume
          ≤ ∫⁻ t in A ∩ Ioi B,
              ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ * C.src.cardyDensity a t) ∂volume := by
            refine setLIntegral_mono' (hA.inter measurableSet_Ioi) fun t ht => ?_
            exact ENNReal.ofReal_le_ofReal (hr_abs_le (Set.mem_Ioi.mp ht.2))
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) *
              ∫⁻ t in A ∩ Ioi B, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
            have heq : (fun t => ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ * C.src.cardyDensity a t)) =
                fun t => ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) * ENNReal.ofReal (C.src.cardyDensity a t) := by
              ext t; exact ENNReal.ofReal_mul (mul_nonneg (by positivity) S.δ_pos.le)
            rw [heq, lintegral_const_mul _ hm_dens]
        _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) *
              ∫⁻ t in A ∩ Ici T, ENNReal.ofReal (C.src.cardyDensity a t) ∂volume := by
            gcongr
            have hsub_BI : Ioi B ⊆ Ici T := fun t ht => by
              change T ≤ t
              have hBt : B < t := Set.mem_Ioi.mp ht
              have hj2_nn : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by positivity
              dsimp [B] at hBt; linarith
            exact hsub_BI
    refine Measure.le_iff.2 fun A hA => ?_
    have hA_val : MeasurableSet (Subtype.val '' A) := hEmb.measurableSet_image.2 hA
    have h1 : (Rp₀ + Rm₀) A = (Rp₀_real + Rm₀_real) (Subtype.val '' A) := by
      simp only [add_apply]
      have hp : Rp₀ A = Rp₀_real (Subtype.val '' A) := by
        rw [← hRp_map, Measure.map_apply hEmb.measurable hA_val]; congr 1
        exact (Subtype.val_injective.preimage_image A).symm
      have hm : Rm₀ A = Rm₀_real (Subtype.val '' A) := by
        rw [← hRm_map, Measure.map_apply hEmb.measurable hA_val]; congr 1
        exact (Subtype.val_injective.preimage_image A).symm
      rw [hp, hm]
    have h2 : S.cm ((1 / 2 : ℝ) ^ (j + 4)) A =
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 4) * S.δ) • atomRhoReal C a T) (Subtype.val '' A) := by
      simp only [ShellSetup.cm, smul_apply, smul_eq_mul]
      congr 1
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
      have h2eq : -2 * π * t / β.1 = -2 * π * β.1⁻¹ * t := by ring
      rw [h2eq] at h1 ⊢
      rwa [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg (Real.rpow_nonneg β.2.le _),
        abs_of_pos (Real.exp_pos _)] at h1
    have hr_int1 := (hr_cross β.2).1
    have hr_int2 := (hr_cross (inv_pos.mpr β.2)).1
    have hK_r_int : IntegrableOn (fun t => thermalDiff C.src.w β.1 t * r t) (Ioi B) := by
      have hdom : IntegrableOn (fun t =>
          Real.exp (-2 * π * β.1 * t) * |r t| +
            β.1 ^ (-(C.src.w : ℝ)) * (Real.exp (-2 * π * β.1⁻¹ * t) * |r t|)) (Ioi B) :=
        hr_int1.add (hr_int2.const_mul _)
      refine hdom.mono' (hcK.aestronglyMeasurable.mul
        (hr_cont.aestronglyMeasurable measurableSet_Ioi)) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun t ht => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |thermalDiff C.src.w β.1 t| * |r t|
          ≤ (Real.exp (-2 * π * β.1 * t) + β.1 ^ (-(C.src.w : ℝ)) * Real.exp (-2 * π * β.1⁻¹ * t)) * |r t| :=
            mul_le_mul_of_nonneg_right (hK_bd (Set.mem_Ioi.mp ht)) (abs_nonneg _)
        _ = Real.exp (-2 * π * β.1 * t) * |r t| +
              β.1 ^ (-(C.src.w : ℝ)) * (Real.exp (-2 * π * β.1⁻¹ * t) * |r t|) := by ring
    have hrestrict_wd : ∀ (f : ℝ → ℝ≥0∞),
        (volume.withDensity f).restrict (Ioi B) = (volume.restrict (Ioi B)).withDensity f := by
      intro f
      ext A hA
      rw [Measure.restrict_apply hA, withDensity_apply _ (hA.inter measurableSet_Ioi),
        withDensity_apply _ hA, Measure.restrict_restrict hA, Set.inter_comm]
    have hp_int_real : Integrable (fun t => thermalDiff C.src.w β.1 t) Rp₀_real := by
      dsimp [Rp₀_real]
      rw [hrestrict_wd, integrable_withDensity_iff_integrable_smul' hr_pos_meas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine hK_r_int.abs.mono'
        (hr_pos_meas.ennreal_toReal.aestronglyMeasurable.smul hcK.aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun t ht => ?_
      have hrp_nn : 0 ≤ r_pos t := by rw [hr_pos_eq ht]; exact le_max_right _ _
      calc ‖(ENNReal.ofReal (r_pos t)).toReal • thermalDiff C.src.w β.1 t‖
          = r_pos t * |thermalDiff C.src.w β.1 t| := by
            rw [smul_eq_mul, ENNReal.toReal_ofReal hrp_nn, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg hrp_nn]
        _ = |thermalDiff C.src.w β.1 t| * max (r t) 0 := by rw [hr_pos_eq ht, mul_comm]
        _ ≤ |thermalDiff C.src.w β.1 t| * |r t| :=
            mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (abs_nonneg _)
        _ = |thermalDiff C.src.w β.1 t * r t| := (abs_mul _ _).symm
    have hm_int_real : Integrable (fun t => thermalDiff C.src.w β.1 t) Rm₀_real := by
      dsimp [Rm₀_real]
      rw [hrestrict_wd, integrable_withDensity_iff_integrable_smul' hr_neg_meas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine hK_r_int.abs.mono'
        (hr_neg_meas.ennreal_toReal.aestronglyMeasurable.smul hcK.aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun t ht => ?_
      have hrm_nn : 0 ≤ r_neg t := by rw [hr_neg_eq ht]; exact le_max_right _ _
      calc ‖(ENNReal.ofReal (r_neg t)).toReal • thermalDiff C.src.w β.1 t‖
          = r_neg t * |thermalDiff C.src.w β.1 t| := by
            rw [smul_eq_mul, ENNReal.toReal_ofReal hrm_nn, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg hrm_nn]
        _ = |thermalDiff C.src.w β.1 t| * max (-r t) 0 := by rw [hr_neg_eq ht, mul_comm]
        _ ≤ |thermalDiff C.src.w β.1 t| * |r t| :=
            mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _)) (abs_nonneg _)
        _ = |thermalDiff C.src.w β.1 t * r t| := (abs_mul _ _).symm
    have hRp_int_eq : ∫ x, S.K β x ∂Rp₀ =
        ∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (r t) 0 := by
      have h1 : ∫ x, S.K β x ∂Rp₀ = ∫ t, thermalDiff C.src.w β.1 t ∂Rp₀_real := by
        rw [← hRp_map, integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]
        rfl
      rw [h1]
      dsimp [Rp₀_real]
      rw [hrestrict_wd, integral_withDensity_eq_integral_toReal_smul hr_pos_meas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have hrp_nn : 0 ≤ r_pos t := by rw [hr_pos_eq ht]; exact le_max_right _ _
      rw [smul_eq_mul, ENNReal.toReal_ofReal hrp_nn, hr_pos_eq ht, mul_comm]
    have hRm_int_eq : ∫ x, S.K β x ∂Rm₀ =
        ∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (-r t) 0 := by
      have h1 : ∫ x, S.K β x ∂Rm₀ = ∫ t, thermalDiff C.src.w β.1 t ∂Rm₀_real := by
        rw [← hRm_map, integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]
        rfl
      rw [h1]
      dsimp [Rm₀_real]
      rw [hrestrict_wd, integral_withDensity_eq_integral_toReal_smul hr_neg_meas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have hrm_nn : 0 ≤ r_neg t := by rw [hr_neg_eq ht]; exact le_max_right _ _
      rw [smul_eq_mul, ENNReal.toReal_ofReal hrm_nn, hr_neg_eq ht, mul_comm]
    have hσ_eq : ∫ x, S.K β x ∂σ₀ = ∫ s, thermalDiff C.src.w β.1 s ∂σ₀_real := by
      dsimp [σ₀_real]
      rw [integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]; rfl
    have hμ_eq : ∫ x, S.K β x ∂μ₀ = ∫ s, thermalDiff C.src.w β.1 s ∂μ₀_real := by
      dsimp [μ₀_real]
      rw [integral_map hEmb.measurable.aemeasurable hcK.aestronglyMeasurable]; rfl
    have hrp_int : IntegrableOn (fun t => thermalDiff C.src.w β.1 t * max (r t) 0) (Ioi B) := by
      have hp' : Integrable (fun x => (ENNReal.ofReal (r_pos x)).toReal • thermalDiff C.src.w β.1 x)
          (volume.restrict (Ioi B)) := by
        have hp2 := hp_int_real
        dsimp [Rp₀_real] at hp2
        rwa [hrestrict_wd, integrable_withDensity_iff_integrable_smul' hr_pos_meas
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hp2
      refine hp'.congr ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
      have hrp_nn : 0 ≤ r_pos t := by rw [hr_pos_eq ht]; exact le_max_right _ _
      dsimp only
      rw [smul_eq_mul, ENNReal.toReal_ofReal hrp_nn, hr_pos_eq ht, mul_comm]
    have hrm_int : IntegrableOn (fun t => thermalDiff C.src.w β.1 t * max (-r t) 0) (Ioi B) := by
      have hm' : Integrable (fun x => (ENNReal.ofReal (r_neg x)).toReal • thermalDiff C.src.w β.1 x)
          (volume.restrict (Ioi B)) := by
        have hm2 := hm_int_real
        dsimp [Rm₀_real] at hm2
        rwa [hrestrict_wd, integrable_withDensity_iff_integrable_smul' hr_neg_meas
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hm2
      refine hm'.congr ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
      have hrm_nn : 0 ≤ r_neg t := by rw [hr_neg_eq ht]; exact le_max_right _ _
      dsimp only
      rw [smul_eq_mul, ENNReal.toReal_ofReal hrm_nn, hr_neg_eq ht, mul_comm]
    have hsub_r : (∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (r t) 0) -
          (∫ t in Ioi B, thermalDiff C.src.w β.1 t * max (-r t) 0) =
        ∫ t in Ioi B, thermalDiff C.src.w β.1 t * r t := by
      have hsub_eq := (integral_sub hrp_int hrm_int).symm
      rw [hsub_eq]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rcases le_total 0 (r t) with h | h <;> simp [h]
    have h_comb : ∫ s, thermalDiff C.src.w β.1 s ∂σ₀_real -
          ∫ s, thermalDiff C.src.w β.1 s ∂μ₀_real +
          ∫ t in Ioi B, thermalDiff C.src.w β.1 t * r t = 0 := (hr_cross β.2).2
    rw [← hsub_r] at h_comb
    rw [hσ_eq, hμ_eq, hRp_int_eq, hRm_int_eq]
    linarith
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
        dsimp [S, atomShellSetup]
        have hx_ge : B₀ ≤ x.1 := hx.1
        have hy_le : y.1 ≤ B := hy.2
        have hexp_le : Real.exp (-2 * π * γ.1 * x.1) ≤ Real.exp (4 * π * γ.1) * Real.exp (-2 * π * γ.1 * y.1) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hdiff : y.1 - x.1 ≤ 2 := by
            have hx0 : B₀ = T + (j : ℝ) := rfl
            have hy0 : B = T + ((j + 2 : ℕ) : ℝ) := rfl
            have hcast : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
            linarith
          have hpiγ : 0 ≤ 2 * π * γ.1 := mul_nonneg (by positivity) γ.2.le
          have hmul := mul_le_mul_of_nonneg_left hdiff hpiγ
          linarith
        exact hexp_le }

end FormalResearch.ModularBootstrap.Integrality
