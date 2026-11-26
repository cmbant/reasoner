module

public import FormalResearch.ModularBootstrap.Spin.SpinDLPi
public import FormalResearch.ModularBootstrap.LP.PolyCompact
public import FormalResearch.ModularBootstrap.LP.Continuation
public import FormalResearch.ModularBootstrap.LP.Reference

/-!
# Theorem LP-R (`dsl:reserve`) at `d = 2`: exact derivative separation and reserve

Proves `dslReserve : DslReserve` (`dual_spectrum_limit.tex`, Theorem LP-R `dsl:reserve`,
stated in `Spin/SpinDStatements.lean`): for `a ≥ 2`, `B ≥ 0`, `T₀ > 0`, `0 < s < 1`, closed
swap-invariant `X ⊆ E_B ∩ {t_L + t_R ≥ T₀}`, and a swap-invariant positive measure `σ` carried by
`X` with `∫ e^{-2π s (t_L + t_R)} dσ < ∞`, there exists a swap-invariant crossing measure `ν ≥ σ`
on `X` iff
```
∀ N q, q ∈ spinOddLagPolySpace N → (∀ p ∈ X, 0 ≤ q p) →
  ∫ p, exp(-2π (p.1 + p.2)) * q p ∂σ ≤ -spinVacT a (fun p => exp(-2π (p.1 + p.2)) * q p).
```
Uses `LP.poly_compact_invariant` (with the general odd-target hypothesis `|L v| ≤ (C₂ j)^j`),
`LP.positive_ray`, `LP.ds_cont`, `spin_tensor_cayley_iff`, and 2D real-analytic continuation.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Finset ProbabilityTheory
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP

/-! ### Section 1: Forward direction (`⇒`) -/

private theorem dslReserve_forward {a B : ℝ} (ha : 2 ≤ a) (hB : 0 ≤ B)
    {X : Set (ℝ × ℝ)} (hXB : X ⊆ spinConeB B)
    {σ : Measure (ℝ × ℝ)} (hσsupp : σ Xᶜ = 0)
    (meas : SpinCrossingMeasureOn a X) (hσle : σ ≤ meas.ν) :
    ∀ N q, q ∈ spinOddLagPolySpace N → (∀ p ∈ X, 0 ≤ q p) →
      ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * q p ∂σ ≤
        -spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p) := by
  intro N q hq hqnn
  obtain ⟨hint_ν, hpair⟩ := spin_oddLagPoly_pairing ha hB hXB meas hq
  rw [← hpair]
  set f : ℝ × ℝ → ℝ := fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p
  have hf_nn_ν : ∀ᵐ p ∂meas.ν, 0 ≤ f p := by
    have : ∀ᵐ p ∂meas.ν, p ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 meas.supp
    filter_upwards [this] with p hp using mul_nonneg (Real.exp_pos _).le (hqnn p (not_not.mp hp))
  have hf_nn_σ : ∀ᵐ p ∂σ, 0 ≤ f p := by
    have : ∀ᵐ p ∂σ, p ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hσsupp
    filter_upwards [this] with p hp using mul_nonneg (Real.exp_pos _).le (hqnn p (not_not.mp hp))
  have hint_σ : Integrable f σ := hint_ν.mono_measure hσle
  have hlint : ∫⁻ p, ENNReal.ofReal (f p) ∂σ ≤ ∫⁻ p, ENNReal.ofReal (f p) ∂meas.ν :=
    lintegral_mono' hσle le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hint_σ hf_nn_σ,
      ← ofReal_integral_eq_lintegral_ofReal hint_ν hf_nn_ν] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hf_nn_ν)).1 hlint

/-! ### Section 2: Shared helpers for `d = 2` continuous odd-Laguerre spaces and 2D continuation -/

private noncomputable def spinD2LagPolyBasisC (m n : ℕ) : C(ℝ × ℝ, ℝ) :=
  ⟨spinOddLagPolyBasis m n, by
    unfold spinOddLagPolyBasis
    exact continuous_const.mul
      ((((continuous_lagL (1 / 2) m).comp (continuous_const.mul continuous_fst)).mul
        ((continuous_lagL (1 / 2) n).comp (continuous_const.mul continuous_snd))).add
       (((continuous_lagL (1 / 2) m).comp (continuous_const.mul continuous_snd)).mul
        ((continuous_lagL (1 / 2) n).comp (continuous_const.mul continuous_fst))))⟩

private def spinD2QC (N : ℕ) : Submodule ℝ C(ℝ × ℝ, ℝ) :=
  Submodule.span ℝ {f | ∃ m n : ℕ, Odd (m + n) ∧ m + n ≤ N ∧ f = spinD2LagPolyBasisC m n}

private def spinD2QCall : Submodule ℝ C(ℝ × ℝ, ℝ) :=
  Submodule.span ℝ {f | ∃ m n : ℕ, Odd (m + n) ∧ f = spinD2LagPolyBasisC m n}

private lemma spinD2QC_mono {M N : ℕ} (h : M ≤ N) : spinD2QC M ≤ spinD2QC N :=
  Submodule.span_mono fun _ ⟨m, n, hmn, hle, hf⟩ => ⟨m, n, hmn, hle.trans h, hf⟩

private lemma spinD2QC_le_all (N : ℕ) : spinD2QC N ≤ spinD2QCall :=
  Submodule.span_mono fun _ ⟨m, n, hmn, _, hf⟩ => ⟨m, n, hmn, hf⟩

private lemma exists_N_of_mem_spinD2QCall {f : C(ℝ × ℝ, ℝ)} (hf : f ∈ spinD2QCall) :
    ∃ N : ℕ, f ∈ spinD2QC N := by
  unfold spinD2QCall at hf
  refine Submodule.span_induction (p := fun f _ => ∃ N, f ∈ spinD2QC N) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨m, n, hmn, rfl⟩
    exact ⟨m + n, Submodule.subset_span ⟨m, n, hmn, le_rfl, rfl⟩⟩
  · exact ⟨0, Submodule.zero_mem _⟩
  · rintro f g _ _ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, Submodule.add_mem _ (spinD2QC_mono (le_max_left _ _) h₁)
      (spinD2QC_mono (le_max_right _ _) h₂)⟩
  · rintro c f _ ⟨N, h⟩
    exact ⟨N, Submodule.smul_mem _ c h⟩

private lemma coe_mem_spinOddLagPolySpace' {N : ℕ} {f : C(ℝ × ℝ, ℝ)} (hf : f ∈ spinD2QC N) :
    (f : ℝ × ℝ → ℝ) ∈ spinOddLagPolySpace N := by
  unfold spinD2QC at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨m, n, hmn, hle, rfl⟩ := hg
    exact Submodule.subset_span ⟨m, n, hmn, hle, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

private lemma spinD2QCall_swap_symm {f : C(ℝ × ℝ, ℝ)} (hf : f ∈ spinD2QCall) (p : ℝ × ℝ) :
    f p.swap = f p := by
  unfold spinD2QCall at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨m, n, -, rfl⟩ := hg
    dsimp [spinD2LagPolyBasisC, spinOddLagPolyBasis, Prod.swap]; ring
  | zero => simp
  | add f g _ _ hf hg => simp [hf, hg]
  | smul c f _ hf => simp [hf]

private lemma lagL_poly_growth' (w : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |lagL w k x| ≤ C * (1 + |x|) ^ k := by
  refine ⟨∑ j ∈ Finset.range (k + 1), |(-1 : ℝ) ^ j * lagCoef w j (k - j) / (j.factorial : ℝ)|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x => ?_⟩
  rw [lagL_eq_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |x| ^ j ≤ (1 + |x|) ^ j := pow_le_pow_left₀ (abs_nonneg _) (by linarith) j
    _ ≤ (1 + |x|) ^ k := pow_le_pow_right₀ (by linarith [abs_nonneg x]) hjk

private lemma spinD2QC_growth {B : ℝ} (hB : 0 ≤ B) (N : ℕ) {f : C(ℝ × ℝ, ℝ)} (hf : f ∈ spinD2QC N) :
    ∃ C : ℝ, ∀ p ∈ spinConeB B, 0 ≤ p.1 + p.2 → |f p| ≤ C * (1 + (p.1 + p.2)) ^ N := by
  unfold spinD2QC at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨m, n, -, hle, rfl⟩ := hg
    obtain ⟨C₁, hC₁_nn, hC₁⟩ := lagL_poly_growth' (1 / 2) m
    obtain ⟨C₂, hC₂_nn, hC₂⟩ := lagL_poly_growth' (1 / 2) n
    set K : ℝ := max 1 (4 * π * (1 + 2 * B)) with hK
    have hK_ge1 : 1 ≤ K := le_max_left _ _
    refine ⟨C₁ * C₂ * K ^ (m + n), fun p hp hsum => ?_⟩
    have hcoord : ∀ u : ℝ, -B ≤ u → u ≤ p.1 + p.2 + B → 1 + |4 * π * u| ≤ K * (1 + (p.1 + p.2)) := by
      intro u hu1 hu2
      have habs : |u| ≤ (p.1 + p.2) + B := abs_le.mpr ⟨by linarith, hu2⟩
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
      have h4pi : 4 * π * |u| ≤ 4 * π * ((p.1 + p.2) + B) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      have h1 : 1 + 4 * π * ((p.1 + p.2) + B) ≤ 4 * π * (1 + 2 * B) * (1 + (p.1 + p.2)) := by
        have hpi : (1 : ℝ) ≤ 4 * π := by linarith [Real.pi_gt_three]
        have hBs : 0 ≤ B * (p.1 + p.2) := mul_nonneg hB hsum
        nlinarith [Real.pi_pos]
      have h2 : 4 * π * (1 + 2 * B) ≤ K := le_max_right _ _
      nlinarith
    have hu1 : 1 + |4 * π * p.1| ≤ K * (1 + (p.1 + p.2)) := hcoord p.1 hp.1 (by linarith [hp.2])
    have hu2 : 1 + |4 * π * p.2| ≤ K * (1 + (p.1 + p.2)) := hcoord p.2 hp.2 (by linarith [hp.1])
    have hterm : ∀ (a b : ℝ), 1 + |4 * π * a| ≤ K * (1 + (p.1 + p.2)) →
        1 + |4 * π * b| ≤ K * (1 + (p.1 + p.2)) →
        |lagL (1 / 2) m (4 * π * a) * lagL (1 / 2) n (4 * π * b)| ≤
          C₁ * C₂ * K ^ (m + n) * (1 + (p.1 + p.2)) ^ N := by
      intro a b ha hb
      rw [abs_mul]
      have h1 := (hC₁ (4 * π * a)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha m) hC₁_nn)
      have h2 := (hC₂ (4 * π * b)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb n) hC₂_nn)
      have hprod := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      have hpow : (K * (1 + (p.1 + p.2))) ^ m * (K * (1 + (p.1 + p.2))) ^ n =
          K ^ (m + n) * (1 + (p.1 + p.2)) ^ (m + n) := by
        rw [← pow_add, mul_pow]
      have hpowN : (1 + (p.1 + p.2)) ^ (m + n) ≤ (1 + (p.1 + p.2)) ^ N :=
        pow_le_pow_right₀ (by linarith) hle
      calc |lagL (1 / 2) m (4 * π * a)| * |lagL (1 / 2) n (4 * π * b)|
          ≤ C₁ * (K * (1 + (p.1 + p.2))) ^ m * (C₂ * (K * (1 + (p.1 + p.2))) ^ n) := hprod
        _ = C₁ * C₂ * ((K * (1 + (p.1 + p.2))) ^ m * (K * (1 + (p.1 + p.2))) ^ n) := by ring
        _ = C₁ * C₂ * (K ^ (m + n) * (1 + (p.1 + p.2)) ^ (m + n)) := by rw [hpow]
        _ ≤ C₁ * C₂ * (K ^ (m + n) * (1 + (p.1 + p.2)) ^ N) := by gcongr
        _ = C₁ * C₂ * K ^ (m + n) * (1 + (p.1 + p.2)) ^ N := by ring
    dsimp only [spinD2LagPolyBasisC, ContinuousMap.coe_mk, spinOddLagPolyBasis]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htri := abs_add_le
      (lagL (1 / 2) m (4 * π * p.1) * lagL (1 / 2) n (4 * π * p.2))
      (lagL (1 / 2) m (4 * π * p.2) * lagL (1 / 2) n (4 * π * p.1))
    linarith [hterm p.1 p.2 hu1 hu2, hterm p.2 p.1 hu2 hu1]
  | zero => exact ⟨0, fun p _ _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨C₁, h₁⟩ := hf
    obtain ⟨C₂, h₂⟩ := hg
    refine ⟨C₁ + C₂, fun p hp hsum => ?_⟩
    calc |(f + g) p| ≤ |f p| + |g p| := abs_add_le _ _
      _ ≤ C₁ * (1 + (p.1 + p.2)) ^ N + C₂ * (1 + (p.1 + p.2)) ^ N := add_le_add (h₁ p hp hsum) (h₂ p hp hsum)
      _ = (C₁ + C₂) * (1 + (p.1 + p.2)) ^ N := by ring
  | smul c f _ hf =>
    obtain ⟨C, hC⟩ := hf
    refine ⟨|c| * C, fun p hp hsum => ?_⟩
    show |c * f p| ≤ |c| * C * (1 + (p.1 + p.2)) ^ N
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC p hp hsum) (abs_nonneg c)

private lemma spinD2_lagPC_add_mem_QC {k N : ℕ} (hk : Odd k) (hkN : k ≤ N) :
    ((lagPC 1 k).comp ⟨fun p : ℝ × ℝ => p.1 + p.2, continuous_fst.add continuous_snd⟩) ∈ spinD2QC N := by
  have hfn : (fun p : ℝ × ℝ => lagL 1 k (4 * π * (p.1 + p.2))) =
      fun p => (∑ i ∈ Finset.range (k + 1), spinD2LagPolyBasisC i (k - i)) p := by
    ext p
    rw [ContinuousMap.coe_sum, Finset.sum_apply, show (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) by norm_num,
      show 4 * π * (p.1 + p.2) = 4 * π * p.1 + 4 * π * p.2 by ring,
      spin_lagL_add (by norm_num) (by norm_num)]
    have hrefl : ∑ i ∈ Finset.range (k + 1),
        lagL (1 / 2) i (4 * π * p.2) * lagL (1 / 2) (k - i) (4 * π * p.1) =
        ∑ i ∈ Finset.range (k + 1),
        lagL (1 / 2) i (4 * π * p.1) * lagL (1 / 2) (k - i) (4 * π * p.2) := by
      rw [← Finset.sum_range_reflect (fun i => lagL (1 / 2) i (4 * π * p.2) * lagL (1 / 2) (k - i) (4 * π * p.1)) (k + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show k + 1 - 1 - i = k - i by omega, show k - (k - i) = i by omega, mul_comm]
    have hsum_basis : ∑ i ∈ Finset.range (k + 1), spinD2LagPolyBasisC i (k - i) p =
        (1 / 2 : ℝ) * ((∑ i ∈ Finset.range (k + 1),
            lagL (1 / 2) i (4 * π * p.1) * lagL (1 / 2) (k - i) (4 * π * p.2)) +
          (∑ i ∈ Finset.range (k + 1),
            lagL (1 / 2) i (4 * π * p.2) * lagL (1 / 2) (k - i) (4 * π * p.1))) := by
      dsimp only [spinD2LagPolyBasisC, ContinuousMap.coe_mk, spinOddLagPolyBasis]
      rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hsum_basis, hrefl]; ring
  have heq : ((lagPC 1 k).comp ⟨fun p : ℝ × ℝ => p.1 + p.2, continuous_fst.add continuous_snd⟩) =
      ((-1 : ℝ) ^ k * (k.factorial : ℝ) / (4 * π) ^ k) •
        (∑ i ∈ Finset.range (k + 1), spinD2LagPolyBasisC i (k - i)) := by
    ext p
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, lagPC_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [lagP_eq, congrFun hfn p]
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => ?_)
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Submodule.subset_span ⟨i, k - i, by rwa [Nat.add_sub_cancel' hik], by omega, rfl⟩

private lemma spinD2_isProperMap_sum_on_coneB {B : ℝ} {X : Set (ℝ × ℝ)}
    (hXc : IsClosed X) (hXB : X ⊆ spinConeB B) :
    IsProperMap (fun x : X => x.1.1 + x.1.2) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(continuous_fst.add continuous_snd).comp continuous_subtype_val, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hcl : IsClosed ((fun x : X => x.1.1 + x.1.2) ⁻¹' K) :=
    hK.isClosed.preimage ((continuous_fst.add continuous_snd).comp continuous_subtype_val)
  have hbox_cpt : IsCompact (Icc (-B) (|R| + B) ×ˢ Icc (-B) (|R| + B)) :=
    isCompact_Icc.prod isCompact_Icc
  have hpre_cpt : IsCompact ((Subtype.val : X → ℝ × ℝ) ⁻¹' (Icc (-B) (|R| + B) ×ˢ Icc (-B) (|R| + B))) :=
    hXc.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hbox_cpt
  refine hpre_cpt.of_isClosed_subset hcl fun x hx => ?_
  have hmem : x.1.1 + x.1.2 ∈ Metric.closedBall (0 : ℝ) R := hR hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  have hsum_le : x.1.1 + x.1.2 ≤ |R| := (le_abs_self _).trans (hmem.trans (le_abs_self R))
  have hxB := hXB x.2
  exact ⟨⟨hxB.1, by linarith [hxB.2]⟩, ⟨hxB.2, by linarith [hxB.1]⟩⟩

private lemma spinD2_vac_lagPC_eq_refMeas {a : ℝ} (ha : 2 ≤ a) {k : ℕ} (hk : Odd k) :
    -spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 k (p.1 + p.2)) =
      ∫ s, lagP 1 k s ∂refMeas virasoroProblem a := by
  let g : ℝ → ℝ := fun s => Real.exp (-2 * π * s) * lagP 1 k s
  have hg_eq : spinLiftTToR (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 k (p.1 + p.2)) =
      spinRadialLift g := by
    ext r; unfold spinLiftTToR spinRadialLift; dsimp only [g]
    rw [show r.1 ^ 2 / 2 + r.2 ^ 2 / 2 = (r.1 ^ 2 + r.2 ^ 2) / 2 by ring]
  have hW_cont : Continuous (fun p : ℝ × ℝ => spinV1 a p.1 * spinV1 a p.2) := by
    have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact (hV1.comp continuous_fst).mul (hV1.comp continuous_snd)
  have hW_avg : ∀ {t : ℝ}, 0 < t →
      ∫ ψ in (0 : ℝ)..(2 * π),
        spinV1 a (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ)) *
          spinV1 a (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ)) =
        virasoroProblem.cardyDensity a t := by
    intro t ht
    have h := spinV2Harmonic_zero_eq_cardyDensity ha ht.le
    unfold spinV2Harmonic at h; simpa using h
  have hW_nn : ∀ p : ℝ × ℝ, 0 ≤ spinV1 a p.1 * spinV1 a p.2 := fun p =>
    mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)
  have hW₀_cont : ContinuousOn (virasoroProblem.cardyDensity a) (Ioi 0) :=
    (continuous_const.mul (continuous_cardyV virasoroProblem a)).continuousOn
  have h_int_ref : Integrable (fun s => |lagP 1 k s|) (refMeas virasoroProblem a) := by
    have hw : (virasoroProblem.w : ℝ) = 1 := by simp [virasoroProblem_w]
    have hmem : lagP 1 k ∈ oddSpan (virasoroProblem.w : ℝ) k := by
      rw [hw]; exact lagP_mem_oddSpan 1 hk le_rfl
    exact (integrable_oddSpan_ref (prob := virasoroProblem)
      (by rw [virasoroProblem_totalShift]; exact ha) hmem).abs
  have h_int_on : IntegrableOn (fun s => |g s| * virasoroProblem.cardyDensity a s) (Ioi 0) := by
    rw [integrable_refMeas_iff (prob := virasoroProblem) (by rw [virasoroProblem_totalShift]; exact ha)] at h_int_ref
    refine h_int_ref.congr_fun (fun s _ => ?_) measurableSet_Ioi
    dsimp only [g]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]; ring
  have hg_cont : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (continuous_lagP 1 k)
  have h_abs_int : Integrable (fun p : ℝ × ℝ =>
      |g ((p.1 ^ 2 + p.2 ^ 2) / 2)| * (spinV1 a p.1 * spinV1 a p.2)) :=
    (spin_polar_integrable_iff (f := fun s => |g s|) hg_cont.abs.continuousOn
      (fun _ _ => abs_nonneg _) hW_cont hW_nn hW₀_cont (fun ht => hW_avg ht)).mpr h_int_on
  have h_int : Integrable (fun p : ℝ × ℝ =>
      g ((p.1 ^ 2 + p.2 ^ 2) / 2) * (spinV1 a p.1 * spinV1 a p.2)) := by
    refine h_abs_int.mono'
      ((hg_cont.comp (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)).mul hW_cont).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW_nn p)])
  unfold spinVacT spinPhiVac
  rw [hg_eq, neg_neg]
  have h1 : ∫ p : ℝ × ℝ, spinRadialLift g p * spinV1 a p.1 * spinV1 a p.2 =
      ∫ p : ℝ × ℝ, g ((p.1 ^ 2 + p.2 ^ 2) / 2) * (spinV1 a p.1 * spinV1 a p.2) :=
    integral_congr_ae (Eventually.of_forall fun p => by unfold spinRadialLift; ring)
  rw [h1, spin_polar_integral_eq (g := g) hW_cont (fun ht => hW_avg ht) h_int,
    integral_refMeas (prob := virasoroProblem) (by rw [virasoroProblem_totalShift]; exact ha)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by dsimp only [g]; ring

private lemma spinD2_joint_laplace_integrable {B : ℝ} (hB : 0 ≤ B) {ν : Measure (ℝ × ℝ)}
    (hν : ν (spinConeB B)ᶜ = 0)
    (hdiag : ∀ β : ℝ, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (βL * p.1 + βR * p.2))) ν := by
  have hae : ∀ᵐ p ∂ν, p ∈ spinConeB B := by
    have : ∀ᵐ p ∂ν, p ∉ (spinConeB B)ᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with p hp using not_not.mp hp
  have hmin : 0 < min βL βR := lt_min hβL hβR
  refine Integrable.mono' ((hdiag _ hmin).const_mul (Real.exp (2 * π * B * (βL + βR - 2 * min βL βR))))
    (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-2 * π * (βL * p.1 + βR * p.2))).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact spin_exp_dom_coneB hB hp

private lemma spinD2_analyticOnNhd_laplace_right {B : ℝ} (hB : 0 ≤ B) {ν : Measure (ℝ × ℝ)}
    (hν : ν (spinConeB B)ᶜ = 0)
    (hdiag : ∀ β : ℝ, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    {βL : ℝ} (hβL : 0 < βL) :
    AnalyticOnNhd ℝ (fun βR : ℝ => ∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν) (Ioi 0) := by
  let μL : Measure ℝ :=
    (ν.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-2 * π * βL * p.1)))).map Prod.snd
  have hmeas_d : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-2 * π * βL * p.1))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hmgf_eq : ∀ βR : ℝ,
      mgf lapX μL βR = ∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν := by
    intro βR
    rw [mgf_lapX]
    unfold lapZ μL
    rw [integral_map measurable_snd.aemeasurable (by fun_prop : Continuous fun y : ℝ => Real.exp (-2 * π * βR * y)).aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hmeas_d (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [← Real.exp_add]; congr 1; ring
  have hmem_set : Ioi (0 : ℝ) ⊆ integrableExpSet lapX μL := by
    intro βR hβR
    rw [mem_integrableExpSet_lapX]
    unfold LapFin μL
    rw [integrable_map_measure (by fun_prop : Continuous fun y : ℝ => Real.exp (-2 * π * βR * y)).aestronglyMeasurable
        measurable_snd.aemeasurable,
      integrable_withDensity_iff_integrable_smul' hmeas_d (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine (spinD2_joint_laplace_integrable hB hν hdiag hβL (mem_Ioi.mp hβR)).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [← Real.exp_add]; congr 1; ring
  have hsub_int : Ioi (0 : ℝ) ⊆ interior (integrableExpSet lapX μL) :=
    interior_maximal hmem_set isOpen_Ioi
  intro βR hβR
  have hana : AnalyticAt ℝ (mgf lapX μL) βR := analyticAt_mgf (hsub_int hβR)
  exact hana.congr (Eventually.of_forall hmgf_eq)

private lemma spinD2_analyticOnNhd_laplace_left {B : ℝ} (hB : 0 ≤ B) {ν : Measure (ℝ × ℝ)}
    (hν : ν (spinConeB B)ᶜ = 0)
    (hdiag : ∀ β : ℝ, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    {βR : ℝ} (hβR : 0 < βR) :
    AnalyticOnNhd ℝ (fun βL : ℝ => ∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν) (Ioi 0) := by
  let ν' : Measure (ℝ × ℝ) := ν.map Prod.swap
  have hν' : ν' (spinConeB B)ᶜ = 0 := by
    unfold ν'
    rw [Measure.map_apply measurable_swap (isClosed_spinConeB B).measurableSet.compl]
    have hpre : Prod.swap ⁻¹' (spinConeB B)ᶜ = (spinConeB B)ᶜ := by
      ext p; simp [spinConeB, and_comm]
    rw [hpre]; exact hν
  have hdiag' : ∀ β : ℝ, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν' := by
    intro β hβ
    unfold ν'
    rw [integrable_map_measure (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-2 * π * β * (p.1 + p.2))).aestronglyMeasurable measurable_swap.aemeasurable]
    refine (hdiag β hβ).congr (Eventually.of_forall fun p => ?_)
    simp [add_comm]
  have hana := spinD2_analyticOnNhd_laplace_right hB hν' hdiag' hβR
  intro βL hβL
  refine (hana βL hβL).congr (Eventually.of_forall fun β => ?_)
  dsimp only [ν']
  rw [integral_map measurable_swap.aemeasurable (by fun_prop : Continuous fun p : ℝ × ℝ =>
    Real.exp (-2 * π * (βR * p.1 + β * p.2))).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp [Prod.swap]; ring_nf

private lemma spinD2_analyticOnNhd_vacuumQ (a : ℝ) : AnalyticOnNhd ℝ (spinVacuumQ a) (Ioi 0) := by
  intro β _
  unfold spinVacuumQ
  exact ((analyticAt_const.mul analyticAt_id).rexp).mul
    (analyticAt_const.sub ((analyticAt_const.mul analyticAt_id).rexp))

private lemma spinD2_analytic_continuation_2D {a B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ν : Measure (ℝ × ℝ)} (hν : ν (spinConeB B)ᶜ = 0)
    (hdiag : ∀ β : ℝ, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    (hloc : ∀ βL βR : ℝ, sTheta θ < βL → βL < 1 / sTheta θ → sTheta θ < βR → βR < 1 / sTheta θ →
      ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR) :
    ∀ βL βR : ℝ, 0 < βL → 0 < βR →
      ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR := by
  have hs0 : 0 < sTheta θ := sTheta_pos hθ0 hθ1
  have hs1 : sTheta θ < 1 := by unfold sTheta; exact (div_lt_one (by linarith)).mpr (by linarith)
  have h1_mem : (1 : ℝ) ∈ Ioo (sTheta θ) (1 / sTheta θ) :=
    ⟨hs1, (lt_div_iff₀ hs0).mpr (by linarith)⟩
  have hX_split : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
      ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν =
        (∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) *
          (∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL⁻¹ * p.1 + βR⁻¹ * p.2)) ∂ν) := by
    intro βL βR hβL hβR
    have h1 := spinD2_joint_laplace_integrable hB hν hdiag hβL hβR
    have h2 := (spinD2_joint_laplace_integrable hB hν hdiag (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_mul
      ((βL * βR) ^ (-(1 / 2 : ℝ)))
    have hpt : (fun p : ℝ × ℝ => spinThermalX βL βR p.1 p.2) =
        fun p => Real.exp (-2 * π * (βL * p.1 + βR * p.2)) -
          (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * (βL⁻¹ * p.1 + βR⁻¹ * p.2)) := by
      ext p; unfold spinThermalX; simp only [div_eq_inv_mul]
    rw [hpt, integral_sub h1 h2, integral_const_mul]
  have hstep1 : ∀ βL : ℝ, sTheta θ < βL → βL < 1 / sTheta θ → ∀ βR : ℝ, 0 < βR →
      ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR := by
    intro βL hL1 hL2 βR hβR
    have hβL : 0 < βL := hs0.trans hL1
    let G : ℝ → ℝ := fun β =>
      (∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + β * p.2)) ∂ν) -
      (βL * β) ^ (-(1 / 2 : ℝ)) *
        (∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL⁻¹ * p.1 + β⁻¹ * p.2)) ∂ν) +
      spinThermalXVac a βL β
    have hG_ana : AnalyticOnNhd ℝ G (Ioi 0) := by
      intro β hβ
      have hβ_pos : 0 < β := mem_Ioi.mp hβ
      have hinv_ana : AnalyticAt ℝ (fun x : ℝ => x⁻¹) β := analyticAt_id.inv hβ_pos.ne'
      have h1 := spinD2_analyticOnNhd_laplace_right hB hν hdiag hβL β hβ
      have h2 := (spinD2_analyticOnNhd_laplace_right hB hν hdiag (inv_pos.mpr hβL) β⁻¹
        (inv_pos.mpr hβ_pos)).comp hinv_ana
      have hpow : AnalyticAt ℝ (fun x : ℝ => (βL * x) ^ (-(1 / 2 : ℝ))) β :=
        (analyticAt_rpow_neg (1 / 2) (mul_pos hβL hβ_pos)).comp (analyticAt_const.mul analyticAt_id)
      have hvac : AnalyticAt ℝ (fun x : ℝ => spinThermalXVac a βL x) β := by
        unfold spinThermalXVac spinVacuumV
        have hq1 : AnalyticAt ℝ (fun x : ℝ => spinVacuumQ a βL * spinVacuumQ a x) β :=
          analyticAt_const.mul (spinD2_analyticOnNhd_vacuumQ a β hβ)
        have hq2 : AnalyticAt ℝ (fun x : ℝ => spinVacuumQ a βL⁻¹ * spinVacuumQ a x⁻¹) β :=
          analyticAt_const.mul ((spinD2_analyticOnNhd_vacuumQ a β⁻¹ (inv_pos.mpr hβ_pos)).comp hinv_ana)
        exact hq1.sub (hpow.mul hq2)
      exact (h1.sub (hpow.mul h2)).add hvac
    have hG_ev : G =ᶠ[𝓝 (1 : ℝ)] 0 := by
      refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds h1_mem) fun β hβ => ?_
      have hβ_pos : 0 < β := hs0.trans hβ.1
      dsimp only [G, Pi.zero_apply]
      rw [← hX_split hβL hβ_pos, hloc βL β hL1 hL2 hβ.1 hβ.2]
      ring
    have hG_zero := hG_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi
      (mem_Ioi.mpr one_pos) hG_ev (mem_Ioi.mpr hβR)
    dsimp only [G, Pi.zero_apply] at hG_zero
    rw [hX_split hβL hβR]
    linarith
  intro βL βR hβL hβR
  let H : ℝ → ℝ := fun β =>
    (∫ p : ℝ × ℝ, Real.exp (-2 * π * (β * p.1 + βR * p.2)) ∂ν) -
    (β * βR) ^ (-(1 / 2 : ℝ)) *
      (∫ p : ℝ × ℝ, Real.exp (-2 * π * (β⁻¹ * p.1 + βR⁻¹ * p.2)) ∂ν) +
    spinThermalXVac a β βR
  have hH_ana : AnalyticOnNhd ℝ H (Ioi 0) := by
    intro β hβ
    have hβ_pos : 0 < β := mem_Ioi.mp hβ
    have hinv_ana : AnalyticAt ℝ (fun x : ℝ => x⁻¹) β := analyticAt_id.inv hβ_pos.ne'
    have h1 := spinD2_analyticOnNhd_laplace_left hB hν hdiag hβR β hβ
    have h2 := (spinD2_analyticOnNhd_laplace_left hB hν hdiag (inv_pos.mpr hβR) β⁻¹
      (inv_pos.mpr hβ_pos)).comp hinv_ana
    have hpow : AnalyticAt ℝ (fun x : ℝ => (x * βR) ^ (-(1 / 2 : ℝ))) β :=
      ((analyticAt_rpow_neg (1 / 2) (mul_pos hβR hβ_pos)).comp
        (analyticAt_const.mul analyticAt_id)).congr
        (Eventually.of_forall fun x => by dsimp only [Function.comp_apply]; rw [mul_comm])
    have hvac : AnalyticAt ℝ (fun x : ℝ => spinThermalXVac a x βR) β := by
      unfold spinThermalXVac spinVacuumV
      have hq1 : AnalyticAt ℝ (fun x : ℝ => spinVacuumQ a x * spinVacuumQ a βR) β :=
        (spinD2_analyticOnNhd_vacuumQ a β hβ).mul analyticAt_const
      have hq2 : AnalyticAt ℝ (fun x : ℝ => spinVacuumQ a x⁻¹ * spinVacuumQ a βR⁻¹) β :=
        ((spinD2_analyticOnNhd_vacuumQ a β⁻¹ (inv_pos.mpr hβ_pos)).comp hinv_ana).mul analyticAt_const
      exact hq1.sub (hpow.mul hq2)
    exact (h1.sub (hpow.mul h2)).add hvac
  have hH_ev : H =ᶠ[𝓝 (1 : ℝ)] 0 := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds h1_mem) fun β hβ => ?_
    have hβ_pos : 0 < β := hs0.trans hβ.1
    dsimp only [H, Pi.zero_apply]
    rw [← hX_split hβ_pos hβR, hstep1 β hβ.1 hβ.2 βR hβR]
    ring
  have hH_zero := hH_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi
    (mem_Ioi.mpr one_pos) hH_ev (mem_Ioi.mpr hβL)
  dsimp only [H, Pi.zero_apply] at hH_zero
  rw [hX_split hβL hβR]
  linarith

/-! ### Section 3: Odd-target bound for the reserve functional `L_res` -/

/-- Pointwise bound for `exp(-δ t) |P_j(t)| ≤ (4 max(1/δ, C) j)^j` (`δ > 0`, `t ≥ 0`, `j` odd). -/
private lemma exp_neg_mul_abs_lagP_le {δ : ℝ} (hδ : 0 < δ) {j : ℕ} (hj : Odd j) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-δ * t) * |lagP 1 j t| ≤ (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j := by
  have hF := lagP_oddFam one_pos
  set C : ℝ := (1 + 1) / π
  set M : ℝ := max (1 / δ) C
  have hM_pos : 0 < M := lt_max_of_lt_left (by positivity)
  have hj1 : 1 ≤ j := hj.pos
  have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hup : |lagP 1 j t| ≤ (t + C * j) ^ j := hF.upper j hj t ht
  have hmax : (t + C * j) ^ j ≤ (2 * max t (C * j)) ^ j := by
    refine pow_le_pow_left₀ (by positivity) ?_ j
    have h1 : t ≤ max t (C * j) := le_max_left _ _
    have h2 : C * j ≤ max t (C * j) := le_max_right _ _
    linarith
  have hmax_pow : (max t (C * j)) ^ j ≤ t ^ j + (C * j) ^ j := by
    rcases le_total t (C * j) with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ht j]
    · rw [max_eq_left h]; linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ C * j) j]
  have ht_pow : t ^ j ≤ (j / δ) ^ j * Real.exp (δ * t) := by
    have hexp := Real.pow_div_factorial_le_exp (x := δ * t) (by positivity) j
    have hfac : (j.factorial : ℝ) ≤ (j : ℝ) ^ j := by exact_mod_cast Nat.factorial_le_pow j
    have hfac_pos : (0 : ℝ) < j.factorial := by positivity
    rw [div_le_iff₀ hfac_pos] at hexp
    calc t ^ j = (δ * t) ^ j / δ ^ j := by rw [mul_pow]; field_simp
      _ ≤ (Real.exp (δ * t) * j.factorial) / δ ^ j := by gcongr
      _ ≤ (Real.exp (δ * t) * (j : ℝ) ^ j) / δ ^ j := by gcongr
      _ = (j / δ) ^ j * Real.exp (δ * t) := by rw [div_pow]; ring
  have h1_le_exp : (1 : ℝ) ≤ Real.exp (δ * t) := Real.one_le_exp (by positivity)
  have hjδ_le : (j : ℝ) / δ ≤ M * j := by
    calc (j : ℝ) / δ = 1 / δ * j := by ring
      _ ≤ M * j := by gcongr; exact le_max_left _ _
  have hCj_le : C * j ≤ M * j := by
    gcongr; exact le_max_right _ _
  have hsum : t ^ j + (C * j) ^ j ≤ 2 * (M * j) ^ j * Real.exp (δ * t) := by
    have h1 : t ^ j ≤ (M * j) ^ j * Real.exp (δ * t) :=
      ht_pow.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hjδ_le j)
        (Real.exp_pos _).le)
    have h2 : (C * j) ^ j ≤ (M * j) ^ j * Real.exp (δ * t) := by
      calc (C * j) ^ j ≤ (M * j) ^ j := pow_le_pow_left₀ (by positivity) hCj_le j
        _ = (M * j) ^ j * 1 := (mul_one _).symm
        _ ≤ (M * j) ^ j * Real.exp (δ * t) := by gcongr
    linarith
  have h2le : (2 : ℝ) ≤ 2 ^ j := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj1
  calc Real.exp (-δ * t) * |lagP 1 j t|
      ≤ Real.exp (-δ * t) * ((2 * max t (C * j)) ^ j) := by
        gcongr; exact hup.trans hmax
    _ = Real.exp (-δ * t) * (2 ^ j * (max t (C * j)) ^ j) := by rw [mul_pow]
    _ ≤ Real.exp (-δ * t) * (2 ^ j * (2 * (M * j) ^ j * Real.exp (δ * t))) := by
        gcongr; exact hmax_pow.trans hsum
    _ = (Real.exp (-δ * t) * Real.exp (δ * t)) * (2 * 2 ^ j * (M * j) ^ j) := by ring
    _ = 2 * 2 ^ j * (M * j) ^ j := by rw [← Real.exp_add]; simp
    _ ≤ 2 ^ j * 2 ^ j * (M * j) ^ j := by gcongr
    _ = (4 * M * j) ^ j := by
        rw [← mul_pow, ← mul_pow]; congr 1; ring

/-- Integrability of `exp(-2π(t_L + t_R)) * f(t_L, t_R)` w.r.t. `σ` for all `f ∈ spinD2QCall`. -/
private lemma spinD2QCall_integrable_sigma {B s : ℝ} (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    {σ : Measure (ℝ × ℝ)} (hσB : σ (spinConeB B)ᶜ = 0)
    (hσ_int : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * s * (p.1 + p.2))) σ)
    {f : C(ℝ × ℝ, ℝ)} (hf : f ∈ spinD2QCall) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * f p) σ := by
  set θ₀ : ℝ := (1 - s) / (1 + s) with hθ₀
  have hθ₀_pos : 0 < θ₀ := div_pos (by linarith) (by linarith)
  have hθ₀_lt1 : θ₀ < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hsθ₀ : sTheta θ₀ = s := by
    unfold sTheta; rw [hθ₀]; field_simp [(show 1 + s ≠ 0 by linarith)]; ring
  have hσ_int' : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta θ₀ * (p.1 + p.2))) σ := by
    rwa [hsθ₀]
  have hΨ_int := (spin_tensor_cayley_integral hB hθ₀_pos hθ₀_lt1 hσB hσ_int'
    (ϖL := 0) (ϖR := 0) (βL := 1) (βR := 1) (by simpa using hθ₀_pos) (by simpa using hθ₀_pos)
    (by norm_num) (by norm_num)).1
  unfold spinD2QCall at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨m, n, -, rfl⟩ := hg
    have heq : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * spinD2LagPolyBasisC m n p) =
        fun p => (1 / 2 : ℝ) * (lagPsi (1 / 2) m p.1 * lagPsi (1 / 2) n p.2) +
          (1 / 2 : ℝ) * (lagPsi (1 / 2) n p.1 * lagPsi (1 / 2) m p.2) := by
      ext p; dsimp only [spinD2LagPolyBasisC, ContinuousMap.coe_mk]
      rw [exp_mul_spinOddLagPolyBasis]; unfold spinOddLagBasisT; ring
    rw [heq]
    exact ((hΨ_int m n).const_mul _).add ((hΨ_int n m).const_mul _)
  | zero => simp
  | add x y _ _ hx hy =>
    have h : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * (x + y) p) =
        fun p => Real.exp (-2 * π * (p.1 + p.2)) * x p + Real.exp (-2 * π * (p.1 + p.2)) * y p := by
      ext p; simp [mul_add]
    rw [h]; exact hx.add hy
  | smul c x _ hx =>
    have h : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * (c • x) p) =
        fun p => c * (Real.exp (-2 * π * (p.1 + p.2)) * x p) := by
      ext p; simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring
    rw [h]; exact hx.const_mul c

/-! ### Section 4: Backward direction (`⇐`) via `LP.poly_compact_invariant` -/

private noncomputable def spinD2Lres (a B s : ℝ) (ha : 2 ≤ a) (hB : 0 ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) {σ : Measure (ℝ × ℝ)} (hσB : σ (spinConeB B)ᶜ = 0)
    (hσ_int : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * s * (p.1 + p.2))) σ) :
    spinD2QCall →ₗ[ℝ] ℝ where
  toFun f := -spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * f.1 p) -
    ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * f.1 p ∂σ
  map_add' f g := by
    have hVac_int := (spin_tensor_cayley_vac ha (θ := 1 / 2) (by norm_num) (by norm_num)
      (ϖL := 0) (ϖR := 0) (βL := 1) (βR := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).1
    have hint_vac : ∀ q : C(ℝ × ℝ, ℝ), q ∈ spinD2QCall →
        Integrable (fun r : ℝ × ℝ =>
          Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) * q (r.1 ^ 2 / 2, r.2 ^ 2 / 2) *
            spinV1 a r.1 * spinV1 a r.2) := by
      intro q hq
      unfold spinD2QCall at hq
      induction hq using Submodule.span_induction with
      | mem h hh =>
        obtain ⟨m, n, -, rfl⟩ := hh
        have heq_r : (fun r : ℝ × ℝ =>
            Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
              spinD2LagPolyBasisC m n (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2) =
            fun r => (1 / 2 : ℝ) * (lagPsi (1 / 2) m (r.1 ^ 2 / 2) * lagPsi (1 / 2) n (r.2 ^ 2 / 2) *
                spinV1 a r.1 * spinV1 a r.2) +
              (1 / 2 : ℝ) * (lagPsi (1 / 2) n (r.1 ^ 2 / 2) * lagPsi (1 / 2) m (r.2 ^ 2 / 2) *
                spinV1 a r.1 * spinV1 a r.2) := by
          ext r
          dsimp only [spinD2LagPolyBasisC, ContinuousMap.coe_mk]
          have h := exp_mul_spinOddLagPolyBasis m n (r.1 ^ 2 / 2, r.2 ^ 2 / 2)
          dsimp only at h; rw [h]; unfold spinOddLagBasisT; ring
        rw [heq_r]; exact ((hVac_int m n).const_mul _).add ((hVac_int n m).const_mul _)
      | zero => simp
      | add x y _ _ hx hy =>
        have h : (fun r : ℝ × ℝ => Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
            (x + y) (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2) =
            fun r => Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
              x (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2 +
            Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
              y (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2 := by
          ext r; simp only [ContinuousMap.add_apply]; ring
        rw [h]; exact hx.add hy
      | smul c x _ hx =>
        have h : (fun r : ℝ × ℝ => Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
            (c • x) (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2) =
            fun r => c * (Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
              x (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2) := by
          ext r; simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring
        rw [h]; exact hx.const_mul c
    have hσf := spinD2QCall_integrable_sigma hB hs0 hs1 hσB hσ_int f.2
    have hσg := spinD2QCall_integrable_sigma hB hs0 hs1 hσB hσ_int g.2
    unfold spinVacT spinPhiVac spinLiftTToR
    simp only [Submodule.coe_add, ContinuousMap.add_apply, neg_neg]
    have hpt1 : (fun r : ℝ × ℝ => Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
        (f.1 (r.1 ^ 2 / 2, r.2 ^ 2 / 2) + g.1 (r.1 ^ 2 / 2, r.2 ^ 2 / 2)) *
        spinV1 a r.1 * spinV1 a r.2) =
        fun r => Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
          f.1 (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2 +
        Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
          g.1 (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2 := by
      ext r; ring
    have hpt2 : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * (f.1 p + g.1 p)) =
        fun p => Real.exp (-2 * π * (p.1 + p.2)) * f.1 p + Real.exp (-2 * π * (p.1 + p.2)) * g.1 p := by
      ext p; ring
    rw [hpt1, integral_add (hint_vac f.1 f.2) (hint_vac g.1 g.2), hpt2, integral_add hσf hσg]
    ring
  map_smul' c f := by
    unfold spinVacT spinPhiVac spinLiftTToR
    simp only [SetLike.val_smul, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, neg_neg]
    have hpt1 : (fun r : ℝ × ℝ => Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
        (c * f.1 (r.1 ^ 2 / 2, r.2 ^ 2 / 2)) * spinV1 a r.1 * spinV1 a r.2) =
        fun r => c * (Real.exp (-2 * π * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2)) *
          f.1 (r.1 ^ 2 / 2, r.2 ^ 2 / 2) * spinV1 a r.1 * spinV1 a r.2) := by
      ext r; ring
    have hpt2 : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * (c * f.1 p)) =
        fun p => c * (Real.exp (-2 * π * (p.1 + p.2)) * f.1 p) := by
      ext p; ring
    rw [hpt1, integral_const_mul, hpt2, integral_const_mul]
    ring

private theorem dslReserve_backward {a B T₀ s : ℝ} (ha : 2 ≤ a) (hB : 0 ≤ B) (hT₀ : 0 < T₀)
    (hs0 : 0 < s) (hs1 : s < 1)
    {X : Set (ℝ × ℝ)} (hXc : IsClosed X) (hXs : IsSwapInvariantSet X)
    (hX : X ⊆ spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2})
    {σ : Measure (ℝ × ℝ)} (hσsupp : σ Xᶜ = 0) (hσswap : IsSwapInvariantMeasure σ)
    (hσ_int : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * s * (p.1 + p.2))) σ)
    (hres : ∀ N q, q ∈ spinOddLagPolySpace N → (∀ p ∈ X, 0 ≤ q p) →
      ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * q p ∂σ ≤
        -spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p)) :
    ∃ meas : SpinCrossingMeasureOn a X, IsSwapInvariantMeasure meas.ν ∧ σ ≤ meas.ν := by
  have hXB : X ⊆ spinConeB B := hX.trans inter_subset_left
  have hσB : σ (spinConeB B)ᶜ = 0 := measure_mono_null (compl_subset_compl.mpr hXB) hσsupp
  let t : C(X, ℝ) := ⟨fun x => x.1.1 + x.1.2, (continuous_fst.add continuous_snd).comp continuous_subtype_val⟩
  let restrictX : C(ℝ × ℝ, ℝ) →ₗ[ℝ] C(X, ℝ) :=
    { toFun := fun f => f.comp ⟨Subtype.val, continuous_subtype_val⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let QV : ℕ → Submodule ℝ C(X, ℝ) := fun N => (spinD2QC N).map restrictX
  have hQV_mono : ∀ M N, Odd M → Odd N → M ≤ N → QV M ≤ QV N :=
    fun M N _ _ hMN => Submodule.map_mono (spinD2QC_mono hMN)
  have hmem_QV_union : ∀ {f : C(ℝ × ℝ, ℝ)}, f ∈ spinD2QCall → restrictX f ∈ polyUnion QV := by
    intro f hf
    obtain ⟨N, hN⟩ := exists_N_of_mem_spinD2QCall hf
    exact le_polyUnion (N := 2 * N + 1) ⟨N, rfl⟩ ⟨f, spinD2QC_mono (by omega) hN, rfl⟩
  let Lres := spinD2Lres a B s ha hB hs0 hs1 hσB hσ_int
  let ι' : spinD2QCall →ₗ[ℝ] C(X, ℝ) := restrictX.comp spinD2QCall.subtype
  have hLres_nn : ∀ (f : C(ℝ × ℝ, ℝ)) (hf : f ∈ spinD2QCall), (∀ p ∈ X, 0 ≤ f p) →
      0 ≤ Lres ⟨f, hf⟩ := by
    intro f hf hnn
    obtain ⟨N, hN⟩ := exists_N_of_mem_spinD2QCall hf
    have h := hres N (f : ℝ × ℝ → ℝ) (coe_mem_spinOddLagPolySpace' hN) hnn
    change 0 ≤ -spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * f p) -
      ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * f p ∂σ
    linarith
  have hker : LinearMap.ker ι' ≤ LinearMap.ker Lres := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have hzero : ∀ p ∈ X, f.1 p = 0 := fun p hp => by
      have := congrArg (fun q : C(X, ℝ) => q ⟨p, hp⟩) hf
      simpa [ι', restrictX] using this
    have h1 := hLres_nn f.1 f.2 (fun p hp => by rw [hzero p hp])
    have h2 := hLres_nn (-f.1) (Submodule.neg_mem _ f.2) (fun p hp => by simp [hzero p hp])
    have hneg_eq : Lres ⟨-f.1, Submodule.neg_mem _ f.2⟩ = -Lres f := Lres.map_neg f
    rw [hneg_eq] at h2
    linarith
  have hle_range : polyUnion QV ≤ LinearMap.range ι' := by
    refine iSup_le fun N => ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, spinD2QC_le_all N.1 hf⟩, rfl⟩
  let L₀ : LinearMap.range ι' →ₗ[ℝ] ℝ :=
    ((LinearMap.ker ι').liftQ Lres hker).comp ι'.quotKerEquivRange.symm.toLinearMap
  have hL₀ : ∀ (f : spinD2QCall) (h : ι' f ∈ LinearMap.range ι'), L₀ ⟨ι' f, h⟩ = Lres f := by
    intro f h
    simp only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]; rfl
  let L : polyUnion QV →ₗ[ℝ] ℝ := L₀.comp (Submodule.inclusion hle_range)
  have hL_eval : ∀ (f : C(ℝ × ℝ, ℝ)) (hf : f ∈ spinD2QCall),
      L ⟨restrictX f, hmem_QV_union hf⟩ = Lres ⟨f, hf⟩ :=
    fun f hf => hL₀ ⟨f, hf⟩ _
  have hL_pos : ∀ v : polyUnion QV, (∀ x : X, 0 ≤ v.1 x) → 0 ≤ L v := by
    intro v hv
    obtain ⟨f, hf⟩ := hle_range v.2
    have hLv : L v = Lres f := by
      have : (⟨v.1, hle_range v.2⟩ : LinearMap.range ι') = ⟨ι' f, ⟨f, rfl⟩⟩ := Subtype.ext hf.symm
      show L₀ ⟨v.1, hle_range v.2⟩ = _
      rw [this]; exact hL₀ f _
    rw [hLv]
    refine hLres_nn f.1 f.2 fun p hp => ?_
    have := hv ⟨p, hp⟩
    rw [← hf] at this
    simpa [ι', restrictX] using this
  -- Positive majorant from `LP.positive_ray`
  obtain ⟨N₀, p₀, hp₀, hp₀1⟩ := positive_ray (w := 1) one_pos hT₀
  obtain ⟨f₀, hf₀_mem, hf₀p⟩ : ∃ f ∈ spinD2QC (2 * N₀ + 1), ∀ p : ℝ × ℝ, f p = p₀ (p.1 + p.2) := by
    refine Submodule.span_induction
      (p := fun p _ => ∃ f ∈ spinD2QC (2 * N₀ + 1), ∀ q : ℝ × ℝ, f q = p (q.1 + q.2)) ?_ ?_ ?_ ?_ hp₀
    · rintro g ⟨k, hk, hkN, rfl⟩
      exact ⟨(lagPC 1 k).comp ⟨fun q : ℝ × ℝ => q.1 + q.2, continuous_fst.add continuous_snd⟩,
        spinD2_lagPC_add_mem_QC hk (by omega), fun q => rfl⟩
    · exact ⟨0, Submodule.zero_mem _, fun _ => rfl⟩
    · rintro f g _ _ ⟨f', hf', hf'p⟩ ⟨g', hg', hg'p⟩
      exact ⟨f' + g', Submodule.add_mem _ hf' hg', fun q => by simp [hf'p, hg'p]⟩
    · rintro c f _ ⟨f', hf', hf'p⟩
      exact ⟨c • f', Submodule.smul_mem _ c hf', fun q => by simp [hf'p]⟩
  have hHyp : PolyCompactHyp ((1 + 1) / π) (lagPC 1) T₀ t QV :=
    { fam := lagP_oddFam one_pos
      T₀_nonneg := hT₀.le
      t_ge := fun x => (hX x.2).2
      t_proper := spinD2_isProperMap_sum_on_coneB hXc hXB
      mono := hQV_mono
      growth := by
        rintro N _ _ ⟨f, hf, rfl⟩
        obtain ⟨C, hC⟩ := spinD2QC_growth hB N hf
        exact ⟨C, fun x => hC x.1 (hXB x.2) (hT₀.le.trans (hX x.2).2)⟩
      contains := fun N _ j hj hjN => ⟨(lagPC 1 j).comp ⟨fun p : ℝ × ℝ => p.1 + p.2,
          continuous_fst.add continuous_snd⟩, spinD2_lagPC_add_mem_QC hj hjN, by ext x; rfl⟩
      majorant := ⟨2 * N₀ + 1, restrictX f₀, 1, ⟨N₀, rfl⟩, ⟨f₀, hf₀_mem, rfl⟩, one_pos, fun x => by
        show 1 ≤ f₀ x.1
        rw [hf₀p x.1]
        exact hp₀1 _ (hX x.2).2⟩ }
  -- Odd-target bound `|L v| ≤ (C₂ * j) ^ j`
  set δ : ℝ := 2 * π * (1 - s) with hδ
  have hδ_pos : 0 < δ := by rw [hδ]; nlinarith [Real.pi_pos]
  set Iσ : ℝ := ∫ p : ℝ × ℝ, Real.exp (-2 * π * s * (p.1 + p.2)) ∂σ with hIσ
  have hIσ_nn : 0 ≤ Iσ := integral_nonneg fun _ => (Real.exp_pos _).le
  set Kσ : ℝ := max 1 Iσ with hKσ
  have hKσ_ge1 : 1 ≤ Kσ := le_max_left _ _
  set C_ref : ℝ := momC2 ((1 + 1) / π) (refMeas virasoroProblem a)
  have hC_ref_pos : 0 < C_ref := momC2_pos (lagP_oddFam one_pos).C_pos _
  set C_σ : ℝ := 4 * max (1 / δ) ((1 + 1) / π) * Kσ
  have hC_σ_pos : 0 < C_σ := by
    have : 0 < max (1 / δ) ((1 + 1) / π) := lt_max_of_lt_left (by positivity)
    positivity
  set C₂ : ℝ := 2 * max C_ref C_σ
  have hC₂_pos : 0 < C₂ := by positivity
  have hodd : ∀ j : ℕ, Odd j → ∀ v : polyUnion QV,
      (v : C(X, ℝ)) = pc (lagPC 1) j t → |L v| ≤ (C₂ * j) ^ j := by
    intro j hj v hvj
    let fj : C(ℝ × ℝ, ℝ) := (lagPC 1 j).comp ⟨fun p : ℝ × ℝ => p.1 + p.2, continuous_fst.add continuous_snd⟩
    have hfj : fj ∈ spinD2QCall := spinD2QC_le_all j (spinD2_lagPC_add_mem_QC hj le_rfl)
    have hv_eq : v = ⟨restrictX fj, hmem_QV_union hfj⟩ := Subtype.ext (by rw [hvj]; ext x; rfl)
    rw [hv_eq, hL_eval fj hfj]
    change |-spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2)) -
      ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2) ∂σ| ≤ (C₂ * j) ^ j
    rw [spinD2_vac_lagPC_eq_refMeas ha hj]
    have h1 : |∫ s, lagP 1 j s ∂refMeas virasoroProblem a| ≤ (C_ref * j) ^ j :=
      abs_integral_p_mu0_le (lagP_oddFam one_pos) refMeas_Iio
        (integrable_exp_ref_pi (prob := virasoroProblem) (by rw [virasoroProblem_totalShift]; exact ha)) hj
    have h2 : |∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2) ∂σ| ≤
        (C_σ * j) ^ j := by
      have hae_pos : ∀ᵐ p ∂σ, 0 ≤ p.1 + p.2 := by
        have : ∀ᵐ p ∂σ, p ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hσsupp
        filter_upwards [this] with p hp using hT₀.le.trans (hX (not_not.mp hp)).2
      have hdom : ∀ᵐ p ∂σ, ‖Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2)‖ ≤
          (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j * Real.exp (-2 * π * s * (p.1 + p.2)) := by
        filter_upwards [hae_pos] with p hp
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hexp_split : Real.exp (-2 * π * (p.1 + p.2)) =
            Real.exp (-2 * π * s * (p.1 + p.2)) * Real.exp (-δ * (p.1 + p.2)) := by
          rw [← Real.exp_add]; congr 1; rw [hδ]; ring
        rw [hexp_split, mul_assoc]
        have hpt := exp_neg_mul_abs_lagP_le hδ_pos hj hp
        calc Real.exp (-2 * π * s * (p.1 + p.2)) * (Real.exp (-δ * (p.1 + p.2)) * |lagP 1 j (p.1 + p.2)|)
            ≤ Real.exp (-2 * π * s * (p.1 + p.2)) * (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j :=
              mul_le_mul_of_nonneg_left hpt (Real.exp_pos _).le
          _ = (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j * Real.exp (-2 * π * s * (p.1 + p.2)) := by ring
      have hint_dom : Integrable (fun p : ℝ × ℝ =>
          (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j * Real.exp (-2 * π * s * (p.1 + p.2))) σ :=
        hσ_int.const_mul _
      have hnorm : |∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2) ∂σ| ≤
          (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j * Iσ := by
        calc |∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2) ∂σ|
            ≤ ∫ p : ℝ × ℝ, ‖Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2)‖ ∂σ := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
                (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2))
          _ ≤ ∫ p : ℝ × ℝ, (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j *
                Real.exp (-2 * π * s * (p.1 + p.2)) ∂σ :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint_dom hdom
          _ = (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j * Iσ := integral_const_mul _ _
      have hKpow : Iσ ≤ Kσ ^ j := by
        calc Iσ ≤ Kσ := le_max_right _ _
          _ = Kσ ^ 1 := (pow_one _).symm
          _ ≤ Kσ ^ j := pow_le_pow_right₀ hKσ_ge1 hj.pos
      calc |∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2) ∂σ|
          ≤ (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j * Iσ := hnorm
        _ ≤ (4 * max (1 / δ) ((1 + 1) / π) * j) ^ j * Kσ ^ j := by gcongr
        _ = (C_σ * j) ^ j := by
            rw [← mul_pow]; congr 1; dsimp [C_σ]; ring
    have h2le : (2 : ℝ) ≤ 2 ^ j := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj.pos
    have hA1 : (C_ref * j) ^ j ≤ (max C_ref C_σ * j) ^ j := by gcongr; exact le_max_left _ _
    have hA2 : (C_σ * j) ^ j ≤ (max C_ref C_σ * j) ^ j := by gcongr; exact le_max_right _ _
    calc |∫ s, lagP 1 j s ∂refMeas virasoroProblem a -
            ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2) ∂σ|
        ≤ |∫ s, lagP 1 j s ∂refMeas virasoroProblem a| +
            |∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * lagP 1 j (p.1 + p.2) ∂σ| :=
          abs_sub _ _
      _ ≤ (max C_ref C_σ * j) ^ j + (max C_ref C_σ * j) ^ j := add_le_add (h1.trans hA1) (h2.trans hA2)
      _ = 2 * (max C_ref C_σ * j) ^ j := by ring
      _ ≤ 2 ^ j * (max C_ref C_σ * j) ^ j := by gcongr
      _ = (C₂ * j) ^ j := by rw [← mul_pow]; congr 1; dsimp [C₂]; ring
  -- Swap group action of `Equiv.Perm (Fin 2)` on `X`
  let _instMulAct : MulAction (Equiv.Perm (Fin 2)) X :=
    { smul := fun g x => if g = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩
      one_smul := fun x => by
        change (if (1 : Equiv.Perm (Fin 2)) = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩) = x
        simp
      mul_smul := fun g₁ g₂ x => by
        change (if g₁ * g₂ = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩) =
          (if g₁ = 1 then (if g₂ = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩)
           else ⟨(if g₂ = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩).1.swap,
             hXs _ (if g₂ = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩).2⟩)
        have hperm : ∀ g : Equiv.Perm (Fin 2), g = 1 ∨ g = Equiv.swap 0 1 := by
          intro g; decide +revert
        have hne : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by decide
        have hsq : Equiv.swap (0 : Fin 2) 1 * Equiv.swap 0 1 = 1 := by decide
        rcases hperm g₁ with rfl | rfl <;> rcases hperm g₂ with rfl | rfl
        · simp
        · simp [hne]
        · simp [hne]
        · simp only [hsq, hne, ↓reduceIte]
          ext <;> rfl }
  let _instContSMul : ContinuousConstSMul (Equiv.Perm (Fin 2)) X :=
    { continuous_const_smul := fun g => by
        change Continuous (fun x : X => if g = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩)
        by_cases hg : g = 1
        · simp [hg]; exact continuous_id
        · simp only [hg, ↓reduceIte]
          exact (continuous_swap.comp continuous_subtype_val).subtype_mk _ }
  have hact_t : ∀ (g : Equiv.Perm (Fin 2)) (x : X), t (g • x) = t x := by
    intro g x
    change t (if g = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩) = t x
    split_ifs
    · rfl
    · dsimp [t, Prod.swap]; ring
  have hact_eq : ∀ (g : Equiv.Perm (Fin 2)) {f : C(ℝ × ℝ, ℝ)}, f ∈ spinD2QCall →
      FormalResearch.Measure.actComp g (restrictX f) = restrictX f := by
    intro g f hf
    ext x
    change (restrictX f) (if g = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩) = (restrictX f) x
    split_ifs
    · rfl
    · exact spinD2QCall_swap_symm hf x.1
  have hact_V : ∀ (g : Equiv.Perm (Fin 2)) (N : ℕ), Odd N → ∀ v ∈ QV N,
      FormalResearch.Measure.actComp g v ∈ QV N := by
    rintro g N _ _ ⟨f, hf, rfl⟩
    rw [hact_eq g (spinD2QC_le_all N hf)]
    exact ⟨f, hf, rfl⟩
  have hact_L : ∀ (g : Equiv.Perm (Fin 2)) (v v' : polyUnion QV),
      (v' : C(X, ℝ)) = FormalResearch.Measure.actComp g v → L v' = L v := by
    intro g v v' hvv'
    obtain ⟨f, hf⟩ := hle_range v.2
    have hv_eq : (v : C(X, ℝ)) = restrictX f.1 := hf.symm
    have hv'_eq : (v' : C(X, ℝ)) = (v : C(X, ℝ)) := by
      rw [hvv', hv_eq, hact_eq g f.2]
    exact congrArg L (Subtype.ext hv'_eq)
  have _instLocCpt : LocallyCompactSpace X := hXc.locallyCompactSpace
  obtain ⟨μ, _hreg, _hpoly, hrep, ⟨ε, hε, hexp⟩, hinv⟩ := poly_compact_invariant hHyp
    hC₂_pos L hL_pos hodd hact_t hact_V hact_L
  -- Push `μ` to `ℝ × ℝ`, tilt by `exp(2π(t_L + t_R))`, and add `σ`
  let μ₁ : Measure (ℝ × ℝ) := μ.map Subtype.val
  have hμ₁_supp : μ₁ Xᶜ = 0 := by
    unfold μ₁
    rw [Measure.map_apply measurable_subtype_coe hXc.measurableSet.compl]
    have hemp : (Subtype.val : X → ℝ × ℝ) ⁻¹' Xᶜ = ∅ := by ext x; simp
    rw [hemp, measure_empty]
  have hμ₁_swap : IsSwapInvariantMeasure μ₁ := by
    unfold IsSwapInvariantMeasure μ₁
    have hsw_ne : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by decide
    have hcomp : Prod.swap ∘ (Subtype.val : X → ℝ × ℝ) =
        (Subtype.val : X → ℝ × ℝ) ∘ (fun x : X => Equiv.swap (0 : Fin 2) 1 • x) := by
      funext x
      change x.1.swap = (if Equiv.swap (0 : Fin 2) 1 = 1 then x else ⟨x.1.swap, hXs x.1 x.2⟩).1
      simp [hsw_ne]
    rw [Measure.map_map measurable_swap measurable_subtype_coe, hcomp,
      ← Measure.map_map measurable_subtype_coe (continuous_const_smul _).measurable,
      hinv (Equiv.swap 0 1)]
  have hexp₁ : Integrable (fun p : ℝ × ℝ => Real.exp (ε * (p.1 + p.2))) μ₁ := by
    unfold μ₁
    rw [integrable_map_measure (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (ε * (p.1 + p.2))).aestronglyMeasurable measurable_subtype_coe.aemeasurable]
    exact hexp
  let tiltD : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (2 * π * (p.1 + p.2)))
  have htilt_meas : Measurable tiltD := ENNReal.measurable_ofReal.comp (by fun_prop)
  let ν₀ : Measure (ℝ × ℝ) := μ₁.withDensity tiltD
  have hν₀_supp : ν₀ Xᶜ = 0 := by
    unfold ν₀
    rw [withDensity_apply _ hXc.measurableSet.compl]
    exact setLIntegral_measure_zero _ _ hμ₁_supp
  have hν₀_swap : IsSwapInvariantMeasure ν₀ := by
    unfold IsSwapInvariantMeasure ν₀
    have hsw_inv : ∀ p : ℝ × ℝ, tiltD p.swap = tiltD p := fun p => by
      dsimp only [tiltD, Prod.swap]; rw [add_comm]
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply measurable_swap hS, withDensity_apply _ (measurable_swap hS),
      withDensity_apply _ hS]
    have hpre : ∫⁻ p in Prod.swap ⁻¹' S, tiltD p ∂μ₁ = ∫⁻ p in S, tiltD p.swap ∂(μ₁.map Prod.swap) :=
      (setLIntegral_map (f := fun p : ℝ × ℝ => tiltD p.swap) hS
        (htilt_meas.comp measurable_swap) measurable_swap).symm
    rw [hpre, hμ₁_swap]
    exact setLIntegral_congr_fun hS fun p _ => hsw_inv p
  let ν : Measure (ℝ × ℝ) := σ + ν₀
  have hν_supp : ν Xᶜ = 0 := by
    simp [ν, hσsupp, hν₀_supp]
  have hν_swap : IsSwapInvariantMeasure ν := by
    unfold IsSwapInvariantMeasure ν
    rw [Measure.map_add _ _ measurable_swap, hσswap, hν₀_swap]
  have hσ_le_ν : σ ≤ ν := Measure.le_add_right le_rfl
  -- Choose `θ ∈ (0, 1)` with `2π (1 - s_θ) ≤ ε` and `s ≤ s_θ`
  set θ : ℝ := min (1 / 2) (min (ε / (8 * π)) ((1 - s) / (1 + s))) with hθ
  have hθ0 : 0 < θ := lt_min (by norm_num) (lt_min (div_pos hε (by positivity)) (div_pos (by linarith) (by linarith)))
  have hθ1 : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hsθ0 : 0 < sTheta θ := sTheta_pos hθ0 hθ1
  have hsθ1 : sTheta θ < 1 := by unfold sTheta; exact (div_lt_one (by linarith)).mpr (by linarith)
  have h2pi_le : 2 * π * (1 - sTheta θ) ≤ ε := by
    have h1 : 1 - sTheta θ = 2 * θ / (1 + θ) := by
      unfold sTheta; field_simp [(show 1 + θ ≠ 0 by linarith)]; ring
    have h2 : 2 * θ / (1 + θ) ≤ 2 * θ := div_le_self (by linarith) (by linarith)
    have h3 : θ ≤ ε / (8 * π) := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : 4 * π * θ ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * π)
      calc 4 * π * θ ≤ 4 * π * (ε / (8 * π)) := this
        _ = ε / 2 := by field_simp [Real.pi_pos.ne']; ring
    nlinarith [Real.pi_pos]
  have hs_le_sθ : s ≤ sTheta θ := by
    unfold sTheta
    rw [le_div_iff₀ (by linarith)]
    have h3 : θ ≤ (1 - s) / (1 + s) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h3
    linarith
  have hint_s_ν₀ : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta θ * (p.1 + p.2))) ν₀ := by
    unfold ν₀
    rw [integrable_withDensity_iff_integrable_smul' htilt_meas
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hae_pos : ∀ᵐ p ∂μ₁, 0 ≤ p.1 + p.2 := by
      have : ∀ᵐ p ∂μ₁, p ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hμ₁_supp
      filter_upwards [this] with p hp using hT₀.le.trans (hX (not_not.mp hp)).2
    refine Integrable.mono' hexp₁
      ((ENNReal.measurable_toReal.comp htilt_meas).smul
        (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta θ * (p.1 + p.2)))).aestronglyMeasurable ?_
    filter_upwards [hae_pos] with p hp
    simp only [tiltD, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul,
      Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have heq : 2 * π * (p.1 + p.2) + -2 * π * sTheta θ * (p.1 + p.2) =
        (2 * π * (1 - sTheta θ)) * (p.1 + p.2) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right h2pi_le hp
  have hint_s_σ : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta θ * (p.1 + p.2))) σ := by
    have hae_pos : ∀ᵐ p ∂σ, 0 ≤ p.1 + p.2 := by
      have : ∀ᵐ p ∂σ, p ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hσsupp
      filter_upwards [this] with p hp using hT₀.le.trans (hX (not_not.mp hp)).2
    refine hσ_int.mono' (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.exp (-2 * π * sTheta θ * (p.1 + p.2))).aestronglyMeasurable ?_
    filter_upwards [hae_pos] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have hmul : 2 * π * s * (p.1 + p.2) ≤ 2 * π * sTheta θ * (p.1 + p.2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs_le_sθ (by positivity)) hp
    linarith
  have hint_s : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta θ * (p.1 + p.2))) ν :=
    hint_s_σ.add_measure hint_s_ν₀
  -- Match odd moments on `ν = σ + ν₀`
  have hν₀B : ν₀ (spinConeB B)ᶜ = 0 := measure_mono_null (compl_subset_compl.mpr hXB) hν₀_supp
  have hνB : ν (spinConeB B)ᶜ = 0 := measure_mono_null (compl_subset_compl.mpr hXB) hν_supp
  have hΨ_int_σ := (spin_tensor_cayley_integral hB hθ0 hθ1 hσB hint_s_σ
    (ϖL := 0) (ϖR := 0) (βL := 1) (βR := 1) (by simpa using hθ0) (by simpa using hθ0)
    (by norm_num) (by norm_num)).1
  have hΨ_int_ν₀ := (spin_tensor_cayley_integral hB hθ0 hθ1 hν₀B hint_s_ν₀
    (ϖL := 0) (ϖR := 0) (βL := 1) (βR := 1) (by simpa using hθ0) (by simpa using hθ0)
    (by norm_num) (by norm_num)).1
  have hmom_ν : ∀ m n : ℕ, Odd (m + n) →
      ∫ q : ℝ × ℝ, lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2 ∂ν =
        -spinVacT a (fun q => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) := by
    intro m n hmn
    have hbasis_mem : spinD2LagPolyBasisC m n ∈ spinD2QCall :=
      Submodule.subset_span ⟨m, n, hmn, rfl⟩
    have hrep_mn := hrep ⟨restrictX (spinD2LagPolyBasisC m n), hmem_QV_union hbasis_mem⟩
    rw [hL_eval (spinD2LagPolyBasisC m n) hbasis_mem] at hrep_mn
    have hν₀_basis : ∫ q : ℝ × ℝ, spinOddLagBasisT m n q ∂ν₀ =
        ∫ x : X, (restrictX (spinD2LagPolyBasisC m n)) x ∂μ := by
      unfold ν₀
      rw [integral_withDensity_eq_integral_toReal_smul htilt_meas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      have hsimp : (fun p : ℝ × ℝ => (tiltD p).toReal • spinOddLagBasisT m n p) =
          fun p => spinOddLagPolyBasis m n p := by
        ext p
        simp only [tiltD, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
        rw [← exp_mul_spinOddLagPolyBasis, ← mul_assoc, ← Real.exp_add]
        simp
      rw [hsimp]
      unfold μ₁
      change ∫ p : ℝ × ℝ, (spinD2LagPolyBasisC m n) p ∂(μ.map Subtype.val) = _
      rw [integral_map measurable_subtype_coe.aemeasurable (spinD2LagPolyBasisC m n).continuous.aestronglyMeasurable]
      rfl
    have hswap_gen : ∀ (ρ : Measure (ℝ × ℝ)), IsSwapInvariantMeasure ρ →
        Integrable (fun q : ℝ × ℝ => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) ρ →
        Integrable (fun q : ℝ × ℝ => lagPsi (1 / 2) n q.1 * lagPsi (1 / 2) m q.2) ρ →
        ∫ q : ℝ × ℝ, spinOddLagBasisT m n q ∂ρ =
          ∫ q : ℝ × ℝ, lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2 ∂ρ := by
      intro ρ hρswap hI1 hI2
      have hswap_eq : ∫ q : ℝ × ℝ, lagPsi (1 / 2) m q.2 * lagPsi (1 / 2) n q.1 ∂ρ =
          ∫ q : ℝ × ℝ, lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2 ∂ρ := by
        conv_rhs => rw [← hρswap]
        exact (integral_map (f := fun q : ℝ × ℝ => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2)
          measurable_swap.aemeasurable
          (((continuous_lagPsi (1 / 2) m).comp continuous_fst).mul
            ((continuous_lagPsi (1 / 2) n).comp continuous_snd)).aestronglyMeasurable).symm
      unfold spinOddLagBasisT
      rw [integral_const_mul, integral_add hI1
        (hI2.congr (Eventually.of_forall fun q => mul_comm _ _)), hswap_eq]
      ring
    have hsym_σ := hswap_gen σ hσswap (hΨ_int_σ m n) (hΨ_int_σ n m)
    have hsym_ν₀ := hswap_gen ν₀ hν₀_swap (hΨ_int_ν₀ m n) (hΨ_int_ν₀ n m)
    have hvac_sym : spinVacT a (spinOddLagBasisT m n) =
        spinVacT a (fun q => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) := by
      unfold spinVacT spinPhiVac spinLiftTToR spinOddLagBasisT
      have hVac_int := (spin_tensor_cayley_vac ha hθ0 hθ1
        (ϖL := 0) (ϖR := 0) (βL := 1) (βR := 1) (by simpa using hθ0) (by simpa using hθ0)
        (by norm_num) (by norm_num)).1
      have hswap_r : ∫ r : ℝ × ℝ,
          lagPsi (1 / 2) m (r.2 ^ 2 / 2) * lagPsi (1 / 2) n (r.1 ^ 2 / 2) *
            spinV1 a r.1 * spinV1 a r.2 =
          ∫ r : ℝ × ℝ,
          lagPsi (1 / 2) m (r.1 ^ 2 / 2) * lagPsi (1 / 2) n (r.2 ^ 2 / 2) *
            spinV1 a r.1 * spinV1 a r.2 := by
        have hmp : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
            (volume : Measure (ℝ × ℝ)) volume := Measure.measurePreserving_swap
        rw [← hmp.integral_comp' (g := fun r : ℝ × ℝ =>
          lagPsi (1 / 2) m (r.1 ^ 2 / 2) * lagPsi (1 / 2) n (r.2 ^ 2 / 2) *
            spinV1 a r.1 * spinV1 a r.2)]
        refine integral_congr_ae (Eventually.of_forall fun r => by dsimp [MeasurableEquiv.prodComm]; ring)
      have hpt : (fun r : ℝ × ℝ =>
          (1 / 2 : ℝ) * (lagPsi (1 / 2) m (r.1 ^ 2 / 2) * lagPsi (1 / 2) n (r.2 ^ 2 / 2) +
            lagPsi (1 / 2) m (r.2 ^ 2 / 2) * lagPsi (1 / 2) n (r.1 ^ 2 / 2)) *
            spinV1 a r.1 * spinV1 a r.2) =
          fun r => (1 / 2 : ℝ) * (lagPsi (1 / 2) m (r.1 ^ 2 / 2) * lagPsi (1 / 2) n (r.2 ^ 2 / 2) *
              spinV1 a r.1 * spinV1 a r.2) +
            (1 / 2 : ℝ) * (lagPsi (1 / 2) m (r.2 ^ 2 / 2) * lagPsi (1 / 2) n (r.1 ^ 2 / 2) *
              spinV1 a r.1 * spinV1 a r.2) := by
        ext r; ring
      rw [hpt, integral_add ((hVac_int m n).const_mul _)
        (((hVac_int n m).congr (Eventually.of_forall fun r => by ring)).const_mul _),
        integral_const_mul, integral_const_mul, hswap_r]
      ring
    have hfun : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * spinOddLagPolyBasis m n p) =
        spinOddLagBasisT m n := funext (exp_mul_spinOddLagPolyBasis m n)
    unfold ν
    rw [integral_add_measure (hΨ_int_σ m n) (hΨ_int_ν₀ m n), ← hsym_σ, ← hsym_ν₀, hν₀_basis, hrep_mn]
    change ∫ q, spinOddLagBasisT m n q ∂σ +
      (-spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * spinOddLagPolyBasis m n p) -
        ∫ p, Real.exp (-2 * π * (p.1 + p.2)) * spinOddLagPolyBasis m n p ∂σ) = _
    rw [hfun, hvac_sym]
    ring
  -- Local crossing on `(s_θ, 1/s_θ)²`
  have hloc := (spin_tensor_cayley_iff ha hB hθ0 hθ1 hνB hint_s).2 hmom_ν
  -- Diagonal continuation via `LP.ds_cont`
  let νrad : Measure ℝ := spinRadMarginal ν
  have hmeas_sum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hνrad_Iio : νrad (Iio 0) = 0 := by
    unfold νrad spinRadMarginal
    rw [Measure.map_apply hmeas_sum measurableSet_Iio]
    have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio 0 ⊆ Xᶜ := by
      intro p hp hpX; have h1 : T₀ ≤ p.1 + p.2 := (hX hpX).2; have h2 : p.1 + p.2 < 0 := hp; linarith
    exact measure_mono_null hsub hν_supp
  have hνrad_s : LapFin νrad (sTheta θ) := by
    unfold LapFin νrad spinRadMarginal
    rw [integrable_map_measure (by fun_prop : Continuous fun s : ℝ =>
        Real.exp (-2 * π * sTheta θ * s)).aestronglyMeasurable hmeas_sum.aemeasurable]
    exact hint_s
  have hνrad_cross : ∀ β, sTheta θ < β → β < 1 / sTheta θ →
      lapZ νrad β + srcV virasoroProblem a β =
        β ^ (-(1 : ℝ)) * (lapZ νrad (1 / β) + srcV virasoroProblem a (1 / β)) := by
    intro β h1 h2
    have hβ : 0 < β := hsθ0.trans h1
    have hloc_d := hloc β β h1 h2 h1 h2
    have h1_int : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν := by
      have := hνrad_s.mono hνrad_Iio h1.le
      unfold LapFin νrad spinRadMarginal at this
      rwa [integrable_map_measure (by fun_prop : Continuous fun s : ℝ =>
        Real.exp (-2 * π * β * s)).aestronglyMeasurable hmeas_sum.aemeasurable] at this
    have hinv_gt : sTheta θ < 1 / β := by
      rw [lt_div_iff₀ hβ]; rw [lt_div_iff₀ hsθ0] at h2; linarith
    have h2_int : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (1 / β) * (p.1 + p.2))) ν := by
      have := hνrad_s.mono hνrad_Iio hinv_gt.le
      unfold LapFin νrad spinRadMarginal at this
      rwa [integrable_map_measure (by fun_prop : Continuous fun s : ℝ =>
        Real.exp (-2 * π * (1 / β) * s)).aestronglyMeasurable hmeas_sum.aemeasurable] at this
    have hZ1 : lapZ νrad β = ∫ p : ℝ × ℝ, Real.exp (-2 * π * β * (p.1 + p.2)) ∂ν := by
      unfold lapZ νrad spinRadMarginal
      rw [integral_map hmeas_sum.aemeasurable (by fun_prop : Continuous fun s : ℝ =>
        Real.exp (-2 * π * β * s)).aestronglyMeasurable]
    have hZ2 : lapZ νrad (1 / β) = ∫ p : ℝ × ℝ, Real.exp (-2 * π * (1 / β) * (p.1 + p.2)) ∂ν := by
      unfold lapZ νrad spinRadMarginal
      rw [integral_map hmeas_sum.aemeasurable (by fun_prop : Continuous fun s : ℝ =>
        Real.exp (-2 * π * (1 / β) * s)).aestronglyMeasurable]
    have hpt : (fun p : ℝ × ℝ => spinThermalX β β p.1 p.2) =
        fun p => Real.exp (-2 * π * β * (p.1 + p.2)) -
          β ^ (-(1 : ℝ)) * Real.exp (-2 * π * (1 / β) * (p.1 + p.2)) := by
      ext p; rw [spinThermalX_diag_pos hβ]; unfold thermalDiff; simp only [Nat.cast_one]; ring_nf
    rw [hpt, integral_sub h1_int (h2_int.const_mul _), integral_const_mul, ← hZ1, ← hZ2,
      spinThermalXVac_diag_pos a hβ, ← virasoroProblem_w, virasoroProblem.gVac_thermalDiff a hβ,
      virasoroProblem_w] at hloc_d
    unfold srcV
    simp only [Nat.cast_one] at hloc_d ⊢
    have hdiv : 2 * π * a * (1 / β) = 2 * π * a / β := by ring
    have hdiv2 : -2 * π * (1 / β) = -2 * π / β := by ring
    rw [hdiv, hdiv2]
    linarith
  have hdiag_all : ∀ β : ℝ, 0 < β →
      Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν := by
    have hall := (ds_cont (w := 1) (analyticOnNhd_srcV virasoroProblem a) hνrad_Iio hsθ0 hsθ1
      hνrad_s hνrad_cross).1
    intro β hβ
    have h := hall β hβ
    unfold LapFin νrad spinRadMarginal at h
    rwa [integrable_map_measure (by fun_prop : Continuous fun s : ℝ =>
      Real.exp (-2 * π * β * s)).aestronglyMeasurable hmeas_sum.aemeasurable] at h
  have hfull_cross := spinD2_analytic_continuation_2D hB hθ0 hθ1 hνB hdiag_all hloc
  exact ⟨⟨ν, hν_supp, fun {β} hβ => hdiag_all β hβ, fun {βL βR} hL hR => hfull_cross βL βR hL hR⟩,
    hν_swap, hσ_le_ν⟩

/-! ### Section 5: Theorem LP-R (`dsl:reserve`) -/

/-- **Theorem LP-R** (`dsl:reserve`, `dual_spectrum_limit.tex`, work package LP2) at `d = 2`:
exact derivative separation and reserve on closed swap-invariant `X ⊆ E_B ∩ {t_L + t_R ≥ T₀}`. -/
theorem dslReserve : DslReserve := by
  intro a B T₀ s ha hB hT₀ hs0 hs1 X hXc hXs hX σ hσsupp hσswap hσint
  exact ⟨fun ⟨meas, _, hσle⟩ => dslReserve_forward ha hB (hX.trans inter_subset_left) hσsupp meas hσle,
    dslReserve_backward ha hB hT₀ hs0 hs1 hXc hXs hX hσsupp hσswap hσint⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.dslReserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.dslReserve

end FormalResearch.ModularBootstrap.Spin
