module

public import FormalResearch.ModularBootstrap.Spin.Statements
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedFinal
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# SPIN-F skeleton assembly: continuous-spin slope (`spinnotes:S3`) and `s4:S4` consequences

Proves `spinnotes:S3` (`SpinS3`) from the `Prop`s `SpinS1b`, `SpinS1c`, `SpinS22`, `SpinS22b`
and the already-proved spinless `O(1)` upper bound `Upper.Ramped.virasoro_corollary_E1_unconditional`,
following the paper's proof in `spinning_foundations.tex` (§4) and `spinning_s4.tex` (`s4:2.1`):

1. `spinFeasible_nonempty_of_S1b`: lifts a feasible spinless test from
   `virasoroProblem.feasible_nonempty` via `SpinS1b`.
2. `spinG_tendsto_zero_cocompact`, `spinDeltaA_partial_sum`, `lintegral_spinG_quad_le_tsum`:
   outward telescoping of `\mathcal G` via Riemann–Lebesgue and Tonelli/Fatou.
3. `spin_tip_localisation_quad` (`s4:2.1` at the `(\log n)^{2/3}` scale): three-class
   decomposition of dilated images using `SpinS22` (outward `L^1` control), `SpinS22b`
   (slit-strip fold estimate), and `spinWc_exp_mono`.
4. `lintegral_disc_le_four_quad`, **`spinS3_of_props`**: `D_4` symmetrisation, contradiction
   with `spin_half_mass` (`spinnotes:half`), and assembly of `SpinS3`.
5. **`spinS4_consequences_of_S3`**: the part of `s4:S4` supplied by `SpinS3` and `SpinS1e`
   (positivity of `T_L`, strong duality `\Delta_L = \Delta_{\rm spin} = a + \tau_{\max}(\Omega_L)`
   with attainment, and the leading-slope/Airy-upper chain for `a + \tau_{\max}(\Omega_L)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Ramped

/-! ### Section 1: Nonemptiness of the feasible set via `SpinS1b` -/

lemma spinFeasible_nonempty_of_S1b (hS1b : SpinS1b) {c : ℝ} (hc : 25 ≤ c) :
    {T : ℝ | 0 < T ∧ ∃ Φ,
      SpinIsFeasible (SpinTestClass ((c - 1) / 12)) liouvilleCone ((c - 1) / 12) T Φ}.Nonempty := by
  have ha : 2 ≤ (c - 1) / 12 := by linarith
  have hc_vir : 12 * virasoroProblem.totalShift ≤ c - 1 := by
    rw [virasoroProblem_totalShift]; linarith
  obtain ⟨T, hT, g, hg_cls, hg_vac, hg_pos⟩ := virasoroProblem.feasible_nonempty hc_vir
  obtain ⟨hcls_iff, hnorm_vac⟩ := (hS1b ha).2.2 g
  refine ⟨T, hT, spinRadialLift g, hcls_iff.mp hg_cls, ?_, ?_⟩
  · rw [(hnorm_vac hg_cls).2]; exact hg_vac
  · intro p hp
    rw [spinEvalT_radialLift g hp.1 hp.2.1]
    exact hg_pos (p.1 + p.2) hp.2.2

/-! ### Section 2: Outward telescoping and Tonelli/Fatou bound -/

/-- Riemann–Lebesgue for `Φ ∈ \overline{\mathcal A}_{\rm spin}`: `spinG a Φ → 0` at infinity. -/
lemma spinG_tendsto_zero_cocompact {a : ℝ} (ha : 0 < a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    Tendsto (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) (cocompact (ℝ × ℝ)) (𝓝 0) := by
  have hrl : Tendsto (𝓕 (spinToEuc Φ)) (cocompact (EuclideanSpace ℝ (Fin 2))) (𝓝 0) := by
    have h := tendsto_integral_exp_inner_smul_cocompact (spinToEuc Φ)
    exact h.congr fun w => (Real.fourier_eq (spinToEuc Φ) w).symm
  rw [hΦ.fourier_odd] at hrl
  have hneg : Tendsto (spinToEuc Φ) (cocompact (EuclideanSpace ℝ (Fin 2))) (𝓝 0) := by
    simpa using hrl.neg
  let e : ℝ × ℝ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![2 * Real.sqrt a * p.1, 2 * Real.sqrt a * p.2]
      invFun := fun x => (x 0 / (2 * Real.sqrt a), x 1 / (2 * Real.sqrt a))
      left_inv := fun p => by
        have hne : 2 * Real.sqrt a ≠ 0 := by positivity
        ext <;> simp [hne]
      right_inv := fun x => by
        have hne : 2 * Real.sqrt a ≠ 0 := by positivity
        ext i; fin_cases i <;> simp [mul_div_cancel₀ _ hne]
      continuous_toFun := by
        refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
        fin_cases i
        · exact continuous_const.mul continuous_fst
        · exact continuous_const.mul continuous_snd
      continuous_invFun :=
        ((EuclideanSpace.proj (0 : Fin 2)).continuous.div_const _).prodMk
          ((EuclideanSpace.proj (1 : Fin 2)).continuous.div_const _) }
  have hcomp : Tendsto (fun p : ℝ × ℝ => ((spinG a Φ p.1 p.2 : ℝ) : ℂ))
      (cocompact (ℝ × ℝ)) (𝓝 0) := by
    have he_coco : Tendsto e (cocompact (ℝ × ℝ)) (cocompact (EuclideanSpace ℝ (Fin 2))) := by
      rw [hasBasis_cocompact.tendsto_iff hasBasis_cocompact]
      intro K hK
      refine ⟨e ⁻¹' K, e.isCompact_preimage.mpr hK, fun p hp => hp⟩
    have h1 := hneg.comp he_coco
    refine h1.congr fun p => ?_
    simp [spinToEuc, spinG, e]
  have hre : Tendsto (fun p : ℝ × ℝ => (((spinG a Φ p.1 p.2 : ℝ) : ℂ)).re)
      (cocompact (ℝ × ℝ)) (𝓝 (0 : ℂ).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hcomp
  simpa using hre

/-- Finite outward telescoping identity for `\Delta_a \mathcal G`. -/
lemma spinDeltaA_partial_sum {a : ℝ} (ha : 2 < a) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) (M : ℕ) :
    ∑ m ∈ Finset.range M, ∑ ℓ ∈ Finset.range M,
        spinDeltaA a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR) =
      spinG a Φ xL xR - spinG a Φ (spinLambda a ^ M * xL) xR -
        spinG a Φ xL (spinLambda a ^ M * xR) +
        spinG a Φ (spinLambda a ^ M * xL) (spinLambda a ^ M * xR) := by
  have hgl : spinGamma a * spinLambda a = 1 :=
    mul_inv_cancel₀ (spinGamma_pos ha).ne'
  have hstep : ∀ u v : ℝ,
      spinDeltaA a Φ u v =
        spinG a Φ (spinLambda a * u) (spinLambda a * v) -
          spinG a Φ u (spinLambda a * v) -
          spinG a Φ (spinLambda a * u) v +
          spinG a Φ u v := by
    intro u v
    unfold spinDeltaA spinDa
    have h1 : spinGamma a * (spinLambda a * u) = u := by rw [← mul_assoc, hgl, one_mul]
    have h2 : spinGamma a * (spinLambda a * v) = v := by rw [← mul_assoc, hgl, one_mul]
    rw [h1, h2]
  have hinner : ∀ u : ℝ,
      ∑ ℓ ∈ Finset.range M,
          (spinG a Φ (spinLambda a * u) (spinLambda a ^ (ℓ + 1) * xR) -
            spinG a Φ u (spinLambda a ^ (ℓ + 1) * xR) -
            spinG a Φ (spinLambda a * u) (spinLambda a ^ ℓ * xR) +
            spinG a Φ u (spinLambda a ^ ℓ * xR)) =
        (spinG a Φ (spinLambda a * u) (spinLambda a ^ M * xR) -
          spinG a Φ u (spinLambda a ^ M * xR)) -
        (spinG a Φ (spinLambda a * u) xR - spinG a Φ u xR) := by
    intro u
    induction M with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hrew : ∀ m ∈ Finset.range M,
      ∑ ℓ ∈ Finset.range M, spinDeltaA a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR) =
        (spinG a Φ (spinLambda a ^ (m + 1) * xL) (spinLambda a ^ M * xR) -
          spinG a Φ (spinLambda a ^ m * xL) (spinLambda a ^ M * xR)) -
        (spinG a Φ (spinLambda a ^ (m + 1) * xL) xR -
          spinG a Φ (spinLambda a ^ m * xL) xR) := by
    intro m _
    have hpow : spinLambda a * (spinLambda a ^ m * xL) = spinLambda a ^ (m + 1) * xL := by
      rw [pow_succ']; ring
    have hsum_eq :
        ∑ ℓ ∈ Finset.range M, spinDeltaA a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR) =
          ∑ ℓ ∈ Finset.range M,
            (spinG a Φ (spinLambda a * (spinLambda a ^ m * xL)) (spinLambda a ^ (ℓ + 1) * xR) -
              spinG a Φ (spinLambda a ^ m * xL) (spinLambda a ^ (ℓ + 1) * xR) -
              spinG a Φ (spinLambda a * (spinLambda a ^ m * xL)) (spinLambda a ^ ℓ * xR) +
              spinG a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR)) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [hstep, show spinLambda a * (spinLambda a ^ ℓ * xR) = spinLambda a ^ (ℓ + 1) * xR by
        rw [pow_succ']; ring]
    rw [hsum_eq, hinner, hpow]
  rw [Finset.sum_congr rfl hrew, Finset.sum_sub_distrib]
  have h1 : ∑ m ∈ Finset.range M,
      (spinG a Φ (spinLambda a ^ (m + 1) * xL) (spinLambda a ^ M * xR) -
        spinG a Φ (spinLambda a ^ m * xL) (spinLambda a ^ M * xR)) =
      spinG a Φ (spinLambda a ^ M * xL) (spinLambda a ^ M * xR) -
        spinG a Φ xL (spinLambda a ^ M * xR) := by
    simpa using Finset.sum_range_sub
      (fun m => spinG a Φ (spinLambda a ^ m * xL) (spinLambda a ^ M * xR)) M
  have h2 : ∑ m ∈ Finset.range M,
      (spinG a Φ (spinLambda a ^ (m + 1) * xL) xR -
        spinG a Φ (spinLambda a ^ m * xL) xR) =
      spinG a Φ (spinLambda a ^ M * xL) xR - spinG a Φ xL xR := by
    simpa using Finset.sum_range_sub (fun m => spinG a Φ (spinLambda a ^ m * xL) xR) M
  rw [h1, h2]; ring

/-- Pointwise `ENNReal` outward telescoping bound for `xL, xR > 0`. -/
lemma spinG_abs_le_tsum_ennreal {a : ℝ} (ha : 2 < a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {xL xR : ℝ} (hxL : 0 < xL) (hxR : 0 < xR) :
    ENNReal.ofReal |spinG a Φ xL xR| ≤
      ∑' q : ℕ × ℕ, ENNReal.ofReal |spinDeltaA a Φ (spinLambda a ^ q.1 * xL) (spinLambda a ^ q.2 * xR)| := by
  have ha0 : 0 < a := by linarith
  have hrl := spinG_tendsto_zero_cocompact ha0 hΦ
  have hlam : 1 < spinLambda a := spinLambda_gt_one ha
  have hpow : Tendsto (fun M : ℕ => spinLambda a ^ M) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlam
  have hcoco_of_norm : ∀ f : ℕ → ℝ × ℝ, Tendsto (fun M => ‖f M‖) atTop atTop →
      Tendsto f atTop (cocompact (ℝ × ℝ)) := by
    intro f hf
    rw [tendsto_iff_forall_eventually_mem]
    intro s hs
    rw [mem_cocompact] at hs
    obtain ⟨K, hK, hKs⟩ := hs
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    filter_upwards [hf.eventually (eventually_gt_atTop R)] with M hM
    refine hKs ?_
    intro hmem
    have hle : ‖f M‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hmem
    linarith
  have hcoco1 : Tendsto (fun M : ℕ => (spinLambda a ^ M * xL, xR)) atTop (cocompact (ℝ × ℝ)) := by
    refine hcoco_of_norm _ (tendsto_atTop_mono (fun M => ?_) (hpow.atTop_mul_const hxL))
    calc spinLambda a ^ M * xL = |spinLambda a ^ M * xL| :=
          (abs_of_pos (mul_pos (pow_pos (by linarith) M) hxL)).symm
      _ = ‖(spinLambda a ^ M * xL, xR).1‖ := rfl
      _ ≤ ‖(spinLambda a ^ M * xL, xR)‖ := norm_fst_le _
  have hcoco2 : Tendsto (fun M : ℕ => (xL, spinLambda a ^ M * xR)) atTop (cocompact (ℝ × ℝ)) := by
    refine hcoco_of_norm _ (tendsto_atTop_mono (fun M => ?_) (hpow.atTop_mul_const hxR))
    calc spinLambda a ^ M * xR = |spinLambda a ^ M * xR| :=
          (abs_of_pos (mul_pos (pow_pos (by linarith) M) hxR)).symm
      _ = ‖(xL, spinLambda a ^ M * xR).2‖ := rfl
      _ ≤ ‖(xL, spinLambda a ^ M * xR)‖ := norm_snd_le _
  have hcoco3 : Tendsto (fun M : ℕ => (spinLambda a ^ M * xL, spinLambda a ^ M * xR))
      atTop (cocompact (ℝ × ℝ)) := by
    refine hcoco_of_norm _ (tendsto_atTop_mono (fun M => ?_) (hpow.atTop_mul_const hxL))
    calc spinLambda a ^ M * xL = |spinLambda a ^ M * xL| :=
          (abs_of_pos (mul_pos (pow_pos (by linarith) M) hxL)).symm
      _ = ‖(spinLambda a ^ M * xL, spinLambda a ^ M * xR).1‖ := rfl
      _ ≤ ‖(spinLambda a ^ M * xL, spinLambda a ^ M * xR)‖ := norm_fst_le _
  have h1 : Tendsto (fun M : ℕ => spinG a Φ (spinLambda a ^ M * xL) xR) atTop (𝓝 0) :=
    hrl.comp hcoco1
  have h2 : Tendsto (fun M : ℕ => spinG a Φ xL (spinLambda a ^ M * xR)) atTop (𝓝 0) :=
    hrl.comp hcoco2
  have h3 : Tendsto (fun M : ℕ => spinG a Φ (spinLambda a ^ M * xL) (spinLambda a ^ M * xR))
      atTop (𝓝 0) := hrl.comp hcoco3
  have hsum_lim : Tendsto (fun M : ℕ =>
      ∑ m ∈ Finset.range M, ∑ ℓ ∈ Finset.range M,
        spinDeltaA a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR))
      atTop (𝓝 (spinG a Φ xL xR)) := by
    have hlim : Tendsto (fun M : ℕ =>
        spinG a Φ xL xR - spinG a Φ (spinLambda a ^ M * xL) xR -
          spinG a Φ xL (spinLambda a ^ M * xR) +
          spinG a Φ (spinLambda a ^ M * xL) (spinLambda a ^ M * xR))
        atTop (𝓝 (spinG a Φ xL xR - 0 - 0 + 0)) :=
      ((tendsto_const_nhds.sub h1).sub h2).add h3
    simp only [sub_zero, add_zero] at hlim
    exact hlim.congr fun M => (spinDeltaA_partial_sum ha Φ xL xR M).symm
  have hlim_en : Tendsto (fun M : ℕ =>
      ENNReal.ofReal |∑ m ∈ Finset.range M, ∑ ℓ ∈ Finset.range M,
        spinDeltaA a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR)|)
      atTop (𝓝 (ENNReal.ofReal |spinG a Φ xL xR|)) :=
    (ENNReal.continuous_ofReal.comp continuous_abs).continuousAt.tendsto.comp hsum_lim
  refine le_of_tendsto hlim_en (Eventually.of_forall fun M => ?_)
  have htri : |∑ m ∈ Finset.range M, ∑ ℓ ∈ Finset.range M,
      spinDeltaA a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR)| ≤
      ∑ q ∈ Finset.range M ×ˢ Finset.range M,
        |spinDeltaA a Φ (spinLambda a ^ q.1 * xL) (spinLambda a ^ q.2 * xR)| := by
    rw [Finset.sum_product]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
  calc ENNReal.ofReal |∑ m ∈ Finset.range M, ∑ ℓ ∈ Finset.range M,
          spinDeltaA a Φ (spinLambda a ^ m * xL) (spinLambda a ^ ℓ * xR)|
      ≤ ENNReal.ofReal (∑ q ∈ Finset.range M ×ˢ Finset.range M,
          |spinDeltaA a Φ (spinLambda a ^ q.1 * xL) (spinLambda a ^ q.2 * xR)|) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ∑ q ∈ Finset.range M ×ˢ Finset.range M,
          ENNReal.ofReal |spinDeltaA a Φ (spinLambda a ^ q.1 * xL) (spinLambda a ^ q.2 * xR)| :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ ∑' q : ℕ × ℕ,
          ENNReal.ofReal |spinDeltaA a Φ (spinLambda a ^ q.1 * xL) (spinLambda a ^ q.2 * xR)| :=
        sum_le_tsum _

/-- Tonelli/Fatou outward telescoping bound on any measurable subset of the open first quadrant. -/
lemma lintegral_spinG_quad_le_tsum {a : ℝ} (ha : 2 < a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    (hE_pos : E ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}) :
    ∫⁻ p in E, ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ≤
      ∑' q : ℕ × ℕ, ∫⁻ p in E,
        ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
          spinWc a p.1 * spinWc a p.2) := by
  have hmeas : ∀ q : ℕ × ℕ, Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
        spinWc a p.1 * spinWc a p.2)) := by
    intro q
    have hG : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
      unfold spinG
      exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
    have hDa : Continuous (fun p : ℝ × ℝ => spinDa a Φ p.1 p.2) := by
      unfold spinDa
      exact (((hG.sub (hG.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).sub
        (hG.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).add
        (hG.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
    have hDelta : Continuous (fun p : ℝ × ℝ =>
        spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)) := by
      unfold spinDeltaA
      exact hDa.comp (((continuous_const.mul (continuous_const.mul continuous_fst)).prodMk
        (continuous_const.mul (continuous_const.mul continuous_snd))))
    have hWc : Continuous (spinWc a) := by
      unfold spinWc spinV1; fun_prop
    exact (ENNReal.continuous_ofReal.comp
      ((hDelta.abs.mul (hWc.comp continuous_fst)).mul (hWc.comp continuous_snd))).measurable
  rw [← lintegral_tsum fun q => (hmeas q).aemeasurable]
  refine setLIntegral_mono_ae' hE (Eventually.of_forall fun p hp => ?_)
  have hp_pos := hE_pos hp
  have h1 := spinG_abs_le_tsum_ennreal ha hΦ hp_pos.1 hp_pos.2
  calc ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
      = ENNReal.ofReal |spinG a Φ p.1 p.2| * ENNReal.ofReal (spinWc a p.1 * spinWc a p.2) := by
        rw [mul_assoc, ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ (∑' q : ℕ × ℕ, ENNReal.ofReal |spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)|) *
          ENNReal.ofReal (spinWc a p.1 * spinWc a p.2) := by gcongr
    _ = ∑' q : ℕ × ℕ,
          ENNReal.ofReal |spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
            ENNReal.ofReal (spinWc a p.1 * spinWc a p.2) := ENNReal.tsum_mul_right.symm
    _ = ∑' q : ℕ × ℕ,
          ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
            spinWc a p.1 * spinWc a p.2) := by
        refine tsum_congr fun q => ?_
        rw [mul_assoc, ENNReal.ofReal_mul (abs_nonneg _)]

/-! ### Section 3: Change-of-variables and asymptotic helpers -/

/-- `ENNReal` scaling change of variables on `ℝ × ℝ`. -/
private lemma lintegral_prod_scale {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, f (c₁ * p.1, c₂ * p.2) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) * ∫⁻ p : ℝ × ℝ, f p := by
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.mulLeft₀ c₁ hc₁.ne').prodCongr (MeasurableEquiv.mulLeft₀ c₂ hc₂.ne')
  have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) • (volume : Measure (ℝ × ℝ)) := by
    have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (c₁ * ·) (c₂ * ·) := rfl
    rw [he, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ (measurable_const_mul c₁) (measurable_const_mul c₂),
      Real.map_volume_mul_left hc₁.ne', Real.map_volume_mul_left hc₂.ne',
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      abs_of_pos (inv_pos.mpr hc₁), abs_of_pos (inv_pos.mpr hc₂),
      ENNReal.ofReal_mul (inv_pos.mpr hc₁).le]
  have heq : ∫⁻ p : ℝ × ℝ, f (c₁ * p.1, c₂ * p.2) =
      ∫⁻ p : ℝ × ℝ, f p ∂(Measure.map e volume) :=
    (lintegral_map_equiv f e).symm
  rw [heq, hmp, lintegral_smul_measure, smul_eq_mul]

/-- `ENNReal` `(ξ, d) ↦ (ξ + d, ξ - d)` change of variables (Jacobian `2`). -/
private lemma lintegral_xi_d (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, f p =
      ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, f (q.1 + q.2, q.1 - q.2) := by
  let e₁ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun q => (q.1 + q.2, q.2)
      invFun := fun q => (q.1 - q.2, q.2)
      left_inv := fun q => by ext <;> simp
      right_inv := fun q => by ext <;> simp
      measurable_toFun := (measurable_fst.add measurable_snd).prodMk measurable_snd
      measurable_invFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd }
  let e₂ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun q => (q.1, q.1 - 2 * q.2)
      invFun := fun q => (q.1, (q.1 - q.2) / 2)
      left_inv := fun q => Prod.ext rfl (by ring)
      right_inv := fun q => Prod.ext rfl (by ring)
      measurable_toFun := measurable_fst.prodMk (measurable_fst.sub (measurable_const.mul measurable_snd))
      measurable_invFun := measurable_fst.prodMk ((measurable_fst.sub measurable_snd).div_const 2) }
  have hcomp : ∀ q : ℝ × ℝ, e₂ (e₁ q) = (q.1 + q.2, q.1 - q.2) := fun q =>
    Prod.ext rfl (by dsimp [e₁, e₂]; ring)
  have h1 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ q : ℝ × ℝ, g (e₁ q) = ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
      lintegral_prod (fun q => g (e₁ q)) (hg.comp e₁.measurable).aemeasurable]
    have hswap1 : ∫⁻ x : ℝ, ∫⁻ y : ℝ, g (e₁ (x, y)) = ∫⁻ y : ℝ, ∫⁻ x : ℝ, g (e₁ (x, y)) :=
      lintegral_lintegral_swap (f := fun x y => g (e₁ (x, y))) (hg.comp e₁.measurable).aemeasurable
    have hswap2 : ∫⁻ x : ℝ, ∫⁻ y : ℝ, g (x, y) = ∫⁻ y : ℝ, ∫⁻ x : ℝ, g (x, y) :=
      lintegral_lintegral_swap (f := fun x y => g (x, y)) hg.aemeasurable
    rw [hswap1, hswap2]
    refine lintegral_congr fun y => ?_
    simpa [e₁] using lintegral_add_right_eq_self (fun x => g (x, y)) y
  have h2 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ q : ℝ × ℝ, g (e₂ q) = ENNReal.ofReal (1 / 2) * ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
      lintegral_prod (fun q => g (e₂ q)) (hg.comp e₂.measurable).aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    let e4 : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ (-2 : ℝ) (by norm_num)
    have hm4 : Measure.map e4 (volume : Measure ℝ) = ENNReal.ofReal (1 / 2) • (volume : Measure ℝ) := by
      have h := Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0)
      have habs : |(-2 : ℝ)⁻¹| = 1 / 2 := by norm_num
      rw [habs] at h
      exact h
    have hl : ∫⁻ y : ℝ, g (x, x + (-2 : ℝ) * y) =
        ENNReal.ofReal (1 / 2) * ∫⁻ z : ℝ, g (x, x + z) := by
      have h := (lintegral_map_equiv (μ := (volume : Measure ℝ)) (fun z => g (x, x + z)) e4).symm
      rw [hm4, lintegral_smul_measure, smul_eq_mul] at h
      exact h
    have hshift : ∫⁻ z : ℝ, g (x, x + z) = ∫⁻ z : ℝ, g (x, z) :=
      lintegral_add_left_eq_self (fun z => g (x, z)) x
    have heq : (fun y : ℝ => g (e₂ (x, y))) = fun y : ℝ => g (x, x + (-2 : ℝ) * y) := by
      ext y; simp [e₂, sub_eq_add_neg]
    rw [heq, hl, hshift]
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := e₁.trans e₂
  have he_eq : ∀ q : ℝ × ℝ, e q = (q.1 + q.2, q.1 - q.2) := fun q => hcomp q
  have hmap_e : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2) • (volume : Measure (ℝ × ℝ)) := by
    ext s hs
    rw [Measure.map_apply e.measurable hs, smul_apply, smul_eq_mul]
    have h_ind := h1 (fun q => (s.indicator 1) (e₂ q))
      ((measurable_const.indicator hs).comp e₂.measurable)
    have h_ind2 := h2 (s.indicator 1) (measurable_const.indicator hs)
    have h_lhs : ∫⁻ q : ℝ × ℝ, (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (e₂ (e₁ q)) = volume (e ⁻¹' s) := by
      have : (fun q => (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (e₂ (e₁ q))) =
          (e ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞) := by
        ext q; rfl
      rw [this, lintegral_indicator_one (e.measurable hs)]
    have h_rhs : ∫⁻ q : ℝ × ℝ, (s.indicator 1) q = volume s := lintegral_indicator_one hs
    rw [← h_lhs, h_ind, h_ind2, h_rhs]
  have hl : ∫⁻ q : ℝ × ℝ, f (q.1 + q.2, q.1 - q.2) =
      ENNReal.ofReal (1 / 2) * ∫⁻ p : ℝ × ℝ, f p := by
    have h := (lintegral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) f e).symm
    simp_rw [he_eq] at h
    rw [h, hmap_e, lintegral_smul_measure, smul_eq_mul]
  rw [hl, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Sum of Jacobians `∑'_{q : ℕ × ℕ} γ^{q.1 + q.2} = (1 - γ)⁻²` in `ℝ≥0∞`. -/
private lemma tsum_gamma_pair {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∑' q : ℕ × ℕ, ENNReal.ofReal (γ ^ q.1 * γ ^ q.2) = ENNReal.ofReal ((1 - γ)⁻¹ * (1 - γ)⁻¹) := by
  have h1 : ∑' m : ℕ, ENNReal.ofReal (γ ^ m) = ENNReal.ofReal (1 - γ)⁻¹ := by
    have hs := hasSum_geometric_of_lt_one hγ0 hγ1
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => pow_nonneg hγ0 m) hs.summable, hs.tsum_eq]
  rw [tsum_prod']
  calc ∑' m : ℕ, ∑' ℓ : ℕ, ENNReal.ofReal (γ ^ m * γ ^ ℓ)
      = ∑' m : ℕ, ∑' ℓ : ℕ, ENNReal.ofReal (γ ^ m) * ENNReal.ofReal (γ ^ ℓ) := by
        refine tsum_congr fun m => tsum_congr fun ℓ => ENNReal.ofReal_mul (pow_nonneg hγ0 m)
    _ = ∑' m : ℕ, ENNReal.ofReal (γ ^ m) * ∑' ℓ : ℕ, ENNReal.ofReal (γ ^ ℓ) := by
        refine tsum_congr fun m => ENNReal.tsum_mul_left
    _ = (∑' m : ℕ, ENNReal.ofReal (γ ^ m)) * (∑' ℓ : ℕ, ENNReal.ofReal (γ ^ ℓ)) :=
        ENNReal.tsum_mul_right
    _ = ENNReal.ofReal ((1 - γ)⁻¹ * (1 - γ)⁻¹) := by
        rw [h1, ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith))]

private lemma rpow_one_mul_neg_two_thirds {n : ℝ} (hn : 0 < n) :
    n * n ^ (-(2 / 3 : ℝ)) = n ^ ((1 : ℝ) / 3) := by
  calc n * n ^ (-(2 / 3 : ℝ))
      = n ^ (1 : ℝ) * n ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
    _ = n ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := (Real.rpow_add hn _ _).symm
    _ = n ^ ((1 : ℝ) / 3) := by norm_num

private lemma tendsto_delta_zero (K : ℝ) :
    Tendsto (fun n : ℝ => K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) atTop (𝓝 0) := by
  have hlog := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)
  have h1 : Tendsto (fun n : ℝ => Real.log n / n) atTop (𝓝 0) := by
    simpa [Real.rpow_one] using hlog.tendsto_div_nhds_zero
  have h2 : Tendsto (fun n : ℝ => (Real.log n / n) ^ ((2 : ℝ) / 3)) atTop (𝓝 0) := by
    have hc := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).continuousAt.tendsto.comp h1
    rw [Real.zero_rpow (by norm_num : ((2 : ℝ) / 3) ≠ 0)] at hc
    exact hc
  have h3 : Tendsto (fun n : ℝ => K * (Real.log n / n) ^ ((2 : ℝ) / 3)) atTop (𝓝 0) := by
    simpa using h2.const_mul K
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  have hn0 : 0 < n := by linarith
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn.le
  rw [Real.div_rpow hl0 hn0.le, div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  ring

private lemma tendsto_term2_zero {K : ℝ} (hK : 0 < K) :
    Tendsto (fun n : ℝ =>
      4 * n ^ 2 * Real.exp (-(π * n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) / 3)))
      atTop (𝓝 0) := by
  have hlog_o : Tendsto (fun n : ℝ => Real.log n / n) atTop (𝓝 0) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun n : ℝ => 4 * n⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (4 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hinv
  have hsmall : ∀ᶠ n : ℝ in atTop, Real.log n / n ≤ (π * K / 9) ^ 3 :=
    hlog_o.eventually (ge_mem_nhds (by positivity))
  filter_upwards [eventually_ge_atTop (Real.exp 1), hsmall] with n hn1 hln
  have hn_pos : 0 < n := lt_of_lt_of_le (Real.exp_pos 1) hn1
  have hlog_ge1 : 1 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 1) hn1; rwa [Real.log_exp] at this
  have hlog_le : Real.log n ≤ (π * K / 9) ^ 3 * n := (div_le_iff₀ hn_pos).mp hln
  have hlog13 : (Real.log n) ^ ((1 : ℝ) / 3) ≤ (π * K / 9) * n ^ ((1 : ℝ) / 3) := by
    have hc_nn : 0 ≤ π * K / 9 := by positivity
    calc (Real.log n) ^ ((1 : ℝ) / 3)
        ≤ ((π * K / 9) ^ 3 * n) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by linarith) hlog_le (by norm_num)
      _ = ((π * K / 9) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) * n ^ ((1 : ℝ) / 3) :=
          Real.mul_rpow (by positivity) hn_pos.le
      _ = ((π * K / 9) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) * n ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_natCast (π * K / 9) 3]; norm_num
      _ = (π * K / 9) * n ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_mul hc_nn]; norm_num
  have hprod_log : 3 * Real.log n ≤
      π * n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) / 3 := by
    have hnr := rpow_one_mul_neg_two_thirds hn_pos
    have hlr : (Real.log n) ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) = Real.log n := by
      rw [← Real.rpow_add (by linarith : 0 < Real.log n)]; norm_num
    have hmul := mul_le_mul_of_nonneg_right hlog13
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log n) ((2 : ℝ) / 3))
    rw [hlr] at hmul
    calc 3 * Real.log n
        ≤ 3 * ((π * K / 9) * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3)) := by linarith
      _ = π * (n ^ ((1 : ℝ) / 3)) * (K * (Real.log n) ^ ((2 : ℝ) / 3)) / 3 := by ring
      _ = π * (n * n ^ (-(2 / 3 : ℝ))) * (K * (Real.log n) ^ ((2 : ℝ) / 3)) / 3 := by rw [hnr]
      _ = π * n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) / 3 := by ring
  have hexp_le : Real.exp (-(π * n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) / 3)) ≤
      n ^ (-(3 : ℝ)) := by
    calc Real.exp (-(π * n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) / 3))
        ≤ Real.exp (-(3 * Real.log n)) := Real.exp_le_exp.mpr (by linarith)
      _ = n ^ (-(3 : ℝ)) := by rw [Real.rpow_def_of_pos hn_pos]; congr 1; ring
  have hpow_eq : n ^ 2 * n ^ (-(3 : ℝ)) = n⁻¹ := by
    rw [← Real.rpow_natCast n 2, ← Real.rpow_add hn_pos]
    norm_num
    exact Real.rpow_neg_one n
  calc 4 * n ^ 2 * Real.exp (-(π * n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) / 3))
      ≤ 4 * n ^ 2 * n ^ (-(3 : ℝ)) := by gcongr
    _ = 4 * n⁻¹ := by rw [mul_assoc, hpow_eq]

private lemma tendsto_term1_zero {C_cls1 K k : ℝ} (hC : 0 ≤ C_cls1) (hK : 0 < K) :
    Tendsto (fun n : ℝ =>
      C_cls1 * n ^ (k + 2) * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3))⁻¹ *
        n ^ (-(k + 4))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℝ => (C_cls1 / K) * n ^ (-(4 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)).const_mul (C_cls1 / K)
  refine squeeze_zero' ?_ ?_ hinv
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with n hn1
    have hn_pos : 0 < n := lt_of_lt_of_le (Real.exp_pos 1) hn1
    have hlog_ge1 : 1 ≤ Real.log n := by
      have := Real.log_le_log (Real.exp_pos 1) hn1; rwa [Real.log_exp] at this
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with n hn1
    have hn_pos : 0 < n := lt_of_lt_of_le (Real.exp_pos 1) hn1
    have hlog_ge1 : 1 ≤ Real.log n := by
      have := Real.log_le_log (Real.exp_pos 1) hn1; rwa [Real.log_exp] at this
    have hlog_rpow : 1 ≤ (Real.log n) ^ ((2 : ℝ) / 3) := Real.one_le_rpow hlog_ge1 (by norm_num)
    have hinv_le : (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3))⁻¹ ≤
        K⁻¹ * n ^ ((2 : ℝ) / 3) := by
      rw [mul_inv, mul_inv, ← Real.rpow_neg hn_pos.le, neg_neg]
      have h1 : ((Real.log n) ^ ((2 : ℝ) / 3))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlog_rpow
      calc K⁻¹ * n ^ ((2 : ℝ) / 3) * ((Real.log n) ^ ((2 : ℝ) / 3))⁻¹
          ≤ K⁻¹ * n ^ ((2 : ℝ) / 3) * 1 := by gcongr
        _ = K⁻¹ * n ^ ((2 : ℝ) / 3) := mul_one _
    have hexp : n ^ (k + 2) * n ^ ((2 : ℝ) / 3) * n ^ (-(k + 4)) = n ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]; congr 1; ring
    calc C_cls1 * n ^ (k + 2) * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3))⁻¹ *
            n ^ (-(k + 4))
        ≤ C_cls1 * n ^ (k + 2) * (K⁻¹ * n ^ ((2 : ℝ) / 3)) * n ^ (-(k + 4)) := by gcongr
      _ = (C_cls1 / K) * (n ^ (k + 2) * n ^ ((2 : ℝ) / 3) * n ^ (-(k + 4))) := by
          rw [div_eq_mul_inv]; ring
      _ = (C_cls1 / K) * n ^ (-(4 / 3 : ℝ)) := by rw [hexp]

/-! ### Section 4: Tip localisation (`s4:2.1` at the `(\log n)^{2/3}` scale) -/

/-- Elementary geometric gap lemma for the complement of Class 1. -/
private lemma spin_gap_ge_delta {bStar δ p1 p2 y1 y2 : ℝ}
    (hb_pos : 0 < bStar) (hδ_pos : 0 < δ) (hδ_lt : δ < bStar / 100)
    (hp1 : 0 < p1) (hp2 : 0 < p2) (hdisc : (p1 ^ 2 + p2 ^ 2) / 2 < (bStar - δ) ^ 2)
    (hy1 : p1 ≤ y1) (hy2 : p2 ≤ y2)
    (hnot : ¬ ((y1 + y2) / 2 ≤ bStar - δ / 2 ∧ |(y1 - y2) / 2| ≤ 3 * bStar / 4)) :
    δ ≤ (y1 - p1) + (y2 - p2) := by
  have hx1_pos : 0 < bStar - δ := by linarith
  rw [not_and_or, not_le, not_le] at hnot
  rcases hnot with hξ_gt | hd_gt
  · have hξx_lt : (p1 + p2) / 2 < bStar - δ := by
      have hsq : ((p1 + p2) / 2) ^ 2 < (bStar - δ) ^ 2 := by
        have : ((p1 + p2) / 2) ^ 2 + ((p1 - p2) / 2) ^ 2 = (p1 ^ 2 + p2 ^ 2) / 2 := by ring
        nlinarith [sq_nonneg ((p1 - p2) / 2)]
      nlinarith
    linarith
  · have hy1_pos : 0 < y1 := lt_of_lt_of_le hp1 hy1
    have hy2_pos : 0 < y2 := lt_of_lt_of_le hp2 hy2
    have hmax_gt : 3 * bStar / 2 < max y1 y2 := by
      have h1 : 2 * |(y1 - y2) / 2| = |y1 - y2| := by
        rw [abs_div, abs_two]; ring
      have h2 : |y1 - y2| < max y1 y2 := by
        rcases le_total y1 y2 with hle | hle
        · rw [abs_of_nonpos (by linarith), max_eq_right hle]; linarith
        · rw [abs_of_nonneg (by linarith), max_eq_left hle]; linarith
      linarith
    have hx1_lt_b : (bStar - δ) ^ 2 < bStar ^ 2 := by nlinarith
    have hsb_nn : 0 ≤ Real.sqrt 2 * bStar := mul_nonneg (Real.sqrt_nonneg 2) hb_pos.le
    have hp1_lt : p1 < Real.sqrt 2 * bStar := by
      have hsq : p1 ^ 2 < (Real.sqrt 2 * bStar) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        nlinarith [sq_nonneg p2]
      nlinarith
    have hp2_lt : p2 < Real.sqrt 2 * bStar := by
      have hsq : p2 ^ 2 < (Real.sqrt 2 * bStar) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        nlinarith [sq_nonneg p1]
      nlinarith
    have hsqrt2 : Real.sqrt 2 < 149 / 100 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h149 : Real.sqrt 2 * bStar < (149 / 100) * bStar :=
      mul_lt_mul_of_pos_right hsqrt2 hb_pos
    rcases le_total y1 y2 with hle | hle
    · rw [max_eq_right hle] at hmax_gt; linarith
    · rw [max_eq_left hle] at hmax_gt; linarith

set_option maxHeartbeats 400000 in
/-- Three-class bound on the first-quadrant cap `E` (`s4:2.1` at `p = 1`) from `SpinS22` and `SpinS22b`. -/
theorem spin_tip_localisation_quad (hS22 : SpinS22) (hS22b : SpinS22b) :
    ∃ K c₁ : ℝ, 0 < K ∧ 40 ≤ c₁ ∧
      ∀ {c : ℝ}, c₁ ≤ c →
        let n := c - 1
        let a := n / 12
        let δ := K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)
        let x1 := spinBStar a - δ
        0 < δ ∧ δ < spinBStar a / 100 ∧
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
          ∫⁻ p in {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < x1 ^ 2},
            ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) <
              ENNReal.ofReal (1 / 8) := by
  obtain ⟨k, C, κ, δ₀, n₀, hk0, hC0, hκ0, hδ₀, hn₀, hS22b_main⟩ := hS22b
  let M_exp : ℝ := (k + 4) / (κ * (2 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hM_pos : 0 < M_exp := by positivity
  let K : ℝ := max 1 (M_exp ^ ((2 : ℝ) / 3))
  have hK_pos : 0 < K := by positivity
  have hK_exp : k + 4 ≤ κ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) * K ^ ((3 : ℝ) / 2) := by
    have h1 : M_exp ≤ K ^ ((3 : ℝ) / 2) := by
      calc M_exp = (M_exp ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) := by
            rw [← Real.rpow_mul hM_pos.le]; norm_num
        _ ≤ K ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow (by positivity) (le_max_right _ _) (by norm_num)
    have hfac : 0 < κ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
    calc k + 4 = (κ * (2 : ℝ) ^ (-(3 / 2 : ℝ))) * M_exp := by
          dsimp [M_exp]; field_simp [hfac.ne']
      _ ≤ (κ * (2 : ℝ) ^ (-(3 / 2 : ℝ))) * K ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h1 hfac.le
  let C_cls1 : ℝ := 2 * xiStar * (2 * xiStar + C) * C * 2
  have hC1_nn : 0 ≤ C_cls1 := by dsimp [C_cls1]; have := xiStar_pos; positivity
  have hev_δ : ∀ᶠ n : ℝ in atTop,
      K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3) < (xiStar / 2) / 100 :=
    (tendsto_delta_zero K).eventually (gt_mem_nhds (by have := xiStar_pos; positivity))
  have hev_t1 : ∀ᶠ n : ℝ in atTop,
      C_cls1 * n ^ (k + 2) * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3))⁻¹ *
        n ^ (-(k + 4)) < 1 / 16 :=
    (tendsto_term1_zero hC1_nn hK_pos).eventually (gt_mem_nhds (by norm_num))
  have hev_t2 : ∀ᶠ n : ℝ in atTop,
      4 * n ^ 2 * Real.exp (-(π * n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) / 3)) <
        1 / 16 :=
    (tendsto_term2_zero hK_pos).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hev_δ.and (hev_t1.and hev_t2))
  let c₁ : ℝ := max (max 40 (n₀ + 1)) (max (N₁ + 1) (Real.exp 1 + 1))
  refine ⟨K, c₁, hK_pos, (le_max_left _ _).trans (le_max_left _ _), fun {c} hc => ?_⟩
  have hc40 : 40 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcn0 : n₀ + 1 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcN1 : N₁ ≤ c - 1 := by
    have : N₁ + 1 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
    linarith
  have hce : Real.exp 1 ≤ c - 1 := by
    have : Real.exp 1 + 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
    linarith
  set n : ℝ := c - 1
  set a : ℝ := n / 12
  set δ : ℝ := K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)
  set bStar : ℝ := spinBStar a
  set x1 : ℝ := bStar - δ
  set D : ℝ := 3 * bStar / 4
  have hn_pos : 0 < n := by linarith
  have ha_ge : (13 / 4 : ℝ) ≤ a := by dsimp [a, n]; linarith
  have ha2 : 2 < a := by linarith
  have hlog_ge1 : 1 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 1) hce; rwa [Real.log_exp] at this
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hγ_pos : 0 < spinGamma a := spinGamma_pos ha2
  have hγ_lt1 : spinGamma a < 1 := spinGamma_lt_one ha2
  have hγ_ge_half : 1 / 2 ≤ spinGamma a := by
    unfold spinGamma
    have : (1 / 4 : ℝ) ≤ 1 - 2 / a := by
      have : 2 / a ≤ 2 / (13 / 4 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha_ge
      linarith
    calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by norm_num
      _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt this
  have hbStar_ge : xiStar / 2 ≤ bStar := by
    dsimp [bStar]; unfold spinBStar; nlinarith [xiStar_pos]
  have hbStar_le : bStar ≤ xiStar := by
    dsimp [bStar]; unfold spinBStar; nlinarith [xiStar_pos]
  obtain ⟨hδ_sm, ht1_sm, ht2_sm⟩ := hN₁ n hcN1
  have hδ_lt : δ < bStar / 100 := lt_of_lt_of_le hδ_sm (by linarith)
  have hx1_pos : 0 < x1 := by dsimp [x1]; linarith [xiStar_pos]
  refine ⟨hδ_pos, hδ_lt, fun {Φ} hΦ hM2 => ?_⟩
  set E : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < x1 ^ 2}
  have hE_meas : MeasurableSet E :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        (isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet)
  have hE_pos : E ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := fun _ hp => ⟨hp.1, hp.2.1⟩
  obtain ⟨_, _, _, _, hDelta_int, hDelta_L1⟩ := (hS22 hc40).1 hΦ
  have hDelta_le4 : ∫ p : ℝ × ℝ, |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤ 4 := by
    have hlam_inv : (spinLambda a)⁻¹ ≤ 1 := by
      unfold spinLambda; rw [inv_inv]; exact hγ_lt1.le
    have hlam_inv_nn : 0 ≤ (spinLambda a)⁻¹ := by
      unfold spinLambda; rw [inv_inv]; exact hγ_pos.le
    have hsq : (1 + (spinLambda a)⁻¹) ^ 2 ≤ 4 := by nlinarith
    rw [hM2, mul_one] at hDelta_L1
    exact hDelta_L1.trans hsq
  obtain ⟨⟨hS_int, hS_le⟩, hfold_b, _⟩ := hS22b_main hcn0 hΦ hM2
  have htel := lintegral_spinG_quad_le_tsum ha2 hΦ hE_meas hE_pos
  let A_cls1 : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧ (y.1 + y.2) / 2 ≤ bStar - δ / 2 ∧ |(y.1 - y.2) / 2| ≤ D}
  have hA1_meas : MeasurableSet A_cls1 :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet.inter
          (isClosed_le (((continuous_fst.sub continuous_snd).div_const 2).abs)
            continuous_const).measurableSet))
  have hfold_exp : Real.exp (-κ * n * (δ / 2) ^ ((3 : ℝ) / 2)) ≤ n ^ (-(k + 4)) := by
    have hnd : n * δ ^ ((3 : ℝ) / 2) = K ^ ((3 : ℝ) / 2) * Real.log n := by
      dsimp [δ]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hK_pos.le (by positivity),
        ← Real.rpow_mul hn_pos.le, ← Real.rpow_mul (by linarith : 0 ≤ Real.log n)]
      have h1 : (-(2 / 3 : ℝ)) * ((3 : ℝ) / 2) = -1 := by norm_num
      have h2 : ((2 : ℝ) / 3) * ((3 : ℝ) / 2) = 1 := by norm_num
      rw [h1, h2, Real.rpow_neg_one, Real.rpow_one]
      field_simp [hn_pos.ne']
    have hhalf : (δ / 2) ^ ((3 : ℝ) / 2) = (2 : ℝ) ^ (-(3 / 2 : ℝ)) * δ ^ ((3 : ℝ) / 2) := by
      rw [div_eq_mul_inv, Real.mul_rpow hδ_pos.le (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), mul_comm]
    have hexp_le : -κ * n * (δ / 2) ^ ((3 : ℝ) / 2) ≤ -(k + 4) * Real.log n := by
      rw [hhalf]
      have hrew : -κ * n * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * δ ^ ((3 : ℝ) / 2)) =
          -(κ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) * (n * δ ^ ((3 : ℝ) / 2))) := by ring
      rw [hrew, hnd]
      have : (k + 4) * Real.log n ≤ κ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) * (K ^ ((3 : ℝ) / 2) * Real.log n) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hK_exp (by linarith)
      linarith
    calc Real.exp (-κ * n * (δ / 2) ^ ((3 : ℝ) / 2))
        ≤ Real.exp (-(k + 4) * Real.log n) := Real.exp_le_exp.mpr hexp_le
      _ = n ^ (-(k + 4)) := by rw [Real.rpow_def_of_pos hn_pos]; congr 1; ring
  have hA1_bound :
      ∫⁻ y in A_cls1, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
        ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4))) := by
    let K_fac : ℝ := C * n ^ k * (δ / 2)⁻¹ * n ^ (-(k + 4))
    have hK_nn : 0 ≤ K_fac := by dsimp [K_fac]; positivity
    let F1 : ℝ × ℝ → ℝ≥0∞ := fun y =>
      if y ∈ A_cls1 then
        ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ ((y.1 - y.2) / 2)))
      else 0
    have hpt : ∀ y ∈ A_cls1,
        ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
          ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ ((y.1 - y.2) / 2))) := by
      intro y hy
      refine ENNReal.ofReal_le_ofReal ?_
      set ξ := (y.1 + y.2) / 2
      set d := (y.1 - y.2) / 2
      have hξ_pos : 0 < ξ := by dsimp [ξ]; linarith [hy.1, hy.2.1]
      have hξ_le : ξ ≤ bStar - δ / 2 := hy.2.2.1
      have hξ_lt : |ξ| < bStar := by rw [abs_of_pos hξ_pos]; linarith [hξ_le, hδ_pos]
      have hd_le : |d| ≤ D := hy.2.2.2
      have hδy_ge : δ / 2 ≤ bStar - |ξ| := by rw [abs_of_pos hξ_pos]; linarith [hξ_le]
      have hw : spinWc a y.1 * spinWc a y.2 ≤ a * Real.exp (n * spinL ξ) := by
        simpa [a, n, show 12 * (n / 12) = n by ring] using
          spinWc_mul_le_exp ha2.le hy.1.le hy.2.1.le
      have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
        unfold spinSlitIntegral
        exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet
          fun _ _ => by positivity
      have hfb := hfold_b ξ d hξ_lt hd_le
      have hy1 : ξ + d = y.1 := by dsimp [ξ, d]; ring
      have hy2 : ξ - d = y.2 := by dsimp [ξ, d]; ring
      rw [hy1, hy2] at hfb
      have hinv_le : (bStar - |ξ|)⁻¹ ≤ (δ / 2)⁻¹ := inv_anti₀ (half_pos hδ_pos) hδy_ge
      have hexp_mono : Real.exp (-κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2)) ≤
          Real.exp (-κ * n * (δ / 2) ^ ((3 : ℝ) / 2)) := by
        refine Real.exp_le_exp.mpr ?_
        have hpow_le : (δ / 2) ^ ((3 : ℝ) / 2) ≤ (bStar - |ξ|) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow (half_pos hδ_pos).le hδy_ge (by norm_num)
        have hmul : κ * n * (δ / 2) ^ ((3 : ℝ) / 2) ≤ κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hpow_le (mul_pos hκ0 hn_pos).le
        linarith
      calc |spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2
          = |spinDeltaA a Φ y.1 y.2| * (spinWc a y.1 * spinWc a y.2) := by ring
        _ ≤ |spinDeltaA a Φ y.1 y.2| * (a * Real.exp (n * spinL ξ)) :=
            mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ y.1 y.2| := by ring
        _ ≤ C * n ^ k * (1 + spinSlitIntegral a Φ d) * (bStar - |ξ|)⁻¹ *
              Real.exp (-κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2)) := hfb
        _ ≤ C * n ^ k * (1 + spinSlitIntegral a Φ d) * (δ / 2)⁻¹ *
              Real.exp (-κ * n * (δ / 2) ^ ((3 : ℝ) / 2)) := by gcongr
        _ ≤ C * n ^ k * (1 + spinSlitIntegral a Φ d) * (δ / 2)⁻¹ * n ^ (-(k + 4)) := by gcongr
        _ = K_fac * (1 + spinSlitIntegral a Φ d) := by dsimp [K_fac]; ring
    have hstep1 : ∫⁻ y in A_cls1,
          ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
        ∫⁻ y : ℝ × ℝ, F1 y := by
      rw [← lintegral_indicator hA1_meas]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ A_cls1
      · simp only [Set.indicator_of_mem hy, F1, hy, ↓reduceIte]; exact hpt y hy
      · simp only [Set.indicator_of_notMem hy, F1, hy, ↓reduceIte, le_rfl]
    refine hstep1.trans ?_
    rw [lintegral_xi_d F1]
    have hdom : ∀ q : ℝ × ℝ, F1 (q.1 + q.2, q.1 - q.2) ≤
        (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) q.1 *
        ((Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) q.2) := by
      intro q
      by_cases hq : (q.1 + q.2, q.1 - q.2) ∈ A_cls1
      · have hsum : (q.1 + q.2 + (q.1 - q.2)) / 2 = q.1 := by ring
        have hdiff : (q.1 + q.2 - (q.1 - q.2)) / 2 = q.2 := by ring
        have hq1a : 0 ≤ q.1 := by have := hq.1; have := hq.2.1; linarith
        have hq1b : q.1 ≤ bStar := by have := hq.2.2.1; rw [hsum] at this; linarith [hδ_pos]
        have hq1 : q.1 ∈ Icc (0 : ℝ) bStar := ⟨hq1a, hq1b⟩
        have hq2 : q.2 ∈ Icc (-D) D := by
          have := hq.2.2.2; rw [hdiff] at this; exact abs_le.mp this
        simp only [F1, hq, ↓reduceIte, Set.indicator_of_mem hq1, Set.indicator_of_mem hq2,
          Pi.one_apply, one_mul, hdiff, le_rfl]
      · simp only [F1, hq, ↓reduceIte, zero_le]
    have hprod_int : ∫⁻ q : ℝ × ℝ,
        (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) q.1 *
        ((Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) q.2) =
        (∫⁻ ξ : ℝ, (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) ξ) *
        (∫⁻ d : ℝ, (Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) d) := by
      rw [Measure.volume_eq_prod]
      refine lintegral_prod_mul ?_ ?_
      · exact (measurable_const.indicator measurableSet_Icc).aemeasurable
      · rw [aemeasurable_indicator_iff measurableSet_Icc]
        exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          ((aemeasurable_const.add hS_int.aestronglyMeasurable.aemeasurable).const_mul K_fac)
    have hξ_val : ∫⁻ ξ : ℝ, (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) ξ =
        ENNReal.ofReal bStar := by
      rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc, sub_zero]
    have hd_val : ∫⁻ d : ℝ,
        (Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) d ≤
        ENNReal.ofReal (K_fac * (2 * D + C)) := by
      rw [lintegral_indicator measurableSet_Icc]
      have hint_1S : IntegrableOn (fun d : ℝ => K_fac * (1 + spinSlitIntegral a Φ d)) (Icc (-D) D) :=
        ((integrableOn_const (hs := measure_Icc_lt_top.ne)).add hS_int).const_mul K_fac
      have hnn_1S : ∀ d ∈ Icc (-D) D, 0 ≤ K_fac * (1 + spinSlitIntegral a Φ d) := fun d _ => by
        have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
          unfold spinSlitIntegral
          exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet
            fun _ _ => by positivity
        positivity
      rw [← ofReal_integral_eq_lintegral_ofReal hint_1S (ae_restrict_of_forall_mem measurableSet_Icc hnn_1S)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [integral_const_mul, integral_add (integrableOn_const (hs := measure_Icc_lt_top.ne)) hS_int]
      have h1 : ∫ _ in Icc (-D) D, (1 : ℝ) = 2 * D := by
        rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by dsimp [D]; linarith [xiStar_pos])]
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (by linarith) hK_nn
    calc ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, F1 (q.1 + q.2, q.1 - q.2)
        ≤ ENNReal.ofReal 2 *
            ((∫⁻ ξ : ℝ, (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) ξ) *
             (∫⁻ d : ℝ, (Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) d)) := by
          rw [← hprod_int]; gcongr; exact hdom _
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal bStar * ENNReal.ofReal (K_fac * (2 * D + C))) := by
          rw [hξ_val]; gcongr
      _ = ENNReal.ofReal (2 * (bStar * (K_fac * (2 * D + C)))) := by
          rw [← ENNReal.ofReal_mul (by linarith [xiStar_pos]),
            ← ENNReal.ofReal_mul (by norm_num)]
      _ ≤ ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hD_le : D ≤ xiStar := by dsimp [D]; linarith
          have hK_eq : K_fac = C * n ^ k * (2 * δ⁻¹) * n ^ (-(k + 4)) := by
            dsimp [K_fac]; rw [inv_div]; ring
          rw [hK_eq]
          have h2D : 2 * D + C ≤ 2 * xiStar + C := by linarith
          have hfac_nn : 0 ≤ C * n ^ k * (2 * δ⁻¹) * n ^ (-(k + 4)) := by positivity
          have h2D_nn : 0 ≤ 2 * D + C := by dsimp [D]; linarith [hbStar_ge, xiStar_pos, hC0]
          calc 2 * (bStar * (C * n ^ k * (2 * δ⁻¹) * n ^ (-(k + 4)) * (2 * D + C)))
              ≤ 2 * (xiStar * (C * n ^ k * (2 * δ⁻¹) * n ^ (-(k + 4)) * (2 * xiStar + C))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hbStar_le (mul_le_mul_of_nonneg_left h2D hfac_nn)
                    (mul_nonneg hfac_nn h2D_nn) xiStar_pos.le)
                  two_pos.le
            _ = C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4)) := by dsimp [C_cls1]; ring
  have hDelta_en :
      ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
        ENNReal.ofReal 4 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hDelta_int
      (Eventually.of_forall fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le p.1))
        (spinWc_nonneg ha2.le p.2))]
    exact ENNReal.ofReal_le_ofReal hDelta_le4
  have hterm_q : ∀ q : ℕ × ℕ,
      ∫⁻ p in E,
        ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
          spinWc a p.1 * spinWc a p.2) ≤
      ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
        (ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4))) +
         ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 3)))) := by
    intro q
    have hlam1 : 0 < spinLambda a ^ q.1 := pow_pos (by linarith [spinLambda_gt_one ha2]) _
    have hlam2 : 0 < spinLambda a ^ q.2 := pow_pos (by linarith [spinLambda_gt_one ha2]) _
    have hlam1_ge : 1 ≤ spinLambda a ^ q.1 := one_le_pow₀ (spinLambda_gt_one ha2).le
    have hlam2_ge : 1 ≤ spinLambda a ^ q.2 := one_le_pow₀ (spinLambda_gt_one ha2).le
    let g1 : ℝ × ℝ → ℝ≥0∞ := fun y =>
      A_cls1.indicator (fun y => ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)) y
    let g2 : ℝ × ℝ → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (Real.exp (-(π * n * δ / 3))) *
        ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)
    have hpt_q : ∀ p ∈ E,
        ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
          spinWc a p.1 * spinWc a p.2) ≤
        g1 (spinLambda a ^ q.1 * p.1, spinLambda a ^ q.2 * p.2) +
        g2 (spinLambda a ^ q.1 * p.1, spinLambda a ^ q.2 * p.2) := by
      intro p hp
      set y1 := spinLambda a ^ q.1 * p.1
      set y2 := spinLambda a ^ q.2 * p.2
      have hy1_pos : 0 < y1 := mul_pos hlam1 hp.1
      have hy2_pos : 0 < y2 := mul_pos hlam2 hp.2.1
      have hpx1 : p.1 ≤ y1 := le_mul_of_one_le_left hp.1.le hlam1_ge
      have hpx2 : p.2 ≤ y2 := le_mul_of_one_le_left hp.2.1.le hlam2_ge
      have hw_ratio : spinWc a p.1 * spinWc a p.2 ≤
          Real.exp (-(4 * π * a * ((y1 - p.1) + (y2 - p.2)))) * (spinWc a y1 * spinWc a y2) := by
        have hw1 := spinWc_exp_mono ha2.le hp.1.le hpx1
        have hw2 := spinWc_exp_mono ha2.le hp.2.1.le hpx2
        have hmul := mul_le_mul hw1 hw2 (spinWc_nonneg ha2.le p.2)
          (mul_nonneg (Real.exp_pos _).le (spinWc_nonneg ha2.le y1))
        calc spinWc a p.1 * spinWc a p.2
            ≤ (Real.exp (-(4 * π * a * (y1 - p.1))) * spinWc a y1) *
                (Real.exp (-(4 * π * a * (y2 - p.2))) * spinWc a y2) := hmul
          _ = Real.exp (-(4 * π * a * (y1 - p.1)) + -(4 * π * a * (y2 - p.2))) *
                (spinWc a y1 * spinWc a y2) := by rw [Real.exp_add]; ring
          _ = Real.exp (-(4 * π * a * ((y1 - p.1) + (y2 - p.2)))) *
                (spinWc a y1 * spinWc a y2) := by congr 2; ring
      by_cases hy : (y1, y2) ∈ A_cls1
      · refine le_trans ?_ le_self_add
        simp only [g1, Set.indicator_of_mem hy]
        refine ENNReal.ofReal_le_ofReal ?_
        have hexp1 : Real.exp (-(4 * π * a * ((y1 - p.1) + (y2 - p.2)))) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_)
          exact mul_nonneg (by positivity) (by linarith [hpx1, hpx2])
        have hw_le : spinWc a p.1 * spinWc a p.2 ≤ spinWc a y1 * spinWc a y2 :=
          hw_ratio.trans (mul_le_of_le_one_left
            (mul_nonneg (spinWc_nonneg ha2.le y1) (spinWc_nonneg ha2.le y2)) hexp1)
        calc |spinDeltaA a Φ y1 y2| * spinWc a p.1 * spinWc a p.2
            = |spinDeltaA a Φ y1 y2| * (spinWc a p.1 * spinWc a p.2) := by ring
          _ ≤ |spinDeltaA a Φ y1 y2| * (spinWc a y1 * spinWc a y2) :=
              mul_le_mul_of_nonneg_left hw_le (abs_nonneg _)
          _ = |spinDeltaA a Φ y1 y2| * spinWc a y1 * spinWc a y2 := by ring
      · refine le_trans ?_ le_add_self
        dsimp [g2]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        have hgap : δ ≤ (y1 - p.1) + (y2 - p.2) :=
          spin_gap_ge_delta (by linarith [hbStar_ge, xiStar_pos]) hδ_pos hδ_lt hp.1 hp.2.1 hp.2.2
            hpx1 hpx2 (fun h => hy ⟨hy1_pos, hy2_pos, h.1, h.2⟩)
        have hexp_le : Real.exp (-(4 * π * a * ((y1 - p.1) + (y2 - p.2)))) ≤
            Real.exp (-(π * n * δ / 3)) := by
          refine Real.exp_le_exp.mpr ?_
          have h4a : 4 * π * a = π * n / 3 := by dsimp [a]; ring
          rw [h4a]
          have : π * n / 3 * δ ≤ π * n / 3 * ((y1 - p.1) + (y2 - p.2)) :=
            mul_le_mul_of_nonneg_left hgap (by positivity)
          linarith
        have hw_le : spinWc a p.1 * spinWc a p.2 ≤
            Real.exp (-(π * n * δ / 3)) * (spinWc a y1 * spinWc a y2) :=
          hw_ratio.trans (mul_le_mul_of_nonneg_right hexp_le
            (mul_nonneg (spinWc_nonneg ha2.le y1) (spinWc_nonneg ha2.le y2)))
        calc |spinDeltaA a Φ y1 y2| * spinWc a p.1 * spinWc a p.2
            = |spinDeltaA a Φ y1 y2| * (spinWc a p.1 * spinWc a p.2) := by ring
          _ ≤ |spinDeltaA a Φ y1 y2| * (Real.exp (-(π * n * δ / 3)) * (spinWc a y1 * spinWc a y2)) :=
              mul_le_mul_of_nonneg_left hw_le (abs_nonneg _)
          _ = Real.exp (-(π * n * δ / 3)) * (|spinDeltaA a Φ y1 y2| * spinWc a y1 * spinWc a y2) := by
              ring
    have hinv_eq : (spinLambda a ^ q.1)⁻¹ * (spinLambda a ^ q.2)⁻¹ =
        spinGamma a ^ q.1 * spinGamma a ^ q.2 := by
      unfold spinLambda; simp [inv_pow]
    calc ∫⁻ p in E,
            ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
              spinWc a p.1 * spinWc a p.2)
        ≤ ∫⁻ p : ℝ × ℝ,
            (g1 (spinLambda a ^ q.1 * p.1, spinLambda a ^ q.2 * p.2) +
             g2 (spinLambda a ^ q.1 * p.1, spinLambda a ^ q.2 * p.2)) := by
          rw [← lintegral_indicator hE_meas]
          refine lintegral_mono fun p => ?_
          by_cases hp : p ∈ E
          · simp only [Set.indicator_of_mem hp]; exact hpt_q p hp
          · simp [Set.indicator_of_notMem hp]
      _ = ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
            ∫⁻ y : ℝ × ℝ, (g1 y + g2 y) := by
          rw [lintegral_prod_scale hlam1 hlam2 (fun y => g1 y + g2 y), hinv_eq]
      _ = ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
            ((∫⁻ y : ℝ × ℝ, g1 y) + (∫⁻ y : ℝ × ℝ, g2 y)) := by
          congr 1
          refine lintegral_add_left' ?_ _
          have hG : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
            unfold spinG
            exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
          have hDa : Continuous (fun p : ℝ × ℝ => spinDa a Φ p.1 p.2) := by
            unfold spinDa
            exact (((hG.sub (hG.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).sub
              (hG.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).add
              (hG.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
          have hDelta : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
            unfold spinDeltaA
            exact hDa.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
          have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
          exact ((ENNReal.continuous_ofReal.comp
            ((hDelta.abs.mul (hWc.comp continuous_fst)).mul (hWc.comp continuous_snd))).measurable.indicator
              hA1_meas).aemeasurable
      _ ≤ ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
            (ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4))) +
             ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 3)))) := by
          gcongr
          · rw [lintegral_indicator hA1_meas]; exact hA1_bound
          · dsimp [g2]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            calc ENNReal.ofReal (Real.exp (-(π * n * δ / 3))) *
                    ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)
                ≤ ENNReal.ofReal (Real.exp (-(π * n * δ / 3))) * ENNReal.ofReal 4 := by gcongr
              _ = ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 3))) := by
                  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  have hjac_le : (1 - spinGamma a)⁻¹ ≤ n := by
    have hdiff : 1 - spinGamma a ^ 2 = 2 / a := by rw [spinGamma_sq ha2.le]; ring
    have hpos : 0 < 1 - spinGamma a := by linarith
    have hle : (1 - spinGamma a)⁻¹ = a * (1 + spinGamma a) / 2 := by
      have ha_ne : a ≠ 0 := by linarith
      have hprod : (1 - spinGamma a) * (a * (1 + spinGamma a) / 2) = 1 := by
        calc (1 - spinGamma a) * (a * (1 + spinGamma a) / 2)
            = a * (1 - spinGamma a ^ 2) / 2 := by ring
          _ = a * (2 / a) / 2 := by rw [hdiff]
          _ = 1 := by field_simp [ha_ne]
      exact inv_eq_of_mul_eq_one_right hprod
    rw [hle]
    have hle_a : a * (1 + spinGamma a) / 2 ≤ a := by
      have : 1 + spinGamma a ≤ 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ a)
      linarith
    have ha_le_n : a ≤ n := by dsimp [a]; linarith
    exact hle_a.trans ha_le_n
  have hjac_sq : (1 - spinGamma a)⁻¹ * (1 - spinGamma a)⁻¹ ≤ n ^ 2 := by
    have hnn : 0 ≤ (1 - spinGamma a)⁻¹ := inv_nonneg.mpr (by linarith)
    nlinarith
  have htotal :
      ∫⁻ p in E, ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ≤
        ENNReal.ofReal (n ^ 2 * (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4)) +
          4 * Real.exp (-(π * n * δ / 3)))) := by
    calc ∫⁻ p in E, ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
        ≤ ∑' q : ℕ × ℕ,
            ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
              (ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4))) +
               ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 3)))) :=
          htel.trans (tsum_le_tsum hterm_q)
      _ = (∑' q : ℕ × ℕ, ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2)) *
            (ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4))) +
             ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 3)))) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal ((1 - spinGamma a)⁻¹ * (1 - spinGamma a)⁻¹) *
            ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4)) +
              4 * Real.exp (-(π * n * δ / 3))) := by
          rw [tsum_gamma_pair hγ_pos.le hγ_lt1,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ = ENNReal.ofReal (((1 - spinGamma a)⁻¹ * (1 - spinGamma a)⁻¹) *
            (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4)) + 4 * Real.exp (-(π * n * δ / 3)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (n ^ 2 * (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4)) +
            4 * Real.exp (-(π * n * δ / 3)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_right hjac_sq (add_nonneg (by positivity) (by positivity))
  have hlt : n ^ 2 * (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4)) +
      4 * Real.exp (-(π * n * δ / 3))) < 1 / 8 := by
    have hnk : n ^ 2 * n ^ k = n ^ (k + 2) := by
      rw [← Real.rpow_natCast n 2, ← Real.rpow_add hn_pos]; congr 1; ring
    have h1 : n ^ 2 * (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + 4))) =
        C_cls1 * n ^ (k + 2) * δ⁻¹ * n ^ (-(k + 4)) := by
      rw [← hnk]; ring
    have h2 : n ^ 2 * (4 * Real.exp (-(π * n * δ / 3))) =
        4 * n ^ 2 * Real.exp (-(π * n * δ / 3)) := by ring
    rw [mul_add, h1, h2]
    linarith
  exact htotal.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt)

/-! ### Section 5: `D_4` reflection symmetry and `SpinS3` -/

/-- `D_4` reflection invariance: the integral over the whole disc `B` is at most `4` times the
first-quadrant integral. -/
private lemma lintegral_disc_le_four_quad {a r : ℝ} (_ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    ∫⁻ p in {p : ℝ × ℝ | (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2},
        ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ≤
      4 * ∫⁻ p in {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2},
        ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by
  let f : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
  let B : Set (ℝ × ℝ) := {p : ℝ × ℝ | (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2}
  let Qpp : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2}
  let Qnp : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < 0 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2}
  let Qpn : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.1 ∧ p.2 < 0 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2}
  let Qnn : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < 0 ∧ p.2 < 0 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2}
  have hf_neg1 : ∀ p : ℝ × ℝ, f (-p.1, p.2) = f p := fun p => by
    dsimp [f]; unfold spinG
    rw [mul_neg, hΦ.d4_inv.1, spinWc_even]
  have hf_neg2 : ∀ p : ℝ × ℝ, f (p.1, -p.2) = f p := fun p => by
    dsimp [f]; unfold spinG
    rw [mul_neg, hΦ.d4_inv.2.1, spinWc_even]
  have hQpp_m : MeasurableSet Qpp :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        (isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet)
  have hQnp_m : MeasurableSet Qnp :=
    (isOpen_lt continuous_fst continuous_const).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        (isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet)
  have hQpn_m : MeasurableSet Qpn :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_snd continuous_const).measurableSet.inter
        (isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet)
  have hQnn_m : MeasurableSet Qnn :=
    (isOpen_lt continuous_fst continuous_const).measurableSet.inter
      ((isOpen_lt continuous_snd continuous_const).measurableSet.inter
        (isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet)
  have href1 : ∫⁻ p in Qnp, f p = ∫⁻ p in Qpp, f p := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
    have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) = volume := by
      have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) id := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_id,
        Measure.map_neg_eq_self, Measure.map_id]
    have hpre : e ⁻¹' Qnp = Qpp := by
      ext p
      change -p.1 < 0 ∧ 0 < p.2 ∧ ((-p.1) ^ 2 + p.2 ^ 2) / 2 < r ^ 2 ↔
        0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2
      simp
    have h1 := (lintegral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) (Qnp.indicator f) e).symm
    rw [hmp] at h1
    rw [← lintegral_indicator hQnp_m, ← h1, ← lintegral_indicator hQpp_m]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ Qpp
    · have hep : e p ∈ Qnp := by rw [← Set.mem_preimage, hpre]; exact hp
      rw [Set.indicator_of_mem hep, Set.indicator_of_mem hp]
      exact hf_neg1 p
    · have hep : e p ∉ Qnp := by rw [← Set.mem_preimage, hpre]; exact hp
      simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hep]
  have href2 : ∫⁻ p in Qpn, f p = ∫⁻ p in Qpp, f p := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) = volume := by
      have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map id (-·) := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id measurable_neg,
        Measure.map_id, Measure.map_neg_eq_self]
    have hpre : e ⁻¹' Qpn = Qpp := by
      ext p
      change 0 < p.1 ∧ -p.2 < 0 ∧ (p.1 ^ 2 + (-p.2) ^ 2) / 2 < r ^ 2 ↔
        0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2
      simp
    have h1 := (lintegral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) (Qpn.indicator f) e).symm
    rw [hmp] at h1
    rw [← lintegral_indicator hQpn_m, ← h1, ← lintegral_indicator hQpp_m]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ Qpp
    · have hep : e p ∈ Qpn := by rw [← Set.mem_preimage, hpre]; exact hp
      rw [Set.indicator_of_mem hep, Set.indicator_of_mem hp]
      exact hf_neg2 p
    · have hep : e p ∉ Qpn := by rw [← Set.mem_preimage, hpre]; exact hp
      simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hep]
  have href3 : ∫⁻ p in Qnn, f p = ∫⁻ p in Qpp, f p := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) = volume := by
      have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) (-·) := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_neg,
        Measure.map_neg_eq_self]
    have hpre : e ⁻¹' Qnn = Qpp := by
      ext p
      change -p.1 < 0 ∧ -p.2 < 0 ∧ ((-p.1) ^ 2 + (-p.2) ^ 2) / 2 < r ^ 2 ↔
        0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < r ^ 2
      simp
    have h1 := (lintegral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) (Qnn.indicator f) e).symm
    rw [hmp] at h1
    rw [← lintegral_indicator hQnn_m, ← h1, ← lintegral_indicator hQpp_m]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ Qpp
    · have hep : e p ∈ Qnn := by rw [← Set.mem_preimage, hpre]; exact hp
      rw [Set.indicator_of_mem hep, Set.indicator_of_mem hp]
      change f (-p.1, -p.2) = f p
      exact (hf_neg1 (p.1, -p.2)).trans (hf_neg2 p)
    · have hep : e p ∉ Qnn := by rw [← Set.mem_preimage, hpre]; exact hp
      simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hep]
  have haxes : volume ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) = 0 := by
    have h1 : volume {p : ℝ × ℝ | p.1 = 0} = 0 := by
      rw [show {p : ℝ × ℝ | p.1 = 0} = {(0 : ℝ)} ×ˢ (univ : Set ℝ) by ext p; simp,
        Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    have h2 : volume {p : ℝ × ℝ | p.2 = 0} = 0 := by
      rw [show {p : ℝ × ℝ | p.2 = 0} = (univ : Set ℝ) ×ˢ {(0 : ℝ)} by ext p; simp,
        Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
    exact measure_union_null h1 h2
  have hsub : B ⊆ Qpp ∪ Qnp ∪ Qpn ∪ Qnn ∪ ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) := by
    intro p hp
    rcases lt_trichotomy p.1 0 with h1 | h1 | h1
    · rcases lt_trichotomy p.2 0 with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2, hp⟩)
      · exact Or.inr (Or.inr h2)
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h1, h2, hp⟩)))
    · exact Or.inr (Or.inl h1)
    · rcases lt_trichotomy p.2 0 with h2 | h2 | h2
      · exact Or.inl (Or.inl (Or.inr ⟨h1, h2, hp⟩))
      · exact Or.inr (Or.inr h2)
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, h2, hp⟩)))
  calc ∫⁻ p in B, f p
      ≤ ∫⁻ p in (Qpp ∪ Qnp ∪ Qpn ∪ Qnn ∪ ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0})), f p :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ p in Qpp, f p) + (∫⁻ p in Qnp, f p) + (∫⁻ p in Qpn, f p) + (∫⁻ p in Qnn, f p) +
          ∫⁻ p in ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}), f p := by
        refine (lintegral_union_le _ _ _).trans ?_
        gcongr
        refine (lintegral_union_le _ _ _).trans ?_
        gcongr
        refine (lintegral_union_le _ _ _).trans ?_
        gcongr
        exact lintegral_union_le _ _ _
    _ = 4 * ∫⁻ p in Qpp, f p := by
        rw [setLIntegral_measure_zero _ _ haxes, add_zero, href1, href2, href3]
        ring

/-- **Skeleton headline (`spinnotes:S3`)**: the large-`c` continuous-spin slope proved from
`SpinS1b`, `SpinS1c`, `SpinS22`, `SpinS22b` and the already-proved spinless `O(1)` upper bound
`virasoro_corollary_E1_unconditional`. -/
theorem spinS3_of_props (hS1b : SpinS1b) (hS1c : SpinS1c) (hS22 : SpinS22) (hS22b : SpinS22b) :
    SpinS3 := by
  obtain ⟨K, c₁, hK_pos, hc₁40, hloc⟩ := spin_tip_localisation_quad hS22 hS22b
  obtain ⟨c_vir, C_vir, _, hC_vir_nn, hvir, _⟩ := virasoro_corollary_E1_unconditional
  let C_lo : ℝ := (2 * xiStar * K / 3) + 8 * xiStar ^ 2
  let C_hi : ℝ := C_vir + 1
  let c₀ : ℝ := max (max c₁ (c_vir + 1)) (Real.exp 1 + 1)
  have hC_lo_pos : 0 < C_lo := by dsimp [C_lo]; have := xiStar_pos; positivity
  have hC_hi_pos : 0 < C_hi := by dsimp [C_hi]; linarith
  have hc₀40 : 40 ≤ c₀ := hc₁40.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨C_lo, C_hi, c₀, hC_lo_pos, hC_hi_pos, hc₀40, fun {c} hc => ?_⟩
  have hc40 : 40 ≤ c := hc₀40.trans hc
  have hcc1 : c₁ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcvir : c_vir ≤ c - 1 := by
    have : c_vir + 1 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
    linarith
  have hce : Real.exp 1 ≤ c - 1 := by
    have : Real.exp 1 + 1 ≤ c := (le_max_right _ _).trans hc
    linarith
  set n : ℝ := c - 1
  set a : ℝ := n / 12
  set δ : ℝ := K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)
  set x1 : ℝ := spinBStar a - δ
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hlog_ge1 : 1 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 1) hce; rwa [Real.log_exp] at this
  obtain ⟨hδ_pos, hδ_lt, hquad⟩ := hloc hcc1
  have hb_pos : 0 < spinBStar a := mul_pos (spinGamma_pos ha2) xiStar_pos
  have hx1_pos : 0 < x1 := by dsimp [x1]; linarith
  obtain ⟨_, hL_le_spin, hspin_le_vir⟩ := hS1c hc40
  have hvir_up : virasoroProblem.Delta_best n ≤ n / lambdaV + Aopt * n ^ ((1 : ℝ) / 3) + C_hi := by
    have h := (abs_le.mp (hvir hcvir).2.2.1).2
    dsimp [C_hi]; linarith
  have hno_feas : ∀ T : ℝ, T < (n / 3) * x1 ^ 2 →
      ¬ ∃ Φ, SpinIsFeasible (SpinTestClass a) liouvilleCone a T Φ := by
    rintro T hT ⟨Φ, hfeas⟩
    have hweak := hfeas.isWeaklyFeasible ha2.le
    have hM_pos : 0 < spinM2 a Φ := hweak.2.1
    let α : ℝ := (spinM2 a Φ)⁻¹
    have hα_pos : 0 < α := inv_pos.mpr hM_pos
    let Ψ : ℝ × ℝ → ℝ := fun p => α * Φ p
    have hΨ_cls : SpinTestClass a Ψ :=
      { cont := continuous_const.mul hweak.1.cont
        int := hweak.1.int.const_mul α
        d4_inv := ⟨fun rL rR => by dsimp [Ψ]; rw [hweak.1.d4_inv.1],
          fun rL rR => by dsimp [Ψ]; rw [hweak.1.d4_inv.2.1],
          fun rL rR => by dsimp [Ψ]; rw [hweak.1.d4_inv.2.2]⟩
        fourier_odd := by
          have heq : spinToEuc Ψ = fun x => (α : ℂ) • spinToEuc Φ x := by
            ext x; simp [spinToEuc, Ψ]
          rw [heq]
          ext w
          simp only [Real.fourier_eq, Pi.neg_apply]
          simp_rw [smul_comm _ (α : ℂ), integral_smul]
          have hfo := congrFun hweak.1.fourier_odd w
          simp only [Real.fourier_eq, Pi.neg_apply] at hfo
          rw [hfo, smul_neg]
        int_M2 := by
          have heq : (fun p : ℝ × ℝ => |Ψ p| * spinV1 a p.1 * spinV1 a p.2) =
              fun p => α * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
            ext p; dsimp [Ψ]; rw [abs_mul, abs_of_pos hα_pos]; ring
          rw [heq]; exact hweak.1.int_M2.const_mul α }
    have hΨ_M2 : spinM2 a Ψ = 1 := by
      unfold spinM2
      have heq : (fun p : ℝ × ℝ => |Ψ p| * spinV1 a p.1 * spinV1 a p.2) =
          fun p => α * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
        ext p; dsimp [Ψ]; rw [abs_mul, abs_of_pos hα_pos]; ring
      rw [heq, integral_const_mul]
      exact inv_mul_cancel₀ hM_pos.ne'
    have hΨ_vac : 0 ≤ spinPhiVac a Ψ := by
      unfold spinPhiVac
      have heq : (fun p : ℝ × ℝ => Ψ p * spinV1 a p.1 * spinV1 a p.2) =
          fun p => α * (Φ p * spinV1 a p.1 * spinV1 a p.2) := by ext p; dsimp [Ψ]; ring
      rw [heq, integral_const_mul]
      have hv : 0 ≤ -(∫ p : ℝ × ℝ, Φ p * spinV1 a p.1 * spinV1 a p.2) := hweak.2.2.1
      nlinarith
    have hΨ_pos : ∀ p ∈ liouvilleCone ((n / 3) * x1 ^ 2), 0 ≤ spinEvalT Ψ p := by
      intro p hp
      dsimp [Ψ, spinEvalT]
      exact mul_nonneg hα_pos.le (hweak.2.2.2 p ⟨hp.1, hp.2.1, hT.le.trans hp.2.2⟩)
    let B : Set (ℝ × ℝ) := {p : ℝ × ℝ | (p.1 ^ 2 + p.2 ^ 2) / 2 < x1 ^ 2}
    have hG_nonneg_off_B : ∀ p : ℝ × ℝ, p ∉ B → 0 ≤ spinG a Ψ p.1 p.2 := by
      intro p hp
      simp only [B, mem_ofPred_eq, not_lt] at hp
      let tL := (2 * Real.sqrt a * p.1) ^ 2 / 2
      let tR := (2 * Real.sqrt a * p.2) ^ 2 / 2
      have htL : 0 ≤ tL := by dsimp [tL]; positivity
      have htR : 0 ≤ tR := by dsimp [tR]; positivity
      have htsum : (n / 3) * x1 ^ 2 ≤ tL + tR := by
        have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
        have hsum_eq : tL + tR = 4 * a * ((p.1 ^ 2 + p.2 ^ 2) / 2) := by
          dsimp [tL, tR]; rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq]; ring
        have h4a : 4 * a = n / 3 := by dsimp [a]; ring
        rw [hsum_eq, h4a]
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      have heval := hΨ_pos (tL, tR) ⟨htL, htR, htsum⟩
      have hsr1 : Real.sqrt (2 * tL) = |2 * Real.sqrt a * p.1| := by
        dsimp [tL]; rw [show 2 * ((2 * Real.sqrt a * p.1) ^ 2 / 2) = (2 * Real.sqrt a * p.1) ^ 2 by ring,
          Real.sqrt_sq_eq_abs]
      have hsr2 : Real.sqrt (2 * tR) = |2 * Real.sqrt a * p.2| := by
        dsimp [tR]; rw [show 2 * ((2 * Real.sqrt a * p.2) ^ 2 / 2) = (2 * Real.sqrt a * p.2) ^ 2 by ring,
          Real.sqrt_sq_eq_abs]
      have hG_eq : spinG a Ψ p.1 p.2 = spinEvalT Ψ (tL, tR) := by
        unfold spinG spinEvalT
        rw [hsr1, hsr2]
        rcases le_total 0 (2 * Real.sqrt a * p.1) with h1 | h1 <;>
        rcases le_total 0 (2 * Real.sqrt a * p.2) with h2 | h2
        · rw [abs_of_nonneg h1, abs_of_nonneg h2]
        · rw [abs_of_nonneg h1, abs_of_nonpos h2, hΨ_cls.d4_inv.2.1]
        · rw [abs_of_nonpos h1, abs_of_nonneg h2, hΨ_cls.d4_inv.1]
        · rw [abs_of_nonpos h1, abs_of_nonpos h2, hΨ_cls.d4_inv.1, hΨ_cls.d4_inv.2.1]
      rw [hG_eq]; exact heval
    have hhalf := spin_half_mass ha2.le hΨ_cls hΨ_vac
    rw [hΨ_M2, mul_one] at hhalf
    have hhalf_en : ENNReal.ofReal (1 / 2) ≤
        ∫⁻ p in B, ENNReal.ofReal (|spinG a Ψ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by
      have h1 : ENNReal.ofReal (1 / 2) ≤
          ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max (-Ψ p) 0 * spinV1 a p.1 * spinV1 a p.2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hΨ_cls.int_neg_part ha2.le)
          (Eventually.of_forall fun p => mul_nonneg (mul_nonneg (le_max_right _ _)
            (spinV1_nonneg ha2.le p.1)) (spinV1_nonneg ha2.le p.2))]
        exact ENNReal.ofReal_le_ofReal hhalf
      let s : ℝ := 2 * Real.sqrt a
      have hs : 0 < s := by positivity
      have hscale : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max (-Ψ p) 0 * spinV1 a p.1 * spinV1 a p.2) =
          ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max (-spinG a Ψ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := by
        have hsc := lintegral_prod_scale hs hs
          (fun p => ENNReal.ofReal (max (-Ψ p) 0 * spinV1 a p.1 * spinV1 a p.2))
        have hmul : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max (-Ψ p) 0 * spinV1 a p.1 * spinV1 a p.2) =
            ENNReal.ofReal (s * s) *
              ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max (-Ψ (s * p.1, s * p.2)) 0 *
                spinV1 a (s * p.1) * spinV1 a (s * p.2)) := by
          rw [hsc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          have : s * s * (s⁻¹ * s⁻¹) = 1 := by field_simp [hs.ne']
          rw [this, ENNReal.ofReal_one, one_mul]
        rw [hmul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun p => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; unfold spinG spinWc; dsimp [s]; ring
      rw [hscale] at h1
      have hB_meas : MeasurableSet B :=
        (isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet
      calc ENNReal.ofReal (1 / 2)
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max (-spinG a Ψ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := h1
        _ ≤ ∫⁻ p : ℝ × ℝ, B.indicator
              (fun p => ENNReal.ofReal (|spinG a Ψ p.1 p.2| * spinWc a p.1 * spinWc a p.2)) p := by
            refine lintegral_mono fun p => ?_
            by_cases hp : p ∈ B
            · simp only [Set.indicator_of_mem hp]
              refine ENNReal.ofReal_le_ofReal ?_
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _))
                  (spinWc_nonneg ha2.le p.1))
                (spinWc_nonneg ha2.le p.2)
            · have hnn := hG_nonneg_off_B p hp
              have hmax : max (-spinG a Ψ p.1 p.2) 0 = 0 := max_eq_right (by linarith)
              simp [Set.indicator_of_notMem hp, hmax]
        _ = ∫⁻ p in B, ENNReal.ofReal (|spinG a Ψ p.1 p.2| * spinWc a p.1 * spinWc a p.2) :=
            lintegral_indicator hB_meas _
    have hupper : ∫⁻ p in B, ENNReal.ofReal (|spinG a Ψ p.1 p.2| * spinWc a p.1 * spinWc a p.2) <
        ENNReal.ofReal (1 / 2) := by
      have h4 := lintegral_disc_le_four_quad (r := x1) ha2.le hΨ_cls
      have hq := hquad hΨ_cls hΨ_M2
      calc ∫⁻ p in B, ENNReal.ofReal (|spinG a Ψ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
          ≤ 4 * ∫⁻ p in {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 2 < x1 ^ 2},
              ENNReal.ofReal (|spinG a Ψ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := h4
        _ < 4 * ENNReal.ofReal (1 / 8) := by
            rw [mul_comm (4 : ℝ≥0∞), mul_comm (4 : ℝ≥0∞)]
            exact ENNReal.mul_lt_mul_left (by norm_num : (4 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top hq
        _ = ENNReal.ofReal (1 / 2) := by
            rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
              ← ENNReal.ofReal_mul (by norm_num)]
            norm_num
    exact not_lt_of_ge hhalf_en hupper
  have hthr_ge : (n / 3) * x1 ^ 2 ≤ spinThrInf (SpinTestClass a) liouvilleCone a := by
    unfold spinThrInf
    refine le_csInf (spinFeasible_nonempty_of_S1b hS1b (by linarith)) ?_
    rintro T ⟨_, hfeas⟩
    by_contra hlt
    exact hno_feas T (not_le.mp hlt) hfeas
  have hlo : n / lambdaV - C_lo * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) ≤
      spinDeltaL c := by
    have hlam_id : n / lambdaV = a + (n / 3) * xiStar ^ 2 := by
      have h1 := xiBar_eq_inv_lambdaV_sub
      unfold xiBar at h1
      dsimp [a]
      have : 1 / lambdaV = 1 / 12 + xiStar ^ 2 / 3 := by linarith
      calc n / lambdaV = n * (1 / lambdaV) := by ring
        _ = n * (1 / 12 + xiStar ^ 2 / 3) := by rw [this]
        _ = n / 12 + n / 3 * xiStar ^ 2 := by ring
    have hbStar_sq : spinBStar a ^ 2 = (1 - 24 / n) * xiStar ^ 2 := by
      unfold spinBStar
      rw [mul_pow, spinGamma_sq ha2.le]
      dsimp [a]; field_simp [hn_pos.ne']; ring
    have hx1_sq : (1 - 24 / n) * xiStar ^ 2 - 2 * xiStar * δ ≤ x1 ^ 2 := by
      have hb_le : spinBStar a ≤ xiStar := by
        unfold spinBStar; nlinarith [spinGamma_lt_one ha2, xiStar_pos]
      dsimp [x1]
      nlinarith [sq_nonneg δ, hbStar_sq]
    have hnd : n * δ = K * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) := by
      dsimp [δ]
      calc n * (K * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3))
          = K * (n * n ^ (-(2 / 3 : ℝ))) * (Real.log n) ^ ((2 : ℝ) / 3) := by ring
        _ = K * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) := by
            rw [rpow_one_mul_neg_two_thirds hn_pos]
    have hpow_ge1 : 1 ≤ n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) := by
      have h1 : 1 ≤ n ^ ((1 : ℝ) / 3) := Real.one_le_rpow (by linarith) (by norm_num)
      have h2 : 1 ≤ (Real.log n) ^ ((2 : ℝ) / 3) := Real.one_le_rpow hlog_ge1 (by norm_num)
      nlinarith
    have hconst_le : 8 * xiStar ^ 2 ≤
        8 * xiStar ^ 2 * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) := by
      have hnn : 0 ≤ 8 * xiStar ^ 2 := by positivity
      calc 8 * xiStar ^ 2 = 8 * xiStar ^ 2 * 1 := (mul_one _).symm
        _ ≤ 8 * xiStar ^ 2 * (n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_left hpow_ge1 hnn
        _ = 8 * xiStar ^ 2 * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) := by ring
    unfold spinDeltaL
    have hstep : a + (n / 3) * ((1 - 24 / n) * xiStar ^ 2 - 2 * xiStar * δ) ≤
        a + spinThrInf (SpinTestClass a) liouvilleCone a := by
      have h1 : (n / 3) * ((1 - 24 / n) * xiStar ^ 2 - 2 * xiStar * δ) ≤ (n / 3) * x1 ^ 2 :=
        mul_le_mul_of_nonneg_left hx1_sq (by positivity)
      linarith
    have halg : a + (n / 3) * ((1 - 24 / n) * xiStar ^ 2 - 2 * xiStar * δ) =
        n / lambdaV - (2 * xiStar * K / 3) * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) -
          8 * xiStar ^ 2 := by
      rw [hlam_id]
      have hcancel : (n / 3) * (24 / n) = 8 := by field_simp [hn_pos.ne']; ring
      calc a + (n / 3) * ((1 - 24 / n) * xiStar ^ 2 - 2 * xiStar * δ)
          = a + (n / 3) * xiStar ^ 2 - ((n / 3) * (24 / n)) * xiStar ^ 2 -
              (2 * xiStar / 3) * (n * δ) := by ring
        _ = a + (n / 3) * xiStar ^ 2 - 8 * xiStar ^ 2 -
              (2 * xiStar / 3) * (K * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3)) := by
            rw [hcancel, hnd]
        _ = a + (n / 3) * xiStar ^ 2 -
              (2 * xiStar * K / 3) * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) -
              8 * xiStar ^ 2 := by ring
    rw [halg] at hstep
    have hfin : n / lambdaV - C_lo * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) ≤
        a + spinThrInf (SpinTestClass a) liouvilleCone a := by
      dsimp [C_lo]; linarith
    exact hfin
  exact ⟨hlo, hL_le_spin, hspin_le_vir, hvir_up⟩

/-! ### Section 6: Consequences for `s4:S4` -/

/-- The part of `s4:S4` delivered by `SpinS3` and `SpinS1e`:
for all sufficiently large `c`, `T(\overline{\mathcal A}_{\rm spin}; \Omega_L) > 0`, so strong
duality holds with attainment (`\Delta_L = \Delta_{\rm spin} = a + \tau_{\max}(\Omega_L)`),
and the positive-measure optimum `a + \tau_{\max}(\Omega_L)` obeys the leading-slope lower bound
and Airy-order upper bound. -/
theorem spinS4_consequences_of_S3 (hS3 : SpinS3) (hS1e : SpinS1e) :
    ∃ (C C_plus c₁ : ℝ), 0 < C ∧ 0 < C_plus ∧ 40 ≤ c₁ ∧
      ∀ {c : ℝ}, c₁ ≤ c →
        let a := (c - 1) / 12
        0 < spinThrInf (SpinTestClass a) liouvilleCone a ∧
        spinDeltaL c = spinDeltaSpin c ∧
        spinDeltaL c = a + spinTauMax a liouvilleCone ∧
        (∃ meas : SpinCrossingMeasure a,
          meas.ν (liouvilleCone (spinTauMax a liouvilleCone))ᶜ = 0) ∧
        (c - 1) / lambdaV - C * (c - 1) ^ ((1 : ℝ) / 3) * (Real.log (c - 1)) ^ ((2 : ℝ) / 3) ≤
          a + spinTauMax a liouvilleCone ∧
        a + spinTauMax a liouvilleCone ≤
          (c - 1) / lambdaV + Aopt * (c - 1) ^ ((1 : ℝ) / 3) + C_plus := by
  obtain ⟨C, C_plus, c₀, hC, hCp, hc₀40, hS3_main⟩ := hS3
  have hxiBar_pos : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((tendsto_delta_zero C).eventually (gt_mem_nhds hxiBar_pos))
  let c₁ : ℝ := max c₀ (N₀ + 1)
  refine ⟨C, C_plus, c₁, hC, hCp, hc₀40.trans (le_max_left _ _), fun {c} hc => ?_⟩
  have hcc0 : c₀ ≤ c := (le_max_left _ _).trans hc
  have hcN0 : N₀ ≤ c - 1 := by have : N₀ + 1 ≤ c := (le_max_right _ _).trans hc; linarith
  have hc25 : 25 ≤ c := by linarith
  obtain ⟨hlo, hL_spin, hspin_vir, hvir_hi⟩ := hS3_main hcc0
  set n : ℝ := c - 1
  set a : ℝ := n / 12
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hthr_pos : 0 < spinThrInf (SpinTestClass a) liouvilleCone a := by
    have hlt := hN₀ n hcN0
    have hmul : C * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) < xiBar * n := by
      calc C * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3)
          = n * (C * n ^ (-(2 / 3 : ℝ)) * (Real.log n) ^ ((2 : ℝ) / 3)) := by
            rw [← rpow_one_mul_neg_two_thirds hn_pos]; ring
        _ < n * xiBar := mul_lt_mul_of_pos_left hlt hn_pos
        _ = xiBar * n := mul_comm _ _
    have hxi_id : n / lambdaV - a = xiBar * n := by
      rw [xiBar_eq_inv_lambdaV_sub]; dsimp [a]; ring
    have hlo' : n / lambdaV - C * n ^ ((1 : ℝ) / 3) * (Real.log n) ^ ((2 : ℝ) / 3) ≤
        a + spinThrInf (SpinTestClass a) liouvilleCone a := hlo
    linarith
  obtain ⟨hL_eq_spin, hL_eq_tau, hattain⟩ := (hS1e hc25).1 hthr_pos
  refine ⟨hthr_pos, hL_eq_spin, hL_eq_tau, hattain, ?_, ?_⟩
  · rw [← hL_eq_tau]; exact hlo
  · rw [← hL_eq_tau]; linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS3_of_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS3_of_props

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_consequences_of_S3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_consequences_of_S3

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_tip_localisation_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_tip_localisation_quad

end FormalResearch.ModularBootstrap.Spin
