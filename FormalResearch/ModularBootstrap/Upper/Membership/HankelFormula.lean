module

public import FormalResearch.ModularBootstrap.WeightAxioms.HankelContinuation
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import FormalResearch.ModularBootstrap.Upper.Membership.RadialFourier

/-!
# Hankel formula for the radial Fourier transform on `ℝ^{2w}` (all `w ≥ 1`)

For `u` continuous on `[0, ∞)` with integrable radial lift, the Mathlib Fourier transform of
`radialLift w u` at the point `x₀ = (b √(2c'/3)) e₀` (where `‖x₀‖² / 2 = c' b² / 3`) is

`𝓕 (radialLift w u) x₀ = -hankelContinuationW w c' u b = 2π ∫₀^∞ u(t) K^{(w)}_{-c' b²/3}(t) dt`,

i.e. the order-`(w-1)` Hankel transform of the bootstrap (`fw:FWM`, `cmb:K7`).  This is the
computation behind `WeightAxioms.hankelContinuationW_ofReal`, stated without Fourier-oddness
(that theorem is the case `𝓕 (radialLift w u) = -(radialLift w u)`); the spherical reduction to
`ℝ × ℝ^{2w-1}` and polar coordinates is reproduced here because the original proof is
inseparable from its oddness hypothesis.  Consequences for Fourier pairs are
`hankelContinuationW_of_pair`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat FourierTransform ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.Bessel

private lemma sphere_const_cancel (k : ℕ) :
    (2 * k + 1 : ℝ) * (Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℝ)) *
      ((k ! : ℝ) * sinEvenIntegral k) = 2 * Real.pi ^ (k + 1) := by
  rw [sinEvenIntegral_eq]
  have hfac := Nat.factorial_eq_mul_doubleFactorial (2 * k)
  rw [Nat.doubleFactorial_two_mul] at hfac
  have hfac_cast : (((2 * k + 1)! : ℕ) : ℝ) = ((2 * k + 1 : ℕ)‼ : ℝ) * ((2 : ℝ) ^ k * (k ! : ℝ)) := by
    exact_mod_cast hfac
  have hfac_succ : (((2 * k + 1)! : ℕ) : ℝ) = (2 * (k : ℝ) + 1) * ((2 * k)! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1 : (2 * (k : ℝ) + 1) * ((2 * k)! : ℝ) = ((2 * k + 1 : ℕ)‼ : ℝ) * ((2 : ℝ) ^ k * (k ! : ℝ)) := by
    linarith [hfac_cast, hfac_succ]
  have hdd_ne : ((2 * k + 1 : ℕ)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * k + 1)).ne'
  have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
  rw [h4]
  field_simp [hdd_ne, hk_ne]
  calc (2 * (k : ℝ) + 1) * Real.pi ^ k * 2 ^ (k + 1) * Real.pi * ((2 * k)! : ℝ)
      = Real.pi ^ (k + 1) * 2 ^ (k + 1) * ((2 * (k : ℝ) + 1) * ((2 * k)! : ℝ)) := by
          rw [pow_succ Real.pi k]; ring
    _ = Real.pi ^ (k + 1) * 2 ^ (k + 1) * (((2 * k + 1 : ℕ)‼ : ℝ) * (2 ^ k * (k ! : ℝ))) := by
          rw [h1]
    _ = 2 * ((2 * k + 1 : ℕ)‼ : ℝ) * (k ! : ℝ) * (2 ^ k) ^ 2 * Real.pi ^ (k + 1) := by
          rw [pow_succ (2 : ℝ) k]; ring

private noncomputable def splitEuclideanEquiv (w : ℕ) (hw : 1 ≤ w) :
    EuclideanSpace ℝ (Fin (2 * w)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin (2 * (w - 1) + 1)) :=
  let hdim : 2 * w = (2 * (w - 1) + 1) + 1 := by omega
  (MeasurableEquiv.toLp 2 (Fin (2 * w) → ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (finCongr hdim)).trans
      ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.toLp 2 (Fin (2 * (w - 1) + 1) → ℝ)))))

private lemma measurePreserving_splitEuclideanEquiv (w : ℕ) (hw : 1 ≤ w) :
    MeasurePreserving (splitEuclideanEquiv w hw) volume volume := by
  unfold splitEuclideanEquiv
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (2 * w))).trans ?_
  refine (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℝ) _).trans ?_
  refine (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (2 * (w - 1) + 1 + 1) => ℝ) 0).trans ?_
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (μ := volume)).prod (PiLp.volume_preserving_toLp (Fin (2 * (w - 1) + 1)))

private lemma splitEuclideanEquiv_symm_apply_eq {w : ℕ} (hw : 1 ≤ w)
    (hdim : 2 * w = (2 * (w - 1) + 1) + 1) (u : ℝ)
    (y : EuclideanSpace ℝ (Fin (2 * (w - 1) + 1))) (j : Fin (2 * w)) :
    ((splitEuclideanEquiv w hw).symm (u, y)) j =
      @Fin.insertNth (2 * (w - 1) + 1) (fun _ => ℝ) 0 u (fun m => y m) (finCongr hdim j) := by
  rfl

private lemma splitEuclideanEquiv_symm_norm_sq {w : ℕ} (hw : 1 ≤ w) (u : ℝ)
    (y : EuclideanSpace ℝ (Fin (2 * (w - 1) + 1))) :
    ‖(splitEuclideanEquiv w hw).symm (u, y)‖ ^ 2 = u ^ 2 + ‖y‖ ^ 2 := by
  let hdim : 2 * w = (2 * (w - 1) + 1) + 1 := by omega
  have hnorm_sum : ∀ (v : EuclideanSpace ℝ (Fin (2 * w))),
      ‖v‖ ^ 2 = ∑ i : Fin (2 * w), (v i) ^ 2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm_sum, EuclideanSpace.norm_sq_eq]
  have hmap : ∑ j : Fin (2 * w), (((splitEuclideanEquiv w hw).symm (u, y)) j) ^ 2 =
      ∑ i : Fin (2 * (w - 1) + 1 + 1),
        (@Fin.insertNth (2 * (w - 1) + 1) (fun _ => ℝ) 0 u (fun m => y m) i) ^ 2 := by
    have hpt : ∀ j : Fin (2 * w),
        (((splitEuclideanEquiv w hw).symm (u, y)) j) ^ 2 =
          (@Fin.insertNth (2 * (w - 1) + 1) (fun _ => ℝ) 0 u (fun m => y m) (finCongr hdim j)) ^ 2 :=
      fun j => by rw [splitEuclideanEquiv_symm_apply_eq hw hdim]
    simp_rw [hpt]
    exact Fintype.sum_equiv (finCongr hdim) _ _ fun j => rfl
  rw [hmap, Fin.sum_univ_succ]
  simp only [Fin.insertNth_apply_same, ← Fin.succAbove_zero, Fin.insertNth_apply_succAbove,
    Real.norm_eq_abs, sq_abs]

private lemma splitEuclideanEquiv_symm_inner {w : ℕ} (hw : 1 ≤ w) (u : ℝ)
    (y : EuclideanSpace ℝ (Fin (2 * (w - 1) + 1))) (r : ℝ) :
    let i0 : Fin (2 * w) := ⟨0, by omega⟩
    inner ℝ ((splitEuclideanEquiv w hw).symm (u, y)) (EuclideanSpace.single i0 r) = u * r := by
  intro i0
  rw [EuclideanSpace.inner_single_right]
  have hi0 : ((splitEuclideanEquiv w hw).symm (u, y)) i0 = u := by
    have hdim : 2 * w = (2 * (w - 1) + 1) + 1 := by omega
    rw [splitEuclideanEquiv_symm_apply_eq hw hdim]
    have h0 : finCongr hdim i0 = 0 := Fin.ext rfl
    rw [h0, Fin.insertNth_apply_same]
  simp [hi0, mul_comm]

private lemma setIntegral_polarCoord_Ioi (H : ℝ × ℝ → ℂ)
    (hH : IntegrableOn H ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ))) (hH_cont : Continuous H) :
    (∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p) =
      ∫ s in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) Real.pi,
        s • H (s * Real.cos θ, s * Real.sin θ) := by
  have h1 : (∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p) =
      ∫ p : ℝ × ℝ, ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator H p :=
    (integral_indicator (MeasurableSet.univ.prod measurableSet_Ioi) (f := H)).symm
  rw [h1, ← integral_comp_polarCoord_symm (((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator H)]
  have hpt : EqOn
      (fun p : ℝ × ℝ => p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator H (polarCoord.symm p))
      (Set.indicator (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi)
        (fun p : ℝ × ℝ => p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)))
      polarCoord.target := by
    intro p hp
    rcases hp with ⟨hs, hθ⟩
    simp only [polarCoord_symm_apply]
    by_cases hθ0 : p.2 ∈ Ioo (0 : ℝ) Real.pi
    · have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hθ0.1 hθ0.2
      have hmem : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) :=
        ⟨trivial, mul_pos hs hsin⟩
      have hmem2 : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi := ⟨hs, hθ0⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem2]
    · have hnot : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∉ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
        intro hmem
        have hsin : 0 < Real.sin p.2 := pos_of_mul_pos_right hmem.2 (mem_Ioi.mp hs).le
        have hlt : 0 < p.2 := by
          by_contra hle
          push Not at hle
          have : Real.sin p.2 ≤ 0 := by
            rcases eq_or_lt_of_le hle with h0 | hneg
            · rw [h0]; simp
            · rw [← neg_neg p.2, Real.sin_neg]
              exact neg_nonpos.mpr (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [hθ.1])).le
          linarith
        exact hθ0 ⟨hlt, hθ.2⟩
      rw [Set.indicator_of_notMem hnot, smul_zero, Set.indicator_of_notMem (fun h => hθ0 h.2)]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt,
    setIntegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  have hsub : polarCoord.target ∩ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) =
      Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi := by
    refine inter_eq_right.mpr fun p hp => ⟨hp.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
  rw [hsub]
  have hint_pol : IntegrableOn
      (fun p : ℝ × ℝ => p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) := by
    refine ⟨?_, ?_⟩
    · have hcont : Continuous fun p : ℝ × ℝ => p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2) :=
        continuous_fst.smul (hH_cont.comp (by fun_prop))
      exact hcont.continuousOn.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioo)
    · have h_lin := lintegral_comp_polarCoord_symm
        (fun q => (((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞)) q))
      have h_fin_tar : (∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞))
            (polarCoord.symm p)) < ⊤ := by
        rw [h_lin]
        calc ∫⁻ q : ℝ × ℝ, ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞)) q
            = ∫⁻ q in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), (‖H q‖₊ : ℝ≥0∞) :=
              lintegral_indicator (MeasurableSet.univ.prod measurableSet_Ioi) _
          _ < ⊤ := hH.2
      have h_sub_le : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            (‖p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞) ≤
          ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞))
              (polarCoord.symm p) := by
        calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
              (‖p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞)
            = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
                ENNReal.ofReal p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞))
                  (polarCoord.symm p) := by
              refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
              have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
              have hmem : polarCoord.symm p ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
                simp only [polarCoord_symm_apply]; exact ⟨trivial, mul_pos hp.1 hsin⟩
              rw [Set.indicator_of_mem hmem]
              simp only [polarCoord_symm_apply, nnnorm_smul, ENNReal.coe_mul,
                smul_eq_mul, Real.nnnorm_of_nonneg hp.1.le, ENNReal.ofReal_eq_coe_nnreal hp.1.le]
          _ ≤ _ := lintegral_mono_set (by rw [← hsub]; exact inter_subset_left)
      exact lt_of_le_of_lt h_sub_le h_fin_tar
  rw [Measure.volume_eq_prod] at hint_pol ⊢
  exact setIntegral_prod _ hint_pol

private lemma setIntegral_sq_div_two_Ioi {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Φ : ℝ → F) :
    ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) = ∫ t in Ioi (0 : ℝ), Φ t := by
  have him : (fun s : ℝ => s ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
    ext t
    refine ⟨?_, ?_⟩
    · rintro ⟨s, hs, rfl⟩; exact div_pos (sq_pos_of_pos hs) zero_lt_two
    · intro ht
      refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (mul_pos zero_lt_two ht), ?_⟩
      dsimp only
      rw [Real.sq_sqrt (mul_pos zero_lt_two ht).le]; ring
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2 / 2) s (Ioi 0) s := fun s _ => by
    have h1 := ((hasDerivAt_pow 2 s).div_const 2).hasDerivWithinAt (s := Ioi 0)
    simpa [Nat.cast_ofNat] using h1
  have hinj : InjOn (fun s : ℝ => s ^ 2 / 2) (Ioi 0) := fun x hx y hy hxy => by
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    have hy0 : 0 ≤ y := (mem_Ioi.mp hy).le
    have hsq : x ^ 2 = y ^ 2 := by linarith
    nlinarith [sq_nonneg (x - y)]
  symm
  calc ∫ t in Ioi (0 : ℝ), Φ t
      = ∫ t in (fun s : ℝ => s ^ 2 / 2) '' Ioi 0, Φ t := by rw [him]
    _ = ∫ s in Ioi (0 : ℝ), |s| • Φ (s ^ 2 / 2) :=
        integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj Φ
    _ = ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        rw [abs_of_pos hs]

/-- **Hankel formula** (`fw:FWM`, `cmb:K7`): for `u` continuous on `[0, ∞)` with integrable radial
lift, `𝓕 (radialLift w u)` at `(b √(2c'/3)) e₀` equals `-hankelContinuationW w c' u b`
`= 2π ∫₀^∞ u(t) K^{(w)}_{-c' b²/3}(t) dt` (no oddness assumed). -/
theorem fourier_radialLift_apply_eq {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (b : ℝ) :
    𝓕 (radialLift w g) (EuclideanSpace.single (⟨0, by omega⟩ : Fin (2 * w))
        (b * Real.sqrt (2 * c' / 3))) = -(hankelContinuationW w c' g (b : ℂ)) := by
  let k : ℕ := w - 1
  let d : ℕ := 2 * k + 1
  let i0 : Fin (2 * w) := ⟨0, by omega⟩
  let r : ℝ := b * Real.sqrt (2 * c' / 3)
  let x₀ : EuclideanSpace ℝ (Fin (2 * w)) := EuclideanSpace.single i0 r
  have hfour_eq : 𝓕 (radialLift w g) x₀ =
      ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v) := by
    simp only [Real.fourier_eq', smul_eq_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    refine congrArg (· * radialLift w g v) (congrArg Complex.exp ?_)
    push_cast; ring
  have he_mp := measurePreserving_splitEuclideanEquiv w hw
  have hint_four : Integrable fun v : EuclideanSpace ℝ (Fin (2 * w)) =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v) := by
    have haesm : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin (2 * w)) =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v)) volume := by
      have hlift : Continuous (radialLift w g) :=
        Complex.continuous_ofReal.comp
          (hg_cont.comp_continuous ((continuous_norm.pow 2).div_const 2) fun v =>
            mem_Ici.mpr (by positivity))
      exact ((Complex.continuous_exp.comp (by fun_prop)).mul hlift).aestronglyMeasurable
    refine ⟨haesm, ?_⟩
    have hfin := hg_int.hasFiniteIntegral
    refine lt_of_le_of_lt (lintegral_mono fun v => ?_) hfin
    rw [← ofReal_norm, ← ofReal_norm, norm_mul,
      show -2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ) =
        ((-2 * Real.pi * inner ℝ v x₀ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hint_prod : Integrable fun p : ℝ × EuclideanSpace ℝ (Fin (2 * k + 1)) =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (p.1 * r : ℂ)) *
        (g ((p.1 ^ 2 + ‖p.2‖ ^ 2) / 2) : ℂ) := by
    refine ((he_mp.symm.integrable_comp_emb (splitEuclideanEquiv w hw).symm.measurableEmbedding).mpr
      hint_four).congr (Eventually.of_forall fun p => ?_)
    dsimp only [Function.comp_apply, radialLift, x₀]
    rw [splitEuclideanEquiv_symm_norm_sq hw p.1 p.2, splitEuclideanEquiv_symm_inner hw p.1 p.2 r]
    push_cast; rfl
  have hstep1 : ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v) =
      ∫ u : ℝ, ∫ y : EuclideanSpace ℝ (Fin (2 * k + 1)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) *
          (g ((u ^ 2 + ‖y‖ ^ 2) / 2) : ℂ) := by
    rw [← he_mp.symm.integral_comp']
    have heq : (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * k + 1)) =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          (inner ℝ ((splitEuclideanEquiv w hw).symm p) x₀ : ℂ)) *
          radialLift w g ((splitEuclideanEquiv w hw).symm p)) =
        fun p : ℝ × EuclideanSpace ℝ (Fin (2 * k + 1)) =>
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (p.1 * r : ℂ)) *
            (g ((p.1 ^ 2 + ‖p.2‖ ^ 2) / 2) : ℂ) := by
      ext ⟨u, y⟩
      dsimp only [radialLift, x₀]
      rw [splitEuclideanEquiv_symm_norm_sq hw u y, splitEuclideanEquiv_symm_inner hw u y r]
      push_cast; rfl
    rw [heq, Measure.volume_eq_prod, integral_prod _ hint_prod]
  let c_sph : ℝ := (2 * k + 1 : ℝ) * (Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℝ))
  let H : ℝ × ℝ → ℂ := fun p =>
    (p.2 ^ (2 * k) : ℝ) •
      (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (p.1 * r : ℂ)) * (g ((p.1 ^ 2 + p.2 ^ 2) / 2) : ℂ))
  have hH_cont : Continuous H := by
    dsimp [H]
    exact ((continuous_snd.pow (2 * k)).smul
      ((Complex.continuous_exp.comp (by fun_prop)).mul
        (Complex.continuous_ofReal.comp
          (hg_cont.comp_continuous (by fun_prop) fun p => mem_Ici.mpr (by positivity)))))
  have hstep2 : (∫ u : ℝ, ∫ y : EuclideanSpace ℝ (Fin (2 * k + 1)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) *
          (g ((u ^ 2 + ‖y‖ ^ 2) / 2) : ℂ)) =
      c_sph • ∫ u : ℝ, ∫ ρ in Ioi (0 : ℝ), H (u, ρ) := by
    have h_inner : ∀ u : ℝ,
        (∫ y : EuclideanSpace ℝ (Fin (2 * k + 1)),
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) *
            (g ((u ^ 2 + ‖y‖ ^ 2) / 2) : ℂ)) =
        c_sph • ∫ ρ in Ioi (0 : ℝ), H (u, ρ) := by
      intro u
      let ψ : ℝ → ℂ := fun ρ =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) * (g ((u ^ 2 + ρ ^ 2) / 2) : ℂ)
      have hsph := MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure (EuclideanSpace ℝ (Fin (2 * k + 1))))) ψ
      have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * k + 1))) = 2 * k + 1 :=
        finrank_euclideanSpace_fin
      have hvol := InnerProductSpace.volume_ball_of_dim_odd (E := EuclideanSpace ℝ (Fin (2 * k + 1)))
        (k := k) hdim 0 1
      have hvol_real : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * k + 1))) 1) =
          Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℝ) := by
        rw [Measure.real_def, hvol, ENNReal.ofReal_one, one_pow, one_mul, hdim,
          ENNReal.toReal_ofReal (by positivity)]
      rw [hdim, hvol_real, Nat.add_sub_cancel] at hsph
      simp_rw [nsmul_eq_mul, Complex.real_smul] at hsph
      rw [Complex.real_smul]
      dsimp [c_sph]
      push_cast at hsph ⊢
      have hnorm_fac : ((2 * (k : ℂ) + 1) * ((Real.pi : ℂ) ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℂ))) *
          ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (2 * k) * ψ ρ =
          (2 * (k : ℂ) + 1) * (((Real.pi : ℂ) ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℂ)) *
            ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (2 * k) * ψ ρ) := by ring
      have heq_rhs : ∫ ρ in Ioi (0 : ℝ), H (u, ρ) = ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (2 * k) * ψ ρ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
        dsimp [H, ψ]; push_cast; rfl
      rw [heq_rhs, hnorm_fac]
      exact hsph
    simp_rw [h_inner]
    rw [integral_smul]
  have ht_int : IntegrableOn (fun t : ℝ => t ^ k * |g t|) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => ‖t ^ k * g t‖) (Ioi 0) :=
      ((integrable_radialLift_iff hw g).1 hg_int).norm
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (mem_Ioi.mp ht).le _)]
  have hH_int : IntegrableOn H ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := by
    have haesm_H : AEStronglyMeasurable H (volume.restrict ((univ : Set ℝ) ×ˢ Ioi 0)) :=
      hH_cont.continuousOn.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioi)
    have hs_int : IntegrableOn (fun s : ℝ => s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|)) (Ioi 0) := by
      have him : (fun s : ℝ => s ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
        ext t; refine ⟨fun ⟨s, hs, h⟩ => h ▸ div_pos (sq_pos_of_pos hs) zero_lt_two,
          fun ht => ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (mul_pos zero_lt_two ht), ?_⟩⟩
        dsimp only; rw [Real.sq_sqrt (mul_pos zero_lt_two ht).le]; ring
      have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2 / 2) s (Ioi 0) s :=
        fun s _ => by simpa [Nat.cast_ofNat] using ((hasDerivAt_pow 2 s).div_const 2).hasDerivWithinAt
      have hinj : InjOn (fun s : ℝ => s ^ 2 / 2) (Ioi 0) := fun x hx y hy hxy => by
        have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le; have hy0 : 0 ≤ y := (mem_Ioi.mp hy).le
        have : x ^ 2 = y ^ 2 := by linarith
        nlinarith [sq_nonneg (x - y)]
      have ht_int_img : IntegrableOn (fun t : ℝ => t ^ k * |g t|) ((fun s : ℝ => s ^ 2 / 2) '' Ioi 0) := by
        rwa [him]
      have hcomp := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj
        (f' := fun x => x) (g := fun t => t ^ k * |g t|)).mp ht_int_img
      refine hcomp.congr_fun (fun s hs => ?_) measurableSet_Ioi
      dsimp only
      rw [abs_of_pos hs, smul_eq_mul]
    have hfin : (∫⁻ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), (‖H p‖₊ : ℝ≥0∞)) < ⊤ := by
      have hlin := lintegral_comp_polarCoord_symm
        (fun p : ℝ × ℝ => ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) p)
      have h_eq_lhs : (∫⁻ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), (‖H p‖₊ : ℝ≥0∞)) =
          ∫⁻ p : ℝ × ℝ, ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) p :=
        (lintegral_indicator (MeasurableSet.univ.prod measurableSet_Ioi) _).symm
      rw [h_eq_lhs, ← hlin]
      have hsub : polarCoord.target ∩ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) =
          Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi :=
        inter_eq_right.mpr fun p hp => ⟨hp.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
      have h_le_ub : ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 •
              ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) (polarCoord.symm p) ≤
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|))) := by
        calc ∫⁻ p in polarCoord.target,
                ENNReal.ofReal p.1 •
                  ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) (polarCoord.symm p)
            = ∫⁻ p in polarCoord.target,
                (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi).indicator
                  (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞)) p := by
              refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
              rw [polarCoord_symm_apply]
              by_cases hθ0 : p.2 ∈ Ioo (0 : ℝ) Real.pi
              · have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hθ0.1 hθ0.2
                have hmem : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) :=
                  ⟨trivial, mul_pos hp.1 hsin⟩
                have hmem2 : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi := ⟨hp.1, hθ0⟩
                rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem2, smul_eq_mul]
              · have hnot : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∉ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
                  intro hmem
                  have hsin : 0 < Real.sin p.2 := pos_of_mul_pos_right hmem.2 (mem_Ioi.mp hp.1).le
                  have hlt : 0 < p.2 := by
                    by_contra hle; push Not at hle
                    have : Real.sin p.2 ≤ 0 := by
                      rcases eq_or_lt_of_le hle with h0 | hneg
                      · rw [h0]; simp
                      · rw [← neg_neg p.2, Real.sin_neg]
                        exact neg_nonpos.mpr (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [hp.2.1])).le
                    linarith
                  exact hθ0 ⟨hlt, hp.2.2⟩
                rw [Set.indicator_of_notMem hnot, smul_zero, Set.indicator_of_notMem (fun h => hθ0 h.2)]
          _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
                ENNReal.ofReal p.1 * (‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞) := by
              rw [setLIntegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo), inter_comm, hsub]
          _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
                ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|))) := by
              refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
              have hsin_nn : 0 ≤ Real.sin p.2 := (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2).le
              have htrig : ((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) / 2 = p.1 ^ 2 / 2 := by
                calc ((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) / 2
                    = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) / 2 := by ring
                  _ = p.1 ^ 2 * 1 / 2 := by rw [Real.cos_sq_add_sin_sq]
                  _ = p.1 ^ 2 / 2 := by ring
              have hval : p.1 * ‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖ ≤
                  2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|)) := by
                dsimp [H]
                rw [htrig, norm_mul, Complex.norm_real,
                  Real.norm_of_nonneg (pow_nonneg (mul_nonneg hp.1.le hsin_nn) _),
                  norm_mul, show -2 * (Real.pi : ℂ) * Complex.I * ((p.1 * Real.cos p.2 : ℝ) * (r : ℂ)) =
                    ((-2 * Real.pi * (p.1 * Real.cos p.2 * r) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                  Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
                have hsin_le1 : Real.sin p.2 ≤ 1 := Real.sin_le_one p.2
                have hpow : (p.1 * Real.sin p.2) ^ (2 * k) ≤ p.1 ^ (2 * k) := by
                  calc (p.1 * Real.sin p.2) ^ (2 * k) ≤ (p.1 * 1) ^ (2 * k) :=
                        pow_le_pow_left₀ (mul_nonneg hp.1.le hsin_nn)
                          (mul_le_mul_of_nonneg_left hsin_le1 hp.1.le) _
                    _ = p.1 ^ (2 * k) := by rw [mul_one]
                calc p.1 * ((p.1 * Real.sin p.2) ^ (2 * k) * |g (p.1 ^ 2 / 2)|)
                    ≤ p.1 * (p.1 ^ (2 * k) * |g (p.1 ^ 2 / 2)|) := by
                      gcongr
                      exact hp.1.le
                  _ = 2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|)) := by
                      have h2ne : (2 : ℝ) ^ k ≠ 0 := by positivity
                      rw [div_pow, show (p.1 ^ 2) ^ k = p.1 ^ (2 * k) from (pow_mul p.1 2 k).symm]
                      field_simp [h2ne]
              rw [show (‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞) =
                  ENNReal.ofReal ‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖ from
                  (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm,
                ← ENNReal.ofReal_mul hp.1.le]
              exact ENNReal.ofReal_le_ofReal hval
      have h_prod_lt : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|)))) < ⊤ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        have hm_f : Measurable fun p : ℝ × ℝ =>
            ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|))) := by
          refine ENNReal.continuous_ofReal.measurable.comp ?_
          exact (continuous_const.mul (continuous_fst.mul
            (((continuous_fst.pow 2).div_const 2 |>.pow k).mul
              (continuous_abs.comp (hg_cont.comp_continuous ((continuous_fst.pow 2).div_const 2) fun p =>
                mem_Ici.mpr (div_nonneg (sq_nonneg _) zero_lt_two.le)))))).measurable
        rw [MeasureTheory.lintegral_prod _ hm_f.aemeasurable]
        have h_eq : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ _θ in Ioo (0 : ℝ) Real.pi,
              ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|)))) =
            ENNReal.ofReal Real.pi * ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))) := by
          simp_rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
          have hm1 : Measurable fun s : ℝ =>
              ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))) :=
            ENNReal.continuous_ofReal.measurable.comp
              ((continuous_const.mul (continuous_id.mul (((continuous_pow 2).div_const 2 |>.pow k).mul
                (continuous_abs.comp (hg_cont.comp_continuous ((continuous_pow 2).div_const 2) fun s =>
                  mem_Ici.mpr (div_nonneg (sq_nonneg _) zero_lt_two.le))))))).measurable
          rw [lintegral_mul_const _ hm1, mul_comm]
        rw [h_eq]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        have hlt := (hs_int.const_mul ((2 : ℝ) ^ k)).hasFiniteIntegral
        have h_eq2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))) =
            ∫⁻ s in Ioi (0 : ℝ), (‖(2 : ℝ) ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))‖₊ : ℝ≥0∞) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
          have hs0 : 0 ≤ s := (mem_Ioi.mp hs).le
          rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (by positivity)]
        rw [h_eq2]
        exact hlt
      exact lt_of_le_of_lt h_le_ub h_prod_lt
    exact ⟨haesm_H, hfin⟩
  have hstep3 : (∫ u : ℝ, ∫ ρ in Ioi (0 : ℝ), H (u, ρ)) =
      ∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p := by
    rw [Measure.volume_eq_prod] at hH_int ⊢
    have hprod := (setIntegral_prod H hH_int).symm
    simp_rw [setIntegral_univ] at hprod
    exact hprod
  have hstep4 : (∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p) =
      ∫ s in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) Real.pi, s • H (s * Real.cos θ, s * Real.sin θ) :=
    setIntegral_polarCoord_Ioi H hH_int hH_cont
  have hstep5 : ∀ s ∈ Ioi (0 : ℝ),
      (∫ θ in Ioo (0 : ℝ) Real.pi, s • H (s * Real.cos θ, s * Real.sin θ)) =
        s • (((2 * (s ^ 2 / 2)) ^ k : ℂ) * ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g (s ^ 2 / 2) : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ))) := by
    intro s hs
    have htrig : ∀ θ : ℝ, ((s * Real.cos θ) ^ 2 + (s * Real.sin θ) ^ 2) / 2 = s ^ 2 / 2 := fun θ => by
      calc ((s * Real.cos θ) ^ 2 + (s * Real.sin θ) ^ 2) / 2
          = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) / 2 := by ring
        _ = s ^ 2 * 1 / 2 := by rw [Real.cos_sq_add_sin_sq]
        _ = s ^ 2 / 2 := by ring
    have heq_θ : ∀ θ : ℝ, s • H (s * Real.cos θ, s * Real.sin θ) =
        (s : ℂ) * (((2 * (s ^ 2 / 2) : ℝ) : ℂ) ^ k * (g (s ^ 2 / 2) : ℂ) *
          (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) *
          ((((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)⁻¹ *
            (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
              ((Real.sin θ ^ (2 * k) : ℝ) : ℂ))) := by
      intro θ
      have hfac_ne : (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (by positivity) (sinEvenIntegral_pos k)).ne'
      have hmul : (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ) *
          (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hfac_ne
      dsimp [H]
      rw [htrig θ]
      have hcast :
          (s : ℂ) * ((((s * Real.sin θ) ^ (2 * k) : ℝ) : ℂ) *
            (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((s * Real.cos θ : ℝ) * r : ℂ)) *
              (g (s ^ 2 / 2) : ℂ))) =
          (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ)) *
            (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
              ((Real.sin θ ^ (2 * k) : ℝ) : ℂ)) := by
        rw [Complex.ofReal_pow, Complex.ofReal_mul, mul_pow, Complex.ofReal_pow, Complex.ofReal_mul]
        rw [show (-2 * (Real.pi : ℂ) * Complex.I * ((s : ℂ) * (Real.cos θ : ℂ) * (r : ℂ))) =
          (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ) by ring]
        ring
      rw [hcast]
      have hcast2 :
          (s : ℂ) * (((2 * (s ^ 2 / 2) : ℝ) : ℂ) ^ k * (g (s ^ 2 / 2) : ℂ) *
            (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) =
          (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ) *
            (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) := by
        push_cast
        rw [show (2 : ℂ) * ((s : ℂ) ^ 2 / 2) = (s : ℂ) ^ 2 by ring, ← pow_mul]
      rw [hcast2]
      calc (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ)) *
            (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
              ((Real.sin θ ^ (2 * k) : ℝ) : ℂ))
          = (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ) * 1) *
              (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
                ((Real.sin θ ^ (2 * k) : ℝ) : ℂ)) := by ring
        _ = (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ) *
                (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) *
              ((((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)⁻¹ *
                (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
                  ((Real.sin θ ^ (2 * k) : ℝ) : ℂ))) := by
            rw [← hmul]; ring
    simp_rw [heq_θ, integral_const_mul]
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    have hbes := besselSC_eq_sin_integral k (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ))
    have hz_sq : (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) ^ 2 / 4 =
        4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ) := by
      have hr_sq : (r : ℂ) ^ 2 = (2 : ℂ) * (c' : ℂ) * (b : ℂ) ^ 2 / 3 := by
        dsimp [r]; push_cast
        rw [mul_pow, show ((Real.sqrt (2 * c' / 3) : ℝ) : ℂ) ^ 2 = ((2 * c' / 3 : ℝ) : ℂ) by
          exact_mod_cast Real.sq_sqrt (by positivity)]
        push_cast; ring
      calc (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) ^ 2 / 4
          = 4 * (Real.pi : ℂ) ^ 2 * (Complex.I ^ 2) * (r : ℂ) ^ 2 * (s : ℂ) ^ 2 / 4 := by ring
        _ = 4 * (Real.pi : ℂ) ^ 2 * (-1) * ((2 : ℂ) * (c' : ℂ) * (b : ℂ) ^ 2 / 3) * (s : ℂ) ^ 2 / 4 := by
            rw [Complex.I_sq, hr_sq]
        _ = _ := by push_cast; ring
    rw [← hbes, hz_sq, Complex.real_smul]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hstep5] at hstep4
  have hstep6 : ∫ s in Ioi (0 : ℝ), s • (((2 * (s ^ 2 / 2)) ^ k : ℂ) *
        ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g (s ^ 2 / 2) : ℂ) *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ))) =
      ((k ! : ℝ) * sinEvenIntegral k : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ)) := by
    let Φ : ℝ → ℂ := fun t => ((2 * t : ℝ) : ℂ) ^ k *
      ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g t : ℂ) *
      besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ))
    have h6 : ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) = ∫ t in Ioi (0 : ℝ), Φ t :=
      setIntegral_sq_div_two_Ioi Φ
    have h6l : ∫ s in Ioi (0 : ℝ), s • (((2 * (s ^ 2 / 2)) ^ k : ℂ) *
          ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g (s ^ 2 / 2) : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ))) =
        ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      dsimp [Φ]; push_cast; rfl
    rw [h6l, h6, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp [Φ]; ring
  have hfour_final : 𝓕 (radialLift w g) x₀ =
      c_sph • (((k ! : ℝ) * sinEvenIntegral k : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ))) := by
    rw [hfour_eq, hstep1, hstep2, hstep3, hstep4, hstep6]
  have hconst_c : (c_sph : ℂ) * ((k ! : ℝ) * sinEvenIntegral k : ℂ) =
      2 * (Real.pi : ℂ) * ((Real.pi : ℂ) ^ k) := by
    calc (c_sph : ℂ) * ((k ! : ℝ) * sinEvenIntegral k : ℂ)
        = ((c_sph * ((k ! : ℝ) * sinEvenIntegral k) : ℝ) : ℂ) := by push_cast; ring
      _ = ((2 * Real.pi ^ (k + 1) : ℝ) : ℂ) := by rw [sphere_const_cancel k]
      _ = 2 * (Real.pi : ℂ) * ((Real.pi : ℂ) ^ k) := by push_cast; rw [pow_succ']; ring
  rw [Complex.real_smul, ← mul_assoc, hconst_c] at hfour_final
  have hint_pull : 2 * (Real.pi : ℂ) * ((Real.pi : ℂ) ^ k) *
      ∫ t in Ioi (0 : ℝ), ((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ)) =
      2 * (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ),
        (g t : ℂ) * kernelKC w (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) (t : ℂ) := by
    rw [mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    unfold kernelKC
    change (Real.pi : ℂ) ^ k * (((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ))) =
      (g t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ k *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ)))
    rw [show (2 * (Real.pi : ℂ) * (t : ℂ)) = (Real.pi : ℂ) * ((2 * t : ℝ) : ℂ) by push_cast; ring, mul_pow]
    ring
  rw [hint_pull] at hfour_final
  show 𝓕 (radialLift w g) x₀ = _
  rw [hfour_final]
  unfold hankelContinuationW
  ring


/-- The radial lift evaluated at `(b √(2c'/3)) e₀` is the profile at `c' b² / 3`. -/
lemma radialLift_single {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') (u : ℝ → ℝ) (b : ℝ) :
    radialLift w u (EuclideanSpace.single (⟨0, by omega⟩ : Fin (2 * w))
        (b * Real.sqrt (2 * c' / 3))) = (u (c' * b ^ 2 / 3) : ℂ) := by
  have hnorm : ‖(EuclideanSpace.single (⟨0, by omega⟩ : Fin (2 * w))
      (b * Real.sqrt (2 * c' / 3)) : EuclideanSpace ℝ (Fin (2 * w)))‖ =
      |b * Real.sqrt (2 * c' / 3)| := by
    have := PiLp.norm_single 2 (fun _ : Fin (2 * w) => ℝ) (⟨0, by omega⟩ : Fin (2 * w))
      (b * Real.sqrt (2 * c' / 3))
    rw [Real.norm_eq_abs] at this
    exact this
  have hsq : ‖(EuclideanSpace.single (⟨0, by omega⟩ : Fin (2 * w))
      (b * Real.sqrt (2 * c' / 3)) : EuclideanSpace ℝ (Fin (2 * w)))‖ ^ 2 / 2 = c' * b ^ 2 / 3 := by
    rw [hnorm, sq_abs, mul_pow, Real.sq_sqrt (by positivity)]; ring
  simp only [radialLift, hsq]

/-- **Hankel formula for a Fourier pair** (`fw:FWM` item 3, `cmb:K7` "Vacuum"): for real `b`,
`hankelContinuationW w c' h b = -ĥ(c' b²/3)`. -/
theorem hankelContinuationW_of_pair {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c')
    {h ĥ : ℝ → ℝ} (hp : RadialFourierPair w h ĥ) (b : ℝ) :
    hankelContinuationW w c' h (b : ℂ) = -(ĥ (c' * b ^ 2 / 3) : ℂ) := by
  have := fourier_radialLift_apply_eq hw hc' hp.cont hp.int b
  rw [hp.transform, radialLift_single hw hc'] at this
  rw [this]; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.fourier_radialLift_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_radialLift_apply_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.hankelContinuationW_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelContinuationW_of_pair

end FormalResearch.ModularBootstrap.Upper.Membership
