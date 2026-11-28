module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Slit-Plane Maximum Modulus (`int:sonine`)

Proves the elementary Phragmén–Lindelöf / maximum-modulus bound on the doubly-slit plane
`ℂ \ ((-∞, -R] ∪ [R, ∞))` used in `int:sonine`:
`slit_plane_max_mod`: If `h : ℂ → ℂ` is entire with `‖h z‖ ≤ M₀ * exp (a * |z.im|)` and
`‖h x‖ ≤ D` for `R ≤ |x|`, then `‖h x‖ ≤ D * exp (a * √(R^2 - x^2))` for `|x| ≤ R`.
-/

@[expose] public section

open Real Complex Filter Topology Set

namespace FormalResearch.ModularBootstrap.Integrality

private noncomputable def slitOmega (R : ℝ) (z : ℂ) : ℂ :=
  ((R : ℂ) ^ 2 - z ^ 2) ^ (1 / 2 : ℂ)

private lemma mem_slitPlane_sub_sq {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ¬ (z.im = 0 ∧ R ≤ |z.re|)) :
    (R : ℂ) ^ 2 - z ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left
    have hlt : |z.re| < R := not_le.mp fun hle => hz ⟨him, hle⟩
    have hre_sq : z.re ^ 2 < R ^ 2 := by
      simpa [sq_abs] using sq_lt_sq' (by linarith [abs_nonneg z.re]) hlt
    have hz_eq : z = (z.re : ℂ) := Complex.ext rfl him
    rw [hz_eq]
    have hre_eq : ((R : ℂ) ^ 2 - (z.re : ℂ) ^ 2).re = R ^ 2 - z.re ^ 2 := by
      simp [pow_two, Complex.mul_re]
    linarith
  · by_cases hre : z.re = 0
    · left
      have hz_eq : z = z.im * Complex.I := Complex.ext (by simpa using hre) (by simp)
      rw [hz_eq]
      have hre_eq : ((R : ℂ) ^ 2 - (z.im * Complex.I) ^ 2).re = R ^ 2 + z.im ^ 2 := by
        simp [pow_two, Complex.mul_re]
      nlinarith [sq_nonneg z.im]
    · right
      have him_eq : ((R : ℂ) ^ 2 - z ^ 2).im = -2 * z.re * z.im := by
        simp [pow_two, Complex.mul_im]; ring
      rw [him_eq]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hre) him

private lemma slitOmega_sq {R : ℝ} (_hR : 0 < R) {z : ℂ}
    (_hz : ¬ (z.im = 0 ∧ R ≤ |z.re|)) :
    slitOmega R z ^ 2 = (R : ℂ) ^ 2 - z ^ 2 := by
  unfold slitOmega
  rw [← Complex.cpow_nat_mul]
  have h12 : (((2 : ℕ) : ℂ) * (1 / 2 : ℂ)) = 1 := by norm_num
  rw [h12, Complex.cpow_one]

private lemma slitOmega_re_pos {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ¬ (z.im = 0 ∧ R ≤ |z.re|)) :
    0 < (slitOmega R z).re := by
  unfold slitOmega
  set w := (R : ℂ) ^ 2 - z ^ 2
  have hw_slit : w ∈ Complex.slitPlane := mem_slitPlane_sub_sq hR hz
  have hw_ne : w ≠ 0 := Complex.slitPlane_ne_zero hw_slit
  rw [Complex.cpow_def_of_ne_zero hw_ne]
  have hre : (Complex.log w * (1 / 2 : ℂ)).re = Real.log ‖w‖ / 2 := by
    simp [div_eq_mul_inv, Complex.log_re]
  have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by
    simp [div_eq_mul_inv, Complex.log_im]
  rw [Complex.exp_re, hre, him]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have harg := Complex.mem_slitPlane_iff_arg.mp hw_slit
  have hlt_pi : w.arg < π := lt_of_le_of_ne (Complex.arg_le_pi w) harg.1
  have hgt_neg_pi : -π < w.arg := Complex.neg_pi_lt_arg w
  exact ⟨by linarith, by linarith⟩

private lemma slitOmega_ofReal {R x : ℝ} (hx : |x| < R) :
    slitOmega R (x : ℂ) = (Real.sqrt (R ^ 2 - x ^ 2) : ℂ) := by
  unfold slitOmega
  have hpos : 0 < R ^ 2 - x ^ 2 := by
    have : x ^ 2 < R ^ 2 := by simpa [sq_abs] using sq_lt_sq' (by linarith [abs_nonneg x]) hx
    linarith
  have heq : ((R : ℂ) ^ 2 - (x : ℂ) ^ 2) = ((R ^ 2 - x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [heq, hhalf, ← Complex.ofReal_cpow hpos.le, Real.sqrt_eq_rpow]

private lemma abs_im_le_slitOmega_re {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ¬ (z.im = 0 ∧ R ≤ |z.re|)) :
    |z.im| ≤ (slitOmega R z).re := by
  set ω := slitOmega R z
  have hre_pos : 0 < ω.re := slitOmega_re_pos hR hz
  have hsq : ω ^ 2 = (R : ℂ) ^ 2 - z ^ 2 := slitOmega_sq hR hz
  have h2re : 2 * ω.re ^ 2 = ‖(R : ℂ) ^ 2 - z ^ 2‖ + ((R : ℂ) ^ 2 - z ^ 2).re := by
    have hnorm : ‖ω ^ 2‖ = ω.re ^ 2 + ω.im ^ 2 := by
      rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hre : (ω ^ 2).re = ω.re ^ 2 - ω.im ^ 2 := by
      simp [pow_two, Complex.mul_re]
    rw [← hsq, hnorm, hre]; ring
  have hre_val : ((R : ℂ) ^ 2 - z ^ 2).re = R ^ 2 - z.re ^ 2 + z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]; ring
  have him_val : ((R : ℂ) ^ 2 - z ^ 2).im = -2 * z.re * z.im := by
    simp [pow_two, Complex.mul_im]; ring
  have hnorm_sq : ‖(R : ℂ) ^ 2 - z ^ 2‖ ^ 2 =
      (R ^ 2 - z.re ^ 2 + z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre_val, him_val]
    ring
  have hgoal_sq : 2 * z.im ^ 2 ≤ 2 * ω.re ^ 2 := by
    rw [h2re, hre_val]
    have hle : z.im ^ 2 - R ^ 2 + z.re ^ 2 ≤ ‖(R : ℂ) ^ 2 - z ^ 2‖ := by
      rcases le_total (z.im ^ 2 - R ^ 2 + z.re ^ 2) 0 with hneg | hpos
      · exact hneg.trans (norm_nonneg _)
      · refine (abs_le_of_sq_le_sq' ?_ (norm_nonneg _)).2
        rw [hnorm_sq]
        nlinarith [sq_nonneg R, sq_nonneg z.im]
    linarith
  have habs : |z.im| ^ 2 ≤ ω.re ^ 2 := by rw [sq_abs]; linarith
  exact (Real.sqrt_sq (abs_nonneg _)).symm.le.trans ((Real.sqrt_le_sqrt habs).trans_eq (Real.sqrt_sq hre_pos.le))

private lemma norm_cpow_ofReal_neg {w : ℂ} (hw : w ≠ 0) (η : ℝ) :
    ‖w ^ ((-η : ℝ) : ℂ)‖ = ‖w‖ ^ (-η) := by
  rw [Complex.cpow_def_of_ne_zero hw, Complex.norm_exp]
  have hre : (Complex.log w * ((-η : ℝ) : ℂ)).re = -η * Real.log ‖w‖ := by
    simp [Complex.mul_re, Complex.log_re]; ring
  rw [hre, Real.rpow_def_of_pos (norm_pos_iff.mpr hw)]
  congr 1; ring

private lemma norm_slitOmega_ge {R : ℝ} {z : ℂ} (hR : 0 < R)
    (hz : ¬ (z.im = 0 ∧ R ≤ |z.re|)) :
    Real.sqrt (‖z‖ ^ 2 - R ^ 2) ≤ ‖slitOmega R z‖ := by
  have hsq : ‖slitOmega R z‖ ^ 2 = ‖(R : ℂ) ^ 2 - z ^ 2‖ := by
    rw [← norm_pow, slitOmega_sq hR hz]
  have htri : ‖z‖ ^ 2 - R ^ 2 ≤ ‖(R : ℂ) ^ 2 - z ^ 2‖ := by
    have h1 := norm_sub_norm_le (z ^ 2) ((R : ℂ) ^ 2)
    rw [norm_sub_rev] at h1
    simpa [norm_pow, abs_of_pos hR] using h1
  rw [← hsq] at htri
  exact (Real.sqrt_le_sqrt htri).trans_eq (Real.sqrt_sq (norm_nonneg _))

/-- Elementary slit-plane maximum modulus (`int:sonine`):
if `h` is entire with exponential type `a` along `ℂ` (`‖h z‖ ≤ M₀ exp(a |Im z|)`) and
`‖h x‖ ≤ D` for `x ∈ ℝ` with `|x| ≥ R`, then `‖h x‖ ≤ D exp(a √(R^2 - x^2))` for `|x| ≤ R`. -/
theorem slit_plane_max_mod {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    {M₀ a R D : ℝ} (hM0 : 0 ≤ M₀) (ha : 0 ≤ a) (hR : 0 < R) (hD : 0 ≤ D)
    (hbound : ∀ z : ℂ, ‖h z‖ ≤ M₀ * Real.exp (a * |z.im|))
    (hslit : ∀ x : ℝ, R ≤ |x| → ‖h (x : ℂ)‖ ≤ D) :
    ∀ x : ℝ, |x| ≤ R → ‖h (x : ℂ)‖ ≤ D * Real.exp (a * Real.sqrt (R ^ 2 - x ^ 2)) := by
  intro x₀ hx₀
  rcases eq_or_lt_of_le hx₀ with heq | hx₀_lt
  · have hsub : R ^ 2 - x₀ ^ 2 = 0 := by rw [← sq_abs x₀, heq, sub_self]
    rw [hsub, Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one]
    exact hslit x₀ heq.symm.le
  · suffices hε : ∀ ε : ℝ, 0 < ε →
        ‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) ≤ D + ε by
      have hle : ‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) ≤ D :=
        le_of_forall_pos_le_add fun ε hεp => by simpa using hε ε hεp
      calc ‖h (x₀ : ℂ)‖
          = (‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2))) *
              Real.exp (a * Real.sqrt (R ^ 2 - x₀ ^ 2)) := by
              rw [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ D * Real.exp (a * Real.sqrt (R ^ 2 - x₀ ^ 2)) := by
              gcongr
    intro ε hε
    suffices hη : ∀ η : ℝ, 0 < η →
        ‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) *
          (1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R) ^ (-η) ≤ D + ε by
      have hbase : 0 < 1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R := by positivity
      have htend : Tendsto (fun η : ℝ =>
            ‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) *
              (1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R) ^ (-η))
          (𝓝[>] (0 : ℝ))
          (𝓝 (‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) * 1)) := by
        refine tendsto_const_nhds.mul ?_
        have hfn : (fun η : ℝ => (1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R) ^ (-η)) =
            fun η => Real.exp (Real.log (1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R) * (-η)) := by
          ext η; exact Real.rpow_def_of_pos hbase _
        rw [hfn, ← Real.exp_zero]
        refine ((Real.continuous_exp.comp (continuous_const.mul continuous_neg)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds).congr (fun _ => rfl) |>.mono_right ?_
        simp
      have hev : ∀ᶠ η : ℝ in 𝓝[>] 0,
          ‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) *
            (1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R) ^ (-η) ≤ D + ε :=
        eventually_nhdsWithin_of_forall fun η hηp => hη η hηp
      simpa using le_of_tendsto htend hev
    intro η hη
    let M_val : ℝ := max 2 (((M₀ + 1) / (D + ε)) ^ (1 / η))
    let R_big : ℝ := R * (M_val + 2)
    have hM_ge2 : 2 ≤ M_val := le_max_left _ _
    have hRbig_gt : R < R_big := by
      have : 1 < M_val + 2 := by linarith
      simpa [R_big] using (lt_mul_of_one_lt_right hR this)
    have huc : UniformContinuousOn h (Metric.closedBall (0 : ℂ) (R_big + 1)) :=
      (isCompact_closedBall (0 : ℂ) (R_big + 1)).uniformContinuousOn_of_continuous
        hd.continuous.continuousOn
    obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    let δ : ℝ := min ((R - |x₀|) / 4) (min (δ₀ / 4) (1 / 2))
    have hδ_pos : 0 < δ := by positivity
    have hδ_lt_R : δ < R - |x₀| := by
      have h1 : δ ≤ (R - |x₀|) / 4 := min_le_left _ _
      linarith
    have h3δ_lt : 3 * δ < δ₀ := by
      have h1 : δ ≤ δ₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    let F : Set ℂ := {z : ℂ | |z.im| ≤ δ ∧ R - δ ≤ |z.re|}
    let U : Set ℂ := Metric.ball (0 : ℂ) R_big \ F
    have hF_closed : IsClosed F :=
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const).inter
        (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_re))
    have hU_bdd : Bornology.IsBounded U := Metric.isBounded_ball.subset sdiff_subset
    have hcl_slit : ∀ z ∈ closure U, ¬ (z.im = 0 ∧ R ≤ |z.re|) := by
      intro z hz hbad
      let F_int : Set ℂ := {w : ℂ | |w.im| < δ ∧ R - δ < |w.re|}
      have hF_int_open : IsOpen F_int :=
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).inter
          (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_re))
      have hz_int : z ∈ F_int := ⟨by simpa [hbad.1] using hδ_pos, by linarith [hbad.2]⟩
      have hdisj : Disjoint F_int U := by
        rw [Set.disjoint_iff]
        intro w ⟨hw1, hw2⟩
        exact hw2.2 ⟨hw1.1.le, hw1.2.le⟩
      exact (hdisj.closure_right hF_int_open).notMem_of_mem_left hz_int hz
    let G : ℂ → ℂ := fun z =>
      h z * Complex.exp (-(a : ℂ) * slitOmega R z) * (1 + slitOmega R z / (R : ℂ)) ^ ((-η : ℝ) : ℂ)
    have hG_diff : ∀ z ∈ closure U, DifferentiableAt ℂ G z := by
      intro z hz
      have hz_slit := hcl_slit z hz
      have hw_mem : (R : ℂ) ^ 2 - z ^ 2 ∈ Complex.slitPlane := mem_slitPlane_sub_sq hR hz_slit
      have hω_diff : DifferentiableAt ℂ (slitOmega R) z := by
        have hf1 := (((hasDerivAt_id z).pow 2).const_sub ((R : ℂ) ^ 2)).hasFDerivAt
        have hf2 : HasFDerivAt (fun _ : ℂ => (1 / 2 : ℂ)) (0 : ℂ →L[ℂ] ℂ) z := hasFDerivAt_const _ _
        exact (hf1.cpow hf2 hw_mem).differentiableAt
      have hre1 : 1 + (slitOmega R z).re / R > 0 := by
        have := slitOmega_re_pos hR hz_slit
        positivity
      have hbase_mem : 1 + slitOmega R z / (R : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        left
        simpa [Complex.div_ofReal_re] using hre1
      have hpow_diff : DifferentiableAt ℂ
          (fun w => (1 + slitOmega R w / (R : ℂ)) ^ ((-η : ℝ) : ℂ)) z := by
        have hb : DifferentiableAt ℂ (fun w => 1 + slitOmega R w / (R : ℂ)) z :=
          (hω_diff.div_const _).const_add 1
        exact (hb.hasFDerivAt.cpow (hasFDerivAt_const _ _) hbase_mem).differentiableAt
      have hexp_diff : DifferentiableAt ℂ (fun w => Complex.exp (-(a : ℂ) * slitOmega R w)) z :=
        (hω_diff.const_mul _).cexp
      exact ((hd z).mul hexp_diff).mul hpow_diff
    have hG_dc : DiffContOnCl ℂ G U :=
      DifferentiableOn.diffContOnCl fun z hz => (hG_diff z hz).differentiableWithinAt
    have hx₀_mem : (x₀ : ℂ) ∈ U := by
      refine ⟨?_, fun hF => ?_⟩
      · simpa [Metric.mem_ball, Complex.norm_real] using hx₀_lt.trans hRbig_gt
      · have h2 := hF.2
        simp only [Complex.ofReal_re] at h2
        linarith
    have hfront : ∀ w ∈ frontier U, ‖G w‖ ≤ D + ε := by
      intro w hw
      have hw_cl : w ∈ closure U := hw.1
      have hw_slit := hcl_slit w hw_cl
      have hw_clB : w ∈ Metric.closedBall (0 : ℂ) R_big :=
        closure_minimal (sdiff_subset.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall hw_cl
      have hω_re_pos : 0 < (slitOmega R w).re := slitOmega_re_pos hR hw_slit
      have h1_re : 1 < (1 + slitOmega R w / (R : ℂ)).re := by
        have : (slitOmega R w / (R : ℂ)).re = (slitOmega R w).re / R := by simp
        simp only [Complex.add_re, Complex.one_re, this]
        linarith [div_pos hω_re_pos hR]
      have h1_norm_gt : 1 < ‖1 + slitOmega R w / (R : ℂ)‖ :=
        h1_re.trans_le (Complex.re_le_norm _)
      have h1_ne : 1 + slitOmega R w / (R : ℂ) ≠ 0 := by
        intro h0
        have h0n : ‖1 + slitOmega R w / (R : ℂ)‖ = 0 := by rw [h0, norm_zero]
        linarith
      have hexp_le : ‖Complex.exp (-(a : ℂ) * slitOmega R w)‖ ≤ 1 := by
        rw [Complex.norm_exp, Complex.mul_re]
        simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
          neg_zero, zero_mul, sub_zero, Real.exp_le_one_iff]
        nlinarith [ha, hω_re_pos]
      have hpow_le : ‖(1 + slitOmega R w / (R : ℂ)) ^ ((-η : ℝ) : ℂ)‖ ≤ 1 := by
        rw [norm_cpow_ofReal_neg h1_ne η]
        exact Real.rpow_le_one_of_one_le_of_nonpos h1_norm_gt.le (by linarith)
      have hfront_cases : w ∈ frontier (Metric.ball (0 : ℂ) R_big) ∨ w ∈ frontier F := by
        by_cases hw_intA : w ∈ interior (Metric.ball (0 : ℂ) R_big)
        · right
          refine ⟨?_, fun hw_intF => ?_⟩
          · by_contra hw_nclF
            have hmem_int : w ∈ interior (Metric.ball (0 : ℂ) R_big) ∩ (closure F)ᶜ :=
              ⟨hw_intA, hw_nclF⟩
            have hopen : IsOpen (interior (Metric.ball (0 : ℂ) R_big) ∩ (closure F)ᶜ) :=
              isOpen_interior.inter isClosed_closure.isOpen_compl
            have hsub_U : interior (Metric.ball (0 : ℂ) R_big) ∩ (closure F)ᶜ ⊆ U :=
              fun y hy => ⟨interior_subset hy.1, fun hyF => hy.2 (subset_closure hyF)⟩
            exact hw.2 (interior_maximal hsub_U hopen hmem_int)
          · have hdisj_U : Disjoint (interior F) U :=
              Set.disjoint_iff.mpr fun y hy => hy.2.2 (interior_subset hy.1)
            exact (hdisj_U.closure_right isOpen_interior).notMem_of_mem_left hw_intF hw_cl
        · left
          exact ⟨(closure_mono sdiff_subset) hw_cl, hw_intA⟩
      rcases hfront_cases with hw_sph | hw_F
      · have hw_norm : ‖w‖ = R_big := by
          rw [frontier_ball (0 : ℂ) (by positivity : R_big ≠ 0), Metric.mem_sphere, dist_zero_right] at hw_sph
          exact hw_sph
        have hω_ge : R * (M_val + 1) ≤ ‖slitOmega R w‖ := by
          have hsq : R ^ 2 * (M_val + 1) ^ 2 ≤ R_big ^ 2 - R ^ 2 := by
            dsimp [R_big]
            nlinarith [hM_ge2, sq_nonneg R]
          calc R * (M_val + 1)
              = Real.sqrt (R ^ 2 * (M_val + 1) ^ 2) := by
                  rw [← mul_pow, Real.sqrt_sq (by positivity)]
            _ ≤ Real.sqrt (R_big ^ 2 - R ^ 2) := Real.sqrt_le_sqrt hsq
            _ ≤ ‖slitOmega R w‖ := by
                  rw [← hw_norm]
                  exact norm_slitOmega_ge hR hw_slit
        have h1_ge : M_val ≤ ‖1 + slitOmega R w / (R : ℂ)‖ := by
          have hsub : ‖slitOmega R w‖ / R - 1 ≤ ‖1 + slitOmega R w / (R : ℂ)‖ := by
            have := norm_sub_norm_le (slitOmega R w / (R : ℂ)) (-1 : ℂ)
            simp only [norm_neg, norm_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hR, sub_neg_eq_add, add_comm] at this ⊢
            exact this
          have hdiv : M_val + 1 ≤ ‖slitOmega R w‖ / R := (le_div_iff₀ hR).mpr (by linarith)
          linarith
        have hpow_small : ‖(1 + slitOmega R w / (R : ℂ)) ^ ((-η : ℝ) : ℂ)‖ ≤ (D + ε) / (M₀ + 1) := by
          rw [norm_cpow_ofReal_neg h1_ne η]
          have hge_pow : ((M₀ + 1) / (D + ε)) ^ (1 / η) ≤ ‖1 + slitOmega R w / (R : ℂ)‖ :=
            (le_max_right _ _).trans h1_ge
          have hle_inv := Real.rpow_le_rpow (by positivity) hge_pow (by positivity : 0 ≤ η)
          have hpow_cancel : (((M₀ + 1) / (D + ε)) ^ (1 / η)) ^ η = (M₀ + 1) / (D + ε) := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hη.ne', Real.rpow_one]
          rw [hpow_cancel] at hle_inv
          rw [Real.rpow_neg (by positivity)]
          calc (‖1 + slitOmega R w / (R : ℂ)‖ ^ η)⁻¹
              ≤ ((M₀ + 1) / (D + ε))⁻¹ := inv_anti₀ (by positivity) hle_inv
            _ = (D + ε) / (M₀ + 1) := inv_div _ _
        have hprod_bound : ‖h w * Complex.exp (-(a : ℂ) * slitOmega R w)‖ ≤ M₀ := by
          rw [norm_mul, Complex.norm_exp, Complex.mul_re]
          simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
            neg_zero, zero_mul, sub_zero]
          have h_ab : |w.im| ≤ (slitOmega R w).re := abs_im_le_slitOmega_re hR hw_slit
          have hexp_comb : Real.exp (a * |w.im|) * Real.exp (-a * (slitOmega R w).re) ≤ 1 := by
            rw [← Real.exp_add, Real.exp_le_one_iff]
            nlinarith
          calc ‖h w‖ * Real.exp (-a * (slitOmega R w).re)
              ≤ (M₀ * Real.exp (a * |w.im|)) * Real.exp (-a * (slitOmega R w).re) := by
                  gcongr; exact hbound w
            _ = M₀ * (Real.exp (a * |w.im|) * Real.exp (-a * (slitOmega R w).re)) := by ring
            _ ≤ M₀ * 1 := by gcongr
            _ = M₀ := mul_one _
        calc ‖G w‖
            = ‖h w * Complex.exp (-(a : ℂ) * slitOmega R w)‖ *
                ‖(1 + slitOmega R w / (R : ℂ)) ^ ((-η : ℝ) : ℂ)‖ := norm_mul _ _
          _ ≤ M₀ * ((D + ε) / (M₀ + 1)) := by gcongr
          _ ≤ (M₀ + 1) * ((D + ε) / (M₀ + 1)) := by gcongr; linarith
          _ = D + ε := by field_simp
      · have hw_memF : w ∈ F := hF_closed.frontier_subset hw_F
        have hw_clB1 : w ∈ Metric.closedBall (0 : ℂ) (R_big + 1) :=
          Metric.closedBall_subset_closedBall (by linarith) hw_clB
        have h_approx : ∃ v : ℂ, v ∈ Metric.closedBall (0 : ℂ) (R_big + 1) ∧
            ‖w - v‖ < δ₀ ∧ ‖h v‖ ≤ D := by
          by_cases hreR : R ≤ |w.re|
          · refine ⟨(w.re : ℂ), ?_, ?_, hslit w.re hreR⟩
            · simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
              have := Complex.abs_re_le_norm w
              have := Metric.mem_closedBall.mp hw_clB
              rw [dist_zero_right] at this
              linarith
            · have hdiff : w - (w.re : ℂ) = w.im * Complex.I := Complex.ext (by simp) (by simp)
              rw [hdiff, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
              exact hw_memF.1.trans_lt (by linarith)
          · push Not at hreR
            let vR : ℝ := if 0 ≤ w.re then R else -R
            have hvR_abs : |vR| = R := by
              dsimp [vR]; split_ifs <;> simp [abs_of_pos hR]
            refine ⟨(vR : ℂ), ?_, ?_, hslit vR hvR_abs.symm.le⟩
            · simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
                hvR_abs]
              linarith
            · have hre_dist : |w.re - vR| ≤ δ := by
                have h_re_ge : R - δ ≤ |w.re| := hw_memF.2
                dsimp [vR]
                split_ifs with h0
                · rw [abs_of_nonpos (by linarith [abs_of_nonneg h0 ▸ hreR])]; linarith [abs_of_nonneg h0]
                · push Not at h0
                  rw [abs_of_nonneg (by linarith [abs_of_neg h0 ▸ hreR])]; linarith [abs_of_neg h0]
              have htri : ‖w - (vR : ℂ)‖ ≤ |w.re - vR| + |w.im| := by
                calc ‖w - (vR : ℂ)‖
                    ≤ |(w - (vR : ℂ)).re| + |(w - (vR : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
                  _ = |w.re - vR| + |w.im| := by simp
              have hsum_le : |w.re - vR| + |w.im| ≤ δ + δ := add_le_add hre_dist hw_memF.1
              linarith
        obtain ⟨v, hv_mem, hv_dist, hv_h⟩ := h_approx
        have h_diff_h : ‖h w‖ ≤ ‖h v‖ + ε := by
          have := hδ₀ w hw_clB1 v hv_mem (by simpa [dist_eq_norm] using hv_dist)
          rw [dist_eq_norm] at this
          have := norm_sub_norm_le (h w) (h v)
          linarith
        have hw_h : ‖h w‖ ≤ D + ε := by linarith
        calc ‖G w‖
            = ‖h w‖ * ‖Complex.exp (-(a : ℂ) * slitOmega R w)‖ *
                ‖(1 + slitOmega R w / (R : ℂ)) ^ ((-η : ℝ) : ℂ)‖ := by
                  rw [norm_mul, norm_mul]
          _ ≤ (D + ε) * 1 * 1 := by gcongr
          _ = D + ε := by ring
    obtain ⟨w_max, hw_front, hw_isMax⟩ :=
      Complex.exists_mem_frontier_isMaxOn_norm hU_bdd ⟨(x₀ : ℂ), hx₀_mem⟩ hG_dc
    have hGx₀ : ‖G (x₀ : ℂ)‖ ≤ D + ε :=
      (isMaxOn_iff.mp hw_isMax _ (subset_closure hx₀_mem)).trans (hfront w_max hw_front)
    have hG_eq : ‖G (x₀ : ℂ)‖ =
        ‖h (x₀ : ℂ)‖ * Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) *
          (1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R) ^ (-η) := by
      have hω := slitOmega_ofReal hx₀_lt
      have hexp_eq : ‖Complex.exp (-(a : ℂ) * slitOmega R (x₀ : ℂ))‖ =
          Real.exp (-a * Real.sqrt (R ^ 2 - x₀ ^ 2)) := by
        rw [hω, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
          Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
      have h1_pos : 0 < 1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R := by positivity
      have h1_eq : 1 + slitOmega R (x₀ : ℂ) / (R : ℂ) =
          ((1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R : ℝ) : ℂ) := by
        rw [hω]; push_cast; rfl
      have h1_ne : ((1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h1_pos.ne'
      have hpow_eq : ‖(1 + slitOmega R (x₀ : ℂ) / (R : ℂ)) ^ ((-η : ℝ) : ℂ)‖ =
          (1 + Real.sqrt (R ^ 2 - x₀ ^ 2) / R) ^ (-η) := by
        rw [h1_eq, norm_cpow_ofReal_neg h1_ne η, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos h1_pos]
      dsimp [G]
      rw [norm_mul, norm_mul, hexp_eq, hpow_eq]
    exact hG_eq ▸ hGx₀

/-- info: 'FormalResearch.ModularBootstrap.Integrality.slit_plane_max_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slit_plane_max_mod

end FormalResearch.ModularBootstrap.Integrality
