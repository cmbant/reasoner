module

public import FormalResearch.CohnElkies.PieceCRegularity
public import FormalResearch.CohnElkies.DualPhaseAndO3

/-!
# Uniform `C²` bounds for `H_c` (Piece C, item 3)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, Piece C item 3: `|H_c| + |H_c'| + |H_c''| ≤ C`
on `[-1, 1]`, uniformly in `c ≥ 2`, `δ₀ ∈ (0, 4]`.

Here `pcAmp_bd2` (all `v`) and `pcH_bd2` (`|v| ≤ 1`) bound `g` and `H_c` with `C²` norms independent of `c ≥ 2`, `δ₀ ∈ (0,4]`, and
`exists_uniform_bounds_chi_pcH` gives the `M` of `pieceC_main_term` (hypotheses `hφ`, `b0`-`b2`) for `φ = χ₁ H_c`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.CohnElkies

/-- `f` is `C²` with the three pointwise bounds `‖f‖ ≤ B0`, `‖f'‖ ≤ B1`, `‖f''‖ ≤ B2` on `S`. -/
def Bd2 (S : Set ℝ) (f : ℝ → ℂ) (B0 B1 B2 : ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ v ∈ S, ‖f v‖ ≤ B0 ∧ ‖deriv f v‖ ≤ B1 ∧ ‖deriv (deriv f) v‖ ≤ B2

lemma deriv_mul_of_contDiff {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (v : ℝ) :
    deriv (fun x => f x * g x) v = deriv f v * g v + f v * deriv g v :=
  deriv_mul (hf.differentiable (by norm_num) v) (hg.differentiable (by norm_num) v)

lemma deriv2_mul_of_contDiff {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (v : ℝ) :
    deriv (deriv (fun x => f x * g x)) v =
      deriv (deriv f) v * g v + 2 * (deriv f v * deriv g v) + f v * deriv (deriv g) v := by
  have h1 : deriv (fun x => f x * g x) = fun x => deriv f x * g x + f x * deriv g x :=
    funext fun x => deriv_mul_of_contDiff hf hg x
  have hdf : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hf) |>.2.2
  have hdg : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hg) |>.2.2
  rw [h1]
  have a1 := (hdf.differentiable one_ne_zero v)
  have a2 := (hg.differentiable (by norm_num) v)
  have a3 := (hf.differentiable (by norm_num) v)
  have a4 := (hdg.differentiable one_ne_zero v)
  have := ((a1.hasDerivAt.mul a2.hasDerivAt).add (a3.hasDerivAt.mul a4.hasDerivAt)).deriv
  refine this.trans ?_
  ring

theorem Bd2.mul {S : Set ℝ} {f g : ℝ → ℂ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : Bd2 S f a0 a1 a2) (hg : Bd2 S g b0 b1 b2) :
    Bd2 S (fun x => f x * g x) (a0 * b0) (a1 * b0 + a0 * b1) (a2 * b0 + 2 * (a1 * b1) + a0 * b2) := by
  refine ⟨hf.1.mul hg.1, fun v hv => ?_⟩
  obtain ⟨f0, f1, f2⟩ := hf.2 v hv
  obtain ⟨g0, g1, g2⟩ := hg.2 v hv
  have n0 := norm_nonneg (f v); have n1 := norm_nonneg (deriv f v); have n2 := norm_nonneg (deriv (deriv f) v)
  have m0 := norm_nonneg (g v); have m1 := norm_nonneg (deriv g v); have m2 := norm_nonneg (deriv (deriv g) v)
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul]; exact mul_le_mul f0 g0 m0 (n0.trans f0)
  · rw [deriv_mul_of_contDiff hf.1 hg.1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul f1 g0 m0 (n1.trans f1)) (mul_le_mul f0 g1 m1 (n0.trans f0))
  · rw [deriv2_mul_of_contDiff hf.1 hg.1]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have := mul_le_mul f2 g0 m0 (n2.trans f2)
    have := mul_le_mul f1 g1 m1 (n1.trans f1)
    have := mul_le_mul f0 g2 m2 (n0.trans f0)
    nlinarith

lemma deriv_cexp_of_contDiff {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) (v : ℝ) :
    deriv (fun x => Complex.exp (h x)) v = Complex.exp (h v) * deriv h v :=
  (hh.differentiable (by norm_num) v).hasDerivAt.cexp.deriv

lemma deriv2_cexp_of_contDiff {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) (v : ℝ) :
    deriv (deriv (fun x => Complex.exp (h x))) v = Complex.exp (h v) * (deriv h v ^ 2 + deriv (deriv h) v) := by
  have h1 : deriv (fun x => Complex.exp (h x)) = fun x => Complex.exp (h x) * deriv h x :=
    funext fun x => deriv_cexp_of_contDiff hh x
  have hdh : ContDiff ℝ 1 (deriv h) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hh) |>.2.2
  have a1 := (hh.differentiable (by norm_num) v)
  have a2 := hdh.differentiable one_ne_zero v
  rw [h1]
  have := (a1.hasDerivAt.cexp.mul a2.hasDerivAt).deriv
  refine this.trans ?_
  ring

theorem Bd2.cexp {S : Set ℝ} {h : ℝ → ℂ} {h1 h2 E : ℝ} (hh : ContDiff ℝ 2 h) (hE : ∀ v ∈ S, ‖Complex.exp (h v)‖ ≤ E)
    (b1 : ∀ v ∈ S, ‖deriv h v‖ ≤ h1) (b2 : ∀ v ∈ S, ‖deriv (deriv h) v‖ ≤ h2) :
    Bd2 S (fun x => Complex.exp (h x)) E (E * h1) (E * (h1 ^ 2 + h2)) := by
  refine ⟨Complex.contDiff_exp.comp hh, fun v hv => ⟨hE v hv, ?_, ?_⟩⟩
  · rw [deriv_cexp_of_contDiff hh, norm_mul]
    exact mul_le_mul (hE v hv) (b1 v hv) (norm_nonneg _) ((norm_nonneg _).trans (hE v hv))
  · rw [deriv2_cexp_of_contDiff hh, norm_mul]
    refine mul_le_mul (hE v hv) ((norm_add_le _ _).trans (add_le_add ?_ (b2 v hv))) (norm_nonneg _) ((norm_nonneg _).trans (hE v hv))
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (b1 v hv) 2

/-- Derivative identity `h_th(πτ/2) = Φ'(τ; 0) + π²τ²/12`. -/
lemma ceHth_eq_edgePhiDeriv_zero (τ : ℝ) :
    ceHth (Real.pi * τ / 2) = edgePhiDeriv 0 τ + Real.pi ^ 2 * τ ^ 2 / 12 := by
  have h1 := hasDerivAt_edgePhi 0 τ
  have hf : edgePhi 0 = fun τ => 0 * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ := funext (edgePhi_eq_cubic_add_ceHth 0)
  have h2 : HasDerivAt (fun τ : ℝ => 0 * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ)
      (0 * 1 - Real.pi ^ 2 / 36 * (3 * τ ^ 2) + ceHth (Real.pi * τ / 2)) τ :=
    (((hasDerivAt_id τ).const_mul 0).sub (((hasDerivAt_pow 3 τ).const_mul (Real.pi ^ 2 / 36)))).add (hasDerivAt_edgeR τ)
  rw [← hf] at h2
  have := h1.unique h2
  linarith

/-- The remainder part `S(v) = c R(εv)` of the phase. -/
noncomputable def pcS (c v : ℝ) : ℝ := c * edgeR (liftEps c * v)

lemma hasDerivAt_pcS {c : ℝ} (_hc : 0 < c) (v : ℝ) :
    HasDerivAt (pcS c) (c * liftEps c * ceHth (Real.pi * (liftEps c * v) / 2)) v := by
  have := ((hasDerivAt_edgeR (liftEps c * v)).comp v ((hasDerivAt_id v).const_mul (liftEps c))).const_mul c
  exact this.congr_deriv (by ring)

lemma hasDerivAt_deriv_pcS {c : ℝ} (hc : 0 < c) (v : ℝ) :
    HasDerivAt (deriv (pcS c)) (c * liftEps c ^ 2 * edgePhiDeriv2 (liftEps c * v) + Real.pi ^ 2 * v / 6) v := by
  have h3 := liftEps_cube hc
  have hd : deriv (pcS c) = fun v => c * liftEps c * (edgePhiDeriv 0 (liftEps c * v) + Real.pi ^ 2 * (liftEps c * v) ^ 2 / 12) :=
    funext fun v => by rw [(hasDerivAt_pcS hc v).deriv, ceHth_eq_edgePhiDeriv_zero]
  rw [hd]
  have h := (((hasDerivAt_edgePhiDeriv 0 (liftEps c * v)).comp v ((hasDerivAt_id v).const_mul (liftEps c))).add
    ((((hasDerivAt_id v).const_mul (liftEps c)).pow 2).const_mul (Real.pi ^ 2) |>.div_const 12)).const_mul (c * liftEps c)
  refine h.congr_deriv ?_
  simp only [id, Nat.cast_ofNat]
  have : c * liftEps c ^ 3 = 1 := h3
  linear_combination (Real.pi ^ 2 * v / 6) * this

lemma pcS_contDiff (c : ℝ) : ContDiff ℝ 2 (pcS c) :=
  contDiff_const.mul ((edgeR_contDiff.of_le (by norm_num)).comp (contDiff_const.mul contDiff_id))

lemma pcS_deriv_bounds {c : ℝ} (hc : 0 < c) {v : ℝ} (hv : |v| ≤ 1) :
    |deriv (pcS c) v| ≤ Real.pi ^ 2 / 12 ∧ |deriv (deriv (pcS c)) v| ≤ Real.pi ^ 2 / 3 := by
  have hε := liftEps_pos hc
  have h3 := liftEps_cube hc
  constructor
  · rw [(hasDerivAt_pcS hc v).deriv, abs_of_nonneg (mul_nonneg (mul_nonneg hc.le hε.le) (ceHth_nonneg _))]
    calc c * liftEps c * ceHth (Real.pi * (liftEps c * v) / 2)
        ≤ c * liftEps c * ((Real.pi * (liftEps c * v) / 2) ^ 2 / 3) :=
          mul_le_mul_of_nonneg_left (ceHth_le_sq_div_three _) (mul_nonneg hc.le hε.le)
      _ = (c * liftEps c ^ 3) * (Real.pi ^ 2 * v ^ 2 / 12) := by ring
      _ ≤ Real.pi ^ 2 / 12 := by
          rw [h3, one_mul]
          have : v ^ 2 ≤ 1 := by nlinarith [abs_nonneg v, sq_abs v]
          have hp : 0 < Real.pi ^ 2 := by positivity
          nlinarith
  · rw [(hasDerivAt_deriv_pcS hc v).deriv]
    have hv1 : |v| ≤ 1 := hv
    have hΦ : |edgePhiDeriv2 (liftEps c * v)| ≤ Real.pi ^ 2 / 6 * (liftEps c * |v|) := by
      by_cases hτ : liftEps c * v = 0
      · rw [hτ]; simp [edgePhiDeriv2]; positivity
      · have := (edgePhiDeriv2_abs_le hτ).trans (min_le_left _ _)
        rwa [abs_mul, abs_of_pos hε] at this
    calc |c * liftEps c ^ 2 * edgePhiDeriv2 (liftEps c * v) + Real.pi ^ 2 * v / 6|
        ≤ |c * liftEps c ^ 2 * edgePhiDeriv2 (liftEps c * v)| + |Real.pi ^ 2 * v / 6| := abs_add_le _ _
      _ ≤ Real.pi ^ 2 / 6 * |v| + Real.pi ^ 2 / 6 * |v| := by
          refine add_le_add ?_ ?_
          · rw [abs_mul, abs_of_pos (by positivity : 0 < c * liftEps c ^ 2)]
            calc c * liftEps c ^ 2 * |edgePhiDeriv2 (liftEps c * v)| ≤ c * liftEps c ^ 2 * (Real.pi ^ 2 / 6 * (liftEps c * |v|)) :=
                  mul_le_mul_of_nonneg_left hΦ (by positivity)
              _ = (c * liftEps c ^ 3) * (Real.pi ^ 2 / 6 * |v|) := by ring
              _ = _ := by rw [h3, one_mul]
          · rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < Real.pi ^ 2)]; norm_num; ring_nf; rfl
      _ ≤ Real.pi ^ 2 / 3 := by
          have hp : 0 < Real.pi ^ 2 := by positivity
          nlinarith

lemma bd2_edgeFactor {c : ℝ} (hc : 0 < c) :
    Bd2 (Icc (-1) 1) (fun v : ℝ => Complex.exp (Complex.I * ((c * edgeR (liftEps c * v) : ℝ) : ℂ))) 1 (1 * (Real.pi ^ 2 / 12))
      (1 * ((Real.pi ^ 2 / 12) ^ 2 + Real.pi ^ 2 / 3)) := by
  have hcd : ContDiff ℝ 2 (fun v : ℝ => Complex.I * ((pcS c v : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (pcS_contDiff c))
  have hd : deriv (fun v : ℝ => Complex.I * ((pcS c v : ℝ) : ℂ)) = fun v => Complex.I * ((deriv (pcS c) v : ℝ) : ℂ) :=
    funext fun v => (((hasDerivAt_pcS hc v).ofReal_comp).const_mul Complex.I).deriv.trans (by rw [(hasDerivAt_pcS hc v).deriv])
  have hd2 : ∀ v, deriv (deriv (fun v : ℝ => Complex.I * ((pcS c v : ℝ) : ℂ))) v = Complex.I * ((deriv (deriv (pcS c)) v : ℝ) : ℂ) := fun v => by
    rw [hd]; exact (((hasDerivAt_deriv_pcS hc v).ofReal_comp).const_mul Complex.I).deriv.trans (by rw [(hasDerivAt_deriv_pcS hc v).deriv])
  refine Bd2.cexp (h := fun v : ℝ => Complex.I * ((pcS c v : ℝ) : ℂ)) hcd (fun v _ => ?_) (fun v hv => ?_) (fun v hv => ?_) <;> (try have hv := abs_le.mpr (show -1 ≤ v ∧ v ≤ 1 from hv))
  · rw [Complex.norm_exp]; simp
  · rw [hd]; simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact (pcS_deriv_bounds hc hv).1
  · rw [hd2]; simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact (pcS_deriv_bounds hc hv).2

lemma liftEps_le_one {c : ℝ} (hc : 1 ≤ c) : liftEps c ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)

lemma one_le_norm_one_sub (ε v : ℝ) : 1 ≤ ‖(1 - (((ε * v : ℝ) : ℂ) * Complex.I))‖ := by
  refine le_trans ?_ (Complex.abs_re_le_norm _); simp

lemma slit_one_sub (ε v : ℝ) : (1 - (((ε * v : ℝ) : ℂ) * Complex.I)) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))

lemma bd2_sqrtFactor {c : ℝ} (hc : 1 ≤ c) :
    Bd2 univ (fun v : ℝ => (1 - (((liftEps c * v : ℝ) : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ))) 1 (1 * (1 / 2))
      (1 * ((1 / 2) ^ 2 + 1 / 2)) := by
  have hε : 0 < liftEps c := liftEps_pos (by linarith)
  have hε1 := liftEps_le_one hc
  set z : ℝ → ℂ := fun v => 1 - (((liftEps c * v : ℝ) : ℂ) * Complex.I) with hz
  have hzd : ∀ v, HasDerivAt z (-(liftEps c : ℂ) * Complex.I) v := fun v => by
    have := ((((hasDerivAt_id v).const_mul (liftEps c)).ofReal_comp).mul_const Complex.I).const_sub 1
    exact this.congr_deriv (by simp)
  set h : ℝ → ℂ := fun v => Complex.log (z v) * (-(1 / 2 : ℂ)) with hh
  have hfun : (fun v : ℝ => (z v) ^ (-(1 / 2 : ℂ))) = fun v => Complex.exp (h v) := funext fun v =>
    Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (slit_one_sub (liftEps c) v)) _
  have hhd : ∀ v, HasDerivAt h ((liftEps c : ℂ) * Complex.I / 2 / z v) v := fun v => by
    have := ((hzd v).clog_real (slit_one_sub (liftEps c) v)).mul_const (-(1 / 2 : ℂ))
    refine this.congr_deriv ?_
    have hz0 : z v ≠ 0 := Complex.slitPlane_ne_zero (slit_one_sub (liftEps c) v)
    field_simp
  have hderiv : deriv h = fun v => (liftEps c : ℂ) * Complex.I / 2 / z v := funext fun v => (hhd v).deriv
  have hzv : ∀ v, 1 ≤ ‖z v‖ := fun v => one_le_norm_one_sub (liftEps c) v
  have hz0 : ∀ v, z v ≠ 0 := fun v => Complex.slitPlane_ne_zero (slit_one_sub (liftEps c) v)
  have hhd2 : ∀ v, HasDerivAt (deriv h) (-((liftEps c : ℂ) ^ 2 / 2 / z v ^ 2)) v := fun v => by
    rw [hderiv]
    have := (((hasDerivAt_const v ((liftEps c : ℂ) * Complex.I / 2))).div (hzd v) (hz0 v))
    refine this.congr_deriv ?_
    field_simp
    simp only [Complex.I_sq]; ring
  have hcd : ContDiff ℝ 2 h := by
    refine contDiff_iff_contDiffAt.mpr fun v => ?_
    have hzc : ContDiff ℝ 2 z := contDiff_const.sub ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)
    exact ((Complex.contDiffAt_log (n := 2) (slit_one_sub (liftEps c) v)).restrict_scalars ℝ).comp v hzc.contDiffAt |>.mul contDiffAt_const
  have hd1 : ∀ v : ℝ, ‖deriv h v‖ ≤ 1 / 2 := fun v => by
    rw [hderiv]; dsimp only
    rw [norm_div, norm_div, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_pos hε]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this, div_le_div_iff₀ (by have := hzv v; positivity) (by norm_num)]
    nlinarith [hzv v]
  have hd2 : ∀ v : ℝ, ‖deriv (deriv h) v‖ ≤ 1 / 2 := fun v => by
    rw [(hhd2 v).deriv, norm_neg, norm_div, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_pow]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    have h1 := hzv v
    have h2 : 1 ≤ ‖z v‖ ^ 2 := one_le_pow₀ h1
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (liftEps c), mul_le_mul hε1 hε1 hε.le zero_le_one]
  rw [hfun]
  refine Bd2.cexp hcd (fun v _ => ?_) (fun v _ => hd1 v) (fun v _ => hd2 v)
  rw [Complex.norm_exp]
  have : (h v).re ≤ 0 := by
    simp only [hh, Complex.mul_re, Complex.log_re, Complex.log_im]
    have : 0 ≤ Real.log ‖z v‖ := Real.log_nonneg (hzv v)
    simp; linarith
  exact Real.exp_le_one_iff.mpr this

lemma binetDiff_differentiableOn {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (FormalResearch.Asymptotics.binetDiff c) {ζ : ℂ | ζ.re < 1} := by
  unfold FormalResearch.Asymptotics.binetDiff
  refine DifferentiableOn.sub_const ?_ _
  refine FormalResearch.Asymptotics.binetRem_differentiableOn.comp (by fun_prop) (fun ζ hζ => ?_)
  simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, zero_mul, sub_zero]
  have : ζ.re < 1 := hζ
  nlinarith

lemma bd2_binetFactor {c : ℝ} (hc : 2 ≤ c) :
    Bd2 univ (fun v : ℝ => Complex.exp (FormalResearch.Asymptotics.binetDiff c (((liftEps c * v : ℝ) : ℂ) * Complex.I)))
      (Real.exp (1 / 12)) (Real.exp (1 / 12) * (1 / 24)) (Real.exp (1 / 12) * ((1 / 24) ^ 2 + 1 / 12)) := by
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hε1 := liftEps_le_one (by linarith : 1 ≤ c)
  set B := FormalResearch.Asymptotics.binetDiff c with hB
  have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hBd : DifferentiableOn ℂ B {ζ : ℂ | ζ.re < 1} := binetDiff_differentiableOn hc0
  have hBd1 : DifferentiableOn ℂ (deriv B) {ζ : ℂ | ζ.re < 1} := hBd.deriv hopen
  have hBd2 : DifferentiableOn ℂ (deriv (deriv B)) {ζ : ℂ | ζ.re < 1} := hBd1.deriv hopen
  set ζ : ℝ → ℂ := fun v => ((liftEps c * v : ℝ) : ℂ) * Complex.I with hζ
  have hζd : ∀ v, HasDerivAt ζ ((liftEps c : ℂ) * Complex.I) v := fun v => by
    have := (((hasDerivAt_id v).const_mul (liftEps c)).ofReal_comp).mul_const Complex.I
    exact this.congr_deriv (by simp)
  have hζre : ∀ v, (ζ v).re < 1 := fun v => by simp [hζ]
  have hat : ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f {ζ : ℂ | ζ.re < 1} → ∀ v, DifferentiableAt ℂ f (ζ v) := fun f hf v =>
    (hf (ζ v) (hζre v)).differentiableAt (hopen.mem_nhds (hζre v))
  set h : ℝ → ℂ := fun v => B (ζ v) with hh
  have hhd : ∀ v, HasDerivAt h ((liftEps c : ℂ) * Complex.I * deriv B (ζ v)) v := fun v => by
    have := ((hat B hBd v).hasDerivAt).scomp v (hζd v)
    exact this.congr_deriv (by rw [smul_eq_mul])
  have hderiv : deriv h = fun v => (liftEps c : ℂ) * Complex.I * deriv B (ζ v) := funext fun v => (hhd v).deriv
  have hhd2 : ∀ v, HasDerivAt (deriv h) ((liftEps c : ℂ) * Complex.I * ((liftEps c : ℂ) * Complex.I * deriv (deriv B) (ζ v))) v := fun v => by
    rw [hderiv]
    have := ((hat (deriv B) hBd1 v).hasDerivAt).scomp v (hζd v)
    have := this.const_mul ((liftEps c : ℂ) * Complex.I)
    exact this.congr_deriv (by rw [smul_eq_mul])
  have hcd : ContDiff ℝ 2 h := by
    have hb : ContDiffOn ℂ 2 FormalResearch.Asymptotics.binetRem {w : ℂ | 0 < w.re} :=
      FormalResearch.Asymptotics.binetRem_differentiableOn.contDiffOn (isOpen_lt continuous_const Complex.continuous_re)
    have hb' := hb.restrict_scalars ℝ
    have hz : ContDiff ℝ 2 ζ := (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
    exact (hb'.comp_contDiff (contDiff_const.mul (contDiff_const.sub hz)) (fun v => by
      simp [hζ, hc0])).sub contDiff_const
  have hn1 : ∀ v, ‖deriv B (ζ v)‖ ≤ 1 / (12 * c) := fun v => by
    have := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc0 (ζ := ζ v) (by simp [hζ]) (r := 1) le_rfl
    simpa [iteratedDeriv_one] using this
  have hn2 : ∀ v, ‖deriv (deriv B) (ζ v)‖ ≤ 2 / (12 * c) := fun v => by
    have := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc0 (ζ := ζ v) (by simp [hζ]) (r := 2) (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this
  have hc12 : 1 / (12 * c) ≤ 1 / 24 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine Bd2.cexp hcd (fun v _ => ?_) (fun v _ => ?_) (fun v _ => ?_)
  · rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    have := FormalResearch.Asymptotics.binetDiff_norm_le_left hc0 (ζ := ζ v) (by simp [hζ])
    refine this.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · rw [hderiv]; dsimp only
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_pos hε, mul_one]
    exact (mul_le_mul hε1 (hn1 v) (norm_nonneg _) zero_le_one).trans (by linarith)
  · rw [(hhd2 v).deriv]
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_pos hε, mul_one]
    have h2 : 2 / (12 * c) ≤ 1 / 12 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hε2 : liftEps c * liftEps c ≤ 1 := by nlinarith
    calc liftEps c * (liftEps c * ‖deriv (deriv B) (ζ v)‖) = (liftEps c * liftEps c) * ‖deriv (deriv B) (ζ v)‖ := by ring
      _ ≤ 1 * (1 / 12) := mul_le_mul hε2 ((hn2 v).trans h2) (norm_nonneg _) zero_le_one
      _ = 1 / 12 := by ring

lemma bd2_multiplier (m : ℕ) : ∃ B0 B1 B2 : ℝ, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ 4 →
    Bd2 univ (fun v : ℝ => liftMultiplier δ₀ m ((v : ℂ) * Complex.I)) B0 B1 B2 := by
  obtain ⟨C0, hC0, h0⟩ := bsplineE1_imag_pow_deriv_bound m 0
  obtain ⟨C1, hC1, h1⟩ := bsplineE1_imag_pow_deriv_bound m 1
  obtain ⟨C2, hC2, h2⟩ := bsplineE1_imag_pow_deriv_bound m 2
  refine ⟨max C0 1, C1 * (4 * ceCs), C2 * (4 * ceCs) ^ 2, fun {δ₀} hδ hδ4 => ?_⟩
  have hm : (fun v : ℝ => liftMultiplier δ₀ m ((v : ℂ) * Complex.I)) =
      fun v : ℝ => bsplineE1 (Complex.I * ((ceCs * δ₀ / m : ℝ) : ℂ) * (v : ℂ)) ^ m := funext fun v => by
    unfold liftMultiplier; congr 2; ring
  rw [hm]
  have hcd : ContDiff ℝ 2 (fun v : ℝ => bsplineE1 (Complex.I * ((ceCs * δ₀ / m : ℝ) : ℂ) * (v : ℂ)) ^ m) := by
    have : ContDiff ℂ 2 bsplineE1 := contDiff_bsplineE1.of_le (by norm_cast)
    exact ((this.restrict_scalars ℝ).comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).pow m
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · refine ⟨hcd, fun v _ => ?_⟩
    simp only [pow_zero]
    have hd1 : deriv (fun _ : ℝ => (1 : ℂ)) = fun _ => 0 := by funext x; simp
    have hz : deriv (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := funext fun x => deriv_const x 0
    have hcs := ceCs_pos
    rw [hd1, hz]
    refine ⟨by simp, ?_, ?_⟩
    · simp only [norm_zero]; positivity
    · simp only [norm_zero]; positivity
  · have hβ : 0 < ceCs * δ₀ / m := by
      have h1 := ceCs_pos
      have h2 : (0 : ℝ) < m := by exact_mod_cast hmpos
      positivity
    have hβ4 : ceCs * δ₀ / m ≤ 4 * ceCs := by
      have := ceCs_pos
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
      rw [div_le_iff₀ (by linarith)]; nlinarith
    refine ⟨hcd, fun v _ => ⟨?_, ?_, ?_⟩⟩
    · have := h0 hβ v; simp only [iteratedDeriv_zero, pow_zero, mul_one] at this
      exact (this.trans (mul_le_of_le_one_right hC0.le (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg v]) (by simp)))).trans (le_max_left _ _)
    · have := h1 hβ v; rw [iteratedDeriv_one] at this
      refine this.trans ?_
      have hr : (1 + ceCs * δ₀ / m * |v|) ^ (-(m : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg v]) (by simp)
      calc C1 * (ceCs * δ₀ / m) ^ 1 * (1 + ceCs * δ₀ / m * |v|) ^ (-(m : ℝ)) ≤ C1 * (ceCs * δ₀ / m) ^ 1 * 1 :=
            mul_le_mul_of_nonneg_left hr (by positivity)
        _ ≤ C1 * (4 * ceCs) := by rw [mul_one, pow_one]; exact mul_le_mul_of_nonneg_left hβ4 hC1.le
    · have := h2 hβ v
      rw [show iteratedDeriv 2 (fun u : ℝ => bsplineE1 (Complex.I * ((ceCs * δ₀ / m : ℝ) : ℂ) * (u : ℂ)) ^ m) v =
        deriv (deriv (fun u : ℝ => bsplineE1 (Complex.I * ((ceCs * δ₀ / m : ℝ) : ℂ) * (u : ℂ)) ^ m)) v by rw [iteratedDeriv_succ, iteratedDeriv_one]] at this
      refine this.trans ?_
      have hr : (1 + ceCs * δ₀ / m * |v|) ^ (-(m : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg v]) (by simp)
      calc C2 * (ceCs * δ₀ / m) ^ 2 * (1 + ceCs * δ₀ / m * |v|) ^ (-(m : ℝ)) ≤ C2 * (ceCs * δ₀ / m) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hr (by positivity)
        _ ≤ C2 * (4 * ceCs) ^ 2 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ.le hβ4 2) hC2.le

theorem Bd2.mono {S T : Set ℝ} {f : ℝ → ℂ} {B0 B1 B2 : ℝ} (h : Bd2 S f B0 B1 B2) (hT : T ⊆ S) : Bd2 T f B0 B1 B2 :=
  ⟨h.1, fun v hv => h.2 v (hT hv)⟩

/-- Uniform `C²` bounds of the amplitude `g = pcAmp` on all of `ℝ`, uniform in `c ≥ 2`, `δ₀ ∈ (0, 4]`. -/
theorem pcAmp_bd2 (m : ℕ) : ∃ B0 B1 B2 : ℝ, ∀ {δ₀ c : ℝ}, 0 < δ₀ → δ₀ ≤ 4 → 2 ≤ c →
    Bd2 univ (pcAmp δ₀ m c) B0 B1 B2 := by
  obtain ⟨M0, M1, M2, hM⟩ := bd2_multiplier m
  let e := Real.exp (1 / 12)
  let sb0 := 1 * e
  let sb1 := (1 * (1 / 2)) * e + 1 * (e * (1 / 24))
  let sb2 := (1 * ((1 / 2) ^ 2 + 1 / 2)) * e + 2 * ((1 * (1 / 2)) * (e * (1 / 24))) + 1 * (e * ((1 / 24) ^ 2 + 1 / 12))
  refine ⟨sb0 * M0, sb1 * M0 + sb0 * M1, sb2 * M0 + 2 * (sb1 * M1) + sb0 * M2, fun {δ₀ c} hδ hδ4 hc => ?_⟩
  exact ((bd2_sqrtFactor (by linarith : 1 ≤ c)).mul (bd2_binetFactor hc)).mul (hM hδ hδ4)

/-- Uniform `C²` bounds of `H_c = g e^{icR(εv)}` on `[-1, 1]`. -/
theorem pcH_bd2 (m : ℕ) : ∃ B0 B1 B2 : ℝ, ∀ {δ₀ c : ℝ}, 0 < δ₀ → δ₀ ≤ 4 → 2 ≤ c →
    Bd2 (Icc (-1) 1) (pcH δ₀ m c) B0 B1 B2 := by
  obtain ⟨M0, M1, M2, hM⟩ := pcAmp_bd2 m
  refine ⟨M0 * 1, M1 * 1 + M0 * (1 * (Real.pi ^ 2 / 12)),
    M2 * 1 + 2 * (M1 * (1 * (Real.pi ^ 2 / 12))) + M0 * (1 * ((Real.pi ^ 2 / 12) ^ 2 + Real.pi ^ 2 / 3)), fun {δ₀ c} hδ hδ4 hc => ?_⟩
  exact ((hM hδ hδ4 hc).mono (subset_univ _)).mul (bd2_edgeFactor (by linarith : 0 < c))

/-- **Uniform bounds for `φ = χ₁ H_c`** (`hφ`, `b0`-`b2` of `pieceC_main_term`, with `M` independent of `c ≥ 2`, `δ₀ ∈ (0, 4]`). -/
theorem exists_uniform_bounds_chi_pcH (m : ℕ) {χ₁ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ₁) (hsupp : ∀ v : ℝ, 1 < |v| → χ₁ v = 0) :
    ∃ M : ℝ, ∀ {δ₀ c : ℝ}, 0 < δ₀ → δ₀ ≤ 4 → 2 ≤ c →
      ContDiff ℝ 2 (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v) ∧
      (∀ v, ‖(χ₁ v : ℂ) * pcH δ₀ m c v‖ ≤ M) ∧ (∀ v, ‖deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v) v‖ ≤ M) ∧
      (∀ v, ‖deriv (deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v)) v‖ ≤ M) := by
  obtain ⟨B0, B1, B2, hB⟩ := pcH_bd2 m
  -- bounds for χ₁ on [-1,1]
  have hχc : ContDiff ℝ 2 (fun v : ℝ => (χ₁ v : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hcs : HasCompactSupport χ₁ := HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun v hv => hsupp v (by
    by_contra h; exact hv ⟨(abs_le.mp (not_lt.mp h)).1, (abs_le.mp (not_lt.mp h)).2⟩)
  have hd1c : Continuous (deriv (fun v : ℝ => (χ₁ v : ℂ))) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hχc) |>.2.2.continuous
  have hd2c : Continuous (deriv (deriv (fun v : ℝ => (χ₁ v : ℂ)))) :=
    ((contDiff_succ_iff_deriv (n := 0)).mp (by simpa using ((contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hχc) |>.2.2 : ContDiff ℝ 1 (deriv fun v : ℝ => (χ₁ v : ℂ))))).2.2.continuous
  have hs0 : HasCompactSupport (fun v : ℝ => (χ₁ v : ℂ)) := hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hs1 := hs0.deriv; have hs2 := hs1.deriv
  obtain ⟨K0, hK0⟩ := hs0.exists_bound_of_continuous hχc.continuous
  obtain ⟨K1, hK1⟩ := hs1.exists_bound_of_continuous hd1c
  obtain ⟨K2, hK2⟩ := hs2.exists_bound_of_continuous hd2c
  have hχB : Bd2 univ (fun v : ℝ => (χ₁ v : ℂ)) K0 K1 K2 := ⟨hχc, fun v _ => ⟨hK0 v, hK1 v, hK2 v⟩⟩
  refine ⟨max 0 (max (K0 * B0) (max (K1 * B0 + K0 * B1) (K2 * B0 + 2 * (K1 * B1) + K0 * B2))), fun {δ₀ c} hδ hδ4 hc => ?_⟩
  set φ : ℝ → ℂ := fun v => (χ₁ v : ℂ) * pcH δ₀ m c v with hφ
  have hφc : ContDiff ℝ 2 φ := hχc.mul (contDiff_pcH δ₀ m (by linarith))
  have hprod := (hχB.mono (subset_univ (Icc (-1 : ℝ) 1))).mul (hB hδ hδ4 hc)
  have hopen : IsOpen {x : ℝ | 1 < |x|} := isOpen_lt continuous_const continuous_abs
  have hz : ∀ v : ℝ, 1 < |v| → φ v = 0 := fun v hv => by simp [hφ, hsupp v hv]
  have hzd : ∀ v : ℝ, 1 < |v| → deriv φ v = 0 := fun v hv => by
    have : φ =ᶠ[nhds v] fun _ => 0 := Filter.eventually_of_mem (hopen.mem_nhds hv) fun x hx => hz x hx
    rw [this.deriv_eq]; simp
  have hzdd : ∀ v : ℝ, 1 < |v| → deriv (deriv φ) v = 0 := fun v hv => by
    have : deriv φ =ᶠ[nhds v] fun _ => 0 := Filter.eventually_of_mem (hopen.mem_nhds hv) fun x hx => hzd x hx
    rw [this.deriv_eq]; simp
  refine ⟨hφc, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · by_cases hv : |v| ≤ 1
    · exact (hprod.2 v (abs_le.mp hv)).1.trans (le_max_of_le_right (le_max_left _ _))
    · have h0 := hz v (not_le.mp hv); simp only [hφ] at h0; rw [h0]; simp
  · by_cases hv : |v| ≤ 1
    · exact (hprod.2 v (abs_le.mp hv)).2.1.trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    · have h0 := hzd v (not_le.mp hv); simp only [hφ] at h0; rw [h0]; simp
  · by_cases hv : |v| ≤ 1
    · exact (hprod.2 v (abs_le.mp hv)).2.2.trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
    · have h0 := hzdd v (not_le.mp hv); simp only [hφ] at h0; rw [h0]; simp

/-- info: 'FormalResearch.CohnElkies.Bd2.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.Bd2.mul
/-- info: 'FormalResearch.CohnElkies.Bd2.cexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.Bd2.cexp
/-- info: 'FormalResearch.CohnElkies.pcS_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pcS_deriv_bounds
/-- info: 'FormalResearch.CohnElkies.bd2_edgeFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bd2_edgeFactor
/-- info: 'FormalResearch.CohnElkies.bd2_sqrtFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bd2_sqrtFactor
/-- info: 'FormalResearch.CohnElkies.bd2_binetFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bd2_binetFactor
/-- info: 'FormalResearch.CohnElkies.bd2_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bd2_multiplier
/-- info: 'FormalResearch.CohnElkies.pcAmp_bd2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pcAmp_bd2
/-- info: 'FormalResearch.CohnElkies.pcH_bd2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pcH_bd2
/-- info: 'FormalResearch.CohnElkies.exists_uniform_bounds_chi_pcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.exists_uniform_bounds_chi_pcH

end FormalResearch.CohnElkies
