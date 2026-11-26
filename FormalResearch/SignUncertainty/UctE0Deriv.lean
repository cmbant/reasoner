module

public import FormalResearch.SignUncertainty.UctBumpWeightedExp
public import FormalResearch.SignUncertainty.UctWExpW
public import FormalResearch.SignUncertainty.CtDualIdBinet

/-!
# Weighted expansion of the second derivative of the kernel amplitude (F2a, `uct:bump-weighted` far band)

With `K = kernelAmp c`, `h = c^{-1/2}`, `τ = h v`: `K = u e^{S}`, `u = (1-iτ)^{-1/2}`, `S = β + γ`, `β = B_c(iτ)`, `γ = i c N(τ)`, hence
`K'' = (u'' + 2 u' S' + u (S'' + S'²)) e^{S}`.  `K2 h v = h² K''(h v)` has a weak weighted expansion (`WExpW`, order `4`, on `h(1+|v|)³ ≤ 1/2`):
`h u'`, `h² u''` are `h^m ×` smooth functions of `h v`, `h γ' = i h⁻¹ ℓ(hv)` (`ℓ = ellFun`, vanishing to order two) and `h² γ'' = i ℓ'(hv)` are smooth atoms, while the
Binet parts `h β' = O(h³)`, `h² β'' = O(h⁴)` (`ct:binet-decay`) enter only through `O(x⁴)` remainders.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open FormalResearch.Asymptotics
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- `β(τ) = B_c(iτ)`. -/
noncomputable def kBeta (c τ : ℝ) : ℂ := binetDiff c (Complex.I * (τ : ℂ))

/-- `γ(τ) = i c N(τ)`. -/
noncomputable def kGamma (c τ : ℝ) : ℂ := Complex.I * ((c * ellN τ : ℝ) : ℂ)

lemma kernelAmp_eq (c τ : ℝ) :
    kernelAmp c τ = cpowI (-(1 / 2 : ℂ)) τ * Complex.exp (kBeta c τ + kGamma c τ) := by
  unfold kernelAmp kBeta kGamma
  rw [Complex.exp_add]; ring

lemma contDiff_kBeta {c : ℝ} (hc : 2 ≤ c) : ContDiff ℝ 2 (kBeta c) :=
  contDiff_real_line (F := fun τ : ℂ => binetDiff c (Complex.I * τ))
    (isOpen_lt continuous_const Complex.continuous_im) (ct_dual_id_part1.2.1 c hc) (fun τ => by simp)

lemma contDiff_kGamma (c : ℝ) : ContDiff ℝ 2 (kGamma c) := by
  have : ContDiff ℝ (⊤ : ℕ∞) (kGamma c) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_ellN_top))
  exact_mod_cast (contDiff_infty.mp this) 2

lemma deriv_kGamma (c : ℝ) : deriv (kGamma c) = fun τ => Complex.I * ((c * ellFun τ : ℝ) : ℂ) := by
  funext τ
  exact ((((hasDerivAt_ellN τ).const_mul c)).ofReal_comp.const_mul Complex.I).deriv

lemma deriv_deriv_kGamma (c : ℝ) :
    deriv (deriv (kGamma c)) = fun τ => Complex.I * ((c * deriv ellFun τ : ℝ) : ℂ) := by
  rw [deriv_kGamma]
  funext τ
  have hd : Differentiable ℝ ellFun := contDiff_ellFun.differentiable (by simp)
  exact (((hd τ).hasDerivAt.const_mul c).ofReal_comp.const_mul Complex.I).deriv

lemma cd1_of_cd2 {f : ℝ → ℂ} (h : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  have h2 : ContDiff ℝ ((1 : ℕ) + 1) f := by simpa [one_add_one_eq_two] using h
  exact ((contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h2).2.2

lemma deriv_mul_exp {u S : ℝ → ℂ} (hu : ContDiff ℝ 2 u) (hS : ContDiff ℝ 2 S) :
    deriv (fun t => u t * Complex.exp (S t)) =
      fun t => (deriv u t + u t * deriv S t) * Complex.exp (S t) := by
  funext t
  have hu1 : DifferentiableAt ℝ u t := (hu.differentiable (by norm_num)) t
  have hS1 : DifferentiableAt ℝ S t := (hS.differentiable (by norm_num)) t
  have hE : HasDerivAt (fun t => Complex.exp (S t)) (Complex.exp (S t) * deriv S t) t := hS1.hasDerivAt.cexp
  have h' : HasDerivAt (fun t => u t * Complex.exp (S t))
      (deriv u t * Complex.exp (S t) + u t * (Complex.exp (S t) * deriv S t)) t := hu1.hasDerivAt.mul hE
  rw [h'.deriv]; ring

lemma deriv2_mul_exp {u S : ℝ → ℂ} (hu : ContDiff ℝ 2 u) (hS : ContDiff ℝ 2 S) (τ : ℝ) :
    deriv (deriv (fun t => u t * Complex.exp (S t))) τ =
      (deriv (deriv u) τ + 2 * (deriv u τ * deriv S τ) + u τ * (deriv (deriv S) τ + deriv S τ ^ 2)) *
        Complex.exp (S τ) := by
  rw [deriv_mul_exp hu hS]
  have hu1 : DifferentiableAt ℝ u τ := (hu.differentiable (by norm_num)) τ
  have hS1 : DifferentiableAt ℝ S τ := (hS.differentiable (by norm_num)) τ
  have hu2 : DifferentiableAt ℝ (deriv u) τ := ((cd1_of_cd2 hu).differentiable (by norm_num)) τ
  have hS2 : DifferentiableAt ℝ (deriv S) τ := ((cd1_of_cd2 hS).differentiable (by norm_num)) τ
  have hE : HasDerivAt (fun t => Complex.exp (S t)) (Complex.exp (S τ) * deriv S τ) τ := hS1.hasDerivAt.cexp
  have hw : HasDerivAt (fun t => deriv u t + u t * deriv S t)
      (deriv (deriv u) τ + (deriv u τ * deriv S τ + u τ * deriv (deriv S) τ)) τ :=
    hu2.hasDerivAt.add (hu1.hasDerivAt.mul hS2.hasDerivAt)
  have hp : HasDerivAt (fun t => (deriv u t + u t * deriv S t) * Complex.exp (S t))
      ((deriv (deriv u) τ + (deriv u τ * deriv S τ + u τ * deriv (deriv S) τ)) * Complex.exp (S τ) +
        (deriv u τ + u τ * deriv S τ) * (Complex.exp (S τ) * deriv S τ)) τ := hw.mul hE
  rw [hp.deriv]; ring

/-- `K2 h v = h² K''(h v)` for `c = h⁻²`. -/
noncomputable def K2 (h v : ℝ) : ℂ := (h : ℂ) ^ 2 * deriv (deriv (kernelAmp ((h ^ 2)⁻¹))) (h * v)

/-- The auxiliary functions of the structural formula. -/
noncomputable def kSg (h v : ℝ) : ℂ := (((h)⁻¹ : ℝ) : ℂ) * (Complex.I * ((ellFun (h * v) : ℝ) : ℂ))
noncomputable def kDg (h v : ℝ) : ℂ := Complex.I * ((deriv ellFun (h * v) : ℝ) : ℂ)
noncomputable def kSb (h v : ℝ) : ℂ := (h : ℂ) * deriv (kBeta ((h ^ 2)⁻¹)) (h * v)
noncomputable def kDb (h v : ℝ) : ℂ := (h : ℂ) ^ 2 * deriv (deriv (kBeta ((h ^ 2)⁻¹))) (h * v)
noncomputable def kU0 (h v : ℝ) : ℂ := cpowI (-(1 / 2 : ℂ)) (h * v)
noncomputable def kU1 (h v : ℝ) : ℂ := (h : ℂ) * deriv (cpowI (-(1 / 2 : ℂ))) (h * v)
noncomputable def kU2 (h v : ℝ) : ℂ := (h : ℂ) ^ 2 * deriv (deriv (cpowI (-(1 / 2 : ℂ)))) (h * v)
noncomputable def kEx (h v : ℝ) : ℂ := Complex.exp (kBeta ((h ^ 2)⁻¹) (h * v) + kGamma ((h ^ 2)⁻¹) (h * v))

lemma K2_eq {h : ℝ} (hh : 0 < h) (hc : 2 ≤ (h ^ 2)⁻¹) (v : ℝ) :
    K2 h v = (kU2 h v + 2 * (kU1 h v * (kSb h v + kSg h v)) +
      kU0 h v * (kDb h v + kDg h v + (kSb h v + kSg h v) ^ 2)) * kEx h v := by
  set c : ℝ := (h ^ 2)⁻¹ with hcdef
  have hβ := contDiff_kBeta hc
  have hγ := contDiff_kGamma c
  have hu := contDiff_cpowI 2 (-(1 / 2 : ℂ))
  have hS : ContDiff ℝ 2 (fun t => kBeta c t + kGamma c t) := hβ.add hγ
  have hβ1 : Differentiable ℝ (kBeta c) := hβ.differentiable (by norm_num)
  have hγ1 : Differentiable ℝ (kGamma c) := hγ.differentiable (by norm_num)
  have hβ2 : Differentiable ℝ (deriv (kBeta c)) := (cd1_of_cd2 hβ).differentiable (by norm_num)
  have hγ2 : Differentiable ℝ (deriv (kGamma c)) := (cd1_of_cd2 hγ).differentiable (by norm_num)
  have hd1 : deriv (fun t => kBeta c t + kGamma c t) = fun t => deriv (kBeta c) t + deriv (kGamma c) t := by
    funext t
    exact ((hβ1 t).hasDerivAt.add (hγ1 t).hasDerivAt).deriv
  have hd2 : deriv (fun t => deriv (kBeta c) t + deriv (kGamma c) t) =
      fun t => deriv (deriv (kBeta c)) t + deriv (deriv (kGamma c)) t := by
    funext t
    exact ((hβ2 t).hasDerivAt.add (hγ2 t).hasDerivAt).deriv
  have key := deriv2_mul_exp hu hS (h * v)
  have hKf : (fun t => cpowI (-(1 / 2 : ℂ)) t * Complex.exp (kBeta c t + kGamma c t)) = kernelAmp c :=
    funext fun t => (kernelAmp_eq c t).symm
  rw [hKf, hd1, hd2] at key
  beta_reduce at key
  unfold K2 kU2 kU1 kU0 kSb kDb kSg kDg kEx
  rw [← hcdef, key]
  rw [deriv_deriv_kGamma, deriv_kGamma]
  beta_reduce
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hcC : (c : ℂ) = ((h : ℂ) ^ 2)⁻¹ := by rw [hcdef]; push_cast; ring
  push_cast
  rw [hcC]
  field_simp

/-! ### Crude Binet bounds and the expansion of `K2` -/

lemma kBeta_crude : ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 2 ≤ c → ∀ τ : ℝ,
    ‖deriv (kBeta c) τ‖ ≤ C / c ∧ ‖deriv (deriv (kBeta c)) τ‖ ≤ C / c := by
  obtain ⟨C1, h1⟩ := ct_dual_id_part1.1 1 le_rfl
  obtain ⟨C2, h2⟩ := ct_dual_id_part1.1 2 (by norm_num)
  refine ⟨|C1| + |C2|, by positivity, fun c hc τ => ⟨?_, ?_⟩⟩
  · have := h1 c hc τ
    rw [iteratedDeriv_one] at this
    refine this.trans ?_
    have hx : 1 ≤ (1 + |τ|) ^ (1 + 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
    have hc0 : 0 < c := by linarith
    calc C1 / (c * (1 + |τ|) ^ (1 + 1)) ≤ |C1| / (c * (1 + |τ|) ^ (1 + 1)) := by
          gcongr; exact le_abs_self _
      _ ≤ |C1| / c := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) hc0; nlinarith
      _ ≤ (|C1| + |C2|) / c := by gcongr; linarith [abs_nonneg C2]
  · have := h2 c hc τ
    rw [show iteratedDeriv 2 (fun τ : ℝ => binetDiff c (Complex.I * (τ : ℂ))) τ = deriv (deriv (kBeta c)) τ by
      rw [iteratedDeriv_succ, iteratedDeriv_one]; rfl] at this
    refine this.trans ?_
    have hx : 1 ≤ (1 + |τ|) ^ (2 + 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
    have hc0 : 0 < c := by linarith
    calc C2 / (c * (1 + |τ|) ^ (2 + 1)) ≤ |C2| / (c * (1 + |τ|) ^ (2 + 1)) := by
          gcongr; exact le_abs_self _
      _ ≤ |C2| / c := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) hc0; nlinarith
      _ ≤ (|C1| + |C2|) / c := by gcongr; linarith [abs_nonneg C1]

lemma contDiff_deriv_top {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

lemma contDiff_ellFun_deriv : ContDiff ℝ (⊤ : ℕ∞) (deriv ellFun) :=
  (contDiff_infty_iff_deriv.mp contDiff_ellFun).2

lemma h_le_wx {h : ℝ} (v : ℝ) (hh : 0 < h) : h ≤ wx h v := by
  unfold wx
  have : 1 ≤ (1 + |v|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg v])
  nlinarith

lemma wreg_half {h v : ℝ} (hr : WReg (1 / 2) h v) : h ≤ 1 / 2 ∧ 2 ≤ (h ^ 2)⁻¹ := by
  have h1 : h ≤ 1 / 2 := (h_le_wx v hr.1).trans hr.2
  refine ⟨h1, ?_⟩
  have hh := hr.1
  rw [le_inv_comm₀ (by norm_num) (by positivity)]
  nlinarith

lemma kSg_wexpW : WExpW 4 (1 / 2) 0 kSg := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => Complex.I * ((ellFun z : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_ellFun)
  refine WExpW.inv_smooth hg (by norm_num) (by norm_num) ?_
  intro l hl
  have hd1 : deriv (fun z : ℝ => Complex.I * ((ellFun z : ℝ) : ℂ)) = fun z => Complex.I * ((deriv ellFun z : ℝ) : ℂ) := by
    funext z
    have hd : HasDerivAt ellFun (deriv ellFun z) z := (contDiff_ellFun.differentiable (by simp) z).hasDerivAt
    exact (hd.ofReal_comp.const_mul Complex.I).deriv
  interval_cases l
  · simp [ellFun_zero]
  · rw [iteratedDeriv_one, hd1]; simp [deriv_ellFun_zero]

lemma kDg_wexp : WExp 4 (1 / 2) (Complex.I * ((deriv ellFun 0 : ℝ) : ℂ)) kDg :=
  WExp.of_smooth (g := fun z : ℝ => Complex.I * ((deriv ellFun z : ℝ) : ℂ))
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_ellFun_deriv)) (by norm_num) (by norm_num)

lemma kEx_wexp : WExp 4 (1 / 2) 1 kEx := by
  have h3 : WExp 4 1 0 (fun h v => (((h ^ 2)⁻¹ : ℝ) : ℂ) * ellG3 (h * v)) :=
    WExp.of_smooth_inv_sq contDiff_ellG3 (by norm_num) one_pos ellG3_iteratedDeriv_zero
  have hE2 := WExp.exp (by norm_num) (by norm_num : 1 ≤ 4) (binet_wexp (N := 4) (by norm_num) (by norm_num))
  have hE3 := WExp.exp (by norm_num) (by norm_num : 1 ≤ 4) h3
  have hprod := (hE2.mul (by norm_num) hE3).mono (k1 := 1 / 2) (by norm_num)
  rw [one_mul] at hprod
  refine hprod.congr fun h v _ => ?_
  unfold kEx kBeta kGamma ellG3
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem K2_wexpW : WExpW 4 (1 / 2) 0 K2 := by
  obtain ⟨Cb, hCb0, hCb⟩ := kBeta_crude
  have hk1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hk0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hu0 : WExpW 4 (1 / 2) (cpowI (-(1 / 2 : ℂ)) 0) kU0 :=
    (WExp.of_smooth (contDiff_cpowI_top _) (by norm_num) hk0).toW
  have hu1 : WExpW 4 (1 / 2) 0 kU1 := by
    have := WExpW.hpow_smooth (N := 4) (contDiff_deriv_top (contDiff_cpowI_top (-(1 / 2 : ℂ))))
      (by norm_num) hk0 hk1 1 le_rfl
    exact this.congr fun h v _ => by simp [kU1]
  have hu2 : WExpW 4 (1 / 2) 0 kU2 :=
    WExpW.hpow_smooth (N := 4) (contDiff_deriv_top (contDiff_deriv_top (contDiff_cpowI_top (-(1 / 2 : ℂ)))))
      (by norm_num) hk0 hk1 2 (by norm_num)
  -- the remainder
  obtain ⟨Cg, hCg0, hCg⟩ := WExpW.norm_le_x hk1 (by norm_num) kSg_wexpW
  have hT2 : WExpW 4 (1 / 2) 0 (fun h v => 2 * (kU1 h v * kSb h v) +
      kU0 h v * (kDb h v + kSb h v ^ 2 + 2 * kSb h v * kSg h v)) := by
    refine WExpW.bound (C := 2 * Cb + Cb + Cb ^ 2 + 2 * Cb * Cg) (fun h v hr => ?_) (by positivity)
    obtain ⟨hh1, hc2⟩ := wreg_half hr
    have hh := hr.1
    have hxh : h ≤ wx h v := h_le_wx v hh
    have hx0 : 0 ≤ wx h v := wx_nonneg hh
    set x := wx h v with hx
    set τ := h * v with hτ
    have hcpos : 0 < (h ^ 2)⁻¹ := by positivity
    obtain ⟨hb1, hb2⟩ := hCb ((h ^ 2)⁻¹) hc2 τ
    have hhc : Cb / (h ^ 2)⁻¹ = Cb * h ^ 2 := by rw [div_eq_mul_inv, inv_inv]
    rw [hhc] at hb1 hb2
    have e0 := env2_cpowI_half.2 τ
    have nU1 : ‖kU1 h v‖ ≤ h := by
      unfold kU1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]
      have := e0.2.1
      calc h * ‖deriv (cpowI (-(1 / 2 : ℂ))) τ‖ ≤ h * 1 := by gcongr
        _ = h := mul_one h
    have nU0 : ‖kU0 h v‖ ≤ 1 := e0.1
    have nSb : ‖kSb h v‖ ≤ Cb * h ^ 3 := by
      unfold kSb
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]
      calc h * ‖deriv (kBeta ((h ^ 2)⁻¹)) τ‖ ≤ h * (Cb * h ^ 2) := by gcongr
        _ = Cb * h ^ 3 := by ring
    have nDb : ‖kDb h v‖ ≤ Cb * h ^ 4 := by
      unfold kDb
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hh.le]
      calc h ^ 2 * ‖deriv (deriv (kBeta ((h ^ 2)⁻¹))) τ‖ ≤ h ^ 2 * (Cb * h ^ 2) := by gcongr
        _ = Cb * h ^ 4 := by ring
    have nSg : ‖kSg h v‖ ≤ Cg * x := hCg h v hr
    have hh3 : h ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hh.le hxh 3
    have hh4 : h ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hh.le hxh 4
    have hh6 : h ^ 6 ≤ x ^ 4 := by
      calc h ^ 6 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le (by linarith) (by norm_num)
        _ ≤ x ^ 4 := hh4
    have hh3x : h ^ 3 * x ≤ x ^ 4 := by nlinarith [pow_le_pow_left₀ hh.le hxh 3]
    have hn1 : ‖kU1 h v * kSb h v‖ ≤ h * (Cb * h ^ 3) := by
      rw [norm_mul]; exact mul_le_mul nU1 nSb (norm_nonneg _) hh.le
    have hn2 : ‖kDb h v + kSb h v ^ 2 + 2 * kSb h v * kSg h v‖ ≤
        Cb * h ^ 4 + (Cb * h ^ 3) ^ 2 + 2 * (Cb * h ^ 3) * (Cg * x) := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add nDb ?_)) ?_)
      · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) nSb 2
      · rw [norm_mul, norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2]
        exact mul_le_mul (mul_le_mul_of_nonneg_left nSb (by norm_num)) nSg (norm_nonneg _) (by positivity)
    calc ‖2 * (kU1 h v * kSb h v) + kU0 h v * (kDb h v + kSb h v ^ 2 + 2 * kSb h v * kSg h v)‖
        ≤ 2 * ‖kU1 h v * kSb h v‖ + ‖kU0 h v‖ * ‖kDb h v + kSb h v ^ 2 + 2 * kSb h v * kSg h v‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul _ _).le)
          rw [norm_mul]; simp
      _ ≤ 2 * (h * (Cb * h ^ 3)) + 1 * (Cb * h ^ 4 + (Cb * h ^ 3) ^ 2 + 2 * (Cb * h ^ 3) * (Cg * x)) := by
          gcongr
      _ ≤ (2 * Cb + Cb + Cb ^ 2 + 2 * Cb * Cg) * x ^ 4 := by
          have e1 : (Cb * h ^ 3) ^ 2 = Cb ^ 2 * h ^ 6 := by ring
          rw [e1]
          nlinarith [mul_le_mul_of_nonneg_left hh4 hCb0, mul_le_mul_of_nonneg_left hh6 (sq_nonneg Cb),
            mul_le_mul_of_nonneg_left hh3x (mul_nonneg hCb0 hCg0)]
  have hmain : WExpW 4 (1 / 2) _ (fun h v => kU2 h v + 2 * (kU1 h v * kSg h v) + kU0 h v * (kDg h v + kSg h v ^ 2)) :=
    (hu2.add ((WExpW.const 2).mul hk1 (hu1.mul hk1 kSg_wexpW))).add
      (hu0.mul hk1 (kDg_wexp.toW.add ((kSg_wexpW.mul hk1 kSg_wexpW).congr fun h v _ => (sq (kSg h v)).symm)))
  have hLam := hmain.add hT2
  have hE := (kEx_wexp).toW
  have hkey := (hLam.mul hk1 hE).congr (g := K2) fun h v hr => by
    obtain ⟨hh1, hc2⟩ := wreg_half hr
    rw [K2_eq hr.1 hc2 v]
    ring
  simpa [deriv_ellFun_zero] using hkey

/-- info: 'FormalResearch.SignUncertainty.K2_wexpW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K2_wexpW

end FormalResearch.SignUncertainty
