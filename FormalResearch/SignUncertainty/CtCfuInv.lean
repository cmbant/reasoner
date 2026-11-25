module

public import FormalResearch.SignUncertainty.CtCfuGerm
public import FormalResearch.SignUncertainty.CtCfuTheta
public import FormalResearch.SignUncertainty.CtCfuTaylor
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Langer parameter `a` and the phase shift `ψ_ε` as smooth functions of `a` near `0`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 2 and (`ct:psi-def`, `ct:langer-inv`, `ct:psi-coeffs`).  **Proved.**
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtCfu

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `f(z) = n(z) - ñ(z)`, so that `Φ(b; m(b)) = b³ f(b²)` is the critical value. -/
noncomputable def fF (z : ℝ) : ℝ := nfun z - ntil z

/-- `d(z) = ((3/2) f(z))^{1/3}`. -/
noncomputable def dF (z : ℝ) : ℝ := ((3 / 2) * fF z) ^ ((1 : ℝ) / 3)

/-- `A(z) = -z d(z)²`: the Langer parameter as a function of `z = b²`. -/
noncomputable def AF (z : ℝ) : ℝ := -z * dF z ^ 2

/-- `N(z) = z n(z) = m(√z)`: `L` as a function of `z = b²`. -/
noncomputable def NF (z : ℝ) : ℝ := z * nfun z

/-- `d₀ = (π²/12)^{1/3}`. -/
noncomputable def d0 : ℝ := (π ^ 2 / 12) ^ ((1 : ℝ) / 3)

lemma d0_pos : 0 < d0 := by unfold d0; positivity

lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma d0_cube : d0 ^ 3 = π ^ 2 / 12 := rpow_third_cube (by positivity)

lemma contDiffAt_nfun : ContDiffAt ℝ ∞' nfun 0 :=
  contDiffOn_nfun.contDiffAt (Ioo_mem_nhds (by linarith [rr_pos]) rr_pos)

lemma contDiffAt_ntil : ContDiffAt ℝ ∞' ntil 0 :=
  contDiffOn_ntil.contDiffAt (Ioo_mem_nhds (by linarith [rr_pos]) rr_pos)

lemma contDiffAt_fF : ContDiffAt ℝ ∞' fF 0 := contDiffAt_nfun.sub contDiffAt_ntil

lemma fF_zero : fF 0 = π ^ 2 / 18 := by unfold fF; rw [nfun_zero, ntil_zero]; ring

lemma hasDerivAt_fF_zero : HasDerivAt fF (-(7 * π ^ 4 / 1800)) 0 := by
  have := hasDerivAt_nfun_zero.sub hasDerivAt_ntil_zero
  refine this.congr_deriv ?_
  ring

lemma contDiffAt_dF : ContDiffAt ℝ ∞' dF 0 := by
  unfold dF
  refine ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul contDiffAt_fF) ?_
  rw [fF_zero]; positivity

lemma dF_zero : dF 0 = d0 := by
  unfold dF d0; rw [fF_zero]; congr 1; ring

lemma contDiffAt_AF : ContDiffAt ℝ ∞' AF 0 := by
  unfold AF
  exact (contDiffAt_id.neg.mul (contDiffAt_dF.pow 2))

lemma differentiableAt_of_Ioo {f : ℝ → ℝ} (h : ContDiffOn ℝ ∞' f (Ioo (-rr) rr)) {z : ℝ} (hz : z ∈ Ioo (-rr) rr) :
    DifferentiableAt ℝ f z :=
  (h.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hz)

lemma contDiffOn_fF : ContDiffOn ℝ ∞' fF (Ioo (-rr) rr) := contDiffOn_nfun.sub contDiffOn_ntil

lemma contDiffOn_deriv_fF : ContDiffOn ℝ ∞' (deriv fF) (Ioo (-rr) rr) :=
  contDiffOn_fF.deriv_of_isOpen isOpen_Ioo (by exact_mod_cast le_top)

lemma contDiffOn_deriv_nfun : ContDiffOn ℝ ∞' (deriv nfun) (Ioo (-rr) rr) :=
  contDiffOn_nfun.deriv_of_isOpen isOpen_Ioo (by exact_mod_cast le_top)

lemma zero_mem_Ioo : (0 : ℝ) ∈ Ioo (-rr) rr := ⟨by linarith [rr_pos], rr_pos⟩

lemma fF_pos_eventually : ∀ᶠ z in 𝓝 (0 : ℝ), 0 < fF z := by
  have hc : ContinuousAt fF 0 := contDiffAt_fF.continuousAt
  have : 0 < fF 0 := by rw [fF_zero]; positivity
  exact hc.eventually (lt_mem_nhds this)

/-- `dF'(z)` (formula valid where `f > 0`). -/
noncomputable def dFp (z : ℝ) : ℝ := (3 / 2) * deriv fF z * (1 / 3) * ((3 / 2) * fF z) ^ ((1 : ℝ) / 3 - 1)

lemma hasDerivAt_dF {z : ℝ} (hz : z ∈ Ioo (-rr) rr) (hf : 0 < fF z) : HasDerivAt dF (dFp z) z := by
  have h1 : HasDerivAt (fun y => (3 / 2) * fF y) ((3 / 2) * deriv fF z) z :=
    ((differentiableAt_of_Ioo contDiffOn_fF hz).hasDerivAt).const_mul _
  have h2 := h1.rpow_const (p := (1 : ℝ) / 3) (Or.inl (by positivity))
  unfold dF dFp
  refine h2.congr_deriv ?_
  ring

lemma dFp_zero : dFp 0 = -(7 * π ^ 4 / 1800) / (2 * d0 ^ 2) := by
  unfold dFp
  rw [hasDerivAt_fF_zero.deriv, fF_zero]
  have hx : (3 / 2 * (π ^ 2 / 18) : ℝ) = π ^ 2 / 12 := by ring
  rw [hx, Real.rpow_sub (by positivity), Real.rpow_one]
  have : (π ^ 2 / 12) ^ ((1 : ℝ) / 3) = d0 := rfl
  rw [this]
  have h3 := d0_cube
  have hd := d0_pos
  field_simp
  rw [h3]
  ring

lemma hasDerivAt_dF_zero : HasDerivAt dF (-(7 * π ^ 4 / 1800) / (2 * d0 ^ 2)) 0 := by
  have := hasDerivAt_dF zero_mem_Ioo (by rw [fF_zero]; positivity)
  rwa [dFp_zero] at this

lemma differentiableAt_dFp_zero : DifferentiableAt ℝ dFp 0 := by
  have h1 : DifferentiableAt ℝ (deriv fF) 0 :=
    (contDiffOn_deriv_fF.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds zero_mem_Ioo)
  have h2 : DifferentiableAt ℝ fF 0 := differentiableAt_of_Ioo contDiffOn_fF zero_mem_Ioo
  unfold dFp
  have h3 : DifferentiableAt ℝ (fun z => (3 / 2) * fF z) 0 := h2.const_mul _
  have h4 := h3.rpow_const (p := (1 : ℝ) / 3 - 1) (Or.inl (by rw [fF_zero]; positivity))
  exact ((h1.const_mul _).mul_const _).mul h4

/-- `A'(z)` (valid where `f > 0`). -/
noncomputable def AFp (z : ℝ) : ℝ := -(dF z) ^ 2 - z * (2 * dF z * dFp z)

lemma hasDerivAt_AF {z : ℝ} (hz : z ∈ Ioo (-rr) rr) (hf : 0 < fF z) : HasDerivAt AF (AFp z) z := by
  have h := hasDerivAt_dF hz hf
  have h2 : HasDerivAt (fun y => -y * dF y ^ 2) (-1 * dF z ^ 2 + (-z) * (2 * dF z * dFp z)) z := by
    have := (hasDerivAt_id' z).neg.mul (h.pow 2)
    refine this.congr_deriv ?_
    simp
  unfold AF AFp
  refine h2.congr_deriv ?_
  ring

lemma hasDerivAt_AF_zero : HasDerivAt AF (-(d0 ^ 2)) 0 := by
  have := hasDerivAt_AF zero_mem_Ioo (by rw [fF_zero]; positivity)
  refine this.congr_deriv ?_
  unfold AFp; rw [dF_zero]; ring

lemma hasDerivAt_AFp_zero : HasDerivAt AFp (-4 * d0 * (-(7 * π ^ 4 / 1800) / (2 * d0 ^ 2))) 0 := by
  have hd := hasDerivAt_dF_zero
  have hdp : HasDerivAt dFp (deriv dFp 0) 0 := differentiableAt_dFp_zero.hasDerivAt
  have hH := (hd.const_mul 2).mul hdp
  have h2 : HasDerivAt (fun z => z * (2 * dF z * dFp z)) (1 * (2 * dF 0 * dFp 0) + 0 * _) 0 :=
    (hasDerivAt_id' (0 : ℝ)).mul hH
  have h1 := (hd.pow 2).neg
  have h3 := h1.sub h2
  unfold AFp
  refine h3.congr_deriv ?_
  rw [dFp_zero, dF_zero]
  simp
  ring

/-- `N'(z)`. -/
noncomputable def NFp (z : ℝ) : ℝ := nfun z + z * deriv nfun z

lemma hasDerivAt_NF {z : ℝ} (hz : z ∈ Ioo (-rr) rr) : HasDerivAt NF (NFp z) z := by
  have := (hasDerivAt_id' z).mul (differentiableAt_of_Ioo contDiffOn_nfun hz).hasDerivAt
  unfold NF NFp
  refine this.congr_deriv ?_
  ring

lemma NF_zero : NF 0 = 0 := by simp [NF]

lemma NFp_zero : NFp 0 = π ^ 2 / 12 := by simp [NFp, nfun_zero]

lemma hasDerivAt_NFp_zero : HasDerivAt NFp (2 * (-(7 * π ^ 4 / 1440))) 0 := by
  have hdn : HasDerivAt nfun (-(7 * π ^ 4 / 1440)) 0 := hasDerivAt_nfun_zero
  have hd2 : HasDerivAt (deriv nfun) (deriv (deriv nfun) 0) 0 :=
    ((contDiffOn_deriv_nfun.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds zero_mem_Ioo)).hasDerivAt
  have h := hdn.add ((hasDerivAt_id' (0 : ℝ)).mul hd2)
  unfold NFp
  refine h.congr_deriv ?_
  rw [hdn.deriv]; simp; ring

lemma AF_zero : AF 0 = 0 := by simp [AF]

lemma d0_sq_ne : -(d0 ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 d0_pos.ne')

/-- The linear equivalence "multiplication by `-d₀²`". -/
noncomputable def eA : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (-(d0 ^ 2)) d0_sq_ne)

lemma hasFDerivAt_AF_zero : HasFDerivAt AF (eA : ℝ →L[ℝ] ℝ) 0 := by
  have := hasDerivAt_AF_zero.hasFDerivAt
  convert this using 1
  ext
  simp [eA]

/-- The inverse of `A` near `0`: `z = z_A(a)`. -/
noncomputable def zA : ℝ → ℝ := contDiffAt_AF.localInverse hasFDerivAt_AF_zero (by simp)

lemma zA_zero : zA 0 = 0 := by
  have := contDiffAt_AF.localInverse_apply_image hasFDerivAt_AF_zero (by simp : (∞' : WithTop ℕ∞) ≠ 0)
  rw [AF_zero] at this
  exact this

lemma contDiffAt_zA : ContDiffAt ℝ ∞' zA 0 := by
  have := contDiffAt_AF.to_localInverse hasFDerivAt_AF_zero (by simp : (∞' : WithTop ℕ∞) ≠ 0)
  rw [AF_zero] at this
  exact this

lemma AF_zA_eventually : ∀ᶠ a in 𝓝 (0 : ℝ), AF (zA a) = a := by
  have := (contDiffAt_AF.hasStrictFDerivAt hasFDerivAt_AF_zero (by simp : (∞' : WithTop ℕ∞) ≠ 0)).eventually_right_inverse
  rw [AF_zero] at this
  exact this

lemma AFp_zero : AFp 0 = -(d0 ^ 2) := by
  have := hasDerivAt_AF_zero
  have h2 := (hasDerivAt_AF zero_mem_Ioo (by rw [fF_zero]; positivity))
  exact h2.unique this

lemma hasDerivAt_zA_zero : HasDerivAt zA (-(1 / d0 ^ 2)) 0 := by
  have hz : DifferentiableAt ℝ zA 0 := contDiffAt_zA.differentiableAt (by simp)
  have hA : HasDerivAt AF (-(d0 ^ 2)) (zA 0) := by rw [zA_zero]; exact hasDerivAt_AF_zero
  have hc := hA.scomp 0 hz.hasDerivAt
  have hid : HasDerivAt (AF ∘ zA) 1 0 := by
    refine (hasDerivAt_id' (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [AF_zA_eventually] with a ha using ha
  have h1 := hc.unique hid
  have hd := d0_pos
  have : deriv zA 0 = -(1 / d0 ^ 2) := by
    simp only [smul_eq_mul] at h1
    field_simp
    nlinarith [h1]
  rw [← this]; exact hz.hasDerivAt

/-- The ratio `R = N'/A'` (so that `d/da N(z_A(a)) = R(z_A(a))`). -/
noncomputable def RF (z : ℝ) : ℝ := NFp z / AFp z

lemma hasDerivAt_RF_zero : HasDerivAt RF
    ((2 * (-(7 * π ^ 4 / 1440)) * AFp 0 - NFp 0 * (-4 * d0 * (-(7 * π ^ 4 / 1800) / (2 * d0 ^ 2)))) / AFp 0 ^ 2) 0 := by
  have h := hasDerivAt_NFp_zero.div hasDerivAt_AFp_zero (by rw [AFp_zero]; exact d0_sq_ne)
  exact h

lemma RF_zero : RF 0 = -d0 := by
  unfold RF; rw [NFp_zero, AFp_zero]
  have h3 := d0_cube
  have hd := d0_pos
  field_simp
  rw [h3]; ring

lemma tendsto_zA : Tendsto zA (𝓝 0) (𝓝 0) := by
  have := contDiffAt_zA.continuousAt.tendsto
  rwa [zA_zero] at this

lemma AFp_ne_eventually : ∀ᶠ z in 𝓝 (0 : ℝ), AFp z ≠ 0 := by
  have hc : ContinuousAt AFp 0 := hasDerivAt_AFp_zero.continuousAt
  have : AFp 0 ≠ 0 := by rw [AFp_zero]; exact d0_sq_ne
  exact hc.eventually_ne this

lemma Ioo_eventually : ∀ᶠ z in 𝓝 (0 : ℝ), z ∈ Ioo (-rr) rr := isOpen_Ioo.mem_nhds zero_mem_Ioo

/-- Good set for `z_A`. -/
lemma zA_good : ∀ᶠ a in 𝓝 (0 : ℝ), zA a ∈ Ioo (-rr) rr ∧ 0 < fF (zA a) ∧ AFp (zA a) ≠ 0 := by
  filter_upwards [tendsto_zA.eventually Ioo_eventually, tendsto_zA.eventually fF_pos_eventually,
    tendsto_zA.eventually AFp_ne_eventually] with a h1 h2 h3 using ⟨h1, h2, h3⟩

lemma hasDerivAt_zA_eventually : ∀ᶠ a in 𝓝 (0 : ℝ), HasDerivAt zA (1 / AFp (zA a)) a := by
  have h1 : ContDiffAt ℝ 1 zA 0 := contDiffAt_zA.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hdiff : ∀ᶠ a in 𝓝 (0 : ℝ), DifferentiableAt ℝ zA a :=
    (h1.eventually (by simp)).mono fun a ha => ha.differentiableAt (by simp)
  filter_upwards [zA_good, hdiff, AF_zA_eventually.eventually_nhds] with a hg hd hr
  obtain ⟨h1, h2, h3⟩ := hg
  have hA := hasDerivAt_AF h1 h2
  have hc := hA.scomp a hd.hasDerivAt
  have hid : HasDerivAt (AF ∘ zA) 1 a := by
    refine (hasDerivAt_id' a).congr_of_eventuallyEq ?_
    filter_upwards [hr] with y hy using hy
  have := hc.unique hid
  simp only [smul_eq_mul] at this
  have e : deriv zA a = 1 / AFp (zA a) := by field_simp; linarith
  rw [← e]; exact hd.hasDerivAt

/-- `Ξ(a) = exp(L(a))/π²` with `L(a) = N(z_A(a))`: `ξ` as a function of the Langer parameter `a`. -/
noncomputable def Xi (a : ℝ) : ℝ := Real.exp (NF (zA a)) / π ^ 2

lemma Xi_zero : Xi 0 = 1 / π ^ 2 := by simp [Xi, zA_zero, NF_zero]

/-- `Ξ'`. -/
noncomputable def XiP (a : ℝ) : ℝ := RF (zA a) * Real.exp (NF (zA a)) / π ^ 2

lemma hasDerivAt_Xi_eventually : ∀ᶠ a in 𝓝 (0 : ℝ), HasDerivAt Xi (XiP a) a := by
  filter_upwards [zA_good, hasDerivAt_zA_eventually] with a hg hz
  obtain ⟨h1, h2, h3⟩ := hg
  have hN := (hasDerivAt_NF h1).scomp a hz
  have he := hN.exp
  have := he.div_const (π ^ 2)
  unfold Xi XiP RF
  refine this.congr_deriv ?_
  simp only [smul_eq_mul, Function.comp]
  field_simp

lemma XiP_zero : XiP 0 = -d0 / π ^ 2 := by
  simp [XiP, zA_zero, NF_zero, RF_zero]

/-- `R'(0)`. -/
noncomputable def RFp0 : ℝ :=
  (2 * (-(7 * π ^ 4 / 1440)) * AFp 0 - NFp 0 * (-4 * d0 * (-(7 * π ^ 4 / 1800) / (2 * d0 ^ 2)))) / AFp 0 ^ 2

lemma hasDerivAt_RF_zero' : HasDerivAt RF RFp0 0 := hasDerivAt_RF_zero

/-- `Ξ''(0)` (before simplification). -/
noncomputable def Xi2 : ℝ := (RFp0 * (-(1 / d0 ^ 2)) + RF 0 * (NFp 0 * (-(1 / d0 ^ 2)))) / π ^ 2

lemma hasDerivAt_XiP_zero : HasDerivAt XiP Xi2 0 := by
  have hz := hasDerivAt_zA_zero
  have hR : HasDerivAt RF RFp0 (zA 0) := by rw [zA_zero]; exact hasDerivAt_RF_zero'
  have hN : HasDerivAt NF (NFp 0) (zA 0) := by rw [zA_zero]; exact hasDerivAt_NF zero_mem_Ioo
  have h1 := hR.scomp 0 hz
  have h2 := (hN.scomp 0 hz).exp
  have h3 := (h1.mul h2).div_const (π ^ 2)
  unfold XiP
  refine h3.congr_deriv ?_
  simp [zA_zero, NF_zero, smul_eq_mul, Xi2]
  ring

lemma deriv_Xi_zero : deriv Xi 0 = -d0 / π ^ 2 := by
  have h : HasDerivAt Xi (XiP 0) 0 := hasDerivAt_Xi_eventually.self_of_nhds
  rw [h.deriv, XiP_zero]

lemma deriv_deriv_Xi_zero : deriv (deriv Xi) 0 = Xi2 := by
  have hev : deriv Xi =ᶠ[𝓝 0] XiP := by
    filter_upwards [hasDerivAt_Xi_eventually] with a ha using ha.deriv
  rw [hev.deriv_eq, hasDerivAt_XiP_zero.deriv]

lemma d0_pi_sq : π ^ 2 = 12 * d0 ^ 3 := by rw [d0_cube]; ring

lemma Xi2_eq : Xi2 = (-(7 * π ^ 4 / 3600) / d0 ^ 4 + d0 ^ 2) / π ^ 2 := by
  unfold Xi2 RFp0
  rw [RF_zero, NFp_zero, AFp_zero]
  have hd := d0_pos.ne'
  have h2 := d0_pi_sq
  have h4 : π ^ 4 = 144 * d0 ^ 6 := by
    have : π ^ 4 = (π ^ 2) ^ 2 := by ring
    rw [this, h2]; ring
  rw [h4, h2]
  field_simp
  ring

/-- `d₀ · 2^{2/3} β₁ = π²` with `β₁ = (π²√3)^{2/3}`. -/
lemma d0_mul_beta : d0 * (2 : ℝ) ^ ((2 : ℝ) / 3) * (π ^ 2 * Real.sqrt 3) ^ ((2 : ℝ) / 3) = π ^ 2 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hb : ((π ^ 2 * Real.sqrt 3) ^ ((2 : ℝ) / 3)) ^ 3 = 3 * π ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have h2 : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hcube : (d0 * (2 : ℝ) ^ ((2 : ℝ) / 3) * (π ^ 2 * Real.sqrt 3) ^ ((2 : ℝ) / 3)) ^ 3 = (π ^ 2) ^ 3 := by
    rw [mul_pow, mul_pow, hb, h2, d0_cube]; ring
  have hpos : 0 < d0 * (2 : ℝ) ^ ((2 : ℝ) / 3) * (π ^ 2 * Real.sqrt 3) ^ ((2 : ℝ) / 3) := by
    have := d0_pos; positivity
  exact (pow_left_inj₀ hpos.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp hcube

/-- The phase shift `ψ(a) = θ̂(z_A(a)) / d(z_A(a))` for a given `θ̂`. -/
noncomputable def psiOf (th : ℝ → ℝ) (a : ℝ) : ℝ := th (zA a) / dF (zA a)

lemma contDiffAt_psiOf {th : ℝ → ℝ} (hth : AnalyticAt ℝ th 0) : ContDiffAt ℝ ∞' (psiOf th) 0 := by
  unfold psiOf
  have h1 : ContDiffAt ℝ ∞' th (zA 0) := by
    rw [zA_zero]; exact (hth.contDiffAt).of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ ∞' dF (zA 0) := by rw [zA_zero]; exact contDiffAt_dF
  have hne : dF (zA 0) ≠ 0 := by rw [zA_zero, dF_zero]; exact d0_pos.ne'
  exact (h1.comp 0 contDiffAt_zA).div (h2.comp 0 contDiffAt_zA) hne

lemma psiOf_zero {th : ℝ → ℝ} : psiOf th 0 = th 0 / d0 := by simp [psiOf, zA_zero, dF_zero]

lemma deriv_psiOf_zero {th : ℝ → ℝ} (hth : AnalyticAt ℝ th 0) :
    deriv (psiOf th) 0 = (deriv th 0 * d0 - th 0 * (-(7 * π ^ 4 / 1800) / (2 * d0 ^ 2))) / d0 ^ 2 * (-(1 / d0 ^ 2)) := by
  have hz := hasDerivAt_zA_zero
  have hth' : HasDerivAt th (deriv th 0) (zA 0) := by rw [zA_zero]; exact hth.differentiableAt.hasDerivAt
  have hd : HasDerivAt dF (-(7 * π ^ 4 / 1800) / (2 * d0 ^ 2)) (zA 0) := by
    rw [zA_zero]; exact hasDerivAt_dF_zero
  have h1 := hth'.scomp 0 hz
  have h2 := hd.scomp 0 hz
  have hne : dF (zA 0) ≠ 0 := by rw [zA_zero, dF_zero]; exact d0_pos.ne'
  have h3 := h1.div h2 hne
  have := h3.deriv
  show deriv (th ∘ zA / dF ∘ zA) 0 = _
  rw [this]
  simp [zA_zero, dF_zero, smul_eq_mul]
  ring

/-- `ψ'(0)` in the paper's form: `-(7θ₁/25 + 12 θ₃/π²)`. -/
lemma psi_coeff {θ1 θ3 : ℝ} {th : ℝ → ℝ} (hth : AnalyticAt ℝ th 0) (h0 : th 0 = θ1) (h1 : deriv th 0 = θ3) :
    deriv (psiOf th) 0 = -(7 / 25 * θ1 + 12 / π ^ 2 * θ3) := by
  rw [deriv_psiOf_zero hth, h0, h1]
  have hd := d0_pos.ne'
  have h2 := d0_pi_sq
  have h4 : π ^ 4 = 144 * d0 ^ 6 := by
    have : π ^ 4 = (π ^ 2) ^ 2 := by ring
    rw [this, h2]; ring
  rw [h4, h2]
  field_simp
  ring

/-- `τ₀(a) = √(z_A(a))`. -/
noncomputable def tau0 (a : ℝ) : ℝ := Real.sqrt (zA a)

open FormalResearch.CohnElkies in
lemma edgePhi_eq (τ : ℝ) (L : ℝ) : edgePhi L τ = L * τ - ∫ u in (0 : ℝ)..τ, hankelEdgeM u := by
  unfold edgePhi
  have : ∀ u : ℝ, Real.log (Real.tanh (π * u / 2) / (π * u / 2)) = -hankelEdgeM u := by
    intro u
    unfold hankelEdgeM ceEll
    rw [← Real.log_inv, inv_div]
  simp only [this, intervalIntegral.integral_neg]
  ring

open FormalResearch.CohnElkies in
lemma edgePhi_crit {τ : ℝ} (hτ : 0 ≤ τ) (hτ2 : τ ^ 2 < rr) :
    edgePhi (hankelEdgeM τ) τ = τ ^ 3 * fF (τ ^ 2) := by
  rw [edgePhi_eq, integral_hankelEdgeM_eq hτ hτ2, hankelEdgeM_eq hτ hτ2]
  unfold fF; ring

lemma zA_pos {a : ℝ} (ha : a < 0) (hr : AF (zA a) = a) : 0 < zA a := by
  by_contra h
  have h' := not_lt.mp h
  have : 0 ≤ AF (zA a) := by
    unfold AF
    have : 0 ≤ dF (zA a) ^ 2 := sq_nonneg _
    nlinarith
  linarith

/-- Properties of `τ₀(a)` for `a < 0` in the good set. -/
lemma tau0_props {a : ℝ} (ha : a < 0) (hr : AF (zA a) = a) (hg : zA a ∈ Ioo (-rr) rr ∧ 0 < fF (zA a) ∧ AFp (zA a) ≠ 0) :
    0 < tau0 a ∧ hankelEdgeM (tau0 a) = NF (zA a) ∧
    FormalResearch.CohnElkies.edgePhi (hankelEdgeM (tau0 a)) (tau0 a) = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) ∧
    Real.sqrt (-a) = tau0 a * dF (zA a) := by
  obtain ⟨h1, h2, -⟩ := hg
  have hz := zA_pos ha hr
  have hτ : 0 < tau0 a := Real.sqrt_pos.mpr hz
  have hτ2 : tau0 a ^ 2 = zA a := Real.sq_sqrt hz.le
  have hτr : tau0 a ^ 2 < rr := by rw [hτ2]; exact h1.2
  have hdpos : 0 < dF (zA a) := by unfold dF; positivity
  have hdcube : dF (zA a) ^ 3 = (3 / 2) * fF (zA a) := rpow_third_cube (by positivity)
  have hm : hankelEdgeM (tau0 a) = NF (zA a) := by
    rw [hankelEdgeM_eq hτ.le hτr, hτ2]; rfl
  have hAF : -a = zA a * dF (zA a) ^ 2 := by
    have h := hr; unfold AF at h; linarith
  have hneg : -a = (tau0 a * dF (zA a)) ^ 2 := by rw [mul_pow, hτ2]; exact hAF
  refine ⟨hτ, hm, ?_, ?_⟩
  · rw [edgePhi_crit hτ.le hτr, hτ2, hneg]
    have : ((tau0 a * dF (zA a)) ^ 2) ^ ((3 : ℝ) / 2) = (tau0 a * dF (zA a)) ^ 3 := by
      rw [← Real.rpow_natCast (tau0 a * dF (zA a)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [this, mul_pow, hdcube]
    ring
  · rw [hneg, Real.sqrt_sq (by positivity)]

open FormalResearch.CohnElkies in
/-- The critical value `τ ↦ Φ(τ; m(τ)) = τ m(τ) - ∫₀^τ m` is strictly increasing on `[0, ∞)`. -/
lemma critical_value_strictMonoOn : StrictMonoOn (fun τ : ℝ => edgePhi (hankelEdgeM τ) τ) (Ici 0) := by
  set F : ℝ → ℝ := fun τ => edgePhi (hankelEdgeM τ) τ with hF
  have hderiv : ∀ τ : ℝ, 0 < τ → HasDerivAt F (τ * hankelEdgeM' τ) τ := by
    intro τ hτ
    have hmc : ContinuousOn hankelEdgeM (Ici 0) := hankelEdgeM_continuousOn
    have hP : HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..x, hankelEdgeM u) (hankelEdgeM τ) τ := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · exact (hmc.mono (by rw [uIcc_of_le hτ.le]; exact fun x hx => hx.1)).intervalIntegrable
      · exact (hmc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ
      · exact (hankelEdgeM_hasDerivAt hτ).continuousAt
    have h2 := ((hasDerivAt_id' τ).mul (hankelEdgeM_hasDerivAt hτ)).sub hP
    have : F = fun τ => τ * hankelEdgeM τ - ∫ u in (0 : ℝ)..τ, hankelEdgeM u := by
      funext x; simp only [hF, edgePhi_eq]; ring
    rw [this]
    refine h2.congr_deriv ?_
    ring
  have hcont : ContinuousOn F (Ici 0) := by
    intro τ hτ
    rcases (mem_Ici.mp hτ).eq_or_lt with h | hpos
    · subst h
      -- near 0, `F τ = τ³ f(τ²)`
      have hnear : ∀ᶠ τ in 𝓝[Ici 0] (0 : ℝ), F τ = τ ^ 3 * fF (τ ^ 2) := by
        have h1 : ∀ᶠ τ in 𝓝 (0 : ℝ), τ ^ 2 < rr := by
          have : Continuous fun τ : ℝ => τ ^ 2 := by fun_prop
          exact this.continuousAt.eventually (gt_mem_nhds (by simpa using rr_pos))
        filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with τ h1 h2
        exact edgePhi_crit h2 h1
      have hF0 : F 0 = 0 := by
        simp only [hF, edgePhi_eq]; simp [hankelEdgeM_zero]
      have hc : ContinuousWithinAt (fun τ : ℝ => τ ^ 3 * fF (τ ^ 2)) (Ici 0) 0 := by
        have h1 : ContinuousAt fF ((fun τ : ℝ => τ ^ 2) 0) := by simpa using contDiffAt_fF.continuousAt
        exact ((continuousAt_id.pow 3).mul (h1.comp (f := fun τ : ℝ => τ ^ 2) (by fun_prop))).continuousWithinAt
      refine (hc.congr_of_eventuallyEq hnear ?_)
      rw [hF0]; simp [fF_zero]
    · exact (hderiv τ hpos).continuousAt.continuousWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) hcont (fun τ hτ => ?_)
  rw [interior_Ici] at hτ
  have hτ' : 0 < τ := hτ
  rw [(hderiv τ hτ').deriv]
  have := CtOuter.mPrime_bounds hτ'
  rw [← CtOuter.mPrime_eq_hankelEdgeM' hτ']
  have h0 : 0 < τ / (1 + τ ^ 2) := by positivity
  exact mul_pos hτ' (lt_of_lt_of_le h0 this.1)

end FormalResearch.SignUncertainty.CtCfu
