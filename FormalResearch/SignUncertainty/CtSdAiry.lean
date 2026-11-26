module

public import FormalResearch.SignUncertainty.CtSdEval

/-!
# Chain integrals versus the Airy ray integrals (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("extending `Γ_SD` from `p₁` to
`∞e^{iπ/6}` incurs `O(e^{-c₀s₁³c})`", then `(ct:airy-id1)`, `(ct:airy-id2)`).  **Proved.**  For a chain ending at `R e^{iπ/6}`:
`e^{iπ/4}∫_Γ w^{1/2}e^{iPh_U}dw` and `e^{iπ/4}∫_Γ w^{1/2}(κU+w²)e^{iPh_U}dw` equal the full ray integrals of `airy_id1`,
`airy_id2` minus tails of size `O(e^{-R³/12})`, provided `ν U t ≥ -t³/6` and `κ|U| ≤ t²` for `t ≥ R`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

open CtAiry FormalResearch.Special

/-- A chain integral of `csr · g` with `g` entire depends only on the endpoint: it equals the ray integral. -/
lemma chain_int_eq_ray {R R₀ : ℝ} (hR0 : 0 < R₀) (hR : 0 ≤ R) (hRR : R < R₀) (ch : Chain3 R₀ ((R : ℂ) * d6))
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ch.int (fun z => csr z * g z) = (chainA hR hRR).int (fun z => csr z * g z) := by
  obtain ⟨Φ, hΦ⟩ := Chain3.int_csr_uniform hR0 (hg.differentiableOn)
  rw [hΦ ch, hΦ (chainA hR hRR)]

lemma chainA_int {R R₀ : ℝ} (hR : 0 ≤ R) (hRR : R < R₀) (f : ℂ → ℂ) :
    (chainA hR hRR).int f = ∫ t in (0 : ℝ)..R, f (0 + (t : ℂ) * d6) * d6 := by
  unfold Chain3.int lineInt
  simp only [chainA, Piece.z0, Piece.d, Piece.a, Piece.b, intervalIntegral.integral_same, add_zero]

lemma ray1_eq_line (U t : ℝ) :
    ray1 U t = Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (csr (0 + (t : ℂ) * d6) * Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6)) * d6) := by
  unfold ray1 rayPt csr PhU d6
  rw [zero_add, mul_comm (t : ℂ)]
  ring

lemma ray2_eq_line (U t : ℝ) :
    ray2 U t = Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (csr (0 + (t : ℂ) * d6) * ((kap : ℂ) * U + (0 + (t : ℂ) * d6) ^ 2) *
        Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6)) * d6) := by
  unfold ray2 rayPt csr PhU d6
  rw [zero_add, mul_comm (t : ℂ)]
  ring

lemma ray1_integrable (U : ℝ) : IntegrableOn (ray1 U) (Ioi (0 : ℝ)) := by
  have h := (gF_integrable (p := 1 / 2) (by norm_num) U).const_mul Complex.I
  refine h.congr ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => (ray1_eq ht U).symm)

lemma ray2_integrable (U : ℝ) : IntegrableOn (ray2 U) (Ioi (0 : ℝ)) := by
  have a1 := gF_integrable (p := 1 / 2) (by norm_num) U
  have a3 := gF_integrable (p := 5 / 2) (by norm_num) U
  have h := (a3.sub (a1.const_mul (al * U))).const_mul (Complex.I * Complex.exp (Complex.I * (π / 3 : ℝ)))
  refine h.congr ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => (ray2_eq ht U).symm)

lemma integral_split_Ioi {f : ℝ → ℂ} (hi : IntegrableOn f (Ioi (0 : ℝ))) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in Ioi (0 : ℝ), f t = (∫ t in (0 : ℝ)..R, f t) + ∫ t in Ioi R, f t := by
  have hu : Ioc 0 R ∪ Ioi R = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hR
  have h1 : IntegrableOn f (Ioc 0 R) := hi.mono_set (subset_union_left.trans hu.le)
  have h2 : IntegrableOn f (Ioi R) := hi.mono_set (Ioi_subset_Ioi hR)
  calc ∫ t in Ioi (0 : ℝ), f t = ∫ t in Ioc 0 R ∪ Ioi R, f t := by rw [hu]
    _ = (∫ t in Ioc 0 R, f t) + ∫ t in Ioi R, f t :=
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2
    _ = _ := by rw [intervalIntegral.integral_of_le hR]

/-- Tail of a cubic-exponentially decaying integrand. -/
lemma tail_le {f : ℝ → ℂ} {R B : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hf : ∀ t, R < t → ‖f t‖ ≤ B * (t ^ 3 * Real.exp (-(t ^ 3 / 6)))) :
    ‖∫ t in Ioi R, f t‖ ≤ 144 * B * Real.exp (-(R ^ 3 / 12)) := by
  set b : ℝ := R ^ 2 / 12 with hbd
  have hb : 0 < b := by positivity
  have hint := integrableOn_exp_mul_Ioi (a := -b) (by linarith) R
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi R)) (f := f)
    (g := fun t => 12 * B * Real.exp (-b * t)) (hint.const_mul (12 * B)) (by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
      have htR : R < t := ht
      have ht0 : 0 < t := by linarith
      have e1 : t ^ 3 * Real.exp (-(t ^ 3 / 12)) ≤ 12 := by
        have := Real.add_one_le_exp (t ^ 3 / 12)
        have hp : 0 < Real.exp (t ^ 3 / 12) := Real.exp_pos _
        rw [Real.exp_neg]
        rw [← div_eq_mul_inv, div_le_iff₀ hp]
        nlinarith only [this]
      have e2 : Real.exp (-(t ^ 3 / 6)) = Real.exp (-(t ^ 3 / 12)) * Real.exp (-(t ^ 3 / 12)) := by
        rw [← Real.exp_add]; congr 1; ring
      have e3 : Real.exp (-(t ^ 3 / 12)) ≤ Real.exp (-b * t) := by
        apply Real.exp_le_exp.mpr
        have h2 : R ^ 2 ≤ t ^ 2 := by nlinarith only [htR, hR]
        have : R ^ 2 * t ≤ t ^ 3 := by
          calc R ^ 2 * t ≤ t ^ 2 * t := mul_le_mul_of_nonneg_right h2 ht0.le
            _ = t ^ 3 := by ring
        rw [hbd]; nlinarith only [this]
      have e4 : t ^ 3 * Real.exp (-(t ^ 3 / 6)) ≤ 12 * Real.exp (-b * t) := by
        rw [e2, ← mul_assoc]
        calc t ^ 3 * Real.exp (-(t ^ 3 / 12)) * Real.exp (-(t ^ 3 / 12)) ≤ 12 * Real.exp (-(t ^ 3 / 12)) :=
              mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
          _ ≤ 12 * Real.exp (-b * t) := mul_le_mul_of_nonneg_left e3 (by norm_num)
      calc ‖f t‖ ≤ B * (t ^ 3 * Real.exp (-(t ^ 3 / 6))) := hf t htR
        _ ≤ B * (12 * Real.exp (-b * t)) := mul_le_mul_of_nonneg_left e4 hB
        _ = 12 * B * Real.exp (-b * t) := by ring)
  refine h1.trans ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) R]
  have e5 : -b * R = -(R ^ 3 / 12) := by rw [hbd]; ring
  rw [e5]
  have e6 : -Real.exp (-(R ^ 3 / 12)) / -b = Real.exp (-(R ^ 3 / 12)) / b := by rw [neg_div_neg_eq]
  rw [e6]
  have e7 : Real.exp (-(R ^ 3 / 12)) / b ≤ 12 * Real.exp (-(R ^ 3 / 12)) := by
    rw [div_le_iff₀ hb, hbd]
    have : 0 < Real.exp (-(R ^ 3 / 12)) := Real.exp_pos _
    have h1R : 1 ≤ R ^ 2 := by nlinarith only [hR]
    nlinarith only [mul_nonneg (sub_nonneg.2 h1R) this.le]
  calc 12 * B * (Real.exp (-(R ^ 3 / 12)) / b) ≤ 12 * B * (12 * Real.exp (-(R ^ 3 / 12))) :=
        mul_le_mul_of_nonneg_left e7 (by positivity)
    _ = 144 * B * Real.exp (-(R ^ 3 / 12)) := by ring

lemma norm_phase_line {U t : ℝ} :
    ‖Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6))‖ = Real.exp (-(nu * U * t + t ^ 3 / 3)) := by
  rw [norm_exp_I_mul, im_ray]

lemma norm_csr_line {t : ℝ} (ht : 0 ≤ t) : ‖csr (0 + (t : ℂ) * d6)‖ = t ^ (1 / 2 : ℝ) := by
  rw [norm_csr_rpow, norm_ray ht]

lemma norm_phase_pi4 : ‖Complex.exp (Complex.I * (π / 4 : ℝ))‖ = 1 := by
  rw [norm_exp_I_mul]; simp

lemma norm_ray1 {U t : ℝ} (ht : 0 ≤ t) :
    ‖ray1 U t‖ = t ^ (1 / 2 : ℝ) * Real.exp (-(nu * U * t + t ^ 3 / 3)) := by
  rw [ray1_eq_line, norm_mul, norm_mul, norm_mul, norm_phase_pi4, norm_csr_line ht, norm_phase_line, norm_d6]
  ring

lemma norm_ray2_le {U t : ℝ} (ht : 0 ≤ t) (hkU : kap * |U| ≤ t ^ 2) :
    ‖ray2 U t‖ ≤ 2 * (t ^ (1 / 2 : ℝ) * t ^ 2 * Real.exp (-(nu * U * t + t ^ 3 / 3))) := by
  rw [ray2_eq_line, norm_mul, norm_mul, norm_mul, norm_mul, norm_phase_pi4, norm_csr_line ht, norm_phase_line,
    norm_d6]
  have hq : ‖(kap : ℂ) * U + (0 + (t : ℂ) * d6) ^ 2‖ ≤ 2 * t ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖(kap : ℂ) * U‖ = kap * |U| := by rw [norm_mul]; simp [abs_of_pos kap_pos]
    have e2 : ‖(0 + (t : ℂ) * d6) ^ 2‖ = t ^ 2 := by rw [norm_pow, norm_ray ht]
    rw [e1, e2]; linarith only [hkU]
  have hE := Real.exp_pos (-(nu * U * t + t ^ 3 / 3))
  have hp : 0 ≤ t ^ (1 / 2 : ℝ) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hq hp
  have h2 := mul_le_mul_of_nonneg_right h1 hE.le
  nlinarith only [h2]

/-- Tail of the `airy_id1` ray integral. -/
lemma ray1_tail {U R : ℝ} (hR : 1 ≤ R) (hU : ∀ t, R < t → -(t ^ 3 / 6) ≤ nu * U * t) :
    ‖∫ t in Ioi R, ray1 U t‖ ≤ 144 * Real.exp (-(R ^ 3 / 12)) := by
  have := tail_le (f := ray1 U) (R := R) (B := 1) hR zero_le_one (fun t ht => by
    have ht1 : 1 ≤ t := by linarith
    rw [norm_ray1 (by linarith)]
    have e1 : t ^ (1 / 2 : ℝ) ≤ t ^ 3 := by
      calc t ^ (1 / 2 : ℝ) ≤ t ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
        _ = t ^ 3 := by norm_cast
    have e2 : Real.exp (-(nu * U * t + t ^ 3 / 3)) ≤ Real.exp (-(t ^ 3 / 6)) := by
      apply Real.exp_le_exp.mpr
      linarith only [hU t ht]
    calc t ^ (1 / 2 : ℝ) * Real.exp (-(nu * U * t + t ^ 3 / 3)) ≤ t ^ 3 * Real.exp (-(t ^ 3 / 6)) :=
          mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
      _ = 1 * (t ^ 3 * Real.exp (-(t ^ 3 / 6))) := by ring)
  linarith only [this]

/-- Tail of the `airy_id2` ray integral. -/
lemma ray2_tail {U R : ℝ} (hR : 1 ≤ R) (hU : ∀ t, R < t → -(t ^ 3 / 6) ≤ nu * U * t)
    (hkU : kap * |U| ≤ R ^ 2) :
    ‖∫ t in Ioi R, ray2 U t‖ ≤ 288 * Real.exp (-(R ^ 3 / 12)) := by
  have := tail_le (f := ray2 U) (R := R) (B := 2) hR (by norm_num) (fun t ht => by
    have ht1 : 1 ≤ t := by linarith
    have hkt : kap * |U| ≤ t ^ 2 := hkU.trans (by nlinarith only [ht, hR])
    refine (norm_ray2_le (by linarith) hkt).trans ?_
    have e1 : t ^ (1 / 2 : ℝ) * t ^ 2 ≤ t ^ 3 := by
      have : t ^ (1 / 2 : ℝ) ≤ t := by
        calc t ^ (1 / 2 : ℝ) ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
          _ = t := Real.rpow_one t
      nlinarith only [this, ht1]
    have e2 : Real.exp (-(nu * U * t + t ^ 3 / 3)) ≤ Real.exp (-(t ^ 3 / 6)) := by
      apply Real.exp_le_exp.mpr
      linarith only [hU t ht]
    have := mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
    linarith only [this])
  linarith only [this]

/-- `e^{iπ/4} ∫_Γ w^{1/2}e^{iPh_U} = ∫_{ray} ray1 - tail`. -/
lemma intE_csr_ray {R R₀ : ℝ} (hR0 : 0 < R₀) (hR : 0 ≤ R) (hRR : R < R₀) (ch : Chain3 R₀ ((R : ℂ) * d6)) (U : ℝ) :
    Complex.exp (Complex.I * (π / 4 : ℝ)) * ch.intE U csr =
      (∫ t in Ioi (0 : ℝ), ray1 U t) - ∫ t in Ioi R, ray1 U t := by
  have hg : Differentiable ℂ (fun w : ℂ => Complex.exp (Complex.I * PhU U w)) := by
    unfold PhU; fun_prop
  have h1 : ch.intE U csr = (chainA hR hRR).int (fun z => csr z * Complex.exp (Complex.I * PhU U z)) :=
    chain_int_eq_ray hR0 hR hRR ch hg
  rw [h1, chainA_int, integral_split_Ioi (ray1_integrable U) hR]
  have h2 : ∫ t in (0 : ℝ)..R, ray1 U t = Complex.exp (Complex.I * (π / 4 : ℝ)) *
      ∫ t in (0 : ℝ)..R, csr (0 + (t : ℂ) * d6) * Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6)) * d6 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => ray1_eq_line U t)
  rw [← h2]; ring

lemma intE_csrW_ray {R R₀ : ℝ} (hR0 : 0 < R₀) (hR : 0 ≤ R) (hRR : R < R₀) (ch : Chain3 R₀ ((R : ℂ) * d6)) (U : ℝ) :
    Complex.exp (Complex.I * (π / 4 : ℝ)) * ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2)) =
      (∫ t in Ioi (0 : ℝ), ray2 U t) - ∫ t in Ioi R, ray2 U t := by
  have hg : Differentiable ℂ (fun w : ℂ => ((kap : ℂ) * U + w ^ 2) * Complex.exp (Complex.I * PhU U w)) := by
    unfold PhU; fun_prop
  have h1 : ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2)) = (chainA hR hRR).int
      (fun z => csr z * (((kap : ℂ) * U + z ^ 2) * Complex.exp (Complex.I * PhU U z))) := by
    have := chain_int_eq_ray hR0 hR hRR ch hg
    unfold Chain3.intE
    simp only [mul_assoc] at this ⊢
    exact this
  rw [h1, chainA_int, integral_split_Ioi (ray2_integrable U) hR]
  have h2 : ∫ t in (0 : ℝ)..R, ray2 U t = Complex.exp (Complex.I * (π / 4 : ℝ)) *
      ∫ t in (0 : ℝ)..R, csr (0 + (t : ℂ) * d6) * (((kap : ℂ) * U + (0 + (t : ℂ) * d6) ^ 2) *
        Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6))) * d6 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [ray2_eq_line]; ring
  rw [← h2]; ring

/-- **Airy window along a chain (`ct:cfu` Step 3, abstract form).**  With `Q₀ = q₀`, `ψ = ψ`, `Q₁ = i h` real data,
`-(1/√π) Re[e^{iπ/4} ∫_Γ w^{1/2}[1+(s²+a)Q]E e^{iPh_U}]` equals `(1 + c^{-1}C_sub)(-π(AiBi)'(U)) + c^{-2/3} q₀ 2^{-1/3}π AiBi(U)`
with `C_sub = -ψq₀ - (3/2)h`, up to `O(c^{-4/3}(1+|U|)^{1/2}) + O(e^{-R³/12})`. -/
theorem sd_airy {R R₀ ρ0 lam U psi q0 h : ℝ} (ch : Chain3 R₀ ((R : ℂ) * d6)) {a : ℂ} {Q Q' E : ℂ → ℂ}
    {CQ CE CB Cm CU Cend : ℝ}
    (hR0 : 0 < R₀) (hR : 1 ≤ R) (hRR : R < R₀) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hρ : lam * R₀ ≤ ρ0)
    (ha : a = (kap : ℂ) * (lam : ℂ) ^ 2 * (U : ℂ) - (lam : ℂ) ^ 3 * (psi : ℂ))
    (amp : SdAmp lam ρ0 a (q0 : ℂ) (Complex.I * (h : ℂ)) Q Q' E CQ CE CB)
    (hm : MomOK Cm U ch) (hCm : 0 ≤ Cm) (hCU : 0 ≤ CU) (hU : lam * Real.sqrt |U| ≤ CU) (hCend : 0 ≤ Cend)
    (hend : lam ^ 2 * (‖csr ((R : ℂ) * d6)‖ * ‖Q ((lam : ℂ) * ((R : ℂ) * d6)) - (q0 : ℂ)‖ *
      Real.exp (-(PhU U ((R : ℂ) * d6)).im)) ≤ Cend * lam ^ 4)
    (htail : ∀ t, R < t → -(t ^ 3 / 6) ≤ nu * U * t) (hkU : kap * |U| ≤ R ^ 2) :
    |-(1 / √π) * (Complex.exp (Complex.I * (π / 4 : ℝ)) *
        ch.intE U (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) *
          E ((lam : ℂ) * w)))).re -
      ((1 + lam ^ 3 * (-psi * q0 - 3 / 2 * h)) * (-π * (airyAi' U * airyBi U + airyAi U * airyBiDeriv U)) +
        lam ^ 2 * q0 * ((2 : ℝ) ^ (-(1 / 3) : ℝ) * π * (airyAi U * airyBi U)))| ≤
    (1 / √π) * (sdC CQ CE CB Cm CU Cend ρ0 ‖Complex.I * (h : ℂ)‖ ‖(psi : ℂ)‖ * lam ^ 4 * (1 + |U|) ^ (1 / 2 : ℝ) +
      |1 + lam ^ 3 * (-psi * q0 - 3 / 2 * h)| * (144 * Real.exp (-(R ^ 3 / 12))) +
      lam ^ 2 * |q0| * (288 * Real.exp (-(R ^ 3 / 12)))) := by
  have hsd := sd_eval ch hR0 hlam hlam1 hρ ha amp hm hCm hCU hU hCend hend
  set cs : ℝ := 1 + lam ^ 3 * (-psi * q0 - 3 / 2 * h) with hcs
  have hcs' : (1 + (lam : ℂ) ^ 3 * (-((psi : ℂ) * (q0 : ℂ)) + 3 * Complex.I / 2 * (Complex.I * (h : ℂ)))) =
      (cs : ℂ) := by
    rw [hcs]; push_cast
    linear_combination (3 / 2 * (lam : ℂ) ^ 3 * (h : ℂ)) * Complex.I_mul_I
  rw [hcs'] at hsd
  set L := ch.intE U (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) *
    E ((lam : ℂ) * w))) with hL
  set I0 := ch.intE U csr with hI0
  set I2 := ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2)) with hI2
  have hR' : 0 ≤ R := by linarith
  have e1 := intE_csr_ray hR0 hR' hRR ch U
  have e2 := intE_csrW_ray hR0 hR' hRR ch U
  set Iray1 := ∫ t in Ioi (0 : ℝ), ray1 U t with hIray1
  set Iray2 := ∫ t in Ioi (0 : ℝ), ray2 U t with hIray2
  set T1 := ∫ t in Ioi R, ray1 U t with hT1
  set T2 := ∫ t in Ioi R, ray2 U t with hT2
  set ex := Complex.exp (Complex.I * (π / 4 : ℝ)) with hex
  have hexn : ‖ex‖ = 1 := norm_phase_pi4
  have key : ex * L = (cs : ℂ) * (Iray1 - T1) + ((lam ^ 2 * q0 : ℝ) : ℂ) * (Iray2 - T2) +
      ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2)) := by
    push_cast
    linear_combination (cs : ℂ) * e1 + ((lam : ℂ) ^ 2 * (q0 : ℂ)) * e2
  have hre : (ex * L).re = cs * (Iray1.re - T1.re) + lam ^ 2 * q0 * (Iray2.re - T2.re) +
      (ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2))).re := by
    rw [key]
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul]
  have a1 := airy_id1 U
  have a2 := airy_id2 U
  have hq : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hE1 : ‖ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2))‖ ≤
      sdC CQ CE CB Cm CU Cend ρ0 ‖Complex.I * (h : ℂ)‖ ‖(psi : ℂ)‖ * lam ^ 4 * (1 + |U|) ^ (1 / 2 : ℝ) := by
    rw [norm_mul, hexn, one_mul]; exact hsd
  have hr1 : |(ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2))).re| ≤
      sdC CQ CE CB Cm CU Cend ρ0 ‖Complex.I * (h : ℂ)‖ ‖(psi : ℂ)‖ * lam ^ 4 * (1 + |U|) ^ (1 / 2 : ℝ) :=
    (Complex.abs_re_le_norm _).trans hE1
  have hr2 : |T1.re| ≤ 144 * Real.exp (-(R ^ 3 / 12)) :=
    (Complex.abs_re_le_norm _).trans (ray1_tail hR htail)
  have hr3 : |T2.re| ≤ 288 * Real.exp (-(R ^ 3 / 12)) :=
    (Complex.abs_re_le_norm _).trans (ray2_tail hR htail hkU)
  have hmain : -(1 / √π) * (ex * L).re - (cs * (-π * (airyAi' U * airyBi U + airyAi U * airyBiDeriv U)) +
      lam ^ 2 * q0 * ((2 : ℝ) ^ (-(1 / 3) : ℝ) * π * (airyAi U * airyBi U))) =
      (1 / √π) * (cs * T1.re + lam ^ 2 * q0 * T2.re - (ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2))).re) := by
    rw [hre, ← a1, ← a2]
    field_simp
    ring
  rw [hmain, abs_mul, abs_of_pos (by positivity : 0 < 1 / √π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have t1 : |cs * T1.re| ≤ |cs| * (144 * Real.exp (-(R ^ 3 / 12))) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
  have t2 : |lam ^ 2 * q0 * T2.re| ≤ lam ^ 2 * |q0| * (288 * Real.exp (-(R ^ 3 / 12))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ lam ^ 2)]
    exact mul_le_mul_of_nonneg_left hr3 (by positivity)
  calc |cs * T1.re + lam ^ 2 * q0 * T2.re - (ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2))).re|
      ≤ |cs * T1.re + lam ^ 2 * q0 * T2.re| + |(ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2))).re| :=
        abs_sub _ _
    _ ≤ |cs * T1.re| + |lam ^ 2 * q0 * T2.re| + |(ex * (L - ((cs : ℂ) * I0 + (lam : ℂ) ^ 2 * (q0 : ℂ) * I2))).re| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith only [t1, t2, hr1]

/-- info: 'FormalResearch.SignUncertainty.CtSd.sd_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sd_airy

end FormalResearch.SignUncertainty.CtSd
