module

public import FormalResearch.ModularBootstrap.Upper.Hankel.BesselJNat
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Taylor bound for the Bessel kernel against a measure with vanishing moments (`int:repair`)

`CFT/modular_bootstrap/paper/integrality.tex`, Lemma INT-R, proof of part (3), estimate
`int:Hw-eta`.  For a finite signed measure `η` on `[B₀, B]` annihilating all polynomials of degree
`≤ M`, the transform of `η` against the Bessel kernel `φ_t(s) = s^{-p/2} J_p(4π √(t s))` obeys
`|∫ φ_t dη| ≤ ‖η‖ · B₀^{-p/2} (2π √t / √B₀)^m h^m / m!`, `m = M + 1`, `h = (B - B₀)/2`.  This file proves
the Lagrange-remainder estimate for an arbitrary smooth function and the iterated-derivative formula
`∂_s^m [S_p(-c s)] = (-c)^m S_{p+m}(-c s)` for the regularised Bessel series.  **Proved.**
-/

@[expose] public section

open Set Finset MeasureTheory
open scoped Nat

namespace FormalResearch.ModularBootstrap.Integrality

/-- **Lagrange remainder bound** about an arbitrary centre `x₀` (either side). -/
lemma taylor_remainder_bound {f : ℝ → ℝ} (M : ℕ) (hf : ContDiff ℝ (M + 1 : ℕ) f) {x₀ x C : ℝ}
    (hC : ∀ y ∈ uIcc x₀ x, |iteratedDeriv (M + 1) f y| ≤ C) :
    |f x - ∑ k ∈ range (M + 1), iteratedDeriv k f x₀ / (k ! : ℝ) * (x - x₀) ^ k| ≤
      C * |x - x₀| ^ (M + 1) / (M + 1)! := by
  by_cases hx : x₀ = x
  · subst hx
    simp [Finset.sum_range_succ', zero_pow]
  obtain ⟨x', hx', h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := M) hx
    (hf.contDiffOn)
  have hu : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_uIcc hx
  have hxx : x₀ ∈ uIcc x₀ x := left_mem_uIcc
  have hT : taylorWithinEval f M (uIcc x₀ x) x₀ x =
      ∑ k ∈ range (M + 1), iteratedDeriv k f x₀ / (k ! : ℝ) * (x - x₀) ^ k := by
    rw [taylor_within_apply]
    refine sum_congr rfl fun k hk => ?_
    have hkM : (k : ℕ) ≤ M := by simpa [Nat.lt_succ_iff] using hk
    have hcd : ContDiffAt ℝ k f x₀ := (hf.of_le (by exact_mod_cast hkM.trans (Nat.le_succ M))).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hcd hxx, smul_eq_mul]
    ring
  rw [← hT, h, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  have hx'u : x' ∈ uIcc x₀ x := Ioo_subset_Icc_self hx'
  gcongr
  exact hC x' hx'u

/-- **Vanishing moments and a Lagrange bound.**  A finite signed measure `ηp - ηm` supported in
`[s₀ - h, s₀ + h]` and annihilating all polynomials of degree `≤ M` pairs with a smooth `f` at most
`‖η‖ · C h^{M+1}/(M+1)!`, where `C` bounds `|f^{(M+1)}|` on the support. -/
theorem abs_integral_le_of_moments {f : ℝ → ℝ} (M : ℕ) (hf : ContDiff ℝ (M + 1 : ℕ) f)
    {s0 h C : ℝ} (hh : 0 ≤ h)
    (hC : ∀ y ∈ Icc (s0 - h) (s0 + h), |iteratedDeriv (M + 1) f y| ≤ C)
    {ηp ηm : Measure ℝ} [IsFiniteMeasure ηp] [IsFiniteMeasure ηm]
    (hp : ηp (Icc (s0 - h) (s0 + h))ᶜ = 0) (hm : ηm (Icc (s0 - h) (s0 + h))ᶜ = 0)
    (hmom : ∀ P : Polynomial ℝ, P.degree ≤ M → ∫ s, P.eval s ∂ηp = ∫ s, P.eval s ∂ηm) :
    |∫ s, f s ∂ηp - ∫ s, f s ∂ηm| ≤
      (ηp.real univ + ηm.real univ) * (C * h ^ (M + 1) / (M + 1)!) := by
  set a : ℕ → ℝ := fun k => iteratedDeriv k f s0 / (k ! : ℝ) with ha
  set Q : Polynomial ℝ := ∑ k ∈ range (M + 1),
    Polynomial.C (a k) * (Polynomial.X - Polynomial.C s0) ^ k with hQ
  have hQdeg : Q.degree ≤ M := by
    refine (Polynomial.degree_sum_le _ _).trans ?_
    refine Finset.sup_le fun k hk => ?_
    have hk' : k ≤ M := by simpa [Nat.lt_succ_iff] using hk
    have hp1 : (Polynomial.X - Polynomial.C s0 : Polynomial ℝ).degree ≤ 1 :=
      (Polynomial.degree_sub_le _ _).trans (max_le Polynomial.degree_X_le
        (Polynomial.degree_C_le.trans (by norm_num)))
    calc (Polynomial.C (a k) * (Polynomial.X - Polynomial.C s0) ^ k).degree
        ≤ (Polynomial.C (a k)).degree + ((Polynomial.X - Polynomial.C s0) ^ k).degree :=
          Polynomial.degree_mul_le _ _
      _ ≤ 0 + (k : WithBot ℕ) := by
          refine add_le_add Polynomial.degree_C_le ?_
          refine (Polynomial.degree_pow_le _ _).trans ?_
          calc k • (Polynomial.X - Polynomial.C s0 : Polynomial ℝ).degree
              ≤ k • (1 : WithBot ℕ) := nsmul_le_nsmul_right hp1 k
            _ = k := by simp
      _ ≤ M := by simpa using (WithBot.coe_le_coe.2 hk' : (k : WithBot ℕ) ≤ M)
  have hQeval : ∀ x, Q.eval x = ∑ k ∈ range (M + 1), a k * (x - s0) ^ k := by
    intro x; rw [hQ, Polynomial.eval_finsetSum]; simp
  have hI : ∀ (η : Measure ℝ) [IsFiniteMeasure η], η (Icc (s0 - h) (s0 + h))ᶜ = 0 →
      Integrable f η := by
    intro η _ hη
    have hae : ∀ᵐ x ∂η, x ∈ Icc (s0 - h) (s0 + h) := by
      have := measure_eq_zero_iff_ae_notMem.1 hη
      exact this.mono fun x hx => Set.notMem_compl_iff.1 hx
    have h1 : IntegrableOn f (Icc (s0 - h) (s0 + h)) η :=
      (hf.continuous.continuousOn).integrableOn_compact isCompact_Icc
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have hIQ : ∀ (η : Measure ℝ) [IsFiniteMeasure η], η (Icc (s0 - h) (s0 + h))ᶜ = 0 →
      Integrable (fun x => Q.eval x) η := by
    intro η _ hη
    have hae : ∀ᵐ x ∂η, x ∈ Icc (s0 - h) (s0 + h) := by
      have := measure_eq_zero_iff_ae_notMem.1 hη
      exact this.mono fun x hx => Set.notMem_compl_iff.1 hx
    have h1 : IntegrableOn (fun x => Q.eval x) (Icc (s0 - h) (s0 + h)) η :=
      (Q.continuous.continuousOn).integrableOn_compact isCompact_Icc
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC s0 ⟨by linarith, by linarith⟩)
  set E : ℝ := C * h ^ (M + 1) / (M + 1)! with hE
  have hbd : ∀ (η : Measure ℝ) [IsFiniteMeasure η], η (Icc (s0 - h) (s0 + h))ᶜ = 0 →
      ‖∫ s, (f s - Q.eval s) ∂η‖ ≤ E * η.real univ := by
    intro η _ hη
    refine norm_integral_le_of_norm_le_const ?_
    have hae : ∀ᵐ x ∂η, x ∈ Icc (s0 - h) (s0 + h) := by
      have := measure_eq_zero_iff_ae_notMem.1 hη
      exact this.mono fun x hx => Set.notMem_compl_iff.1 hx
    filter_upwards [hae] with x hx
    have hsub : uIcc s0 x ⊆ Icc (s0 - h) (s0 + h) := by
      refine uIcc_subset_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩ hx
    have hr := taylor_remainder_bound M hf (x₀ := s0) (x := x) (C := C)
      (fun y hy => hC y (hsub hy))
    rw [hQeval, Real.norm_eq_abs]
    refine hr.trans ?_
    have hxh : |x - s0| ≤ h := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [hE]
    gcongr
  have hdiff : ∫ s, f s ∂ηp - ∫ s, f s ∂ηm =
      ∫ s, (f s - Q.eval s) ∂ηp - ∫ s, (f s - Q.eval s) ∂ηm := by
    rw [integral_sub (hI ηp hp) (hIQ ηp hp), integral_sub (hI ηm hm) (hIQ ηm hm),
      hmom Q hQdeg]
    ring
  rw [hdiff]
  calc |∫ s, (f s - Q.eval s) ∂ηp - ∫ s, (f s - Q.eval s) ∂ηm|
      ≤ ‖∫ s, (f s - Q.eval s) ∂ηp‖ + ‖∫ s, (f s - Q.eval s) ∂ηm‖ := by
        simpa [Real.norm_eq_abs] using abs_sub (∫ s, (f s - Q.eval s) ∂ηp) (∫ s, (f s - Q.eval s) ∂ηm)
    _ ≤ E * ηp.real univ + E * ηm.real univ := add_le_add (hbd ηp hp) (hbd ηm hm)
    _ = _ := by ring

/-! ### The regularised Bessel series on the real line -/

open FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.WeightAxioms

/-- Real part of the regularised Bessel series `S_q` on the real line. -/
noncomputable def Sre (q : ℕ) (x : ℝ) : ℝ := (besselSC q (x : ℂ)).re

lemma hasDerivAt_Sre (q : ℕ) (x : ℝ) : HasDerivAt (Sre q) (Sre (q + 1) x) x :=
  (hasDerivAt_besselSC q (x : ℂ)).real_of_complex

/-- `∂_s^m [κ S_p(-c s)] = κ (-c)^m S_{p+m}(-c s)`. -/
lemma iteratedDeriv_Sre (κ : ℝ) (p : ℕ) (c : ℝ) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => κ * Sre p (-(c * s))) =
      fun s => κ * ((-c) ^ m * Sre (p + m) (-(c * s))) := by
  induction m with
  | zero => ext s; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    ext s
    have h1 : HasDerivAt (fun s : ℝ => -(c * s)) (-c) s := by
      exact (((hasDerivAt_id s).const_mul (-c)).congr_deriv (by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp)
    have h2 := (hasDerivAt_Sre (p + m) (-(c * s))).comp s h1
    have h3 := h2.const_mul (κ * (-c) ^ m)
    have h4 : HasDerivAt (fun s : ℝ => κ * ((-c) ^ m * Sre (p + m) (-(c * s))))
        (κ * (-c) ^ m * (Sre (p + m + 1) (-(c * s)) * -c)) s := by
      refine h3.congr_deriv rfl |>.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · exact Filter.Eventually.of_forall fun x => by simp [mul_assoc]
      · rfl
    rw [h4.deriv]
    rw [show p + (m + 1) = p + m + 1 by ring, pow_succ]
    ring

lemma contDiff_Sre (κ : ℝ) (p : ℕ) (c : ℝ) (n : ℕ) :
    ContDiff ℝ n (fun s : ℝ => κ * Sre p (-(c * s))) := by
  refine contDiff_of_differentiable_iteratedDeriv (n := (n : ℕ∞)) fun m _ => ?_
  rw [iteratedDeriv_Sre]
  intro s
  have h1 : HasDerivAt (fun s : ℝ => -(c * s)) (-c) s := by
    exact (((hasDerivAt_id s).const_mul (-c)).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  exact (((hasDerivAt_Sre (p + m) (-(c * s))).comp s h1).const_mul ((-c) ^ m)).const_mul κ
    |>.differentiableAt

/-- `|S_q(-c s)| ≤ (√(c s))^{-q}` (from `|J_q| ≤ 1`). -/
lemma abs_Sre_le (q : ℕ) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    |Sre q (-(c * s))| ≤ 1 / (Real.sqrt (c * s)) ^ q := by
  set y : ℝ := 2 * Real.sqrt (c * s) with hy
  have hcs : 0 < c * s := mul_pos hc hs
  have hsq : Real.sqrt (c * s) ^ 2 = c * s := Real.sq_sqrt hcs.le
  have hpos : 0 < Real.sqrt (c * s) := Real.sqrt_pos.2 hcs
  have hJ := besselJ_nat_eq q (y : ℂ)
  have hy2 : -(((y : ℂ)) ^ 2 / 4) = ((-(c * s) : ℝ) : ℂ) := by
    have : (y : ℝ) ^ 2 = 4 * (c * s) := by rw [hy]; nlinarith [hsq]
    have h' : ((y : ℂ)) ^ 2 = ((4 * (c * s) : ℝ) : ℂ) := by exact_mod_cast this
    rw [h']; push_cast; ring
  rw [hy2] at hJ
  have hnorm := norm_besselJ_nat_le_one q y
  rw [hJ, norm_mul, norm_pow] at hnorm
  have hy3 : ‖(y : ℂ) / 2‖ = Real.sqrt (c * s) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by rw [hy]; positivity)]
    simp [hy]
  rw [hy3] at hnorm
  have hS : ‖besselSC q ((-(c * s) : ℝ) : ℂ)‖ ≤ 1 / Real.sqrt (c * s) ^ q := by
    rw [le_div_iff₀ (by positivity)]
    linarith [mul_comm (Real.sqrt (c * s) ^ q) ‖besselSC q ((-(c * s) : ℝ) : ℂ)‖]
  calc |Sre q (-(c * s))| = |(besselSC q ((-(c * s) : ℝ) : ℂ)).re| := rfl
    _ ≤ ‖besselSC q ((-(c * s) : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ _ := hS

/-! ### The Bessel kernel in the paper's form -/

/-- The kernel `s^{-p/2} J_p(4π √(t s))` (`p = w - 1`) of `int:repair`, as a function of `s`. -/
noncomputable def besselKernelR (p : ℕ) (t s : ℝ) : ℝ :=
  (1 / Real.sqrt s) ^ p *
    (Complex.besselJ (p : ℂ) ((4 * Real.pi * Real.sqrt (t * s) : ℝ) : ℂ)).re

lemma besselKernelR_eq (p : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    besselKernelR p t s = (2 * Real.pi * Real.sqrt t) ^ p * Sre p (-(4 * Real.pi ^ 2 * t * s)) := by
  have hk := besselJ_kernel_eq p (s := t) (t := s) ht.le hs
  have hre := congrArg Complex.re hk
  have hD : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ p = (((2 * Real.pi * t) ^ p : ℝ) : ℂ) := by push_cast; rfl
  have hx : (-(4 * (Real.pi : ℂ) ^ 2 * (t : ℂ) * (s : ℂ))) = ((-(4 * Real.pi ^ 2 * t * s) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hD, hx, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
  have hS : (besselSC p ((-(4 * Real.pi ^ 2 * t * s) : ℝ) : ℂ)).re = Sre p (-(4 * Real.pi ^ 2 * t * s)) := rfl
  rw [hS] at hre
  have hst : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have htt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hB : (Real.sqrt (t / s)) ^ p ≠ 0 := by
    have : 0 < Real.sqrt (t / s) := Real.sqrt_pos.2 (div_pos ht hs)
    positivity
  unfold besselKernelR
  have h1 : (1 / Real.sqrt s) ^ p * (Complex.besselJ (p : ℂ) ((4 * Real.pi * Real.sqrt (t * s) : ℝ) : ℂ)).re =
      ((1 / Real.sqrt s) ^ p / (Real.sqrt (t / s)) ^ p) *
        ((Real.sqrt (t / s)) ^ p * (Complex.besselJ (p : ℂ) ((4 * Real.pi * Real.sqrt (t * s) : ℝ) : ℂ)).re) := by
    field_simp
  rw [h1, hre]
  have h2 : (1 / Real.sqrt s) ^ p / (Real.sqrt (t / s)) ^ p * (2 * Real.pi * t) ^ p =
      (2 * Real.pi * Real.sqrt t) ^ p := by
    rw [← div_pow, ← mul_pow]
    congr 1
    rw [Real.sqrt_div ht.le]
    have htt' : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    field_simp
    nlinarith [htt']
  rw [← mul_assoc, h2]

/-- Algebraic identity used for the constant in `hankelDual_bound`. -/
lemma kernel_const_eq (u b : ℝ) (hu : u ≠ 0) (hb : b ≠ 0) (p M : ℕ) :
    u ^ p * (u ^ 2) ^ (M + 1) / (u * b) ^ (p + (M + 1)) = (1 / b) ^ p * (u / b) ^ (M + 1) := by
  have h1 : (u * b) ^ (p + (M + 1)) = u ^ p * u ^ (M + 1) * (b ^ p * b ^ (M + 1)) := by
    rw [mul_pow, pow_add, pow_add]; ring
  have h2 : (u ^ 2) ^ (M + 1) = u ^ (M + 1) * u ^ (M + 1) := by rw [← pow_mul, ← pow_add]; ring_nf
  rw [h1, h2, one_div, inv_pow, div_pow]
  have : u ^ p ≠ 0 := pow_ne_zero _ hu
  have : u ^ (M + 1) ≠ 0 := pow_ne_zero _ hu
  have : b ^ p ≠ 0 := pow_ne_zero _ hb
  have : b ^ (M + 1) ≠ 0 := pow_ne_zero _ hb
  field_simp

/-- **Estimate `int:Hw-eta`** (Taylor part of Lemma INT-R).  For a finite signed measure
`η = ηp - ηm` on `[B₀, B]` annihilating all polynomials of degree `≤ M`, with `m = M + 1` and
`h = (B - B₀)/2`,
`|∫ φ_t dη| ≤ ‖η‖_{TV} · B₀^{-p/2} (2π √t/√B₀)^m h^m / m!`, where `‖η‖_{TV} ≤ ηp(ℝ) + ηm(ℝ)` and
`φ_t(s) = s^{-p/2} J_p(4π √(t s))`, `p = w - 1`. -/
theorem hankelDual_bound (p : ℕ) {t B0 B : ℝ} (ht : 0 < t) (hB0 : 0 < B0) (hB : B0 ≤ B) (M : ℕ)
    {ηp ηm : Measure ℝ} [IsFiniteMeasure ηp] [IsFiniteMeasure ηm]
    (hp : ηp (Icc B0 B)ᶜ = 0) (hm : ηm (Icc B0 B)ᶜ = 0)
    (hmom : ∀ P : Polynomial ℝ, P.degree ≤ M → ∫ s, P.eval s ∂ηp = ∫ s, P.eval s ∂ηm) :
    |∫ s, besselKernelR p t s ∂ηp - ∫ s, besselKernelR p t s ∂ηm| ≤
      (ηp.real univ + ηm.real univ) * ((1 / Real.sqrt B0) ^ p *
        ((2 * Real.pi * Real.sqrt t / Real.sqrt B0) ^ (M + 1) *
          ((B - B0) / 2) ^ (M + 1) / (M + 1)!)) := by
  set u : ℝ := 2 * Real.pi * Real.sqrt t with hu
  have hupos : 0 < u := by rw [hu]; positivity [Real.pi_pos, Real.sqrt_pos.2 ht]
  have hu2 : u ^ 2 = 4 * Real.pi ^ 2 * t := by
    rw [hu, mul_pow, mul_pow, Real.sq_sqrt ht.le]; ring
  set b : ℝ := Real.sqrt B0 with hb
  have hbpos : 0 < b := Real.sqrt_pos.2 hB0
  set f : ℝ → ℝ := fun s => u ^ p * Sre p (-(u ^ 2 * s)) with hf
  have hKf : ∀ s, 0 < s → besselKernelR p t s = f s := by
    intro s hs
    rw [besselKernelR_eq p ht hs, hf]
    simp only
    rw [← hu2]
  have hae : ∀ (η : Measure ℝ), η (Icc B0 B)ᶜ = 0 → ∀ᵐ s ∂η, besselKernelR p t s = f s := by
    intro η hη
    have := measure_eq_zero_iff_ae_notMem.1 hη
    filter_upwards [this] with s hs
    exact hKf s (lt_of_lt_of_le hB0 (Set.notMem_compl_iff.1 hs).1)
  rw [integral_congr_ae (hae ηp hp), integral_congr_ae (hae ηm hm)]
  set s0 : ℝ := (B0 + B) / 2 with hs0
  set h : ℝ := (B - B0) / 2 with hh
  have hIcc : Icc (s0 - h) (s0 + h) = Icc B0 B := by
    rw [hs0, hh]; congr 1 <;> ring
  set C : ℝ := u ^ p * (u ^ 2) ^ (M + 1) / (u * b) ^ (p + (M + 1)) with hC
  have hfd : ContDiff ℝ (M + 1 : ℕ) f := contDiff_Sre (u ^ p) p (u ^ 2) (M + 1)
  have hbound : ∀ y ∈ Icc (s0 - h) (s0 + h), |iteratedDeriv (M + 1) f y| ≤ C := by
    intro y hy
    rw [hIcc] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hB0 hy.1
    rw [hf, iteratedDeriv_Sre]
    simp only
    have h1 := abs_Sre_le (p + (M + 1)) (c := u ^ 2) (s := y) (by positivity) hy0
    have hsq : Real.sqrt (u ^ 2 * y) = u * Real.sqrt y := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hupos.le]
    have hsq0 : Real.sqrt (u ^ 2 * B0) = u * b := by
      rw [hb, Real.sqrt_mul (by positivity), Real.sqrt_sq hupos.le]
    rw [hsq] at h1
    have hyB : b ≤ Real.sqrt y := Real.sqrt_le_sqrt hy.1
    have h2 : 1 / (u * Real.sqrt y) ^ (p + (M + 1)) ≤ 1 / (u * b) ^ (p + (M + 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    calc |u ^ p * ((-u ^ 2) ^ (M + 1) * Sre (p + (M + 1)) (-(u ^ 2 * y)))|
        = u ^ p * ((u ^ 2) ^ (M + 1) * |Sre (p + (M + 1)) (-(u ^ 2 * y))|) := by
          simp only [abs_mul, abs_pow, abs_neg, abs_of_pos hupos]
      _ ≤ u ^ p * ((u ^ 2) ^ (M + 1) * (1 / (u * b) ^ (p + (M + 1)))) := by
          gcongr
          exact h1.trans h2
      _ = C := by rw [hC]; ring
  have key := abs_integral_le_of_moments M hfd (s0 := s0) (h := h) (C := C)
    (by rw [hh]; linarith) hbound (ηp := ηp) (ηm := ηm) (by rwa [hIcc]) (by rwa [hIcc]) hmom
  refine key.trans (le_of_eq ?_)
  have hCeq : C = (1 / b) ^ p * (u / b) ^ (M + 1) := by
    rw [hC]; exact kernel_const_eq u b hupos.ne' hbpos.ne' p M
  rw [hCeq]
  ring

/-- info: 'FormalResearch.ModularBootstrap.Integrality.hankelDual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelDual_bound

end FormalResearch.ModularBootstrap.Integrality
