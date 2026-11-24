module

public import FormalResearch.CohnElkies.AirySeedSymbols
public import FormalResearch.CohnElkies.AirySymbolTransfer
public import FormalResearch.Special.AiryBound
public import FormalResearch.Special.LangerHadamard

/-!
# `GT.1` basis seeds: smoothness and Schwartz decay on `[-R, ∞)`

For the three basis seeds `ceF1`, `ceG1 a₁` and `ceG1Deriv a₁'` (with `a₁ = airyZero 1` and
`a₁' = airyDerivFirstZero`) this module proves:

* `seed_contDiff`: each seed is `C^∞` on `ℝ` (`ContDiff ℝ (⊤ : ℕ∞)`);
* `seed_deriv_decay`: for every `k` and `R`, `(1 + |u|)^5 · |∂^k X(u)|` is bounded on `[-R, ∞)`;
* `seed_cutoff_schwartz`: the cut-off seed `u ↦ X(u) χ(u / x₀)` is `C^13` with the Schwartz seminorm
  bounds of `AiryTailSymbolSeed` (`k ≤ 12`).

The route: `dslope F a` is `C^∞` for `C^∞` `F` (Hadamard's lemma, `contDiffAt_dslope`); on `[1, ∞)`
the seeds are products of `Ai`, `Ai'` and `(u - a)⁻¹`, whose derivatives are controlled by
`Ai^{(k)} = p_k Ai + q_k Ai'` with polynomials `p_k, q_k`, the decay bounds of `airyAi_abs_le` and
`airyAi'_abs_le`, and the Leibniz rule. A weight-times-decay estimate then combines the half-line
bound with compactness on `[L, 1]`.

Status: proved, for the `C^∞` reading of `ContDiff ℝ ⊤` (in this Mathlib `⊤ : WithTop ℕ∞` is
analytic; real-analyticity of the seeds is not formalised here). Not formalised: the Gaussian and
Fourier-side estimates of `GT.1`, and the identification of the seeds with the Airy basis of the paper.
-/

@[expose] public section

open Set Filter Topology FormalResearch.Special FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- Exponential decay of rate `c` on `[1, ∞)`, uniformly in the derivative order `k`. -/
abbrev Gt1dDecay (c : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u → |iteratedDeriv k f u| ≤ C * Real.exp (-c * u)

/-- Pointwise smoothness of `f` at every point of `[1, ∞)`. -/
abbrev Gt1dSmoothHalf (f : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, 1 ≤ u → ContDiffAt ℝ (⊤ : ℕ∞) f u

theorem gt1d_smooth_of {f : ℝ → ℝ} (h : ContDiff ℝ (⊤ : ℕ∞) f) : Gt1dSmoothHalf f :=
  fun _ _ => h.contDiffAt
/-- info: 'FormalResearch.SignUncertainty.gt1d_smooth_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_smooth_of


theorem gt1d_cda {f : ℝ → ℝ} (hf : Gt1dSmoothHalf f) {u : ℝ} (hu : 1 ≤ u) (k : ℕ) :
    ContDiffAt ℝ (k : WithTop ℕ∞) f u :=
  (hf u hu).of_le (by exact_mod_cast le_top)
/-- info: 'FormalResearch.SignUncertainty.gt1d_cda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_cda


/-- Hadamard: the difference quotient of a `C^∞` function is `C^∞`. -/
theorem gt1d_contDiff_dslope {F : ℝ → ℝ} (c : ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (dslope F c) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  refine contDiffAt_infty.2 fun n => ?_
  have hF' : ContDiffAt ℝ (n : WithTop ℕ∞) F q := hF.contDiffAt.of_le (by exact_mod_cast le_top)
  by_cases hq : q = c
  · subst hq
    exact contDiffAt_dslope n (hF.contDiffAt.of_le (by exact_mod_cast le_top))
  · have hqc : q - c ≠ 0 := sub_ne_zero.2 hq
    have hfun : slope F c = fun x => (F x - F c) / (x - c) := funext fun x => slope_def_field F c x
    have hev : dslope F c =ᶠ[𝓝 q] slope F c := dslope_eventuallyEq_slope_of_ne F hq
    rw [hfun] at hev
    have hsl : ContDiffAt ℝ (n : WithTop ℕ∞) (fun x => (F x - F c) / (x - c)) q :=
      (hF'.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const) hqc
    exact hsl.congr_of_eventuallyEq hev
/-- info: 'FormalResearch.SignUncertainty.gt1d_contDiff_dslope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_contDiff_dslope


/-- `dslope F a` on `(a, ∞)` is `F(t) (t - a)⁻¹` when `F a = 0`. -/
theorem gt1d_dslope_eq {F : ℝ → ℝ} {a : ℝ} (hF0 : F a = 0) {t : ℝ} (ht : t ∈ Ioi a) :
    dslope F a t = F t * (t - a)⁻¹ := by
  have hat : a < t := ht
  rw [dslope_of_ne F hat.ne', slope_def_field, hF0, sub_zero, div_eq_mul_inv]
/-- info: 'FormalResearch.SignUncertainty.gt1d_dslope_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_dslope_eq


/-- Leibniz-type estimate: `Gt1dDecay` is closed under products, with rates adding. -/
theorem gt1d_dec_mul {c c' : ℝ} {f g : ℝ → ℝ} (hf : Gt1dSmoothHalf f) (hg : Gt1dSmoothHalf g)
    (Hf : Gt1dDecay c f) (Hg : Gt1dDecay c' g) : Gt1dDecay (c + c') (f * g) := by
  intro k
  have Hf' : ∀ i : ℕ, ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u → |iteratedDeriv i f u| ≤ C * Real.exp (-c * u) :=
    Hf
  have Hg' : ∀ i : ℕ, ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u → |iteratedDeriv i g u| ≤ C * Real.exp (-c' * u) :=
    Hg
  choose Cf hCf using Hf'
  choose Cg hCg using Hg'
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Cf i * Cg (k - i)), fun u hu => ?_⟩
  have hu0 : 0 ≤ u := by linarith
  have hexp : Real.exp (-c * u) * Real.exp (-c' * u) = Real.exp (-(c + c') * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [iteratedDeriv_mul (gt1d_cda hf hu k) (gt1d_cda hg hu k)]
  calc |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * iteratedDeriv i f u * iteratedDeriv (k - i) g u|
      ≤ ∑ i ∈ Finset.range (k + 1), |(k.choose i : ℝ) * iteratedDeriv i f u * iteratedDeriv (k - i) g u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Cf i * Cg (k - i)) * Real.exp (-(c + c') * u) :=
        Finset.sum_le_sum fun i _ => by
          have ha := hCf i u hu
          have hb := hCg (k - i) u hu
          have hnn : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          calc |(k.choose i : ℝ) * iteratedDeriv i f u * iteratedDeriv (k - i) g u|
              = (k.choose i : ℝ) * (|iteratedDeriv i f u| * |iteratedDeriv (k - i) g u|) := by
                rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
            _ ≤ (k.choose i : ℝ) * ((Cf i * Real.exp (-c * u)) * (Cg (k - i) * Real.exp (-c' * u))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)) hnn
            _ = (k.choose i : ℝ) * (Cf i * Cg (k - i)) * Real.exp (-(c + c') * u) := by
                rw [← hexp]; ring
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Cf i * Cg (k - i))) * Real.exp (-(c + c') * u) := by
        rw [Finset.sum_mul]
/-- info: 'FormalResearch.SignUncertainty.gt1d_dec_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_dec_mul


/-- Polynomials are bounded by a power on `[1, ∞)`. -/
theorem gt1d_poly_bound (p : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ u → |p.eval u| ≤ C * u ^ p.natDegree := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|, Finset.sum_nonneg fun i _ => abs_nonneg _,
    fun u hu => ?_⟩
  have hu0 : 0 ≤ u := by linarith
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 i)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hi') (abs_nonneg _)
/-- info: 'FormalResearch.SignUncertainty.gt1d_poly_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_poly_bound


/-- Power against exponential: `u^m ≤ (m! / ε^m) e^{ε u}` for `u ≥ 0`. -/
theorem gt1d_pow_le_exp {ε : ℝ} (hε : 0 < ε) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ m ≤ ((m.factorial : ℝ) / ε ^ m) * Real.exp (ε * u) := by
  have h := Real.pow_div_factorial_le_exp (ε * u) (mul_nonneg hε.le hu) m
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hεm : 0 < ε ^ m := pow_pos hε m
  rw [div_le_iff₀ hf] at h
  have h3 : ε ^ m * u ^ m ≤ (m.factorial : ℝ) * Real.exp (ε * u) := by
    rw [← mul_pow]; linarith
  calc u ^ m = (ε ^ m * u ^ m) / ε ^ m := by field_simp
    _ ≤ ((m.factorial : ℝ) * Real.exp (ε * u)) / ε ^ m := by gcongr
    _ = ((m.factorial : ℝ) / ε ^ m) * Real.exp (ε * u) := by ring
/-- info: 'FormalResearch.SignUncertainty.gt1d_pow_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_pow_le_exp


/-- Polynomial-in-`u` derivative bookkeeping: `∂^k Ai = p_k Ai + q_k Ai'`. -/
theorem gt1d_iter_airyAi (k : ℕ) : ∃ p q : Polynomial ℝ, ∀ u : ℝ,
    iteratedDeriv k airyAi u = p.eval u * airyAi u + q.eval u * airyAi' u := by
  induction k with
  | zero => exact ⟨1, 0, fun u => by simp⟩
  | succ k ih =>
    obtain ⟨p, q, hpq⟩ := ih
    refine ⟨Polynomial.derivative p + Polynomial.X * q, p + Polynomial.derivative q, fun u => ?_⟩
    have hfun : iteratedDeriv k airyAi = fun x => p.eval x * airyAi x + q.eval x * airyAi' x :=
      funext hpq
    have hd : HasDerivAt (fun x => p.eval x * airyAi x + q.eval x * airyAi' x) _ u :=
      ((Polynomial.hasDerivAt p u).mul (hasDerivAt_airyAi u)).add
        ((Polynomial.hasDerivAt q u).mul (hasDerivAt_airyAi' u))
    rw [iteratedDeriv_succ, hfun, hd.deriv]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    ring
/-- info: 'FormalResearch.SignUncertainty.gt1d_iter_airyAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_iter_airyAi


/-- Decay of `Ai` on `[1, ∞)` at rate `1/3`, in every derivative order. -/
theorem gt1d_airyAi_dec : Gt1dDecay (1 / 3) airyAi := by
  intro k
  obtain ⟨p, q, hpq⟩ := gt1d_iter_airyAi k
  obtain ⟨Cp, hCp0, hCp⟩ := gt1d_poly_bound p
  obtain ⟨Cq, hCq0, hCq⟩ := gt1d_poly_bound q
  have hK0 : 0 ≤ 1 / (2 * Real.sqrt Real.pi) := by positivity
  have hK1 : 0 ≤ 1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1) := by positivity
  have hsum0 : 0 ≤ Cp * (1 / (2 * Real.sqrt Real.pi)) + Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1)) :=
    add_nonneg (mul_nonneg hCp0 hK0) (mul_nonneg hCq0 hK1)
  refine ⟨(Cp * (1 / (2 * Real.sqrt Real.pi)) + Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1))) *
    (((p.natDegree + q.natDegree + 2).factorial : ℝ) / (1 / 3 : ℝ) ^ (p.natDegree + q.natDegree + 2)), fun u hu => ?_⟩
  have hu0 : 0 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  have hAi : |airyAi u| ≤ 1 / (2 * Real.sqrt Real.pi) * Real.exp (-(2 / 3) * u) := by
    have h := airyAi_abs_le hupos
    have hr : u ^ (-(1 / 4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    have h32 : u ≤ u ^ (3 / 2 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hu (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      simpa using this
    have he : Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) ≤ Real.exp (-(2 / 3) * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hK0' : 0 ≤ 1 / (2 * Real.sqrt Real.pi) := hK0
    calc |airyAi u| ≤ 1 / (2 * Real.sqrt Real.pi) * u ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) := h
      _ ≤ 1 / (2 * Real.sqrt Real.pi) * 1 * Real.exp (-(2 / 3) * u) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr hK0') he (Real.exp_pos _).le (by positivity)
      _ = 1 / (2 * Real.sqrt Real.pi) * Real.exp (-(2 / 3) * u) := by ring
  have hAi' : |airyAi' u| ≤ 1 / (2 * Real.pi) * ((Real.sqrt Real.pi + 1) * u) * Real.exp (-(2 / 3) * u) := by
    have h := airyAi'_abs_le hupos
    have h14 : u ^ (1 / 4 : ℝ) ≤ u := by
      have := Real.rpow_le_rpow_of_exponent_le hu (show (1 / 4 : ℝ) ≤ 1 by norm_num)
      simpa using this
    have hm12 : u ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    have hsum : Real.sqrt Real.pi * u ^ (1 / 4 : ℝ) + u ^ (-(1 / 2) : ℝ) ≤ (Real.sqrt Real.pi + 1) * u := by
      have := mul_le_mul_of_nonneg_left h14 (Real.sqrt_nonneg Real.pi)
      nlinarith
    have h32 : u ≤ u ^ (3 / 2 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hu (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      simpa using this
    have he : Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) ≤ Real.exp (-(2 / 3) * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hpi : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
    calc |airyAi' u| ≤ 1 / (2 * Real.pi) * (Real.sqrt Real.pi * u ^ (1 / 4 : ℝ) + u ^ (-(1 / 2) : ℝ)) *
          Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) := h
      _ ≤ 1 / (2 * Real.pi) * ((Real.sqrt Real.pi + 1) * u) * Real.exp (-(2 / 3) * u) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsum hpi) he (Real.exp_pos _).le
            (mul_nonneg hpi (mul_nonneg (by positivity) hu0))
  set P := p.natDegree + q.natDegree + 2 with hP
  have hpu : |p.eval u| ≤ Cp * u ^ P := (hCp u hu).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu (by omega)) hCp0)
  have hz : u ^ q.natDegree * u ≤ u ^ P := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hu (by omega)
  have hqu : |q.eval u| ≤ Cq * u ^ q.natDegree := hCq u hu
  rw [hpq u]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have t1 : |p.eval u| * |airyAi u| ≤ (Cp * u ^ P) * (1 / (2 * Real.sqrt Real.pi) * Real.exp (-(2 / 3) * u)) :=
    mul_le_mul hpu hAi (abs_nonneg _) (mul_nonneg hCp0 (pow_nonneg hu0 _))
  have t2 : |q.eval u| * |airyAi' u| ≤ (Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1))) * (u ^ P * Real.exp (-(2 / 3) * u)) := by
    calc |q.eval u| * |airyAi' u| ≤ (Cq * u ^ q.natDegree) * (1 / (2 * Real.pi) * ((Real.sqrt Real.pi + 1) * u) * Real.exp (-(2 / 3) * u)) :=
          mul_le_mul hqu hAi' (abs_nonneg _) (mul_nonneg hCq0 (pow_nonneg hu0 _))
      _ = (Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1))) * ((u ^ q.natDegree * u) * Real.exp (-(2 / 3) * u)) := by ring
      _ ≤ (Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1))) * (u ^ P * Real.exp (-(2 / 3) * u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le) (mul_nonneg hCq0 hK1)
  have hpow := gt1d_pow_le_exp (ε := 1 / 3) (by norm_num) P hu0
  have hE : Real.exp (1 / 3 * u) * Real.exp (-(2 / 3) * u) = Real.exp (-(1 / 3) * u) := by
    rw [← Real.exp_add]; ring_nf
  have hfin : u ^ P * Real.exp (-(2 / 3) * u) ≤ ((P.factorial : ℝ) / (1 / 3 : ℝ) ^ P) * Real.exp (-(1 / 3) * u) := by
    calc u ^ P * Real.exp (-(2 / 3) * u)
        ≤ (((P.factorial : ℝ) / (1 / 3 : ℝ) ^ P) * Real.exp (1 / 3 * u)) * Real.exp (-(2 / 3) * u) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = ((P.factorial : ℝ) / (1 / 3 : ℝ) ^ P) * Real.exp (-(1 / 3) * u) := by rw [mul_assoc, hE]
  have hMain : |p.eval u| * |airyAi u| + |q.eval u| * |airyAi' u| ≤
      (Cp * (1 / (2 * Real.sqrt Real.pi)) + Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1))) * (u ^ P * Real.exp (-(2 / 3) * u)) := by
    have e1 : (Cp * u ^ P) * (1 / (2 * Real.sqrt Real.pi) * Real.exp (-(2 / 3) * u)) =
        (Cp * (1 / (2 * Real.sqrt Real.pi))) * (u ^ P * Real.exp (-(2 / 3) * u)) := by ring
    rw [e1] at t1
    nlinarith [t1, t2]
  calc |p.eval u| * |airyAi u| + |q.eval u| * |airyAi' u|
      ≤ (Cp * (1 / (2 * Real.sqrt Real.pi)) + Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1))) * (u ^ P * Real.exp (-(2 / 3) * u)) := hMain
    _ ≤ (Cp * (1 / (2 * Real.sqrt Real.pi)) + Cq * (1 / (2 * Real.pi) * (Real.sqrt Real.pi + 1))) *
          (((P.factorial : ℝ) / (1 / 3 : ℝ) ^ P) * Real.exp (-(1 / 3) * u)) :=
        mul_le_mul_of_nonneg_left hfin hsum0
    _ = _ := by ring
/-- info: 'FormalResearch.SignUncertainty.gt1d_airyAi_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_airyAi_dec


/-- Closed form of the derivatives of `s ↦ (s - a)⁻¹` on `(a, ∞)`. -/
theorem gt1d_iter_inv (a : ℝ) : ∀ k : ℕ, ∀ t : ℝ, a < t →
    iteratedDeriv k (fun s : ℝ => (s - a)⁻¹) t = (-1) ^ k * (k.factorial : ℝ) * ((t - a) ^ (k + 1))⁻¹ := by
  intro k
  induction k with
  | zero => intro t ht; simp
  | succ k ih =>
    intro t ht
    have hev : iteratedDeriv k (fun s : ℝ => (s - a)⁻¹) =ᶠ[𝓝 t]
        fun s => (-1) ^ k * (k.factorial : ℝ) * ((s - a) ^ (k + 1))⁻¹ :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => ih s hs
    have hts : t - a ≠ 0 := sub_ne_zero.2 ht.ne'
    have hp : HasDerivAt (fun s : ℝ => (s - a) ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * (t - a) ^ k) t := by
      have := (hasDerivAt_pow (k + 1) (t - a)).comp_sub_const t a
      simpa using this
    have hi : HasDerivAt (fun s : ℝ => (-1) ^ k * (k.factorial : ℝ) * ((s - a) ^ (k + 1))⁻¹) _ t :=
      (hp.inv (pow_ne_zero _ hts)).const_mul ((-1) ^ k * (k.factorial : ℝ))
    rw [iteratedDeriv_succ, hev.deriv_eq, hi.deriv, Nat.factorial_succ]
    push_cast
    field_simp
    ring
/-- info: 'FormalResearch.SignUncertainty.gt1d_iter_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_iter_inv


/-- The inverse shift `s ↦ (s - a)⁻¹` for `a < 0`: smooth on `[1, ∞)` with bounded derivatives. -/
theorem gt1d_inv_dec {a : ℝ} (ha : a < 0) :
    Gt1dSmoothHalf (fun s : ℝ => (s - a)⁻¹) ∧ Gt1dDecay 0 (fun s : ℝ => (s - a)⁻¹) := by
  refine ⟨fun u hu => ?_, fun k => ⟨(k.factorial : ℝ), fun u hu => ?_⟩⟩
  · have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s - a) u := (contDiff_id.sub contDiff_const).contDiffAt
    exact h.inv (show (0 : ℝ) < u - a by linarith).ne'
  · rw [gt1d_iter_inv a k u (by linarith)]
    rw [neg_zero, zero_mul, Real.exp_zero, mul_one]
    have hpos : 1 ≤ (u - a) ^ (k + 1) := one_le_pow₀ (by linarith)
    have hinv : |((u - a) ^ (k + 1))⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hpos]))]
      exact inv_le_one_of_one_le₀ hpos
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, one_mul]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) hinv
/-- info: 'FormalResearch.SignUncertainty.gt1d_inv_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_inv_dec


theorem gt1d_airyAi_smooth : ContDiff ℝ (⊤ : ℕ∞) airyAi := contDiff_airyAi.of_le le_top
/-- info: 'FormalResearch.SignUncertainty.gt1d_airyAi_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_airyAi_smooth


theorem gt1d_airyAi'_smooth : ContDiff ℝ (⊤ : ℕ∞) airyAi' := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_airyAi' x).differentiableAt, ?_⟩
  have hd : deriv airyAi' = fun x => x * airyAi x := funext fun x => (hasDerivAt_airyAi' x).deriv
  rw [hd]
  exact contDiff_id.mul gt1d_airyAi_smooth
/-- info: 'FormalResearch.SignUncertainty.gt1d_airyAi'_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_airyAi'_smooth


theorem gt1d_airyAi'_dec : Gt1dDecay (1 / 3) airyAi' := by
  intro k
  obtain ⟨C, hC⟩ := gt1d_airyAi_dec (k + 1)
  refine ⟨C, fun u hu => ?_⟩
  have hder : iteratedDeriv k airyAi' = iteratedDeriv (k + 1) airyAi := by
    rw [iteratedDeriv_succ', show deriv airyAi = airyAi' from funext deriv_airyAi]
  rw [hder]
  exact hC u hu
/-- info: 'FormalResearch.SignUncertainty.gt1d_airyAi'_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_airyAi'_dec


/-- Hadamard decay transfer: if `F a = 0` and `F` decays, so does `dslope F a` on `[1, ∞)`. -/
theorem gt1d_dslope_dec {F : ℝ → ℝ} {a r : ℝ} (ha : a < 0) (hFs : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF0 : F a = 0) (hFd : Gt1dDecay r F) : Gt1dDecay r (dslope F a) := by
  obtain ⟨hIs, hId⟩ := gt1d_inv_dec ha
  have hP := gt1d_dec_mul (gt1d_smooth_of hFs) hIs hFd hId
  intro k
  obtain ⟨C, hC⟩ := hP k
  refine ⟨C, fun u hu => ?_⟩
  have hEq : Set.EqOn (dslope F a) (F * fun s : ℝ => (s - a)⁻¹) (Ioi a) :=
    fun t ht => gt1d_dslope_eq hF0 ht
  have hu' : u ∈ Ioi a := by
    show a < u
    linarith
  rw [hEq.iteratedDeriv_of_isOpen isOpen_Ioi k hu']
  have h := hC u hu
  rw [add_zero] at h
  exact h
/-- info: 'FormalResearch.SignUncertainty.gt1d_dslope_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_dslope_dec


/-- The three basis seeds are `C^∞` and have exponential decay on `[1, ∞)`. -/
theorem gt1d_seed_family (X : ℝ → ℝ)
    (hX : X = ceF1 ∨ X = ceG1 (airyZero 1) ∨ X = ceG1Deriv airyDerivFirstZero) :
    ContDiff ℝ (⊤ : ℕ∞) X ∧ ∃ r : ℝ, 0 < r ∧ Gt1dDecay r X := by
  have ha1 : airyZero 1 < 0 := airyZero_neg 1
  have hz1 : airyAi (airyZero 1) = 0 := airyAi_airyZero 1
  obtain ⟨hlt, hneg', hz'⟩ := airyDerivFirstZero_spec
  rcases hX with rfl | rfl | rfl
  · have hDs := gt1d_contDiff_dslope (airyZero 1) gt1d_airyAi_smooth
    have hD := gt1d_dslope_dec ha1 gt1d_airyAi_smooth hz1 gt1d_airyAi_dec
    refine ⟨gt1d_airyAi_smooth.mul hDs, 1 / 3 + 1 / 3, by norm_num, ?_⟩
    exact gt1d_dec_mul (gt1d_smooth_of gt1d_airyAi_smooth) (gt1d_smooth_of hDs) gt1d_airyAi_dec hD
  · have hDs := gt1d_contDiff_dslope (airyZero 1) gt1d_airyAi_smooth
    have hD := gt1d_dslope_dec ha1 gt1d_airyAi_smooth hz1 gt1d_airyAi_dec
    have hsq : ceG1 (airyZero 1) = dslope airyAi (airyZero 1) * dslope airyAi (airyZero 1) :=
      funext fun u => by simp only [ceG1, Pi.mul_apply, sq]
    rw [hsq]
    exact ⟨hDs.mul hDs, 1 / 3 + 1 / 3, by norm_num,
      gt1d_dec_mul (gt1d_smooth_of hDs) (gt1d_smooth_of hDs) hD hD⟩
  · have ha' : airyDerivFirstZero < 0 := hneg'
    have hDs := gt1d_contDiff_dslope airyDerivFirstZero gt1d_airyAi'_smooth
    have hD := gt1d_dslope_dec ha' gt1d_airyAi'_smooth hz' gt1d_airyAi'_dec
    have hsq : ceG1Deriv airyDerivFirstZero =
        dslope airyAi' airyDerivFirstZero * dslope airyAi' airyDerivFirstZero :=
      funext fun u => by simp only [ceG1Deriv, Pi.mul_apply, sq]
    rw [hsq]
    exact ⟨hDs.mul hDs, 1 / 3 + 1 / 3, by norm_num,
      gt1d_dec_mul (gt1d_smooth_of hDs) (gt1d_smooth_of hDs) hD hD⟩
/-- info: 'FormalResearch.SignUncertainty.gt1d_seed_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_seed_family


/-- Weight times decay: `(1 + |u|)^5 |∂^k F(u)|` is bounded on `[L, ∞)` for `L ≤ 1`. -/
theorem gt1d_weight_bound {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) {r : ℝ} (hr : 0 < r)
    (hd : Gt1dDecay r F) {L : ℝ} (hL : L ≤ 1) (k : ℕ) :
    ∃ S : ℝ, ∀ u : ℝ, L ≤ u → (1 + |u|) ^ 5 * |iteratedDeriv k F u| ≤ S := by
  obtain ⟨C, hC⟩ := hd k
  have hcI : Continuous (iteratedDeriv k F) := hF.continuous_iteratedDeriv k (by exact_mod_cast le_top)
  have hg : Continuous (fun u : ℝ => (1 + |u|) ^ 5 * |iteratedDeriv k F u|) := by fun_prop
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := L) (b := 1)).exists_bound_of_continuousOn hg.continuousOn
  have hK0 : 0 ≤ ((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5 :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (half_pos hr).le 5)
  refine ⟨max B (32 * (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * |C|), fun u hu => ?_⟩
  rcases le_total u 1 with hu1 | hu1
  · have hmem : u ∈ Icc L 1 := ⟨hu, hu1⟩
    have hB' := hB u hmem
    simp only [Real.norm_eq_abs] at hB'
    rw [abs_of_nonneg (by positivity)] at hB'
    exact hB'.trans (le_max_left _ _)
  · have hu0 : 0 ≤ u := by linarith
    have h1 : (1 + |u|) ^ 5 ≤ 32 * u ^ 5 := by
      rw [abs_of_nonneg hu0]
      calc (1 + u) ^ 5 ≤ (2 * u) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        _ = 32 * u ^ 5 := by ring
    have h2 : u ^ 5 ≤ (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * Real.exp ((r / 2) * u) :=
      gt1d_pow_le_exp (half_pos hr) 5 hu0
    have h3 : |iteratedDeriv k F u| ≤ |C| * Real.exp (-r * u) :=
      (hC u hu1).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
    have hexp : Real.exp (-r * u) * Real.exp ((r / 2) * u) ≤ 1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by nlinarith)
    have hmain : (1 + |u|) ^ 5 * |iteratedDeriv k F u| ≤
        (32 * (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * |C|) * (Real.exp (-r * u) * Real.exp ((r / 2) * u)) := by
      calc (1 + |u|) ^ 5 * |iteratedDeriv k F u| ≤ (32 * u ^ 5) * (|C| * Real.exp (-r * u)) :=
            mul_le_mul h1 h3 (abs_nonneg _) (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
        _ ≤ (32 * ((((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * Real.exp ((r / 2) * u))) * (|C| * Real.exp (-r * u)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num))
              (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        _ = (32 * (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * |C|) * (Real.exp (-r * u) * Real.exp ((r / 2) * u)) := by
            ring
    have hpos : 0 ≤ 32 * (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * |C| :=
      mul_nonneg (mul_nonneg (by norm_num) hK0) (abs_nonneg _)
    exact (hmain.trans (by
      calc (32 * (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * |C|) * (Real.exp (-r * u) * Real.exp ((r / 2) * u))
          ≤ (32 * (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * |C|) * 1 := mul_le_mul_of_nonneg_left hexp hpos
        _ = 32 * (((Nat.factorial 5 : ℕ) : ℝ) / (r / 2) ^ 5) * |C| := mul_one _)).trans (le_max_right _ _)
/-- info: 'FormalResearch.SignUncertainty.gt1d_weight_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_weight_bound


/-- Complex lift commutes with `iteratedDeriv` for `C^∞` real functions. -/
theorem gt1d_iteratedDeriv_ofReal {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (k : ℕ) :
    iteratedDeriv k (fun t => (F t : ℂ)) = fun t => ((iteratedDeriv k F t : ℝ) : ℂ) := by
  induction k with
  | zero => funext t; simp
  | succ k ih =>
    have hdiff : Differentiable ℝ (iteratedDeriv k F) :=
      hF.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k)
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [iteratedDeriv_succ]
    exact ((hdiff t).hasDerivAt.ofReal_comp).deriv
/-- info: 'FormalResearch.SignUncertainty.gt1d_iteratedDeriv_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.gt1d_iteratedDeriv_ofReal


/-- **Seed smoothness.** Each basis seed is `C^∞` on `ℝ`. -/
theorem seed_contDiff (X : ℝ → ℝ)
    (hX : X = ceF1 ∨ X = ceG1 (airyZero 1) ∨ X = ceG1Deriv airyDerivFirstZero) :
    ContDiff ℝ (⊤ : ℕ∞) X :=
  (gt1d_seed_family X hX).1
/-- info: 'FormalResearch.SignUncertainty.seed_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.seed_contDiff


/-- **Seed decay.** For every derivative order `k` and `R`, `(1 + |u|)^5 |∂^k X(u)|` is bounded
on `[-R, ∞)`. -/
theorem seed_deriv_decay (X : ℝ → ℝ)
    (hX : X = ceF1 ∨ X = ceG1 (airyZero 1) ∨ X = ceG1Deriv airyDerivFirstZero)
    (k : ℕ) (R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, -R ≤ u → (1 + |u|) ^ 5 * ‖iteratedDeriv k X u‖ ≤ C := by
  obtain ⟨hXs, r, hr, hd⟩ := gt1d_seed_family X hX
  obtain ⟨S, hS⟩ := gt1d_weight_bound hXs hr hd (L := min (-R) 1) (min_le_right _ _) k
  refine ⟨max S 0, le_max_right _ _, fun u hu => ?_⟩
  rw [Real.norm_eq_abs]
  exact (hS u ((min_le_left _ _).trans hu)).trans (le_max_left _ _)
/-- info: 'FormalResearch.SignUncertainty.seed_deriv_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.seed_deriv_decay


/-- **Cut-off seed Schwartz bounds.** For `x₀ ≥ 1` and a smooth cut-off `χ`, the seed `X χ(·/x₀)` is
`C^13` and its derivatives of order `≤ 12` satisfy the weighted bound of `AiryTailSymbolSeed`. -/
theorem seed_cutoff_schwartz (X : ℝ → ℝ)
    (hX : X = ceF1 ∨ X = ceG1 (airyZero 1) ∨ X = ceG1Deriv airyDerivFirstZero) (x₀ : ℝ) (hx₀ : 1 ≤ x₀)
    (χ : AiryCutoff) :
    ContDiff ℝ (13 : ℕ) (fun u => (X u : ℂ) * (χ.val (u / x₀) : ℂ)) ∧
    ∃ S : ℝ, ∀ k : ℕ, k ≤ 12 → ∀ u : ℝ,
      (1 + |u|) ^ 5 * ‖iteratedDeriv k (fun t => (X t : ℂ) * (χ.val (t / x₀) : ℂ)) u‖ ≤ S := by
  obtain ⟨hXs, r, hr, hd⟩ := gt1d_seed_family X hX
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => χ.val (t / x₀)) :=
    χ.contDiff.comp (contDiff_id.div_const x₀)
  have hFs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => X t * χ.val (t / x₀)) := hXs.mul hψ
  have hcomp : (fun t : ℝ => (X t : ℂ) * (χ.val (t / x₀) : ℂ)) =
      fun t => ((fun t : ℝ => X t * χ.val (t / x₀)) t : ℂ) := by
    funext t; simp [Complex.ofReal_mul]
  have hC13 : ContDiff ℝ (13 : ℕ) (fun u => (X u : ℂ) * (χ.val (u / x₀) : ℂ)) := by
    rw [hcomp]
    exact (Complex.ofRealCLM.contDiff.comp hFs).of_le (by norm_cast)
  refine ⟨hC13, ?_⟩
  have hFdec : Gt1dDecay r (fun t : ℝ => X t * χ.val (t / x₀)) := by
    intro k
    obtain ⟨C, hC⟩ := hd k
    refine ⟨C, fun u hu => ?_⟩
    have hEq : Set.EqOn (fun t : ℝ => X t * χ.val (t / x₀)) X (Ioi (-x₀)) := fun t ht => by
      have ht' : -x₀ < t := ht
      have h1 : -1 ≤ t / x₀ := by
        rw [le_div_iff₀ (by linarith)]; linarith
      show X t * χ.val (t / x₀) = X t
      rw [χ.eq_one _ h1, mul_one]
    have hu' : u ∈ Ioi (-x₀) := by
      show -x₀ < u
      linarith
    rw [hEq.iteratedDeriv_of_isOpen isOpen_Ioi k hu']
    exact hC u hu
  have hzero : ∀ k : ℕ, ∀ u : ℝ, u < -2 * x₀ →
      iteratedDeriv k (fun t : ℝ => X t * χ.val (t / x₀)) u = 0 := by
    intro k u hu
    have hEq : Set.EqOn (fun t : ℝ => X t * χ.val (t / x₀)) (fun _ => (0 : ℝ)) (Iio (-2 * x₀)) :=
      fun t ht => by
        have ht' : t < -2 * x₀ := ht
        have h1 : t / x₀ ≤ -2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        show X t * χ.val (t / x₀) = 0
        rw [χ.eq_zero _ h1, mul_zero]
    have hu' : u ∈ Iio (-2 * x₀) := hu
    rw [hEq.iteratedDeriv_of_isOpen isOpen_Iio k hu', iteratedDeriv_fun_const_zero]
  have hbd : ∀ k : ℕ, ∃ S : ℝ, ∀ u : ℝ, -2 * x₀ ≤ u →
      (1 + |u|) ^ 5 * |iteratedDeriv k (fun t : ℝ => X t * χ.val (t / x₀)) u| ≤ S :=
    fun k => gt1d_weight_bound hFs hr hFdec (by linarith) k
  choose Sk hSk using hbd
  refine ⟨∑ k ∈ Finset.range 13, max (Sk k) 0, fun k hk u => ?_⟩
  rw [hcomp, gt1d_iteratedDeriv_ofReal hFs k]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hk' : max (Sk k) 0 ≤ ∑ j ∈ Finset.range 13, max (Sk j) 0 :=
    Finset.single_le_sum (f := fun j => max (Sk j) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_range.2 (by omega))
  by_cases hu : -2 * x₀ ≤ u
  · exact ((hSk k u hu).trans (le_max_left _ _)).trans hk'
  · rw [not_le] at hu
    rw [hzero k u hu, abs_zero, mul_zero]
    exact Finset.sum_nonneg fun i _ => le_max_right _ _
/-- info: 'FormalResearch.SignUncertainty.seed_cutoff_schwartz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.seed_cutoff_schwartz

