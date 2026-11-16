module

public import FormalResearch.Complex.HadamardGeneral
public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryZeroOrder
public import FormalResearch.Special.AiryZeros
public import FormalResearch.Special.AiryBridge
public import FormalResearch.Special.AiryPositive

/-!
# The Hadamard product of the Airy function (milestone H5)

Statement formalised (DLMF 9.9.? / Olver, *Asymptotics and Special Functions*, Ch. 11 §§; the Hadamard product of an
entire function of order `3/2` and genus `1`): with `a_n = airyZero (n+1) < 0` the zeros of `Ai` (simple, real, negative),
`Σ_n |a_n|^{-2} < ∞` and for all `z ∈ ℂ`

`Ai(z) = Ai(0) · exp (z Ai'(0)/Ai(0)) · ∏_{n ≥ 1} (1 - z/a_n) exp (z/a_n)`

(`Hadamard.airyAiC_hadamard`), the product converging locally uniformly.  Inputs: the order-`3/2` growth bound
`airyAiC_norm_le_exp_rpow`, the list of zeros `airyZero` (`AiryZeroOrder`; every zero is real and negative by
`airyAiC_zero_real_neg`, simple by Sturm theory `isSol_airyAi`), and `Hadamard.hadamard` with `p = 1`.  The coefficient of
the exponential factor is identified by differentiating at `0` (the logarithmic derivative of the product at `0` vanishes
because `Σ (0/a)^1/(0 - a) = 0`).  **Proved**; not formalised: the numerical value `Ai'(0)/Ai(0) = -3^{1/3} Γ(2/3)/Γ(1/3)`
combined with it (the identification with `AiryValues` is a one-line rewrite not recorded here), `Σ 1/a_n` (conditionally
convergent), the corresponding product for `Ai'`.
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set FormalResearch.Special
open scoped BigOperators Classical

namespace FormalResearch.Hadamard

/-- The zeros `a_n = airyZero (n+1)` (`n ≥ 0`) of `Ai`, as complex numbers. -/
noncomputable def airyA (n : ℕ) : ℂ := ((airyZero (n + 1) : ℝ) : ℂ)

lemma airyA_injective : Function.Injective airyA := by
  intro m n h
  have h' : airyZero (m + 1) = airyZero (n + 1) := Complex.ofReal_injective h
  have hanti : StrictAnti fun k : ℕ => airyZero (k + 1) :=
    strictAnti_nat_of_succ_lt fun k => airyZero_strictAnti (by omega : 1 ≤ k + 1)
  exact hanti.injective h'

lemma airyA_ne_zero (n : ℕ) : airyA n ≠ 0 := by
  have := airyZero_neg (n + 1)
  intro h
  have h' : airyZero (n + 1) = 0 := Complex.ofReal_eq_zero.mp h
  linarith

lemma airyAiC_airyA (n : ℕ) : airyAiC (airyA n) = 0 := by
  rw [airyA, airyAiC_ofReal, airyAi_airyZero]; simp

/-- Every complex zero of `Ai` is some `a_n`. -/
lemma exists_airyA_eq {w : ℂ} (hw : airyAiC w = 0) : ∃ n, airyA n = w := by
  obtain ⟨him, hre⟩ := airyAiC_zero_real_neg hw
  have hwr : w = ((w.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have h0 : airyAi w.re = 0 := by
    have := hw
    rw [hwr, airyAiC_ofReal] at this
    exact_mod_cast this
  obtain ⟨n, hn, hz⟩ := exists_airyZero_eq h0 hre.le
  refine ⟨n - 1, ?_⟩
  rw [airyA, show n - 1 + 1 = n by omega, ← hz, ← hwr]

lemma airyAi_ne_zero_zero : airyAi 0 ≠ 0 := (airyAi_pos le_rfl).ne'

/-- The zeros of `Ai` are simple. -/
lemma analyticOrderNatAt_airyA (n : ℕ) : analyticOrderNatAt airyAiC (airyA n) = 1 := by
  have han : AnalyticAt ℂ airyAiC (airyA n) := differentiable_airyAiC.analyticAt _
  have hd : deriv airyAiC (airyA n) ≠ 0 := by
    rw [airyA, deriv_airyAiC_ofReal]
    have := isSol_airyAi.deriv_ne_zero_of_zero continuous_id ⟨0, airyAi_ne_zero_zero⟩
      (airyAi_airyZero (n + 1))
    exact_mod_cast this
  have := han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (airyAiC_airyA n) hd
  simp [analyticOrderNatAt, this]

/-- The zeros `airyA` form a `Listing` of the zeros of `Ai`. -/
lemma airy_listing : Listing airyAiC airyA := by
  refine ⟨airyA_ne_zero, fun w => ?_, fun w hw => ?_⟩
  · exact (Set.Subsingleton.finite (fun m hm n hn => airyA_injective (hm.trans hn.symm)))
  · by_cases hex : ∃ n, airyA n = w
    · obtain ⟨n, rfl⟩ := hex
      have : airyA ⁻¹' {airyA n} = {n} := by
        ext m; simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => airyA_injective h, fun h => by rw [h]⟩
      rw [this, Set.ncard_singleton, analyticOrderNatAt_airyA]
    · have h1 : airyA ⁻¹' {w} = ∅ := by
        ext m; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        exact fun h => hex ⟨m, h⟩
      have h2 : airyAiC w ≠ 0 := fun h => hex (exists_airyA_eq h)
      have h3 : analyticOrderAt airyAiC w = 0 := by
        rw [analyticOrderAt_eq_zero]; exact Or.inr h2
      rw [h1, Set.ncard_empty]
      simp [analyticOrderNatAt, h3]

lemma airyAiC_growth : GrowthBound airyAiC (3 / 2) := by
  refine ⟨3, fun z => ?_⟩
  refine (airyAiC_norm_le_exp_rpow z).trans ?_
  have hx : 0 ≤ ‖z‖ ^ (3 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  gcongr
  nlinarith

lemma E_one (w : ℂ) : E 1 w = (1 - w) * cexp w := by simp [E, S]

/-- **The Hadamard product of `Ai`.** -/
theorem airyAiC_hadamard :
    Summable (fun n : ℕ => (‖airyA n‖ ^ 2)⁻¹) ∧
    HasProdLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) => (1 - z / airyA n) * cexp (z / airyA n))
      (fun z => ∏' n : ℕ, (1 - z / airyA n) * cexp (z / airyA n)) Set.univ ∧
    ∀ z : ℂ, airyAiC z = (airyAi 0 : ℂ) * cexp (((airyAi' 0 / airyAi 0 : ℝ) : ℂ) * z) *
      ∏' n : ℕ, (1 - z / airyA n) * cexp (z / airyA n) := by
  have h0 : airyAiC 0 ≠ 0 := by
    have := airyAi_ne_zero_zero
    have e : airyAiC 0 = (airyAi 0 : ℂ) := by
      have := airyAiC_ofReal 0
      simpa using this
    rw [e]; exact_mod_cast this
  obtain ⟨h1, h2, c, P, hc, hdeg, hP0, hid⟩ := hadamard (f := airyAiC) differentiable_airyAiC
    ⟨0, h0⟩ (σ := 3 / 2) (by norm_num) airyAiC_growth airy_listing (p := 1) (by norm_num)
  simp only [E_one] at h1 h2 hid
  have hord0 : analyticOrderNatAt airyAiC 0 = 0 := by
    have : analyticOrderAt airyAiC 0 = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr h0
    simp [analyticOrderNatAt, this]
  simp only [hord0, pow_zero, mul_one] at hid
  have hCD : CanonData 1 airyA := ⟨airyA_ne_zero, by simpa using h1⟩
  have hPeval : ∀ z, P.eval z = P.coeff 1 * z := by
    intro z
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    have hc0 : P.coeff 0 = 0 := by simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0
    simp [Finset.sum_range_succ, hc0]
  set Φ : ℂ → ℂ := fun z => ∏' n : ℕ, (1 - z / airyA n) * cexp (z / airyA n) with hΦ
  have hΦE : Φ = canonProd 1 airyA := by
    funext z; simp [hΦ, canonProd, E_one]
  have hΦd : Differentiable ℂ Φ := by rw [hΦE]; exact differentiable_canonProd hCD
  have hΦ0 : Φ 0 = 1 := by simp [hΦ]
  have hΦ'0 : deriv Φ 0 = 0 := by
    have := logDeriv_canonProd hCD (z := 0) (fun i => (airyA_ne_zero i).symm)
    rw [← hΦE, logDeriv_apply, hΦ0, div_one] at this
    rw [this]; simp
  have hc0 : c = airyAi 0 := by
    have := hid 0
    have e : airyAiC 0 = (airyAi 0 : ℂ) := by
      have := airyAiC_ofReal 0
      simpa using this
    rw [e] at this
    simp only [hPeval, mul_zero, Complex.exp_zero, mul_one] at this
    rw [show (∏' i : ℕ, (1 - (0 : ℂ) / airyA i) * cexp ((0 : ℂ) / airyA i)) = 1 from hΦ0,
      mul_one] at this
    exact this.symm
  have hb : P.coeff 1 = ((airyAi' 0 / airyAi 0 : ℝ) : ℂ) := by
    have hfun : airyAiC = fun z => c * cexp (P.coeff 1 * z) * Φ z :=
      funext fun z => by rw [hid z, hPeval]
    have hd : HasDerivAt (fun z : ℂ => c * cexp (P.coeff 1 * z) * Φ z)
        (c * (cexp (P.coeff 1 * 0) * P.coeff 1) * Φ 0 + c * cexp (P.coeff 1 * 0) * deriv Φ 0) 0 := by
      have h1' : HasDerivAt (fun z : ℂ => P.coeff 1 * z) (P.coeff 1) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul (P.coeff 1)
      have h2' := ((h1'.cexp).const_mul c).fun_mul (hΦd 0).hasDerivAt
      simpa using h2'
    have hderiv : deriv airyAiC 0 = c * P.coeff 1 := by
      rw [hfun, hd.deriv]
      simp [hΦ0, hΦ'0]
    have hd0 : deriv airyAiC 0 = (airyAi' 0 : ℂ) := by
      simpa using deriv_airyAiC_ofReal 0
    rw [hd0, hc0] at hderiv
    have hne : (airyAi 0 : ℂ) ≠ 0 := by exact_mod_cast airyAi_ne_zero_zero
    push_cast
    field_simp
    linear_combination -hderiv
  refine ⟨h1, h2, fun z => ?_⟩
  rw [hid z, hc0, hPeval, hb]

/-- info: 'FormalResearch.Hadamard.airyAiC_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.airyAiC_hadamard


/-- info: 'FormalResearch.Hadamard.airyA_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.airyA_injective

/-- info: 'FormalResearch.Hadamard.exists_airyA_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.exists_airyA_eq

/-- info: 'FormalResearch.Hadamard.analyticOrderNatAt_airyA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.analyticOrderNatAt_airyA

/-- info: 'FormalResearch.Hadamard.airy_listing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.airy_listing

/-- info: 'FormalResearch.Hadamard.airyAiC_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.airyAiC_growth

end FormalResearch.Hadamard
