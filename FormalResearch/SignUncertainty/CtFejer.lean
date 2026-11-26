module

public import Mathlib

/-!
# `ct:fejer`: the finite Fejér inequality

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, eq. `ct:fejer` (proof of `ct:boas`).  **Proved.**
If `g ∈ L¹(ℝ)` is real, `ω > 0`, `φ ∈ ℝ`, `n ≥ 2`, then
`∫ g(x)[1 + 2cos(ωx+φ)] dx ≥ -n‖g_-‖₁ - (2/n)‖g‖₁ - 2∑_{k=2}^{n-1} |ĝ(kω)|`, `ĝ(ν) = ∫ g(x) e^{-iνx} dx`.
The Fejér polynomial `n^{-1}|∑_{j<n} e^{ijθ}|²` lies in `[0,n]` with Fourier coefficients `1 - |k|/n`.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped Real

namespace FormalResearch.SignUncertainty.CtFejer

/-- The Fejér double sum `∑_{j,l<n} cos((j-l)θ)`. -/
noncomputable def fejerS (n : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ range n, ∑ l ∈ range n, Real.cos (((j : ℝ) - l) * θ)

lemma fejerS_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ fejerS n θ := by
  have : fejerS n θ = (∑ j ∈ range n, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range n, Real.sin (j * θ)) ^ 2 := by
    unfold fejerS
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sub_mul, Real.cos_sub]
  rw [this]; positivity

lemma fejerS_le (n : ℕ) (θ : ℝ) : fejerS n θ ≤ (n : ℝ) ^ 2 := by
  unfold fejerS
  calc ∑ j ∈ range n, ∑ l ∈ range n, Real.cos (((j : ℝ) - l) * θ) ≤ ∑ j ∈ range n, ∑ l ∈ range n, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => Real.cos_le_one _
    _ = (n : ℝ) ^ 2 := by simp [sq]

/-- Fourier expansion of the Fejér double sum. -/
lemma fejerS_expand (n : ℕ) (θ : ℝ) :
    fejerS n θ = 2 * ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos (k * θ) - n := by
  induction n with
  | zero => simp [fejerS]
  | succ n ih =>
    have hcast : ∀ j : ℕ, j < n → ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j := fun j hj => by
      rw [show n - 1 - j = n - (j + 1) by omega, Nat.cast_sub (by omega)]
      push_cast; ring
    have h1 : ∑ j ∈ range n, Real.cos (((j : ℝ) - n) * θ) = ∑ k ∈ range n, Real.cos (((k : ℝ) + 1) * θ) := by
      rw [← Finset.sum_range_reflect (fun k => Real.cos (((k : ℝ) + 1) * θ)) n]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hcast j (Finset.mem_range.1 hj), ← Real.cos_neg]
      congr 1; ring
    have h2 : ∑ l ∈ range n, Real.cos (((n : ℝ) - l) * θ) = ∑ k ∈ range n, Real.cos (((k : ℝ) + 1) * θ) := by
      rw [← Finset.sum_range_reflect (fun k => Real.cos (((k : ℝ) + 1) * θ)) n]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hcast j (Finset.mem_range.1 hj)]
      congr 1; ring
    have h3 : ∑ k ∈ range (n + 1), Real.cos (k * θ) = 1 + ∑ k ∈ range n, Real.cos (((k : ℝ) + 1) * θ) := by
      rw [Finset.sum_range_succ']
      simp
      ring
    have e1 : fejerS (n + 1) θ = fejerS n θ + 2 * ∑ k ∈ range (n + 1), Real.cos (k * θ) - 1 := by
      have hin : ∀ j : ℕ, ∑ l ∈ range (n + 1), Real.cos (((j : ℝ) - l) * θ) =
          ∑ l ∈ range n, Real.cos (((j : ℝ) - l) * θ) + Real.cos (((j : ℝ) - n) * θ) := fun j =>
        Finset.sum_range_succ _ n
      unfold fejerS
      rw [Finset.sum_range_succ (fun j : ℕ => ∑ l ∈ range (n + 1), Real.cos (((j : ℝ) - l) * θ)) n]
      simp only [hin]
      rw [Finset.sum_add_distrib]
      simp only [sub_self, zero_mul, Real.cos_zero]
      rw [h1, h2, h3]
      ring
    have e2 : ∑ k ∈ range (n + 1), (((n + 1 : ℕ) : ℝ) - k) * Real.cos (k * θ) =
        ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos (k * θ) + ∑ k ∈ range (n + 1), Real.cos (k * θ) := by
      rw [Finset.sum_range_succ _ n, Finset.sum_range_succ (fun k : ℕ => Real.cos (k * θ)) n]
      have : ∑ k ∈ range n, (((n + 1 : ℕ) : ℝ) - k) * Real.cos (k * θ) =
          ∑ k ∈ range n, ((n : ℝ) - k) * Real.cos (k * θ) + ∑ k ∈ range n, Real.cos (k * θ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast; ring
      rw [this]
      push_cast
      ring
    rw [e1, ih, e2]
    push_cast
    ring

lemma sum_range_split {n : ℕ} (hn : 2 ≤ n) (f : ℕ → ℝ) :
    ∑ k ∈ range n, f k = f 0 + f 1 + ∑ k ∈ Ico 2 n, f k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Finset.sum_Ico_eq_sum_range, show m + 2 - 2 = m by omega, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ x : ℕ, 2 + x = x + 1 + 1 := fun x => by ring
  simp only [h]
  ring

/-- The Fourier-Fejér identity `1 + 2cos θ = S_n/n + (2/n) cos θ - 2∑_{k=2}^{n-1}(1-k/n)cos kθ`. -/
lemma fejer_identity {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    1 + 2 * Real.cos θ = fejerS n θ / n + (2 / n) * Real.cos θ -
      2 * ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * Real.cos (k * θ) := by
  have hn0 : (0 : ℝ) < n := by positivity
  rw [fejerS_expand, sum_range_split hn (fun k => ((n : ℝ) - k) * Real.cos (k * θ))]
  simp only [Nat.cast_zero, sub_zero, zero_mul, Real.cos_zero, mul_one, Nat.cast_one, one_mul]
  have : ∑ k ∈ Ico 2 n, ((n : ℝ) - k) * Real.cos (k * θ) =
      n * ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * Real.cos (k * θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [this]
  generalize ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * Real.cos (k * θ) = Sg
  field_simp
  ring

/-- The Fourier transform `ĝ(ν) = ∫ g(x) e^{-iνx} dx` of a real function. -/
noncomputable def fhat (g : ℝ → ℝ) (ν : ℝ) : ℂ :=
  ∫ x, (g x : ℂ) * Complex.exp (-(Complex.I * (ν : ℂ) * (x : ℂ)))

lemma int_mul_cont {g : ℝ → ℝ} (hg : Integrable g) {w : ℝ → ℝ} (hw : Continuous w) {C : ℝ}
    (hC : ∀ x, |w x| ≤ C) : Integrable (fun x => g x * w x) := by
  refine (hg.norm.mul_const C).mono' (hg.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma cos_harmonic_bound {g : ℝ → ℝ} (hg : Integrable g) (k : ℕ) (ω φ : ℝ) :
    |∫ x, g x * Real.cos (k * (ω * x + φ))| ≤ ‖fhat g (k * ω)‖ := by
  set h : ℝ → ℂ := fun x => (g x : ℂ) * Complex.exp (Complex.I * ((k * (ω * x + φ) : ℝ) : ℂ)) with hh
  have hint : Integrable h := by
    refine hg.norm.mono' ?_ (ae_of_all _ fun x => ?_)
    · refine (Complex.measurable_ofReal.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable.mul ?_
      exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · simp only [hh, norm_mul, Complex.norm_real]
      rw [show Complex.I * ((k * (ω * x + φ) : ℝ) : ℂ) = ((k * (ω * x + φ) : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  have hre : ∫ x, g x * Real.cos (k * (ω * x + φ)) = (∫ x, h x).re := by
    have h1 := integral_re hint
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hh]
    rw [Complex.re_ofReal_mul,
      show Complex.I * ((k * (ω * x + φ) : ℝ) : ℂ) = ((k * (ω * x + φ) : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I_re]
  have hJ : ∫ x, h x = Complex.exp (Complex.I * ((k * φ : ℝ) : ℂ)) * starRingEnd ℂ (fhat g (k * ω)) := by
    unfold fhat
    rw [← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hh]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [hJ, norm_mul, show Complex.I * ((k * φ : ℝ) : ℂ) = ((k * φ : ℝ) : ℂ) * Complex.I by ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  simp

lemma continuous_fejerS (n : ℕ) : Continuous (fun θ => fejerS n θ) := by
  unfold fejerS
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ => by fun_prop

/-- **ct:fejer.** For integrable `g`, `n ≥ 2` and any `ω, φ`,
`∫ g (1 + 2 cos(ωx+φ)) ≥ −n ∫ g₋ − (2/n) ∫ |g| − 2 Σ_{2≤k<n} |ĝ(kω)|`. -/
theorem ct_fejer {g : ℝ → ℝ} (hg : Integrable g) {n : ℕ} (hn : 2 ≤ n) (ω φ : ℝ) :
    -((n : ℝ) * ∫ x, max (-g x) 0) - (2 / n) * (∫ x, |g x|)
        - 2 * ∑ k ∈ Ico 2 n, ‖fhat g (k * ω)‖
      ≤ ∫ x, g x * (1 + 2 * Real.cos (ω * x + φ)) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hθ : ∀ x, g x * (1 + 2 * Real.cos (ω * x + φ)) =
      g x * (fejerS n (ω * x + φ) / n) + (2 / n) * (g x * Real.cos (ω * x + φ))
        - 2 * ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * (g x * Real.cos (k * (ω * x + φ))) := by
    intro x
    rw [fejer_identity hn (ω * x + φ), mul_sub, mul_add]
    have h2 : g x * (2 * ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * Real.cos (k * (ω * x + φ))) =
        2 * ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * (g x * Real.cos (k * (ω * x + φ))) := by
      rw [mul_left_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h2]; ring
  have hcont : Continuous (fun x : ℝ => fejerS n (ω * x + φ) / n) :=
    ((continuous_fejerS n).comp (by fun_prop)).div_const _
  have i1 : Integrable (fun x => g x * (fejerS n (ω * x + φ) / n)) :=
    int_mul_cont hg hcont (C := n) fun x => by
      rw [abs_of_nonneg (div_nonneg (fejerS_nonneg _ _) hn0.le), div_le_iff₀ hn0]
      have := fejerS_le n (ω * x + φ)
      nlinarith
  have i2 : Integrable (fun x => g x * Real.cos (ω * x + φ)) :=
    int_mul_cont hg (by fun_prop) (C := 1) fun x => Real.abs_cos_le_one _
  have i3 : ∀ k : ℕ, Integrable (fun x => g x * Real.cos (k * (ω * x + φ))) := fun k =>
    int_mul_cont hg (by fun_prop) (C := 1) fun x => Real.abs_cos_le_one _
  have i3s : Integrable (fun x => ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * (g x * Real.cos (k * (ω * x + φ)))) :=
    integrable_finsetSum _ fun k _ => (i3 k).const_mul _
  have hmax : Integrable (fun x => max (-g x) 0) := hg.neg.pos_part
  -- A
  have hA : -((n : ℝ) * ∫ x, max (-g x) 0) ≤ ∫ x, g x * (fejerS n (ω * x + φ) / n) := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_mono (hmax.const_mul _).neg i1 fun x => ?_
    simp only
    have h0 : 0 ≤ fejerS n (ω * x + φ) / n := div_nonneg (fejerS_nonneg _ _) hn0.le
    have h1 : fejerS n (ω * x + φ) / n ≤ n := by
      rw [div_le_iff₀ hn0]; have := fejerS_le n (ω * x + φ); nlinarith
    rcases le_total 0 (g x) with hgx | hgx
    · have : max (-g x) 0 = 0 := max_eq_right (by linarith)
      rw [this]; nlinarith
    · have : max (-g x) 0 = -g x := max_eq_left (by linarith)
      rw [this]; nlinarith
  -- B
  have hB : -(∫ x, |g x|) ≤ ∫ x, g x * Real.cos (ω * x + φ) := by
    have := norm_integral_le_of_norm_le hg.norm (μ := volume) (f := fun x => g x * Real.cos (ω * x + φ))
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    have h2 := neg_abs_le (∫ x, g x * Real.cos (ω * x + φ))
    rw [Real.norm_eq_abs] at this
    simp only [Real.norm_eq_abs] at this
    linarith
  -- C
  have hC : ∫ x, ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * (g x * Real.cos (k * (ω * x + φ)))
      ≤ ∑ k ∈ Ico 2 n, ‖fhat g (k * ω)‖ := by
    rw [integral_finsetSum _ fun k _ => (i3 k).const_mul _]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [integral_const_mul]
    have hk' := Finset.mem_Ico.mp hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk'.2.le
    have h0 : 0 ≤ 1 - (k : ℝ) / n := by
      rw [sub_nonneg, div_le_one hn0]; exact hkn
    have h1 : 1 - (k : ℝ) / n ≤ 1 := by
      have : 0 ≤ (k : ℝ) / n := by positivity
      linarith
    calc (1 - (k : ℝ) / n) * ∫ x, g x * Real.cos (k * (ω * x + φ))
        ≤ (1 - (k : ℝ) / n) * ‖fhat g (k * ω)‖ :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans (cos_harmonic_bound hg k ω φ)) h0
      _ ≤ 1 * ‖fhat g (k * ω)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := one_mul _
  have hint : ∫ x, g x * (1 + 2 * Real.cos (ω * x + φ)) =
      (∫ x, g x * (fejerS n (ω * x + φ) / n)) + (2 / n) * (∫ x, g x * Real.cos (ω * x + φ))
        - 2 * ∫ x, ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * (g x * Real.cos (k * (ω * x + φ))) := by
    rw [show (fun x => g x * (1 + 2 * Real.cos (ω * x + φ))) = _ from funext hθ]
    have hsum : Integrable (fun x => g x * (fejerS n (ω * x + φ) / n) +
        (2 / n) * (g x * Real.cos (ω * x + φ))) := i1.add (i2.const_mul _)
    rw [integral_sub hsum (i3s.const_mul 2), integral_add i1 (i2.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hint]
  have hn2 : 0 ≤ 2 / (n : ℝ) := by positivity
  have hB' := mul_le_mul_of_nonneg_left hB hn2
  generalize (∫ x, g x * (fejerS n (ω * x + φ) / n)) = I1 at *
  generalize (∫ x, g x * Real.cos (ω * x + φ)) = Bc at *
  generalize (∫ x, ∑ k ∈ Ico 2 n, (1 - (k : ℝ) / n) * (g x * Real.cos (k * (ω * x + φ)))) = C at *
  generalize (∫ x, |g x|) = A at *
  generalize (∫ x, max (-g x) 0) = M at *
  generalize (∑ k ∈ Ico 2 n, ‖fhat g (k * ω)‖) = S at *
  generalize (2 / (n : ℝ)) = q at *
  linarith

/-- info: 'FormalResearch.SignUncertainty.CtFejer.fejer_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fejer_identity

/-- info: 'FormalResearch.SignUncertainty.CtFejer.ct_fejer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_fejer

end FormalResearch.SignUncertainty.CtFejer
