module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Abel summation for slowly modulated oscillating sums (Airy-free, chain-free)

`rko_abel`: let `f_i` be real weights and `Φ_i` real phases whose increments `Δ_i = Φ_{i+1} - Φ_i` stay away from `0 (mod 2π)`
(`2|sin(Δ_i/2)| ≥ ε`, i.e. `|e^{iΔ_i} - 1| ≥ ε`) and change slowly (`|Δ_{i+1} - Δ_i| ≤ D`), with `|f_i| ≤ F`, `|f_{i+1} - f_i| ≤ F'`.  Then

`|Σ_{i<n} f_i cos Φ_i| ≤ 2F/ε + 2n(F'/ε + F D/ε²)`.

Proof: `z_i = e^{iΦ_i}`, `f_i z_i = u_i (z_{i+1} - z_i)` with `u_i = f_i/(e^{iΔ_i} - 1)`, summation by parts (`Finset.sum_range_by_parts`), `|z_i - z_0| ≤ 2`,
`|e^{iy} - e^{ix}| ≤ |y - x|`.  For `n` sites of a lattice of mesh `h` with `F' = O(h)`, `D = O(h)` and `n h = O(1)` the bound is `O(1)`, i.e. the oscillating part of
`Σ w² cos²` is negligible against the main term `~ 1/h`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Complex

namespace FormalResearch.Special

/-- The summation-by-parts bound (see the module docstring). -/
theorem rko_abel (f Φ : ℕ → ℝ) (n : ℕ) {F F' D ε : ℝ} (hε : 0 < ε) (hF0 : 0 ≤ F) (hF'0 : 0 ≤ F') (hD0 : 0 ≤ D) (hF : ∀ i < n, |f i| ≤ F)
    (hF' : ∀ i, i + 1 < n → |f (i + 1) - f i| ≤ F') (hs : ∀ i < n, ε ≤ 2 * |Real.sin ((Φ (i + 1) - Φ i) / 2)|)
    (hD : ∀ i, i + 1 < n → |(Φ (i + 2) - Φ (i + 1)) - (Φ (i + 1) - Φ i)| ≤ D) :
    |∑ i ∈ range n, f i * Real.cos (Φ i)| ≤ 2 * F / ε + 2 * n * (F' / ε + F * D / ε ^ 2) := by
  set a : ℕ → ℂ := fun i => Complex.exp (Complex.I * ((Φ (i + 1) - Φ i : ℝ) : ℂ)) - 1 with ha
  set z : ℕ → ℂ := fun i => Complex.exp (Complex.I * ((Φ i : ℝ) : ℂ)) with hz
  set u : ℕ → ℂ := fun i => ((f i : ℝ) : ℂ) * (a i)⁻¹ with hu
  have hna : ∀ i < n, ε ≤ ‖a i‖ := by
    intro i hi
    have h1 : ‖a i‖ = ‖2 * Real.sin ((Φ (i + 1) - Φ i) / 2)‖ := Complex.norm_exp_I_mul_ofReal_sub_one _
    rw [h1, Real.norm_eq_abs, abs_mul, abs_two]
    exact hs i hi
  have hnz : ∀ i, ‖z i‖ = 1 := fun i => by
    rw [hz]; simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; simp
  have hstep : ∀ i < n, ((f i : ℝ) : ℂ) * z i = u i * (z (i + 1) - z i) := by
    intro i hi
    have hai : a i ≠ 0 := by
      intro h0; have := hna i hi; rw [h0] at this; simp at this; linarith
    have hzi : z (i + 1) = z i * Complex.exp (Complex.I * ((Φ (i + 1) - Φ i : ℝ) : ℂ)) := by
      rw [hz]; simp only; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have : z (i + 1) - z i = z i * a i := by rw [hzi, ha]; simp only; ring
    rw [this, hu]; simp only; field_simp
  have hsum : ∑ i ∈ range n, ((f i : ℝ) : ℂ) * z i = ∑ i ∈ range n, u i * (z (i + 1) - z i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact hstep i (Finset.mem_range.1 hi)
  have hbp := Finset.sum_range_by_parts u (fun i => z (i + 1) - z i) n
  have hG : ∀ k, ∑ i ∈ range k, (z (i + 1) - z i) = z k - z 0 := fun k => Finset.sum_range_sub z k
  simp only [hG, smul_eq_mul] at hbp
  have hzd : ∀ k, ‖z k - z 0‖ ≤ 2 := fun k => by
    calc ‖z k - z 0‖ ≤ ‖z k‖ + ‖z 0‖ := norm_sub_le _ _
      _ = 2 := by rw [hnz, hnz]; norm_num
  -- bounds on u
  have hnu : ∀ i < n, ‖u i‖ ≤ F / ε := by
    intro i hi
    rw [hu]; simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have h1 : (‖a i‖)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (hna i hi)
    calc |f i| * (‖a i‖)⁻¹ ≤ F * ε⁻¹ := mul_le_mul (hF i hi) h1 (by positivity) ((abs_nonneg _).trans (hF i hi))
      _ = F / ε := by ring
  have hdu : ∀ i, i + 1 < n → ‖u (i + 1) - u i‖ ≤ F' / ε + F * D / ε ^ 2 := by
    intro i hi
    have hi0 : i < n := by omega
    have hai : a i ≠ 0 := by
      intro h0; have := hna i hi0; rw [h0] at this; simp at this; linarith
    have hai1 : a (i + 1) ≠ 0 := by
      intro h0; have := hna (i + 1) hi; rw [h0] at this; simp at this; linarith
    have e : u (i + 1) - u i = ((f (i + 1) - f i : ℝ) : ℂ) * (a (i + 1))⁻¹ + ((f i : ℝ) : ℂ) * ((a (i + 1))⁻¹ - (a i)⁻¹) := by
      rw [hu]; simp only; push_cast; ring
    have hinv : ‖(a (i + 1))⁻¹ - (a i)⁻¹‖ ≤ D / ε ^ 2 := by
      have e2 : (a (i + 1))⁻¹ - (a i)⁻¹ = (a i - a (i + 1)) / (a (i + 1) * a i) := by field_simp
      rw [e2, norm_div, norm_mul]
      have h1 : ‖a i - a (i + 1)‖ ≤ D := by
        have e3 : a i - a (i + 1) = -(Complex.exp (Complex.I * ((Φ (i + 2) - Φ (i + 1) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((Φ (i + 1) - Φ i : ℝ) : ℂ))) := by simp only [ha]; ring
        rw [e3, norm_neg]
        have e4 : Complex.exp (Complex.I * ((Φ (i + 2) - Φ (i + 1) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((Φ (i + 1) - Φ i : ℝ) : ℂ)) =
            Complex.exp (Complex.I * ((Φ (i + 1) - Φ i : ℝ) : ℂ)) *
              (Complex.exp (Complex.I * (((Φ (i + 2) - Φ (i + 1)) - (Φ (i + 1) - Φ i) : ℝ) : ℂ)) - 1) := by
          rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
        rw [e4, norm_mul]
        have : ‖Complex.exp (Complex.I * ((Φ (i + 1) - Φ i : ℝ) : ℂ))‖ = 1 := by
          simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; simp
        rw [this, one_mul]
        refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
        rw [Real.norm_eq_abs]; exact hD i hi
      have h2 : ε ≤ ‖a i‖ := hna i hi0
      have h3 : ε ≤ ‖a (i + 1)‖ := hna (i + 1) hi
      have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD i hi)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc ‖a i - a (i + 1)‖ * ε ^ 2 ≤ D * (ε * ε) := by nlinarith [norm_nonneg (a i - a (i + 1))]
        _ ≤ D * (‖a (i + 1)‖ * ‖a i‖) := by
          apply mul_le_mul_of_nonneg_left _ hD0
          exact mul_le_mul h3 h2 hε.le (hε.le.trans h3)
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, norm_inv]
    have h1 : (‖a (i + 1)‖)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (hna (i + 1) hi)
    have hFi := hF i hi0
    have hF'i := hF' i hi
    have t1 : |f (i + 1) - f i| * (‖a (i + 1)‖)⁻¹ ≤ F' / ε := by
      calc _ ≤ F' * ε⁻¹ := mul_le_mul hF'i h1 (by positivity) ((abs_nonneg _).trans hF'i)
        _ = F' / ε := by ring
    have t2 : |f i| * ‖(a (i + 1))⁻¹ - (a i)⁻¹‖ ≤ F * D / ε ^ 2 := by
      calc _ ≤ F * (D / ε ^ 2) := mul_le_mul hFi hinv (norm_nonneg _) ((abs_nonneg _).trans hFi)
        _ = F * D / ε ^ 2 := by ring
    linarith
  -- assemble
  have hK : 0 ≤ F' / ε + F * D / ε ^ 2 := by positivity
  have hmain : ‖∑ i ∈ range n, ((f i : ℝ) : ℂ) * z i‖ ≤ 2 * F / ε + 2 * n * (F' / ε + F * D / ε ^ 2) := by
    rw [hsum, hbp]
    refine (norm_sub_le _ _).trans ?_
    have t1 : ‖u (n - 1) * (z n - z 0)‖ ≤ 2 * F / ε := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp only [norm_mul]
        have : ‖u (0 - 1)‖ * ‖z 0 - z 0‖ = 0 := by simp
        rw [← norm_mul, sub_self, mul_zero, norm_zero]; positivity
      · rw [norm_mul]
        calc ‖u (n - 1)‖ * ‖z n - z 0‖ ≤ F / ε * 2 :=
              mul_le_mul (hnu (n - 1) (by omega)) (hzd n) (norm_nonneg _) (by positivity)
          _ = 2 * F / ε := by ring
    have t2 : ‖∑ i ∈ range (n - 1), (u (i + 1) - u i) * (z (i + 1) - z 0)‖ ≤ 2 * n * (F' / ε + F * D / ε ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ i ∈ range (n - 1), ‖(u (i + 1) - u i) * (z (i + 1) - z 0)‖ ≤ 2 * (F' / ε + F * D / ε ^ 2) := by
        intro i hi
        have hi' : i + 1 < n := by have := Finset.mem_range.1 hi; omega
        rw [norm_mul]
        calc ‖u (i + 1) - u i‖ * ‖z (i + 1) - z 0‖ ≤ (F' / ε + F * D / ε ^ 2) * 2 :=
              mul_le_mul (hdu i hi') (hzd _) (norm_nonneg _) hK
          _ = _ := by ring
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      nlinarith
    linarith
  have hre : ∀ i, (((f i : ℝ) : ℂ) * z i).re = f i * Real.cos (Φ i) := by
    intro i
    rw [hz]; simp only
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re, Complex.I_re, Complex.I_im]
    simp
  have : ∑ i ∈ range n, f i * Real.cos (Φ i) = (∑ i ∈ range n, ((f i : ℝ) : ℂ) * z i).re := by
    rw [Complex.re_sum]; exact Finset.sum_congr rfl fun i _ => (hre i).symm
  rw [this]
  exact (Complex.abs_re_le_norm _).trans hmain

end FormalResearch.Special
