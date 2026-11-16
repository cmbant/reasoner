module

public import FormalResearch.Special.JacobiMehlerHeineRate

/-!
# Mehler–Heine: the Bessel function, real argument

Consequences of `FormalResearch/Special/JacobiMehlerHeine.lean`:

* `mhLimit_eq_regularizedHGFun`: the Mehler–Heine limit function is Mathlib's regularised `₀F₁`
  `regularizedHGFun 0 {α+1} (-(z/2)²)`, so `besselJ_eq_cpow_mul_mhLimit`:
  `Complex.besselJ α z = (z/2)^α · mhLimit α z`, i.e. `mhLimit α z` is the series
  `∑ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))` of `(z/2)^{-α} J_α(z)` (any real `α`);
* `mehlerHeine_besselJ`: `n^{-α} P_n^{(α,β)}(cos(z/n)) → (z/2)^{-α} J_α(z)` uniformly on bounded
  `K ⊆ ℂ \ {0}`, with `J_α = Complex.besselJ α`;
* `mehlerHeine_real_rate`, from `JacobiMehlerHeineRate`: the same with a remainder `O(1/n)`;
* `mehlerHeine_real`: the real-argument form, uniformly on bounded `K ⊆ ℝ`, for the real polynomial
  `(jacobi α β n).eval (cos (x/n))`; `besselJ_ofReal` shows `J_α(x)` is real for `x > 0`.

All for `α > -1`, `β` real.  Not formalised: explicit constants in the rate, and any statement for
`α ≤ -1`.
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.Special

/-- The Mehler–Heine limit function is the regularised `₀F₁`:
`∑_ℓ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1)) = ₀F₁(-; α+1; -(z/2)²)/Γ(α+1)` in Mathlib's normalisation
`regularizedHGFun`, valid for every real `α`. -/
lemma mhLimit_eq_regularizedHGFun (α : ℝ) (z : ℂ) :
    mhLimit α z = Complex.regularizedHGFun 0 {(α : ℂ) + 1} (-(z / 2) ^ 2) := by
  unfold Complex.regularizedHGFun Complex.regularizedHGFunSeries
  rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  unfold mhLimit
  refine tsum_congr fun ℓ => ?_
  simp only [Complex.regularizedHGFunCoeff, mhLimitCoeff]
  have hG : Complex.Gamma ((α : ℂ) + 1 + ℓ) = ((Real.Gamma (α + ℓ + 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_add,
      Complex.Gamma_ofReal]
    ring_nf
  simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton, smul_eq_mul, hG]
  push_cast
  have : (-(z / 2) ^ 2) ^ ℓ = (-1) ^ ℓ * (z / 2) ^ (2 * ℓ) := by
    rw [neg_pow, ← pow_mul]
  rw [this]
  ring

/-- **Link to Mathlib's `Complex.besselJ`**: `J_α(z) = (z/2)^α ∑_ℓ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))`
(any real `α`). -/
theorem besselJ_eq_cpow_mul_mhLimit (α : ℝ) (z : ℂ) :
    Complex.besselJ α z = (z / 2) ^ (α : ℂ) * mhLimit α z := by
  rw [mhLimit_eq_regularizedHGFun, Complex.besselJ_def]

/-- Away from `0`: `(z/2)^{-α} J_α(z) = ∑_ℓ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))`. -/
theorem mhLimit_eq_cpow_neg_mul_besselJ (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    mhLimit α z = (z / 2) ^ (-(α : ℂ)) * Complex.besselJ α z := by
  have h : (z / 2) ^ (α : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [hz]
  rw [besselJ_eq_cpow_mul_mhLimit, Complex.cpow_neg, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- **Mehler–Heine formula** for bounded sets `K ⊆ ℂ`: `n^{-α} P_n^{(α,β)}(cos(z/n))`
converges uniformly on `K` to `∑_ℓ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))`. -/
theorem mehlerHeine_uniformOn_bounded (α β : ℝ) (hα : -1 < α) {K : Set ℂ}
    (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => (((n : ℝ) ^ (-α) : ℝ) : ℂ) *
      Polynomial.aeval (Complex.cos (z / n)) (jacobi α β n)) (mhLimit α) atTop K := by
  obtain ⟨C, hC⟩ := hK.exists_pos_norm_le
  exact (mehlerHeine_uniform α β hα (R := C) hC.1.le).mono
    fun z hz => by simpa using hC.2 z hz

/-- **Mehler–Heine formula, Bessel form** (Szegő 8.1.1, DLMF 18.11.1): for `α > -1` and every
bounded `K ⊆ ℂ \ {0}`,
`n^{-α} P_n^{(α,β)}(cos(z/n)) → (z/2)^{-α} J_α(z)` uniformly on `K`, with `J_α = Complex.besselJ α`.
(At `z = 0` the right side is `1/Γ(α+1)`, the value of `mhLimit α 0`; `besselJ` itself carries
the branch `(z/2)^α`.) -/
theorem mehlerHeine_besselJ (α β : ℝ) (hα : -1 < α) {K : Set ℂ} (hK : Bornology.IsBounded K)
    (h0 : (0 : ℂ) ∉ K) :
    TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => (((n : ℝ) ^ (-α) : ℝ) : ℂ) *
      Polynomial.aeval (Complex.cos (z / n)) (jacobi α β n))
      (fun z => (z / 2) ^ (-(α : ℂ)) * Complex.besselJ α z) atTop K :=
  (mehlerHeine_uniformOn_bounded α β hα hK).congr_right fun _ hz =>
    mhLimit_eq_cpow_neg_mul_besselJ α (fun h => h0 (h ▸ hz))

/-! ### Real argument -/

/-- The Mehler–Heine limit function on the real line. -/
noncomputable def mhLimitReal (α x : ℝ) : ℝ :=
  ∑' ℓ : ℕ, (-1) ^ ℓ * mhLimitCoeff α ℓ * (x / 2) ^ (2 * ℓ)

lemma ofReal_mhLimitReal (α x : ℝ) : ((mhLimitReal α x : ℝ) : ℂ) = mhLimit α (x : ℂ) := by
  unfold mhLimitReal mhLimit
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun ℓ => ?_
  push_cast
  ring

/-- For `x > 0`, `J_α(x) = (x/2)^α ∑_ℓ (-1)^ℓ (x/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))` is real. -/
theorem besselJ_ofReal (α : ℝ) {x : ℝ} (hx : 0 < x) :
    Complex.besselJ α (x : ℂ) = (((x / 2) ^ α * mhLimitReal α x : ℝ) : ℂ) := by
  rw [besselJ_eq_cpow_mul_mhLimit, ← ofReal_mhLimitReal]
  push_cast
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl

/-- The complex expression at a real point is the cast of the real one. -/
lemma mh_cast_aeval (α β : ℝ) (n : ℕ) (x : ℝ) :
    (((n : ℝ) ^ (-α) : ℝ) : ℂ) * Polynomial.aeval (Complex.cos ((x : ℂ) / n)) (jacobi α β n) =
      (((n : ℝ) ^ (-α) * (jacobi α β n).eval (Real.cos (x / n)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul]
  congr 1
  have : Complex.cos ((x : ℂ) / n) = algebraMap ℝ ℂ (Real.cos (x / n)) := by
    rw [Complex.coe_algebraMap, Complex.ofReal_cos]; push_cast; rfl
  rw [this, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Complex.coe_algebraMap]

/-- **Mehler–Heine formula on the real line** (uniform on bounded sets): for `α > -1`, real `β`,
`n^{-α} P_n^{(α,β)}(cos(x/n)) → ∑_ℓ (-1)^ℓ (x/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))` uniformly for `x` in a bounded
set `K ⊆ ℝ` (the limit is `(x/2)^{-α} J_α(x)` for `x > 0`, `besselJ_ofReal`). -/
theorem mehlerHeine_real (α β : ℝ) (hα : -1 < α) {K : Set ℝ} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) =>
      (n : ℝ) ^ (-α) * (jacobi α β n).eval (Real.cos (x / n))) (mhLimitReal α) atTop K := by
  obtain ⟨C, hC0, hC⟩ := hK.exists_pos_norm_le
  have h := mehlerHeine_uniform α β hα (R := C) hC0.le
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn x hx
  have h1 := hn (x : ℂ) (by simpa using hC x hx)
  have e := mh_cast_aeval α β n x
  rw [e, ← ofReal_mhLimitReal, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real] at h1
  rwa [Real.dist_eq, ← Real.norm_eq_abs]

/-- **Mehler–Heine on the real line with a rate**: for `α > -1`, `β` real and `R ≥ 0`,
`|n^{-α} P_n^{(α,β)}(cos(x/n)) - ∑_ℓ (-1)^ℓ (x/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))| ≤ C/n` for `n ≥ N`,
`|x| ≤ R`; the constants `C, N` are not explicit. -/
theorem mehlerHeine_real_rate (α β : ℝ) (hα : -1 < α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℝ, |x| ≤ R →
      |(n : ℝ) ^ (-α) * (jacobi α β n).eval (Real.cos (x / n)) - mhLimitReal α x| ≤ C / n := by
  obtain ⟨C, N, h⟩ := mehlerHeine_rate α β hα hR
  refine ⟨C, N, fun n hn x hx => ?_⟩
  have h1 := h n hn (x : ℂ) (by simpa using hx)
  rw [mh_cast_aeval, ← ofReal_mhLimitReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h1
  exact h1

/-- For `x > 0`, the limit function is `(x/2)^{-α} J_α(x)` (real part of `Complex.besselJ`). -/
theorem mhLimitReal_eq_rpow_mul_besselJ_re (α : ℝ) {x : ℝ} (hx : 0 < x) :
    mhLimitReal α x = (x / 2) ^ (-α) * (Complex.besselJ α (x : ℂ)).re := by
  rw [besselJ_ofReal α hx, Complex.ofReal_re, ← mul_assoc, ← Real.rpow_add (by positivity)]
  simp

/-! ### Axiom check -/

/-- info: 'FormalResearch.Special.besselJ_eq_cpow_mul_mhLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.besselJ_eq_cpow_mul_mhLimit

/-- info: 'FormalResearch.Special.mehlerHeine_besselJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mehlerHeine_besselJ

/-- info: 'FormalResearch.Special.mehlerHeine_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mehlerHeine_real

/-- info: 'FormalResearch.Special.besselJ_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.besselJ_ofReal

/-- info: 'FormalResearch.Special.mehlerHeine_real_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mehlerHeine_real_rate

/-- info: 'FormalResearch.Special.mhLimit_eq_regularizedHGFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mhLimit_eq_regularizedHGFun

/-- info: 'FormalResearch.Special.mhLimit_eq_cpow_neg_mul_besselJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mhLimit_eq_cpow_neg_mul_besselJ

/-- info: 'FormalResearch.Special.mehlerHeine_uniformOn_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mehlerHeine_uniformOn_bounded

end FormalResearch.Special
