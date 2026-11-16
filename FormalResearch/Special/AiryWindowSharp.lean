module

public import FormalResearch.Special.AiryWindow
public import FormalResearch.Special.AiryWindowSharpEnergy

/-!
# The oscillatory window with a coefficient-variation (polynomial) constant

`AiryWindow` marches the window with the `ℓ¹` Grönwall of `DiscreteJacobiExtrasGronwall`, whose constant is
`windowExp = exp((1 + 2(Sg + Qq)/c_a) S/c₁)`, `Sg ≈ A₀`, i.e. `e^{O(A₀²)}` (`10^{79}`-`10^{91}` at `A₀ = 10`, depending on the constants).
Here the same estimate is proved with the *energy march* of `AiryWindowSharpEnergy`, whose only loss is the relative variation
of the local frequency `λ_k = (a_k + a_{k+1} - c_k)/δ²` and of `a`:

`windowVar a λ J m = Σ_{k ∈ [J+1, m)} (μ_k + μ'_k + μ_kμ'_k)`, `μ_k = |λ_k - λ_{k+1}|/λ_{k+1}`, `μ'_k = |a_{k+2} - a_{k+1}|/a_{k+1}`.

* **`window_sharp_bound`** (Airy-free): `d` with `|jac a c d| ≤ ρ₀` on the rows `Ioc J m`, `c_k = a_k + a_{k+1} - δ² λ_k`,
  `λ ∈ [lo, hi]`, `δ² hi ≤ c_a ≤ a ≤ a_hi`, initial data `|d_m| ≤ e₀`, `|d_{m+1} - d_m|/δ ≤ e₁`:
  `|d_k| ≤ e₀ + K₁ e^{3V/2} (√(3/2) √(hi (e₀ + δ e₁)² + a_hi e₁²) + (m - J) ρ₀/(δ √c_a))` on `[J, m]`,
  `K₁ = √2 (1/√lo + √a_hi/c_a)`, `V = windowVar`;
* **`window_from_top_sharp`**: the analogue of `window_from_top` (same data: exact solution `f` on the top window, parametrix `ψ`
  with the absolute defect `C₀ δ⁶ W`, junction bounds): the continuation `F` satisfies
  `|F_k - ψ_k| ≤ windowConstSharp · δ³ W` on `[J, m]` with
  `windowConstSharp = C₅ + K₁ e^{3V/2} (√(3/2) C₅(2+Λ)√(hi + a_hi) + S C₀/(c₁ √c_a))`.
* `windowVar_le_log`: for `λ` non-increasing with steps `λ_k ≤ (1+θ) λ_{k+1}` and `|a_{k+2} - a_{k+1}| ≤ q δ²`, `a ≥ c_a`,
  `η = q δ²/c_a`: `V ≤ (1+η)(1+θ)(log λ_{J+1} - log λ_m) + (m-J) η`;
* **`window_from_top_sharp_log`**: `window_from_top_sharp` with `V = (1 + qδ²/c_a)(1+θ) log(hi/lo) + S q/(c₁c_a)`,
  i.e. `e^{3V/2} = (hi/lo)^{3(1+qδ²/c_a)(1+θ)/2} e^{3Sq/(2c₁c_a)}`: **a power of `hi/lo ≈ A₀`** (`≈ A₀^{3/2}`
  for `λ ≈ |X|`, `θ, δ → 0`) instead of `e^{O(A₀²)}`.

Numerics (python, constants only; model chain `a ≡ 1`, `c_k = 2 - δ²|X_k|`, `lo = 1`, `hi = A₀`, `C₀ = 1/240`,
`C₅ = Λ = c₁ = c_a = a_hi = 1`, `S = A₀`, `θ = q = 0`): `windowConstSharp = 52, 286, 1095` and `windowConst = 6.6·10⁴,
2.3·10²⁴, 4.9·10⁹¹` for `A₀ = 2, 5, 10`; the true error on the model chain (`d2a-m6` numerics) is `|f - ψ| ≈ 0.0163 h^{4/3} = 0.0163 δ⁴` on `X ∈ [-10, -1]`,
independent of `A₀`, so the remaining pessimism is the coefficient-variation Grönwall factor and the `δ³` (vs `δ⁴`) initial data.
A random-data check of `window_sharp_bound` (`a = 1 + 0.02 sin`, `A₀ ∈ {3, 10, 30}`, `δ ∈ {0.05, 0.01}`, random initial data
and forcing) gave bound/actual ratios between `1.2·10²` and `3.7·10⁷`: the inequality is never violated.

Compared with `discrete_airy_window`: no `Sg`, `Qq`, but the *lower* bound `lo` of `λ` is needed (it is `≈ 1` on `X ≤ -1`) and
the near-hyperbolic constant is replaced by the variation `V` (`≈ ln A₀`).  The error is still `O(δ³)` (the initial-data
term; the forcing contributes `δ⁴`); the brief's `A₀^{3/2} δ³` form is what `window_from_top_sharp_log` gives for `θ, δ → 0`.
**Not formalised:** the verification of `lo ≤ λ_k ≤ hi`, the monotonicity and the variation sum for the Hahn/Racah/W1 chains; the
physical-solution wrapper `discrete_airy_window_physical` and the `δ₀`-existence wrapper `discrete_airy_window` in this form
(both are mechanical from `window_from_top_sharp_log`); the `O(h^{4/3})` truth.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The total relative variation `Σ (μ_k + μ'_k + μ_kμ'_k)` of the frequency `λ` and of `a`. -/
noncomputable def windowVar (a lam : ℤ → ℝ) (J m : ℤ) : ℝ :=
  ∑ k ∈ Ico (J + 1) m, (|lam k - lam (k + 1)| / lam (k + 1) + |a (k + 2) - a (k + 1)| / a (k + 1) +
    (|lam k - lam (k + 1)| / lam (k + 1)) * (|a (k + 2) - a (k + 1)| / a (k + 1)))

/-- **The energy bound for every state of the window** (`J < m`): `√Q_k(y_k, P_k) ≤ e^{3V/2}(T₀ + Σ √β_j |ρ_j|)`. -/
theorem window_sharp_energy {a c d lam : ℤ → ℝ} {J m : ℤ} {δ ca ahi lo hi ρ0 e0 e1 : ℝ}
    (hδ : 0 < δ) (hca : 0 < ca) (hlo : 0 < lo) (hε : δ ^ 2 * hi ≤ ca) (hJm' : J < m)
    (ha : ∀ k ∈ Icc (J + 1) (m + 1), ca ≤ a k) (hahi : ∀ k ∈ Icc (J + 1) (m + 1), a k ≤ ahi)
    (hlam : ∀ k ∈ Ioc J m, lo ≤ lam k ∧ lam k ≤ hi)
    (hcl : ∀ k ∈ Ioc J m, c k = a k + a (k + 1) - δ ^ 2 * lam k)
    (hrow : ∀ k ∈ Ioc J m, |jac a c d k| ≤ ρ0) (he0 : |d m| ≤ e0) (he1 : |d (m + 1) - d m| / δ ≤ e1) :
    ∀ k ∈ Icc (J + 1) m, √(enQ (lam k) (1 / a (k + 1)) δ (d k) (a k * (d k - d (k - 1)) / δ)) ≤
      Real.exp (3 * windowVar a lam J m / 2) * (√(3 / 2) * √(hi * (e0 + δ * e1) ^ 2 + ahi * e1 ^ 2) +
      ((m - J : ℤ) : ℝ) * ρ0 / (δ * √ca)) := by
  have hke : 0 ≤ e0 := (abs_nonneg _).trans he0
  have hk1 : 0 ≤ e1 := (div_nonneg (abs_nonneg _) hδ.le).trans he1
  have hsca : 0 < √ca := Real.sqrt_pos.mpr hca
  -- the main case J < m
  have hcaJ : ∀ k ∈ Icc (J + 1) (m + 1), 0 < a k := fun k hk => lt_of_lt_of_le hca (ha k hk)
  have hloJ : ∀ k ∈ Ioc J m, 0 < lam k := fun k hk => lt_of_lt_of_le hlo (hlam k hk).1
  set V := windowVar a lam J m with hVdef
  -- the oscillator data
  have hmain := energy_march_down (fun k => d k) (fun k => a k * (d k - d (k - 1)) / δ) (fun k => lam k)
    (fun k => 1 / a (k + 1)) (fun k => jac a c d k / δ) (fun k => (lam k - lam (k + 1)) / lam (k + 1))
    (fun k => (a (k + 2) - a (k + 1)) / a (k + 1)) (fun k => |lam k - lam (k + 1)| / lam (k + 1))
    (fun k => |a (k + 2) - a (k + 1)| / a (k + 1)) δ V J m
    (fun k hk => hloJ k (by rw [mem_Icc] at hk; rw [mem_Ioc]; omega))
    (fun k hk => by
      have := hcaJ (k + 1) (by rw [mem_Icc] at hk ⊢; omega)
      simpa using this)
    (fun k hk => by
      rw [mem_Icc] at hk
      have h1 := (hlam k (by rw [mem_Ioc]; omega)).2
      have h2 := ha (k + 1) (by rw [mem_Icc]; omega)
      have hlk := hloJ k (by rw [mem_Ioc]; omega)
      have h3 : δ ^ 2 * lam k ≤ ca := by nlinarith [sq_nonneg δ]
      have h4 : 0 < a (k + 1) := lt_of_lt_of_le hca h2
      show δ ^ 2 * lam k * (1 / a (k + 1)) ≤ 1
      rw [mul_one_div, div_le_one h4]
      linarith)
    (fun k hk => by
      rw [mem_Icc] at hk
      have hk' : k ∈ Ioc J m := by rw [mem_Ioc]; omega
      have h4 := hcaJ (k + 1) (by rw [mem_Icc]; omega)
      have h5 : jac a c d k = a (k + 1) * d (k + 1) + a k * d (k - 1) - c k * d k := rfl
      show a (k + 1) * (d (k + 1) - d (k + 1 - 1)) / δ =
        a k * (d k - d (k - 1)) / δ - δ * lam k * d k + jac a c d k / δ
      rw [show k + 1 - 1 = k by ring, h5, hcl k hk']
      field_simp
      ring)
    (fun k hk => by
      rw [mem_Icc] at hk
      have h4 := hcaJ (k + 1) (by rw [mem_Icc]; omega)
      show d (k + 1) = d k + δ * (1 / a (k + 1)) * (a (k + 1) * (d (k + 1) - d (k + 1 - 1)) / δ)
      rw [show k + 1 - 1 = k by ring]
      field_simp
      ring)
    (fun k hk => by
      rw [mem_Ico] at hk
      have h1 := hloJ (k + 1) (by rw [mem_Ioc]; omega)
      show lam k = lam (k + 1) * (1 + (lam k - lam (k + 1)) / lam (k + 1))
      field_simp; ring)
    (fun k hk => by
      rw [mem_Ico] at hk
      have h1 := hcaJ (k + 1) (by rw [mem_Icc]; omega)
      have h2 := hcaJ (k + 1 + 1) (by rw [mem_Icc]; omega)
      show 1 / a (k + 1) = 1 / a (k + 1 + 1) * (1 + (a (k + 2) - a (k + 1)) / a (k + 1))
      rw [show k + 2 = k + 1 + 1 by ring]
      field_simp; ring)
    (fun k hk => by
      rw [mem_Ico] at hk
      have h1 := hloJ (k + 1) (by rw [mem_Ioc]; omega)
      show |(lam k - lam (k + 1)) / lam (k + 1)| ≤ |lam k - lam (k + 1)| / lam (k + 1)
      rw [abs_div, abs_of_pos h1])
    (fun k hk => by
      rw [mem_Ico] at hk
      have h1 := hcaJ (k + 1) (by rw [mem_Icc]; omega)
      show |(a (k + 2) - a (k + 1)) / a (k + 1)| ≤ |a (k + 2) - a (k + 1)| / a (k + 1)
      rw [abs_div, abs_of_pos h1])
    (le_of_eq rfl)
  beta_reduce at hmain
  have hmI : m ∈ Icc (J + 1) m := by rw [mem_Icc]; omega
  have hmo : m ∈ Ioc J m := by rw [mem_Ioc]; omega
  -- the forcing sum
  have hsum : ∑ j ∈ Icc (J + 1) m, √(1 / a (j + 1)) * |jac a c d j / δ| ≤
      ((m - J : ℤ) : ℝ) * (ρ0 / (δ * √ca)) := by
    have hcard : ((Icc (J + 1) m).card : ℝ) = ((m - J : ℤ) : ℝ) := by
      rw [Int.card_Icc, show m + 1 - (J + 1) = m - J by ring]
      have h0 : (0 : ℤ) ≤ m - J := by omega
      have : (((m - J).toNat : ℕ) : ℤ) = m - J := Int.toNat_of_nonneg h0
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    calc ∑ j ∈ Icc (J + 1) m, √(1 / a (j + 1)) * |jac a c d j / δ| ≤
          ∑ j ∈ Icc (J + 1) m, (ρ0 / (δ * √ca)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [mem_Icc] at hj
          have h1 := ha (j + 1) (by rw [mem_Icc]; omega)
          have hj' : j ∈ Ioc J m := by rw [mem_Ioc]; omega
          have e1 : √(1 / a (j + 1)) ≤ 1 / √ca := by
            have h1' := Real.sqrt_le_sqrt h1
            rw [one_div, Real.sqrt_inv, one_div]; exact inv_anti₀ hsca h1'
          have e2 : |jac a c d j / δ| ≤ ρ0 / δ := by
            rw [abs_div, abs_of_pos hδ]; exact div_le_div_of_nonneg_right (hrow j hj') hδ.le
          calc √(1 / a (j + 1)) * |jac a c d j / δ| ≤ 1 / √ca * (ρ0 / δ) :=
                mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
            _ = ρ0 / (δ * √ca) := by field_simp
      _ = ((m - J : ℤ) : ℝ) * (ρ0 / (δ * √ca)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  -- the initial energy
  have hT0 : √(3 / 2 * (lam m * d (m + 1) ^ 2 + 1 / a (m + 1) *
      (a (m + 1) * (d (m + 1) - d (m + 1 - 1)) / δ) ^ 2)) ≤
      √(3 / 2) * √(hi * (e0 + δ * e1) ^ 2 + ahi * e1 ^ 2) := by
    rw [show m + 1 - 1 = m by ring, ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    have hm1 : m + 1 ∈ Icc (J + 1) (m + 1) := by rw [mem_Icc]; omega
    have ham := hcaJ (m + 1) hm1
    have hahim := hahi (m + 1) hm1
    have hlm := hlam m hmo
    have hw : |(d (m + 1) - d m) / δ| ≤ e1 := by
      rw [abs_div, abs_of_pos hδ]; exact he1
    have hd1 : |d (m + 1)| ≤ e0 + δ * e1 := by
      have h1 : |d (m + 1) - d m| ≤ δ * e1 := by
        rw [div_le_iff₀ hδ] at he1; linarith
      calc |d (m + 1)| = |d m + (d (m + 1) - d m)| := by ring_nf
        _ ≤ |d m| + |d (m + 1) - d m| := abs_add_le _ _
        _ ≤ _ := by linarith
    have t1 : lam m * d (m + 1) ^ 2 ≤ hi * (e0 + δ * e1) ^ 2 := by
      have h1 : d (m + 1) ^ 2 ≤ (e0 + δ * e1) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
      exact mul_le_mul hlm.2 h1 (sq_nonneg _) (by linarith [hlm.1, hlo])
    have t2 : 1 / a (m + 1) * (a (m + 1) * ((d (m + 1) - d m) / δ)) ^ 2 ≤ ahi * e1 ^ 2 := by
      have e : 1 / a (m + 1) * (a (m + 1) * ((d (m + 1) - d m) / δ)) ^ 2 =
          a (m + 1) * ((d (m + 1) - d m) / δ) ^ 2 := by field_simp
      rw [e]
      have h1 : ((d (m + 1) - d m) / δ) ^ 2 ≤ e1 ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hw 2
      exact mul_le_mul hahim h1 (sq_nonneg _) (by linarith)
    rw [mul_div_assoc]
    linarith
  intro k hk
  refine (hmain k hk).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have : ((m - J : ℤ) : ℝ) * ρ0 / (δ * √ca) = ((m - J : ℤ) : ℝ) * (ρ0 / (δ * √ca)) := by ring
  rw [this]
  exact add_le_add hT0 hsum

/-- **Extraction of `|d_k|`** from the energy bound (including the site `J`). -/
theorem window_sharp_extract {a d lam : ℤ → ℝ} {J m : ℤ} {δ ca ahi lo hi Bnd : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hca : 0 < ca) (hlo : 0 < lo) (hε : δ ^ 2 * hi ≤ ca) (hJm' : J < m)
    (hBnd0 : 0 ≤ Bnd) (ha : ∀ k ∈ Icc (J + 1) (m + 1), ca ≤ a k) (hahi : ∀ k ∈ Icc (J + 1) (m + 1), a k ≤ ahi)
    (hlam : ∀ k ∈ Ioc J m, lo ≤ lam k ∧ lam k ≤ hi)
    (hM : ∀ k ∈ Icc (J + 1) m,
      √(enQ (lam k) (1 / a (k + 1)) δ (d k) (a k * (d k - d (k - 1)) / δ)) ≤ Bnd) :
    ∀ k ∈ Icc J m, |d k| ≤ √2 * (1 / √lo + √ahi / ca) * Bnd := by
  have hcaJ : ∀ k ∈ Icc (J + 1) (m + 1), 0 < a k := fun k hk => lt_of_lt_of_le hca (ha k hk)
  have hloJ : ∀ k ∈ Ioc J m, 0 < lam k := fun k hk => lt_of_lt_of_le hlo (hlam k hk).1
  have hEps : ∀ k ∈ Icc (J + 1) m, δ ^ 2 * lam k * (1 / a (k + 1)) ≤ 1 := by
    intro k hk
    rw [mem_Icc] at hk
    have h1 := (hlam k (by rw [mem_Ioc]; omega)).2
    have h2 := ha (k + 1) (by rw [mem_Icc]; omega)
    have h3 : δ ^ 2 * lam k ≤ ca := by nlinarith [sq_nonneg δ]
    have h4 : 0 < a (k + 1) := lt_of_lt_of_le hca h2
    rw [mul_one_div, div_le_one h4]
    linarith
  -- from the energy to the size of d
  have hQ : ∀ k ∈ Icc (J + 1) m, lam k * d k ^ 2 ≤ 2 * Bnd ^ 2 ∧
      1 / a (k + 1) * (a k * (d k - d (k - 1)) / δ) ^ 2 ≤ 2 * Bnd ^ 2 := by
    intro k hk
    have hk' : k ∈ Ioc J m := by rw [mem_Icc] at hk; rw [mem_Ioc]; omega
    have h4 := hcaJ (k + 1) (by rw [mem_Icc] at hk ⊢; omega)
    have hlow := enQ_lower (y := d k) (P := a k * (d k - d (k - 1)) / δ) (hloJ k hk').le
      (by positivity : (0 : ℝ) ≤ 1 / a (k + 1)) (by simpa [mul_assoc] using hEps k hk)
    have hnn := enQ_nonneg (y := d k) (P := a k * (d k - d (k - 1)) / δ) (hloJ k hk').le
      (by positivity : (0 : ℝ) ≤ 1 / a (k + 1)) (by simpa [mul_assoc] using hEps k hk)
    have h5 := hM k hk
    have h6 : enQ (lam k) (1 / a (k + 1)) δ (d k) (a k * (d k - d (k - 1)) / δ) ≤ Bnd ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h5 2
      rwa [Real.sq_sqrt hnn] at this
    have p1 : 0 ≤ lam k * d k ^ 2 := by have := hloJ k hk'; positivity
    have p2 : 0 ≤ 1 / a (k + 1) * (a k * (d k - d (k - 1)) / δ) ^ 2 := by positivity
    constructor <;> linarith
  have hK1 : 0 ≤ √2 * (1 / √lo + √ahi / ca) := by positivity
  have hd0 : ∀ k ∈ Icc (J + 1) m, |d k| ≤ √2 * Bnd / √lo := by
    intro k hk
    have hk' : k ∈ Ioc J m := by rw [mem_Icc] at hk; rw [mem_Ioc]; omega
    have h1 := (hQ k hk).1
    have hlk := (hlam k hk').1
    have h2 : d k ^ 2 ≤ 2 * Bnd ^ 2 / lo := by
      rw [le_div_iff₀ hlo]; nlinarith [sq_nonneg (d k)]
    have h3 : |d k| ≤ √(2 * Bnd ^ 2 / lo) := Real.abs_le_sqrt h2
    have h4 : √(2 * Bnd ^ 2 / lo) = √2 * Bnd / √lo := by
      rw [Real.sqrt_div' _ hlo.le, Real.sqrt_mul (by norm_num), Real.sqrt_sq hBnd0]
    rw [h4] at h3
    exact h3
  have hd : ∀ k ∈ Icc (J + 1) m, |d k| ≤ √2 * (1 / √lo + √ahi / ca) * Bnd := by
    intro k hk
    refine (hd0 k hk).trans ?_
    have : √2 * Bnd / √lo = √2 * (1 / √lo) * Bnd := by ring
    rw [this]
    have : 0 ≤ √2 * (√ahi / ca) * Bnd := by positivity
    nlinarith
  -- the site J
  have hdJ : |d J| ≤ √2 * (1 / √lo + √ahi / ca) * Bnd := by
    have hJ1 : J + 1 ∈ Icc (J + 1) m := by rw [mem_Icc]; omega
    have hJ2 : J + 2 ∈ Icc (J + 1) (m + 1) := by rw [mem_Icc]; omega
    have hJ1' : J + 1 ∈ Icc (J + 1) (m + 1) := by rw [mem_Icc]; omega
    have haJ1 := hcaJ (J + 1) hJ1'
    have haJ2 := hcaJ (J + 2) hJ2
    have hahiJ2 := hahi (J + 2) hJ2
    obtain ⟨-, hQ2⟩ := hQ (J + 1) hJ1
    have hPe : a (J + 1) * (d (J + 1) - d (J + 1 - 1)) / δ = a (J + 1) * (d (J + 1) - d J) / δ := by
      rw [show J + 1 - 1 = J by ring]
    rw [hPe, show J + 1 + 1 = J + 2 by ring] at hQ2
    set Pj := a (J + 1) * (d (J + 1) - d J) / δ with hPj
    have hdJe : d J = d (J + 1) - δ * Pj / a (J + 1) := by
      rw [hPj]; field_simp; ring
    have hP2 : Pj ^ 2 ≤ 2 * ahi * Bnd ^ 2 := by
      have h1 : Pj ^ 2 ≤ a (J + 2) * (2 * Bnd ^ 2) := by
        have := mul_le_mul_of_nonneg_left hQ2 haJ2.le
        rwa [← mul_assoc, mul_one_div_cancel haJ2.ne', one_mul] at this
      nlinarith [sq_nonneg Bnd]
    have hahi0 : 0 ≤ ahi := by linarith
    have hP3 : |Pj| ≤ √2 * √ahi * Bnd := by
      refine abs_le_of_sq_le_sq ?_ (by positivity)
      have : (√2 * √ahi * Bnd) ^ 2 = 2 * ahi * Bnd ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hahi0]
      rw [this]; exact hP2
    have hd1 := hd0 (J + 1) hJ1
    have hP4 : δ * |Pj| / a (J + 1) ≤ √2 * (√ahi / ca) * Bnd := by
      rw [div_le_iff₀ haJ1]
      have h1 : δ * |Pj| ≤ |Pj| := by
        have := abs_nonneg Pj
        nlinarith
      have h2 : |Pj| ≤ √2 * √ahi * Bnd := hP3
      have h3 : √2 * √ahi * Bnd ≤ √2 * (√ahi / ca) * Bnd * a (J + 1) := by
        have hca1 : 1 ≤ a (J + 1) / ca := by rw [le_div_iff₀ hca]; linarith [ha (J + 1) hJ1']
        have e : √2 * (√ahi / ca) * Bnd * a (J + 1) = √2 * √ahi * Bnd * (a (J + 1) / ca) := by
          field_simp
        rw [e]
        have : 0 ≤ √2 * √ahi * Bnd := by positivity
        nlinarith
      linarith
    rw [hdJe]
    calc |d (J + 1) - δ * Pj / a (J + 1)| ≤ |d (J + 1)| + |δ * Pj / a (J + 1)| := abs_sub _ _
      _ ≤ √2 * Bnd / √lo + √2 * (√ahi / ca) * Bnd := by
          refine add_le_add hd1 ?_
          rw [abs_div, abs_mul, abs_of_pos hδ, abs_of_pos haJ1]
          exact hP4
      _ = √2 * (1 / √lo + √ahi / ca) * Bnd := by ring
  intro k hk
  rcases eq_or_lt_of_le (mem_Icc.mp hk).1 with h | h
  · rw [← h]; exact hdJ
  · exact hd k (by rw [mem_Icc] at hk ⊢; omega)

/-- **The sharp window bound for a difference `d` (Airy-free).** -/
theorem window_sharp_bound {a c d lam : ℤ → ℝ} {J m : ℤ} {δ ca ahi lo hi ρ0 e0 e1 : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hca : 0 < ca) (hlo : 0 < lo) (hε : δ ^ 2 * hi ≤ ca) (hJm : J ≤ m)
    (hρ0 : 0 ≤ ρ0) (ha : ∀ k ∈ Icc (J + 1) (m + 1), ca ≤ a k) (hahi : ∀ k ∈ Icc (J + 1) (m + 1), a k ≤ ahi)
    (hlam : ∀ k ∈ Ioc J m, lo ≤ lam k ∧ lam k ≤ hi)
    (hcl : ∀ k ∈ Ioc J m, c k = a k + a (k + 1) - δ ^ 2 * lam k)
    (hrow : ∀ k ∈ Ioc J m, |jac a c d k| ≤ ρ0) (he0 : |d m| ≤ e0) (he1 : |d (m + 1) - d m| / δ ≤ e1) :
    ∀ k ∈ Icc J m, |d k| ≤ e0 + √2 * (1 / √lo + √ahi / ca) * Real.exp (3 * windowVar a lam J m / 2) *
      (√(3 / 2) * √(hi * (e0 + δ * e1) ^ 2 + ahi * e1 ^ 2) + ((m - J : ℤ) : ℝ) * ρ0 / (δ * √ca)) := by
  intro k hk
  have hke : 0 ≤ e0 := (abs_nonneg _).trans he0
  have hk1 : 0 ≤ e1 := (div_nonneg (abs_nonneg _) hδ.le).trans he1
  have hsca : 0 < √ca := Real.sqrt_pos.mpr hca
  have hmJ : (0 : ℝ) ≤ ((m - J : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - J := by omega
    exact_mod_cast this
  have hnn : 0 ≤ Real.exp (3 * windowVar a lam J m / 2) *
      (√(3 / 2) * √(hi * (e0 + δ * e1) ^ 2 + ahi * e1 ^ 2) + ((m - J : ℤ) : ℝ) * ρ0 / (δ * √ca)) := by
    positivity
  rcases eq_or_lt_of_le hJm with hJ | hJm'
  · subst hJ
    rw [mem_Icc] at hk
    have : k = J := by omega
    subst this
    have hK1 : 0 ≤ √2 * (1 / √lo + √ahi / ca) := by positivity
    have := mul_nonneg hK1 hnn
    nlinarith
  · have hE := window_sharp_energy hδ hca hlo hε hJm' ha hahi hlam hcl hrow he0 he1
    have hX := window_sharp_extract (a := a) (d := d) (lam := lam) (hi := hi) hδ hδ1 hca hlo hε hJm' hnn ha hahi
      hlam hE k hk
    have e : √2 * (1 / √lo + √ahi / ca) * Real.exp (3 * windowVar a lam J m / 2) *
      (√(3 / 2) * √(hi * (e0 + δ * e1) ^ 2 + ahi * e1 ^ 2) + ((m - J : ℤ) : ℝ) * ρ0 / (δ * √ca)) =
      √2 * (1 / √lo + √ahi / ca) * (Real.exp (3 * windowVar a lam J m / 2) *
      (√(3 / 2) * √(hi * (e0 + δ * e1) ^ 2 + ahi * e1 ^ 2) + ((m - J : ℤ) : ℝ) * ρ0 / (δ * √ca))) := by ring
    rw [e]
    linarith

/-- The constant of the sharp window bound, `V ≥ windowVar`. -/
noncomputable def windowConstSharp (c1 ca ahi lo hi C0 C5 Λ S V : ℝ) : ℝ :=
  C5 + √2 * (1 / √lo + √ahi / ca) * Real.exp (3 * V / 2) *
    (√(3 / 2) * (√(hi + ahi) * (C5 * (2 + Λ))) + S * C0 / (c1 * √ca))

/-- The numerical estimate closing `window_from_top_sharp`. -/
theorem windowSharp_arith {n δ W c1 ca ahi lo hi C0 C5 Λ S V V' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1)
    (hca : 0 < ca) (hlo : 0 < lo) (hC0 : 0 ≤ C0) (hC5 : 0 ≤ C5) (hΛ : 0 ≤ Λ) (hS : 0 ≤ S) (hW : 0 ≤ W)
    (hhi : 0 ≤ hi) (hahi0 : 0 ≤ ahi) (hmJ : 0 ≤ n) (hnδ : n * δ ≤ S / c1) (hV : V' ≤ V) :
    C5 * δ ^ 3 * W + √2 * (1 / √lo + √ahi / ca) * Real.exp (3 * V' / 2) *
      (√(3 / 2) * √(hi * (C5 * δ ^ 3 * W + δ * (C5 * (1 + Λ) * δ ^ 3 * W)) ^ 2 +
        ahi * (C5 * (1 + Λ) * δ ^ 3 * W) ^ 2) + n * (C0 * δ ^ 6 * W) / (δ * √ca)) ≤
      windowConstSharp c1 ca ahi lo hi C0 C5 Λ S V * δ ^ 3 * W := by
  have hδ4 : δ ^ 4 ≤ δ ^ 3 := by nlinarith [pow_pos hδ 3]
  have hsca : 0 < √ca := Real.sqrt_pos.mpr hca
  set Z : ℝ := δ ^ 3 * W with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have b1 : C5 * δ ^ 3 * W + δ * (C5 * (1 + Λ) * δ ^ 3 * W) ≤ C5 * (2 + Λ) * Z := by
    have h : δ * (C5 * (1 + Λ) * δ ^ 3 * W) ≤ C5 * (1 + Λ) * δ ^ 3 * W := by
      have : 0 ≤ C5 * (1 + Λ) * δ ^ 3 * W := by positivity
      nlinarith
    rw [hZ]; nlinarith
  have b2 : C5 * (1 + Λ) * δ ^ 3 * W ≤ C5 * (2 + Λ) * Z := by
    rw [hZ]; have : 0 ≤ C5 * δ ^ 3 * W := by positivity
    nlinarith
  have b3 : √(hi * (C5 * δ ^ 3 * W + δ * (C5 * (1 + Λ) * δ ^ 3 * W)) ^ 2 +
      ahi * (C5 * (1 + Λ) * δ ^ 3 * W) ^ 2) ≤ √(hi + ahi) * (C5 * (2 + Λ) * Z) := by
    have hp : 0 ≤ C5 * (2 + Λ) * Z := by positivity
    rw [show √(hi + ahi) * (C5 * (2 + Λ) * Z) = √((hi + ahi) * (C5 * (2 + Λ) * Z) ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp]]
    refine Real.sqrt_le_sqrt ?_
    have c1' : (C5 * δ ^ 3 * W + δ * (C5 * (1 + Λ) * δ ^ 3 * W)) ^ 2 ≤ (C5 * (2 + Λ) * Z) ^ 2 :=
      pow_le_pow_left₀ (by positivity) b1 2
    have c2' : (C5 * (1 + Λ) * δ ^ 3 * W) ^ 2 ≤ (C5 * (2 + Λ) * Z) ^ 2 :=
      pow_le_pow_left₀ (by positivity) b2 2
    nlinarith [mul_le_mul_of_nonneg_left c1' hhi, mul_le_mul_of_nonneg_left c2' hahi0]
  have b4 : n * (C0 * δ ^ 6 * W) / (δ * √ca) ≤ S * C0 / (c1 * √ca) * Z := by
    have hn : n ≤ S / (c1 * δ) := by
      rw [le_div_iff₀ (by positivity)]
      calc n * (c1 * δ) = (n * δ) * c1 := by ring
        _ ≤ S / c1 * c1 := by gcongr
        _ = S := by field_simp
    have e : n * (C0 * δ ^ 6 * W) / (δ * √ca) =
        n * (C0 * δ ^ 5 * W / √ca) := by field_simp
    rw [e]
    calc n * (C0 * δ ^ 5 * W / √ca) ≤ S / (c1 * δ) * (C0 * δ ^ 5 * W / √ca) := by gcongr
      _ = S * C0 / (c1 * √ca) * (δ ^ 4 * W) := by field_simp
      _ ≤ S * C0 / (c1 * √ca) * Z := by
          have : 0 ≤ S * C0 / (c1 * √ca) * W := by positivity
          rw [hZ]; nlinarith
  have hexp : Real.exp (3 * V' / 2) ≤ Real.exp (3 * V / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hK1 : 0 ≤ √2 * (1 / √lo + √ahi / ca) := by positivity
  have hbr : √(3 / 2) * √(hi * (C5 * δ ^ 3 * W + δ * (C5 * (1 + Λ) * δ ^ 3 * W)) ^ 2 +
      ahi * (C5 * (1 + Λ) * δ ^ 3 * W) ^ 2) + n * (C0 * δ ^ 6 * W) / (δ * √ca) ≤
      (√(3 / 2) * (√(hi + ahi) * (C5 * (2 + Λ))) + S * C0 / (c1 * √ca)) * Z := by
    have := mul_le_mul_of_nonneg_left b3 (Real.sqrt_nonneg (3 / 2))
    nlinarith
  have hbr0 : 0 ≤ √(3 / 2) * √(hi * (C5 * δ ^ 3 * W + δ * (C5 * (1 + Λ) * δ ^ 3 * W)) ^ 2 +
      ahi * (C5 * (1 + Λ) * δ ^ 3 * W) ^ 2) + n * (C0 * δ ^ 6 * W) / (δ * √ca) := by
    positivity
  have hstep : √2 * (1 / √lo + √ahi / ca) * Real.exp (3 * V' / 2) *
      (√(3 / 2) * √(hi * (C5 * δ ^ 3 * W + δ * (C5 * (1 + Λ) * δ ^ 3 * W)) ^ 2 +
        ahi * (C5 * (1 + Λ) * δ ^ 3 * W) ^ 2) + n * (C0 * δ ^ 6 * W) / (δ * √ca)) ≤
      √2 * (1 / √lo + √ahi / ca) * Real.exp (3 * V / 2) *
        ((√(3 / 2) * (√(hi + ahi) * (C5 * (2 + Λ))) + S * C0 / (c1 * √ca)) * Z) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hexp hK1) hbr hbr0 (by positivity)
  have e : windowConstSharp c1 ca ahi lo hi C0 C5 Λ S V * δ ^ 3 * W = C5 * Z + √2 * (1 / √lo + √ahi / ca) *
      Real.exp (3 * V / 2) * ((√(3 / 2) * (√(hi + ahi) * (C5 * (2 + Λ))) + S * C0 / (c1 * √ca)) * Z) := by
    unfold windowConstSharp; rw [hZ]; ring
  have e2 : C5 * δ ^ 3 * W = C5 * Z := by rw [hZ]; ring
  rw [e]
  linarith [e2, hstep]

/-- **Inhomogeneous energy march through the window** (the sharp analogue of `window_from_top`).  Same data as
`window_from_top`, with the near-hyperbolic hypotheses `Sg, Qq` replaced by the frequency `λ`
(`c_k = a_k + a_{k+1} - δ² λ_k`, `lo ≤ λ ≤ hi`, `δ² hi ≤ c_a`, `a ≤ a_hi`) and the total variation `windowVar ≤ V`.
The continuation `F` of `f` satisfies `|F_k - ψ_k| ≤ windowConstSharp · δ³ W` for `k ∈ [J, m]`. -/
theorem window_from_top_sharp {a c ψ f lam : ℤ → ℝ} {J m N : ℤ}
    {δ W c1 ca ahi lo hi C0 C5 Λ S V : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hca : 0 < ca) (hlo : 0 < lo) (hC0 : 0 ≤ C0) (hC5 : 0 ≤ C5)
    (hΛ : 0 ≤ Λ) (hS : 0 ≤ S) (hhi : 0 ≤ hi) (hahi0 : 0 ≤ ahi) (hε : δ ^ 2 * hi ≤ ca) (hJm : J ≤ m)
    (hmN : m ≤ N) (hnδ : ((m - J : ℤ) : ℝ) * δ ≤ S / c1)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) (hahi : ∀ k ∈ Icc (J + 1) (m + 1), a k ≤ ahi)
    (hlam : ∀ k ∈ Ioc J m, lo ≤ lam k ∧ lam k ≤ hi)
    (hcl : ∀ k ∈ Ioc J m, c k = a k + a (k + 1) - δ ^ 2 * lam k) (hV : windowVar a lam J m ≤ V)
    (hdef : ∀ i ∈ Ioc J m, |jac a c ψ i| ≤ C0 * δ ^ 6 * W)
    (hrow : ∀ k ∈ Icc (m + 1) N, jac a c f k = 0)
    (h1 : |f m - ψ m| ≤ C5 * δ ^ 3 * ψ m)
    (h2 : |(f m - ψ m) - (f (m + 1) - ψ (m + 1))| ≤ C5 * δ ^ 5 * ψ m + C5 * δ ^ 3 * |ψ m - ψ (m + 1)|)
    (hψ0 : 0 ≤ ψ m) (hψW : ψ m ≤ W) (hLip : |ψ m - ψ (m + 1)| ≤ Λ * δ * W) :
    ∃ F : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c F k = 0) ∧ (∀ k ∈ Icc m (N + 1), F k = f k) ∧
      ∀ k ∈ Icc J m, |F k - ψ k| ≤ windowConstSharp c1 ca ahi lo hi C0 C5 Λ S V * δ ^ 3 * W := by
  have hane : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0 := fun k hk => (lt_of_lt_of_le hca (ha k hk)).ne'
  obtain ⟨F, hF, hFf⟩ := extend_below a c f J m N hJm hmN hane hrow
  refine ⟨F, hF, hFf, ?_⟩
  have hW : 0 ≤ W := le_trans hψ0 hψW
  have hmJ : (0 : ℝ) ≤ ((m - J : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - J := by omega
    exact_mod_cast this
  have hFm : F m = f m := hFf m (by rw [mem_Icc]; omega)
  have hFm1 : F (m + 1) = f (m + 1) := hFf (m + 1) (by rw [mem_Icc]; omega)
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  have hδ4 : δ ^ 4 ≤ δ ^ 3 := by nlinarith [pow_pos hδ 3]
  have hδ5 : δ ^ 5 ≤ δ ^ 4 := by nlinarith [pow_pos hδ 4]
  have t1 : |F m - ψ m| ≤ C5 * δ ^ 3 * W := by
    rw [hFm]; refine h1.trans ?_
    nlinarith [mul_nonneg hC5 hδ3]
  have t2 : |(F (m + 1) - ψ (m + 1)) - (F m - ψ m)| / δ ≤ C5 * (1 + Λ) * δ ^ 3 * W := by
    rw [div_le_iff₀ hδ, hFm, hFm1, abs_sub_comm]
    refine h2.trans ?_
    have a1 : C5 * δ ^ 5 * ψ m ≤ C5 * δ ^ 5 * W := by gcongr
    have a2 : C5 * δ ^ 3 * |ψ m - ψ (m + 1)| ≤ C5 * δ ^ 3 * (Λ * δ * W) := by gcongr
    have a3 : C5 * δ ^ 5 * W ≤ C5 * δ ^ 4 * W * δ := by nlinarith [mul_nonneg hC5 hW]
    have a4 : C5 * δ ^ 4 * W * δ ≤ C5 * δ ^ 3 * W * δ := by
      have := mul_nonneg hC5 hW
      nlinarith [mul_nonneg this (sub_nonneg.2 hδ4), hδ]
    have a5 : C5 * δ ^ 3 * (Λ * δ * W) = C5 * Λ * δ ^ 3 * W * δ := by ring
    nlinarith
  have hρ0 : 0 ≤ C0 * δ ^ 6 * W := by positivity
  have hdrow : ∀ k ∈ Ioc J m, |jac a c (fun i => F i - ψ i) k| ≤ C0 * δ ^ 6 * W := by
    intro k hk
    rw [mem_Ioc] at hk
    rw [jac_sub, hF k (by rw [mem_Icc]; omega), zero_sub, abs_neg]
    exact hdef k (by rw [mem_Ioc]; omega)
  have hmain := window_sharp_bound (a := a) (c := c) (d := fun i => F i - ψ i) (lam := lam) (J := J) (m := m)
    (δ := δ) (ca := ca) (ahi := ahi) (lo := lo) (hi := hi) (ρ0 := C0 * δ ^ 6 * W) (e0 := C5 * δ ^ 3 * W)
    (e1 := C5 * (1 + Λ) * δ ^ 3 * W) hδ hδ1 hca hlo hε hJm hρ0
    (fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega)) hahi hlam hcl hdrow t1 t2
  intro k hk
  refine (hmain k hk).trans ?_
  exact windowSharp_arith hδ hδ1 hc1 hca hlo hC0 hC5 hΛ hS hW hhi hahi0 hmJ hnδ hV

lemma windowSharp_telescope (g : ℤ → ℝ) {k m : ℤ} (h : k ≤ m) :
    ∑ j ∈ Ico k m, (g j - g (j + 1)) = g k - g m := by
  have key : ∀ n : ℕ, ∑ j ∈ Ico (m - n) m, (g j - g (j + 1)) = g (m - n) - g m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : m - ((n + 1 : ℕ) : ℤ) + 1 = m - n := by push_cast; ring
      rw [sum_Ico_split_bot _ (by push_cast; omega : m - ((n + 1 : ℕ) : ℤ) < m), e, ih]
      ring
  have := key (m - k).toNat
  rwa [show m - ((m - k).toNat : ℤ) = k by omega] at this

/-- **The variation is logarithmic** (hence `e^{3V/2}` is a power of `hi/lo`): if `λ > 0` is non-increasing with steps
`λ_k ≤ (1 + θ) λ_{k+1}` and `|a_{k+2} - a_{k+1}| ≤ q δ²`, `a ≥ c_a > 0`, `η = q δ²/c_a`, then
`windowVar ≤ (1 + η)(1 + θ) (log λ_{J+1} - log λ_m) + (m - J) η`. -/
theorem windowVar_le_log {a lam : ℤ → ℝ} {J m : ℤ} {θ q ca δ : ℝ} (hca : 0 < ca) (hθ : 0 ≤ θ) (hq : 0 ≤ q)
    (hlam : ∀ k ∈ Icc (J + 1) m, 0 < lam k)
    (hstep : ∀ k ∈ Ico (J + 1) m, lam (k + 1) ≤ lam k ∧ lam k ≤ (1 + θ) * lam (k + 1))
    (ha : ∀ k ∈ Ico (J + 1) m, ca ≤ a (k + 1)) (haq : ∀ k ∈ Ico (J + 1) m, |a (k + 2) - a (k + 1)| ≤ q * δ ^ 2)
    (hJm : J + 1 ≤ m) :
    windowVar a lam J m ≤ (1 + q * δ ^ 2 / ca) * (1 + θ) * (Real.log (lam (J + 1)) - Real.log (lam m)) +
      ((m - J : ℤ) : ℝ) * (q * δ ^ 2 / ca) := by
  set η : ℝ := q * δ ^ 2 / ca with hη
  have hη0 : 0 ≤ η := by positivity
  have hterm : ∀ k ∈ Ico (J + 1) m, |lam k - lam (k + 1)| / lam (k + 1) + |a (k + 2) - a (k + 1)| / a (k + 1) +
      (|lam k - lam (k + 1)| / lam (k + 1)) * (|a (k + 2) - a (k + 1)| / a (k + 1)) ≤
      (1 + η) * (1 + θ) * (Real.log (lam k) - Real.log (lam (k + 1))) + η := by
    intro k hk
    have hk1 : k ∈ Icc (J + 1) m := by rw [mem_Ico] at hk; rw [mem_Icc]; omega
    have hk2 : k + 1 ∈ Icc (J + 1) m := by rw [mem_Ico] at hk; rw [mem_Icc]; omega
    have h0 := hlam k hk1
    have h1 := hlam (k + 1) hk2
    obtain ⟨hs1, hs2⟩ := hstep k hk
    have hμ : |lam k - lam (k + 1)| / lam (k + 1) = lam k / lam (k + 1) - 1 := by
      rw [abs_of_nonneg (by linarith), sub_div, div_self h1.ne']
    have hμ' : |a (k + 2) - a (k + 1)| / a (k + 1) ≤ η := by
      have hac := ha k hk
      have : 0 < a (k + 1) := lt_of_lt_of_le hca hac
      rw [div_le_iff₀ this, hη]
      calc |a (k + 2) - a (k + 1)| ≤ q * δ ^ 2 := haq k hk
        _ = q * δ ^ 2 / ca * ca := by field_simp
        _ ≤ q * δ ^ 2 / ca * a (k + 1) := mul_le_mul_of_nonneg_left hac (by positivity)
    have hμ'0 : 0 ≤ |a (k + 2) - a (k + 1)| / a (k + 1) := by
      have hac := ha k hk
      have : 0 < a (k + 1) := lt_of_lt_of_le hca hac
      positivity
    set r := lam k / lam (k + 1) with hr
    have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ h1]; linarith
    have hr2 : r ≤ 1 + θ := by rw [hr, div_le_iff₀ h1]; linarith
    have hlogr : Real.log (lam k) - Real.log (lam (k + 1)) = Real.log r := by
      rw [hr, Real.log_div h0.ne' h1.ne']
    have hlog : (r - 1) / r ≤ Real.log r := by
      have := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < r)
      have e : (r - 1) / r = 1 - r⁻¹ := by field_simp
      rwa [e]
    have hr0 : 0 < r := by linarith
    have h3 : r - 1 ≤ (1 + θ) * Real.log r := by
      have : (r - 1) / (1 + θ) ≤ (r - 1) / r :=
        div_le_div_of_nonneg_left (by linarith) hr0 hr2
      rw [div_le_iff₀ (by linarith)] at this
      have h4 := hlog
      rw [div_le_iff₀ hr0] at h4
      nlinarith [mul_nonneg hθ (Real.log_nonneg hr1)]
    rw [hμ, hlogr]
    nlinarith [mul_nonneg hη0 (sub_nonneg.2 hr1)]
  unfold windowVar
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, windowSharp_telescope (fun k => Real.log (lam k)) hJm]
  have hcard : (∑ _k ∈ Ico (J + 1) m, η) ≤ ((m - J : ℤ) : ℝ) * η := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((Ico (J + 1) m).card : ℝ) ≤ ((m - J : ℤ) : ℝ) := by
      rw [Int.card_Ico]
      have h0 : (0 : ℤ) ≤ m - (J + 1) := by omega
      have : (((m - (J + 1)).toNat : ℕ) : ℤ) = m - (J + 1) := Int.toNat_of_nonneg h0
      have h2 : ((m - (J + 1)).toNat : ℝ) = ((m - (J + 1) : ℤ) : ℝ) := by exact_mod_cast this
      rw [h2]; push_cast; linarith
    exact mul_le_mul_of_nonneg_right this hη0
  linarith

/-- **`window_from_top_sharp` with an explicit (logarithmic) variation bound.**  If moreover `λ` is non-increasing
with steps `λ_k ≤ (1+θ) λ_{k+1}` and `|a_{k+2} - a_{k+1}| ≤ q δ²`, the constant is
`windowConstSharp` with `V = (1 + qδ²/c_a)(1 + θ) log(hi/lo) + S q/(c₁ c_a)`, so `e^{3V/2} = (hi/lo)^{3(1+qδ²/c_a)(1+θ)/2} ·
e^{3 S q/(2 c₁ c_a)}` is a *power of `hi/lo`* (`≈ A₀^{3/2}` for `λ ≈ |X|` on `[-A₀, -1]`, `θ, δ → 0`), against `e^{O(A₀²)}`. -/
theorem window_from_top_sharp_log {a c ψ f lam : ℤ → ℝ} {J m N : ℤ}
    {δ W c1 ca ahi lo hi C0 C5 Λ S θ q : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hca : 0 < ca) (hlo : 0 < lo) (hlohi : lo ≤ hi) (hC0 : 0 ≤ C0)
    (hC5 : 0 ≤ C5) (hΛ : 0 ≤ Λ) (hS : 0 ≤ S) (hθ : 0 ≤ θ) (hq : 0 ≤ q) (hahi0 : 0 ≤ ahi)
    (hε : δ ^ 2 * hi ≤ ca) (hJm : J ≤ m) (hmN : m ≤ N) (hnδ : ((m - J : ℤ) : ℝ) * δ ≤ S / c1)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) (hahi : ∀ k ∈ Icc (J + 1) (m + 1), a k ≤ ahi)
    (haq : ∀ k ∈ Ico (J + 1) m, |a (k + 2) - a (k + 1)| ≤ q * δ ^ 2)
    (hlam : ∀ k ∈ Ioc J m, lo ≤ lam k ∧ lam k ≤ hi)
    (hstep : ∀ k ∈ Ico (J + 1) m, lam (k + 1) ≤ lam k ∧ lam k ≤ (1 + θ) * lam (k + 1))
    (hcl : ∀ k ∈ Ioc J m, c k = a k + a (k + 1) - δ ^ 2 * lam k)
    (hdef : ∀ i ∈ Ioc J m, |jac a c ψ i| ≤ C0 * δ ^ 6 * W)
    (hrow : ∀ k ∈ Icc (m + 1) N, jac a c f k = 0)
    (h1 : |f m - ψ m| ≤ C5 * δ ^ 3 * ψ m)
    (h2 : |(f m - ψ m) - (f (m + 1) - ψ (m + 1))| ≤ C5 * δ ^ 5 * ψ m + C5 * δ ^ 3 * |ψ m - ψ (m + 1)|)
    (hψ0 : 0 ≤ ψ m) (hψW : ψ m ≤ W) (hLip : |ψ m - ψ (m + 1)| ≤ Λ * δ * W) :
    ∃ F : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c F k = 0) ∧ (∀ k ∈ Icc m (N + 1), F k = f k) ∧
      ∀ k ∈ Icc J m, |F k - ψ k| ≤ windowConstSharp c1 ca ahi lo hi C0 C5 Λ S
        ((1 + q * δ ^ 2 / ca) * (1 + θ) * Real.log (hi / lo) + S * q / (c1 * ca)) * δ ^ 3 * W := by
  have hhi : 0 ≤ hi := le_trans hlo.le hlohi
  have hlog0 : 0 ≤ Real.log (hi / lo) := Real.log_nonneg (by rw [le_div_iff₀ hlo]; linarith)
  have hη0 : 0 ≤ q * δ ^ 2 / ca := by positivity
  have hV0 : 0 ≤ (1 + q * δ ^ 2 / ca) * (1 + θ) * Real.log (hi / lo) + S * q / (c1 * ca) := by positivity
  have hmJ : (0 : ℝ) ≤ ((m - J : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - J := by omega
    exact_mod_cast this
  refine window_from_top_sharp hδ hδ1 hc1 hca hlo hC0 hC5 hΛ hS hhi hahi0 hε hJm hmN hnδ ha hahi hlam hcl ?_ hdef
    hrow h1 h2 hψ0 hψW hLip
  rcases eq_or_lt_of_le hJm with hJ | hJm'
  · subst hJ
    have : windowVar a lam J J = 0 := by unfold windowVar; simp
    rw [this]; exact hV0
  · have hJm1 : J + 1 ≤ m := by omega
    have hlam' : ∀ k ∈ Icc (J + 1) m, 0 < lam k := fun k hk =>
      lt_of_lt_of_le hlo (hlam k (by rw [mem_Icc] at hk; rw [mem_Ioc]; omega)).1
    have hmain := windowVar_le_log (a := a) (lam := lam) (J := J) (m := m) (θ := θ) (q := q) (ca := ca) (δ := δ)
      hca hθ hq hlam' hstep (fun k hk => ha (k + 1) (by rw [mem_Ico] at hk; rw [mem_Icc]; omega)) haq hJm1
    refine hmain.trans ?_
    have hJ1 : J + 1 ∈ Ioc J m := by rw [mem_Ioc]; omega
    have hmm : m ∈ Ioc J m := by rw [mem_Ioc]; omega
    have hlogle : Real.log (lam (J + 1)) - Real.log (lam m) ≤ Real.log (hi / lo) := by
      rw [← Real.log_div (hlam' _ (by rw [mem_Icc]; omega)).ne' (hlam' m (by rw [mem_Icc]; omega)).ne']
      refine Real.log_le_log (by have := hlam' (J + 1) (by rw [mem_Icc]; omega); have := hlam' m (by rw [mem_Icc]; omega); positivity) ?_
      rw [div_le_div_iff₀ (hlam' m (by rw [mem_Icc]; omega)) hlo]
      exact mul_le_mul (hlam _ hJ1).2 (hlam _ hmm).1 hlo.le hhi
    have hc2 : ((m - J : ℤ) : ℝ) * (q * δ ^ 2 / ca) ≤ S * q / (c1 * ca) := by
      have hn : ((m - J : ℤ) : ℝ) ≤ S / (c1 * δ) := by
        rw [le_div_iff₀ (by positivity)]
        calc ((m - J : ℤ) : ℝ) * (c1 * δ) = (((m - J : ℤ) : ℝ) * δ) * c1 := by ring
          _ ≤ S / c1 * c1 := by gcongr
          _ = S := by field_simp
      calc ((m - J : ℤ) : ℝ) * (q * δ ^ 2 / ca) ≤ S / (c1 * δ) * (q * δ ^ 2 / ca) := by gcongr
        _ = S * q / (c1 * ca) * δ := by field_simp
        _ ≤ S * q / (c1 * ca) * 1 := by
            have : 0 ≤ S * q / (c1 * ca) := by positivity
            exact mul_le_mul_of_nonneg_left hδ1 this
        _ = _ := mul_one _
    have : (1 + q * δ ^ 2 / ca) * (1 + θ) * (Real.log (lam (J + 1)) - Real.log (lam m)) ≤
        (1 + q * δ ^ 2 / ca) * (1 + θ) * Real.log (hi / lo) :=
      mul_le_mul_of_nonneg_left hlogle (by positivity)
    linarith

end FormalResearch.Special

/-- info: 'FormalResearch.Special.window_sharp_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_sharp_energy

/-- info: 'FormalResearch.Special.window_sharp_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_sharp_extract

/-- info: 'FormalResearch.Special.window_sharp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_sharp_bound

/-- info: 'FormalResearch.Special.window_from_top_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_from_top_sharp

/-- info: 'FormalResearch.Special.window_from_top_sharp_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_from_top_sharp_log

/-- info: 'FormalResearch.Special.windowVar_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.windowVar_le_log

