module

public import FormalResearch.Wigner.WignerDJacobi
public import FormalResearch.Special.JacobiBasic

/-!
# The Wigner differential equation for `d^j_{m'm}(θ)`

Paper: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:dODE`.  Standard references: Varshalovich
Ch. 4 (the `d`-function and its differential equation), Edmonds 4.1; the Jacobi equation is DLMF 18.8.1.

For `d = wignerSmallD j m' m` (`FormalResearch.Wigner.WignerD`, Condon–Shortley convention, the
paper's `d^j_{m'm}`; the paper writes `d^L_{Mσ}` for `m' = M`, `m = σ`; the equation is symmetric in
`(m, m')`) we prove, **for all rational `j m' m` and all real `θ`**, the division-free form
`wignerSmallD_ode`

  `D² d + (j(j+1) sin²θ - (m² + m'² - 2 m m' cos θ)) d = 0`,   `D = sin θ · d/dθ`,

and, on `θ ∈ (0, π)` (where `sin θ ≠ 0`), the textbook form `wignerSmallD_ode_cot`

  `d'' + cot θ · d' + (j(j+1) - (m² + m'² - 2 m m' cos θ)/sin²θ) d = 0`.

`D² d = sin θ (sin θ d')'` is `sin²θ (d'' + cot θ d')`, so the two are equivalent.  In the variable
`x = cos θ` (the paper's variable) the equation is `eq:dODE`,
`(1-x²) f'' - 2x f' + [j(j+1) - (m²+m'²-2mm'x)/(1-x²)] f = 0`, for `f(x) = d(arccos x)`,
`x ∈ (-1,1)` (`wignerSmallDx_ode`).

The proof is by the Jacobi form of `FormalResearch.Wigner.WignerDJacobi` in the chamber
`m' ≥ m`, `m'+m ≥ 0` (`μ = m'-m`, `ν = m'+m`, `k = j-m'`): the operator `D` acts on
`G_P(θ) = sin(θ/2)^μ cos(θ/2)^ν P(cos θ)` by the polynomial operator
`P ↦ ½ ((μ(1+x) - ν(1-x)) P - 2(1-x²) P')` (`wigG_deriv`), and `jacobi_ode` gives the polynomial
identity `Epoly_Epoly_jacobi`.  The other chambers follow from `d^j_{m'm} = (-1)^{m'-m} d^j_{mm'}
= d^j_{-m,-m'}` (`chamber_reduce`); non-admissible `(j,m',m)` give the zero function.
-/

@[expose] public section

namespace FormalResearch.Wigner

open Polynomial FormalResearch.Special

/-- The polynomial operator `E_{a,b} P = (a(1+x) - b(1-x)) P - 2(1-x²) P'`. -/
noncomputable def Epoly (a b : ℝ) (P : ℝ[X]) : ℝ[X] :=
  (C a * (1 + X) - C b * (1 - X)) * P - 2 * (1 - X ^ 2) * derivative P

lemma Epoly_C_mul (a b c : ℝ) (R : ℝ[X]) : Epoly a b (C c * R) = C c * Epoly a b R := by
  unfold Epoly
  rw [derivative_C_mul]
  ring

/-- `θ ↦ sin(θ/2)^μ cos(θ/2)^ν P(cos θ)`. -/
noncomputable def wigG (μ ν : ℕ) (P : ℝ[X]) (θ : ℝ) : ℝ :=
  Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν * P.eval (Real.cos θ)

lemma pow_pred_mul_self (s : ℝ) (μ : ℕ) : (μ : ℝ) * s ^ (μ - 1) * s = μ * s ^ μ := by
  rcases μ with _ | μ
  · simp
  · simp [pow_succ]; ring

lemma wigG_deriv (μ ν : ℕ) (P : ℝ[X]) (θ : ℝ) :
    ∃ d, HasDerivAt (wigG μ ν P) d θ ∧
      Real.sin θ * d = wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν P) θ := by
  have h0 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
  have h1 : HasDerivAt (fun x : ℝ => Real.sin (x / 2)) (Real.cos (θ / 2) * (1 / 2)) θ := h0.sin
  have h2 : HasDerivAt (fun x : ℝ => Real.cos (x / 2)) (-Real.sin (θ / 2) * (1 / 2)) θ := h0.cos
  have h3 : HasDerivAt (fun x : ℝ => P.eval (Real.cos x))
      ((derivative P).eval (Real.cos θ) * (-Real.sin θ)) θ :=
    (Polynomial.hasDerivAt P (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
  have h := ((h1.pow μ).mul (h2.pow ν)).mul h3
  refine ⟨_, h, ?_⟩
  set s := Real.sin (θ / 2) with hs
  set c := Real.cos (θ / 2) with hc
  have hsin : Real.sin θ = 2 * s * c := by
    rw [hs, hc, ← Real.sin_two_mul]; congr 1; ring
  have hcp : 1 + Real.cos θ = 2 * c ^ 2 := by
    rw [hc, show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    simp only [show 2 * (θ / 2) / 2 = θ / 2 by ring]; ring_nf
  have hcm : 1 - Real.cos θ = 2 * s ^ 2 := by
    rw [hs, show θ = 2 * (θ / 2) by ring, Real.cos_two_mul']
    simp only [show 2 * (θ / 2) / 2 = θ / 2 by ring]
    have := Real.sin_sq_add_cos_sq (θ / 2)
    nlinarith
  have e1 := pow_pred_mul_self s μ
  have e2 := pow_pred_mul_self c ν
  unfold wigG
  simp only [Epoly, eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X,
    eval_ofNat]
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [← hs, ← hc]
  have hcc : 1 - Real.cos θ ^ 2 = 4 * s ^ 2 * c ^ 2 := by
    have : 1 - Real.cos θ ^ 2 = (1 - Real.cos θ) * (1 + Real.cos θ) := by ring
    rw [this, hcm, hcp]; ring
  rw [hsin, hcc, hcp, hcm]
  generalize eval (Real.cos θ) P = p
  generalize eval (Real.cos θ) (derivative P) = q
  linear_combination (c ^ 2 * c ^ ν * p) * e1 - (s ^ 2 * s ^ μ * p) * e2

lemma Epoly_Epoly_jacobi (a b : ℝ) (k : ℕ) :
    Epoly a b (Epoly a b (jacobi a b k)) +
      (C ((2 * (k : ℝ) + a + b) * (2 * k + a + b + 2)) * (1 - X ^ 2)
        - C (2 * (a ^ 2 + b ^ 2)) + C (2 * (b ^ 2 - a ^ 2)) * X) * jacobi a b k = 0 := by
  have hode := jacobi_ode a b k
  simp only [map_sub, map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one] at hode ⊢
  unfold Epoly
  simp only [derivative_mul, derivative_sub, derivative_add, derivative_C, derivative_X,
    derivative_one, derivative_pow, derivative_ofNat, map_natCast]
  generalize derivative (derivative (jacobi a b k)) = P2 at hode ⊢
  generalize derivative (jacobi a b k) = P1 at hode ⊢
  generalize jacobi a b k = P at hode ⊢
  linear_combination (4 * (1 - X ^ 2)) * hode

/-- The operator `D = sin θ · d/dθ` on `θ ↦ sin(θ/2)^μ cos(θ/2)^ν P(cos θ)`. -/
lemma sin_mul_deriv_wigG (μ ν : ℕ) (P : ℝ[X]) (θ : ℝ) :
    Real.sin θ * deriv (wigG μ ν P) θ = wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν P) θ := by
  obtain ⟨d, hd, h⟩ := wigG_deriv μ ν P θ
  rw [hd.deriv]; exact h

lemma wigG_hasDerivAt (μ ν : ℕ) (P : ℝ[X]) (θ : ℝ) :
    HasDerivAt (wigG μ ν P) (deriv (wigG μ ν P) θ) θ := by
  obtain ⟨d, hd, -⟩ := wigG_deriv μ ν P θ
  rw [hd.deriv]; exact hd

/-- The `θ`-form Wigner equation for `wigG μ ν (jacobi μ ν k)`, without any division by `sin θ`:
`D² G + (j(j+1) sin²θ - (m² + m'² - 2 m m' cos θ)) G = 0`, `D = sin θ d/dθ`, with
`j = k + (μ+ν)/2`, `m² + m'² = (μ²+ν²)/2`, `m m' = (ν²-μ²)/4`. -/
theorem wigG_ode (μ ν k : ℕ) (θ : ℝ) :
    Real.sin θ * deriv (fun t => Real.sin t * deriv (wigG μ ν (jacobi μ ν k)) t) θ
      + (((k : ℝ) + (μ + ν) / 2) * ((k : ℝ) + (μ + ν) / 2 + 1) * Real.sin θ ^ 2
          - (((μ : ℝ) ^ 2 + ν ^ 2) / 2 - ((ν : ℝ) ^ 2 - μ ^ 2) / 2 * Real.cos θ))
        * wigG μ ν (jacobi μ ν k) θ = 0 := by
  have h1 : (fun t => Real.sin t * deriv (wigG μ ν (jacobi μ ν k)) t) =
      wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν (jacobi μ ν k)) :=
    funext fun t => sin_mul_deriv_wigG μ ν _ t
  rw [h1, sin_mul_deriv_wigG, Epoly_C_mul, ← mul_assoc, ← C_mul]
  have hp := congrArg (Polynomial.eval (Real.cos θ)) (Epoly_Epoly_jacobi (μ : ℝ) ν k)
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_pow, eval_one, eval_X, eval_zero] at hp
  unfold wigG
  rw [Polynomial.eval_mul, eval_C]
  have hsin : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    rw [Real.sin_sq]
  rw [hsin]
  generalize Epoly (μ : ℝ) ν (Epoly (μ : ℝ) ν (jacobi μ ν k)) = R at hp ⊢
  linear_combination (Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν / 4) * hp


/-! ### Chamber `m' ≥ m`, `m' + m ≥ 0` -/

/-- `√(k!(k+μ+ν)!/((k+μ)!(k+ν)!))`, the normalisation of `d^j_{m'm}` in its Jacobi form. -/
noncomputable def wigNorm (μ ν k : ℕ) : ℝ :=
  Real.sqrt ((k.factorial : ℝ) * (k + μ + ν).factorial /
    (((k + μ).factorial : ℝ) * (k + ν).factorial))

lemma wignerJacobiForm_eq (μ ν k : ℕ) (θ : ℝ) :
    wignerJacobiForm μ ν k θ = wigNorm μ ν k * wigG μ ν (jacobi μ ν k) θ := by
  unfold wignerJacobiForm wigNorm wigG; ring

/-- `d^j_{m'm}(θ) = (-1)^μ N · sin(θ/2)^μ cos(θ/2)^ν P_k^{(μ,ν)}(cos θ)` as an identity of functions. -/
lemma wignerSmallD_chamber_A_fun {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν)
    (hk : j - m' = k) :
    wignerSmallD j m' m =
      fun θ => ((-1 : ℝ) ^ μ * wigNorm μ ν k) * wigG μ ν (jacobi μ ν k) θ :=
  funext fun θ => by rw [wignerSmallD_chamber_A hμ hν hk θ, wignerJacobiForm_eq]; ring

/-- The four numbers `j ± m`, `j ± m'` are natural numbers: `d^j_{m'm}` is not identically zero. -/
def WAdm (j m' m : ℚ) : Prop := IsNat (j + m') ∧ IsNat (j - m') ∧ IsNat (j + m) ∧ IsNat (j - m)

lemma wignerSmallD_eq_zero_of_not_adm {j m' m : ℚ} (h : ¬ WAdm j m' m) :
    wignerSmallD j m' m = 0 := by
  funext θ
  have key : ¬ IsNat (j + m') ∨ ¬ IsNat (j - m') ∨ ¬ IsNat (j + m) ∨ ¬ IsNat (j - m) := by
    unfold WAdm at h; tauto
  unfold wignerSmallD
  rcases key with h | h | h | h <;> simp [fq_of_not_isNat h]

lemma adm_chamberA {j m' m : ℚ} (h : WAdm j m' m) (h1 : 0 ≤ m' - m) (h2 : 0 ≤ m' + m) :
    ∃ μ ν k : ℕ, m' - m = μ ∧ m' + m = ν ∧ j - m' = k := by
  obtain ⟨-, ⟨k, hk⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := h
  have hkc : (k : ℚ) ≤ c := by linarith
  have hkb : (k : ℚ) ≤ b := by linarith
  refine ⟨c - k, b - k, k, ?_, ?_, hk⟩
  · rw [Nat.cast_sub (by exact_mod_cast hkc)]; linarith
  · rw [Nat.cast_sub (by exact_mod_cast hkb)]; linarith

/-- Real-number form of the chamber data. -/
lemma chamberA_real {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν)
    (hk : j - m' = k) :
    (m' : ℝ) = ((μ : ℝ) + ν) / 2 ∧ (m : ℝ) = ((ν : ℝ) - μ) / 2 ∧ (j : ℝ) = k + ((μ : ℝ) + ν) / 2 := by
  have h1 : m' = ((μ : ℚ) + ν) / 2 := by linarith
  have h2 : m = ((ν : ℚ) - μ) / 2 := by linarith
  have h3 : j = (k : ℚ) + ((μ : ℚ) + ν) / 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; push_cast; ring
  · rw [h2]; push_cast; ring
  · rw [h3]; push_cast; ring

/-! ### The `θ`-form ODE for all chambers -/

/-- The Wigner operator `D² f + (λ sin²θ - (a - b cos θ)) f`, `D = sin θ · d/dθ`. -/
noncomputable def wigOdeExpr (f : ℝ → ℝ) (lam a b θ : ℝ) : ℝ :=
  Real.sin θ * deriv (fun t => Real.sin t * deriv f t) θ +
    (lam * Real.sin θ ^ 2 - (a - b * Real.cos θ)) * f θ

lemma wigOdeExpr_smul (c : ℝ) (f : ℝ → ℝ) (lam a b θ : ℝ) :
    wigOdeExpr (fun t => c * f t) lam a b θ = c * wigOdeExpr f lam a b θ := by
  unfold wigOdeExpr
  have h1 : (fun t => Real.sin t * deriv (fun s => c * f s) t) =
      fun t => c * (Real.sin t * deriv f t) := by
    funext t; rw [deriv_const_mul_field']; ring
  rw [h1, deriv_const_mul_field']; ring

lemma wigOdeExpr_zero (lam a b θ : ℝ) : wigOdeExpr (0 : ℝ → ℝ) lam a b θ = 0 := by
  unfold wigOdeExpr
  simp

/-- Reduction of a property of `(m', m)` to the chamber `m' ≥ m`, `m' + m ≥ 0`, given its
invariance under `(m', m) ↦ (m, m')` and `(m', m) ↦ (-m, -m')`. -/
lemma chamber_reduce (S : ℚ → ℚ → Prop)
    (hA : ∀ m' m, 0 ≤ m' - m → 0 ≤ m' + m → S m' m)
    (hswap : ∀ m' m, S m m' → S m' m) (hneg : ∀ m' m, S (-m) (-m') → S m' m) :
    ∀ m' m, S m' m := by
  intro m' m
  by_cases h2 : 0 ≤ m' + m
  · by_cases h1 : 0 ≤ m' - m
    · exact hA m' m h1 h2
    · exact hswap m' m (hA m m' (by linarith) (by linarith))
  · apply hneg
    by_cases h1 : 0 ≤ m' - m
    · exact hA (-m) (-m') (by linarith) (by linarith)
    · exact hswap _ _ (hA (-m') (-m) (by linarith) (by linarith))

/-- The Wigner equation in the chamber `m' ≥ m`, `m' + m ≥ 0`. -/
lemma wignerSmallD_ode_A (j m' m : ℚ) (h1 : 0 ≤ m' - m) (h2 : 0 ≤ m' + m) (θ : ℝ) :
    wigOdeExpr (wignerSmallD j m' m) ((j : ℝ) * (j + 1)) ((m : ℝ) ^ 2 + (m' : ℝ) ^ 2)
      (2 * m * m') θ = 0 := by
  by_cases hadm : WAdm j m' m
  · obtain ⟨μ, ν, k, hμ, hν, hk⟩ := adm_chamberA hadm h1 h2
    obtain ⟨e1, e2, e3⟩ := chamberA_real hμ hν hk
    rw [wignerSmallD_chamber_A_fun hμ hν hk, wigOdeExpr_smul]
    have := wigG_ode μ ν k θ
    have h : wigOdeExpr (wigG μ ν (jacobi μ ν k)) ((j : ℝ) * (j + 1)) ((m : ℝ) ^ 2 + (m' : ℝ) ^ 2)
        (2 * m * m') θ = 0 := by
      rw [e1, e2, e3]
      unfold wigOdeExpr
      convert this using 3
      all_goals ring
    rw [h, mul_zero]
  · rw [wignerSmallD_eq_zero_of_not_adm hadm]
    exact wigOdeExpr_zero _ _ _ _

/-- **Wigner differential equation** for `d^j_{m'm}(θ)` (paper `eq:dODE` in the variable `θ`),
division-free form valid for all rational `j m' m` (the zero function when `j ± m`, `j ± m'` are
not all natural numbers) and all real `θ`:
`sin θ · (sin t · d'(t))'(θ) + (j(j+1) sin²θ - (m² + m'² - 2 m m' cos θ)) d(θ) = 0`. -/
theorem wignerSmallD_ode (j m' m : ℚ) (θ : ℝ) :
    Real.sin θ * deriv (fun t => Real.sin t * deriv (wignerSmallD j m' m) t) θ +
      (((j : ℝ) * (j + 1)) * Real.sin θ ^ 2 -
        (((m : ℝ) ^ 2 + (m' : ℝ) ^ 2) - 2 * m * m' * Real.cos θ)) * wignerSmallD j m' m θ = 0 := by
  have key : ∀ m' m : ℚ, ∀ (j : ℚ) (θ : ℝ),
      wigOdeExpr (wignerSmallD j m' m) ((j : ℝ) * (j + 1)) ((m : ℝ) ^ 2 + (m' : ℝ) ^ 2)
        (2 * m * m') θ = 0 := by
    refine chamber_reduce (fun m' m => ∀ (j : ℚ) (θ : ℝ),
      wigOdeExpr (wignerSmallD j m' m) ((j : ℝ) * (j + 1)) ((m : ℝ) ^ 2 + (m' : ℝ) ^ 2)
        (2 * m * m') θ = 0) ?_ ?_ ?_
    · intro m' m h1 h2 j θ
      exact wignerSmallD_ode_A j m' m h1 h2 θ
    · intro m' m h j θ
      have hf : wignerSmallD j m' m = fun t => sgn (m' - m) * wignerSmallD j m m' t :=
        funext fun t => wignerSmallD_swap j m' m t
      rw [hf, wigOdeExpr_smul]
      have := h j θ
      rw [show (m : ℝ) ^ 2 + (m' : ℝ) ^ 2 = (m' : ℝ) ^ 2 + (m : ℝ) ^ 2 by ring,
        show 2 * (m : ℝ) * m' = 2 * m' * m by ring, this, mul_zero]
    · intro m' m h j θ
      have hf : wignerSmallD j m' m = wignerSmallD j (-m) (-m') :=
        funext fun t => (wignerSmallD_neg j m' m t).symm
      rw [hf]
      have := h j θ
      push_cast at this
      rw [show (m : ℝ) ^ 2 + (m' : ℝ) ^ 2 = (-(m' : ℝ)) ^ 2 + (-(m : ℝ)) ^ 2 by ring,
        show 2 * (m : ℝ) * m' = 2 * -(m' : ℝ) * -(m : ℝ) by ring]
      exact this
  have := key m' m j θ
  unfold wigOdeExpr at this
  exact this

/-! ### Smoothness, the `cot` form and the `x = cos θ` form -/

lemma wignerTerm_contDiff (j m' m : ℚ) (s : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun θ => wignerTerm j m' m θ s) := by
  unfold wignerTerm wignerMag
  fun_prop

/-- `d^j_{m'm}` is smooth in `θ` (a finite sum of products of powers of `sin θ/2`, `cos θ/2`). -/
theorem wignerSmallD_contDiff (j m' m : ℚ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (wignerSmallD j m' m) := by
  have : wignerSmallD j m' m = fun θ =>
      Real.sqrt (fq (j + m') * fq (j - m') * fq (j + m) * fq (j - m)) *
        ∑ s ∈ Finset.range (⌊j - m'⌋₊ + 1), wignerTerm j m' m θ s := by
    funext θ; unfold wignerSmallD; rw [finsum_wignerTerm_eq_sum]
  rw [this]
  exact contDiff_const.mul (ContDiff.sum fun s _ => wignerTerm_contDiff j m' m s)

lemma wignerSmallD_differentiable (j m' m : ℚ) : Differentiable ℝ (wignerSmallD j m' m) :=
  (wignerSmallD_contDiff j m' m (n := 1)).differentiable one_ne_zero

lemma wignerSmallD_deriv_differentiable (j m' m : ℚ) :
    Differentiable ℝ (deriv (wignerSmallD j m' m)) :=
  ((wignerSmallD_contDiff j m' m (n := 1 + 1)).deriv').differentiable one_ne_zero

lemma deriv_sin_mul_deriv {d : ℝ → ℝ} (hd' : Differentiable ℝ (deriv d)) (θ : ℝ) :
    deriv (fun t => Real.sin t * deriv d t) θ =
      Real.cos θ * deriv d θ + Real.sin θ * deriv (deriv d) θ := by
  have h := (Real.hasDerivAt_sin θ).mul (hd' θ).hasDerivAt
  exact h.deriv

/-- **Wigner differential equation, textbook form** (`d'' + cot θ d' + (j(j+1) - (m²+m'²-2mm' cos θ)/sin²θ) d = 0`)
for `θ` with `sin θ ≠ 0`, all rational `j m' m`. -/
theorem wignerSmallD_ode_cot (j m' m : ℚ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    deriv (deriv (wignerSmallD j m' m)) θ + Real.cos θ / Real.sin θ * deriv (wignerSmallD j m' m) θ +
      (((j : ℝ) * (j + 1)) - (((m : ℝ) ^ 2 + (m' : ℝ) ^ 2) - 2 * m * m' * Real.cos θ) /
        Real.sin θ ^ 2) * wignerSmallD j m' m θ = 0 := by
  have h := wignerSmallD_ode j m' m θ
  rw [deriv_sin_mul_deriv (wignerSmallD_deriv_differentiable j m' m)] at h
  generalize deriv (deriv (wignerSmallD j m' m)) θ = D2 at h ⊢
  generalize deriv (wignerSmallD j m' m) θ = D1 at h ⊢
  generalize wignerSmallD j m' m θ = d0 at h ⊢
  generalize Real.sin θ = S at *
  generalize Real.cos θ = C at *
  field_simp
  linear_combination h

section arccos

variable {d : ℝ → ℝ}

lemma sin_arccos_pos {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : 0 < Real.sin (Real.arccos x) := by
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  nlinarith [hx.1, hx.2]

lemma hasDerivAt_comp_arccos (hd : Differentiable ℝ d) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => d (Real.arccos y))
      (-(deriv d (Real.arccos x)) / Real.sin (Real.arccos x)) x := by
  have h1 := Real.hasDerivAt_arccos (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have h2 : HasDerivAt d (deriv d (Real.arccos x)) (Real.arccos x) :=
    (hd (Real.arccos x)).hasDerivAt
  have h := h2.comp x h1
  rw [Real.sin_arccos]
  exact h.congr_deriv (by ring)

lemma deriv_comp_arccos_eventually (hd : Differentiable ℝ d) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun y => d (Real.arccos y)) =ᶠ[nhds x]
      fun y => -(deriv d (Real.arccos y)) / Real.sin (Real.arccos y) := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact (hasDerivAt_comp_arccos hd hy).deriv

/-- Second derivative of `d ∘ arccos`. -/
lemma deriv_deriv_comp_arccos (hd : Differentiable ℝ d) (hd' : Differentiable ℝ (deriv d)) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv (fun y => d (Real.arccos y))) x =
      (deriv (deriv d) (Real.arccos x) - x * deriv d (Real.arccos x) / Real.sin (Real.arccos x)) /
        Real.sin (Real.arccos x) ^ 2 := by
  rw [(deriv_comp_arccos_eventually hd hx).deriv_eq]
  have hS := sin_arccos_pos hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])
  have h1 := Real.hasDerivAt_arccos (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have hu : HasDerivAt (fun y => deriv d (Real.arccos y))
      (deriv (deriv d) (Real.arccos x) * (-(1 / √(1 - x ^ 2)))) x :=
    ((hd' (Real.arccos x)).hasDerivAt).comp x h1
  have hs : HasDerivAt (fun y => Real.sin (Real.arccos y))
      (Real.cos (Real.arccos x) * (-(1 / √(1 - x ^ 2)))) x :=
    (Real.hasDerivAt_sin _).comp x h1
  have hg : HasDerivAt (fun y => -deriv d (Real.arccos y) / Real.sin (Real.arccos y)) _ x :=
    (hu.neg).div hs hS.ne'
  rw [hg.deriv]
  simp only [Pi.neg_apply, Real.sin_arccos, hcos]
  rw [Real.sin_arccos] at hS
  have hq : 0 < √(1 - x ^ 2) := hS
  have hq2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith [hx.1, hx.2])
  generalize deriv (deriv d) (Real.arccos x) = D2
  generalize deriv d (Real.arccos x) = D1
  generalize √(1 - x ^ 2) = S at *
  field_simp

end arccos

/-- `d^j_{m'm}` as a function of `x = cos θ` (the paper's variable): `d(arccos x)`. -/
noncomputable def wignerSmallDx (j m' m : ℚ) (x : ℝ) : ℝ := wignerSmallD j m' m (Real.arccos x)

lemma wignerSmallDx_eq (j m' m : ℚ) :
    wignerSmallDx j m' m = fun y => wignerSmallD j m' m (Real.arccos y) := rfl

/-- On `(-1,1)`: `d/dx d^j_{m'm}(arccos x) = -(∂_θ d)/sin θ`. -/
theorem hasDerivAt_wignerSmallDx (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (wignerSmallDx j m' m)
      (-(deriv (wignerSmallD j m' m) (Real.arccos x)) / Real.sin (Real.arccos x)) x :=
  hasDerivAt_comp_arccos (wignerSmallD_differentiable j m' m) hx

/-- `(1 - x²) d/dx = - sin θ · d/dθ` on `d^j_{m'm}`, `θ = arccos x`, `x ∈ (-1,1)`. -/
theorem one_sub_sq_mul_deriv_wignerSmallDx (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * deriv (wignerSmallDx j m' m) x =
      -(Real.sin (Real.arccos x) * deriv (wignerSmallD j m' m) (Real.arccos x)) := by
  rw [(hasDerivAt_wignerSmallDx j m' m hx).deriv]
  have hS := sin_arccos_pos hx
  have hq : Real.sin (Real.arccos x) ^ 2 = 1 - x ^ 2 := by
    rw [Real.sin_arccos]; exact Real.sq_sqrt (by nlinarith [hx.1, hx.2])
  rw [← hq]
  field_simp

/-- **Wigner differential equation in `x = cos θ`** (paper `eq:dODE`): for `x ∈ (-1,1)` and all
rational `j m' m`, with `f(x) = d^j_{m'm}(arccos x)`,
`(1-x²) f'' - 2x f' + [j(j+1) - (m² + m'² - 2mm'x)/(1-x²)] f = 0`. -/
theorem wignerSmallDx_ode (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * deriv (deriv (wignerSmallDx j m' m)) x -
        2 * x * deriv (wignerSmallDx j m' m) x +
      (((j : ℝ) * (j + 1)) - (((m : ℝ) ^ 2 + (m' : ℝ) ^ 2) - 2 * m * m' * x) / (1 - x ^ 2)) *
        wignerSmallDx j m' m x = 0 := by
  have hθ := wignerSmallD_ode j m' m (Real.arccos x)
  rw [deriv_sin_mul_deriv (wignerSmallD_deriv_differentiable j m' m)] at hθ
  have hcos : Real.cos (Real.arccos x) = x :=
    Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])
  have hS := sin_arccos_pos hx
  have hq : Real.sin (Real.arccos x) ^ 2 = 1 - x ^ 2 := by
    rw [Real.sin_arccos]; exact Real.sq_sqrt (by nlinarith [hx.1, hx.2])
  rw [(hasDerivAt_wignerSmallDx j m' m hx).deriv, wignerSmallDx_eq,
    deriv_deriv_comp_arccos (wignerSmallD_differentiable j m' m)
    (wignerSmallD_deriv_differentiable j m' m) hx]
  beta_reduce
  rw [hcos] at hθ
  rw [← hq]
  generalize deriv (deriv (wignerSmallD j m' m)) (Real.arccos x) = D2 at hθ ⊢
  generalize deriv (wignerSmallD j m' m) (Real.arccos x) = D1 at hθ ⊢
  generalize wignerSmallD j m' m (Real.arccos x) = d0 at hθ ⊢
  generalize Real.sin (Real.arccos x) = S at *
  field_simp
  linear_combination hθ

/-- info: 'FormalResearch.Wigner.wigG_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wigG_ode

/-- info: 'FormalResearch.Wigner.wignerSmallD_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_ode

/-- info: 'FormalResearch.Wigner.wignerSmallD_ode_cot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_ode_cot

/-- info: 'FormalResearch.Wigner.wignerSmallD_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_contDiff

/-- info: 'FormalResearch.Wigner.wignerSmallDx_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallDx_ode

/-- info: 'FormalResearch.Wigner.hasDerivAt_wignerSmallDx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_wignerSmallDx

/-- info: 'FormalResearch.Wigner.one_sub_sq_mul_deriv_wignerSmallDx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_sub_sq_mul_deriv_wignerSmallDx

end FormalResearch.Wigner
