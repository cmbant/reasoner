module

public import FormalResearch.Racah.P2AnalyticHeadline
public import FormalResearch.Racah.P2AnalyticBridge3j
public import FormalResearch.Racah.P2AnalyticBridge6j
public import FormalResearch.Racah.P2AnalyticCarrier6jPoly
public import FormalResearch.Special.JacobiInt
public import FormalResearch.Special.JacobiZeros

/-!
# Weyl P2: the leading coefficients of the carriers (`eq:WignerJacobiMonic`, `lem:sqrtfreecarrier`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:WignerJacobiMonic`,
`lem:sqrtfreecarrier` ("their leading coefficients are the constants `k_{3j}`, `k_{6j}` of
`eq:WignerJacobiMonic`"), and the end of its proof ("the leading coefficient obeys a recursion
independent of the large scale, so it equals its zero-scale value, at which `eq:sqrtfreecarrier` is
`eq:WignerJacobiMonic`").

The paper's statement is
`d^L_{Mσ}(arccos x) = k_{3j} W_{3j}(x) P̂^{(p_+,p_-)}_{L-L₀}((1-x)/2)`, `P̂` the monic Jacobi polynomial in
`τ = (1-x)/2`, and likewise for `6j`.  Here the constants are *identified*: `k_{3j} = lead3 M σ k`,
`k_{6j} = kLead m n d` (the `τ^k`-coefficients of the carriers), and

`k = sign · √(k!(k+μ+ν)!/((k+μ)!(k+ν)!)) · (-2)^k · [X^k] P_k^{(μ,ν)} = sign · (-1)^k
 √(k!(k+μ+ν)!/((k+μ)!(k+ν)!)) · (k+μ+ν+1)_k / k!`,

with `(μ,ν) = (p_+,p_-) = (|M-σ|,|M+σ|)` for `3j` (sign `(-1)^{μ}` if `σ ≤ M`, else `+1`, the sign
`ε(M,σ)` of the Wigner extremal value) and `(μ,ν) = (m-n, m+n)` for `6j` (no sign): the factor
`(-2)^k` is the `k`th power of the leading coefficient of `x = 1 - 2τ`.

## Route

`dZero3_eq_wignerD` (resp. `dZero6c_eq_wignerD`) and the chamber Jacobi forms
`wignerSmallD_chamber_A..D` give `P̃(τ; 0) = sign · c_k · P_k^{(μ,ν)}(1-2τ)` on `τ ∈ (0,1)`; infinitely
many points give the polynomial identity in `τ` (`Polynomial.eq_of_infinite_eval_eq`); the top
coefficients are compared with `jacobi_coeff_self`.  (The paper instead compares the *recursions* of the
leading coefficients; the route here needs no separate recursion for the Jacobi side.)

## Results

* `lead3_eq_jacobi`, `lead3_eq_closed`: `lead3 M σ k` in terms of the Jacobi leading coefficient and in
  closed form; `wignerD3_eq_lead_mul_monic`: `eq:WignerJacobiMonic` for `3j` with `k_{3j} = lead3`.
* `kLead_eq_jacobi`, `kLead_eq_closed`, `wignerD6_eq_kLead_mul_monic`: the same for `6j`
  (canonical sector `m ∓ n` natural).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Special Polynomial Set

/-- The Wigner normalisation `√(k!(k+μ+ν)!/((k+μ)!(k+ν)!))` of the Jacobi form of `d^j_{m'm}`. -/
noncomputable def wignerJacobiNorm (μ ν k : ℕ) : ℝ :=
  Real.sqrt ((k.factorial : ℝ) * (k + μ + ν).factorial /
    (((k + μ).factorial : ℝ) * (k + ν).factorial))

/-- The paper's monic Jacobi polynomial `P̂_k^{(μ,ν)}((1-x)/2)` in `τ = (1-x)/2`: the Jacobi
polynomial `P_k^{(μ,ν)}(1-2τ)` divided by its leading coefficient `(-2)^k [X^k] P_k^{(μ,ν)}`. -/
noncomputable def jacobiMonicTau (μ ν k : ℕ) : ℝ[X] :=
  C (((jacobi (μ : ℝ) (ν : ℝ) k).coeff k * (-2) ^ k)⁻¹) *
    (jacobi (μ : ℝ) (ν : ℝ) k).comp (C (-2) * X + C 1)

/-- `P_k^{(μ,ν)}(1-2τ)` as a polynomial in `τ`. -/
noncomputable def jacobiTau (μ ν k : ℕ) : ℝ[X] :=
  (jacobi (μ : ℝ) (ν : ℝ) k).comp (C (-2) * X + C 1)

lemma eval_jacobiTau (μ ν k : ℕ) (τ : ℝ) :
    (jacobiTau μ ν k).eval τ = (jacobi (μ : ℝ) (ν : ℝ) k).eval (1 - 2 * τ) := by
  simp [jacobiTau, eval_comp]; ring_nf

lemma natDegree_linTau : (C (-2 : ℝ) * X + C 1).natDegree = 1 := by
  compute_degree!

lemma coeff_jacobiTau_top (μ ν k : ℕ) :
    (jacobiTau μ ν k).coeff k = (jacobi (μ : ℝ) (ν : ℝ) k).coeff k * (-2) ^ k := by
  have hd : (jacobiTau μ ν k).natDegree = k := by
    unfold jacobiTau
    rw [natDegree_comp, natDegree_linTau, jacobi_natDegree, mul_one]
  have hl : (C (-2 : ℝ) * X + C 1).leadingCoeff = -2 := by
    rw [leadingCoeff, natDegree_linTau]; simp [coeff_one]
  have hlc : (jacobi (μ : ℝ) (ν : ℝ) k).leadingCoeff = (jacobi (μ : ℝ) (ν : ℝ) k).coeff k := by
    rw [leadingCoeff, jacobi_natDegree]
  have := leadingCoeff_comp (p := jacobi (μ : ℝ) (ν : ℝ) k) (q := C (-2 : ℝ) * X + C 1)
    (by rw [natDegree_linTau]; norm_num)
  rw [hl, hlc, jacobi_natDegree] at this
  calc (jacobiTau μ ν k).coeff k = (jacobiTau μ ν k).leadingCoeff := by rw [leadingCoeff, hd]
    _ = _ := this

lemma jacobi_lead_ne_zero (μ ν k : ℕ) : (jacobi (μ : ℝ) (ν : ℝ) k).coeff k * (-2) ^ k ≠ 0 :=
  mul_ne_zero (jacobi_coeff_self_ne_zero (μ : ℝ) (ν : ℝ) (by positivity) (by positivity) k)
    (pow_ne_zero _ (by norm_num))

/-- The paper's `P̂` is monic of degree `k`. -/
theorem jacobiMonicTau_monic (μ ν k : ℕ) : (jacobiMonicTau μ ν k).Monic := by
  have hne := jacobi_lead_ne_zero μ ν k
  have hd : (jacobiTau μ ν k).natDegree = k := by
    unfold jacobiTau
    rw [natDegree_comp, natDegree_linTau, jacobi_natDegree, mul_one]
  unfold Monic
  have : jacobiMonicTau μ ν k = C (((jacobi (μ : ℝ) (ν : ℝ) k).coeff k * (-2) ^ k)⁻¹) *
      jacobiTau μ ν k := rfl
  rw [this, leadingCoeff_mul, leadingCoeff_C, leadingCoeff, hd, coeff_jacobiTau_top]
  exact inv_mul_cancel₀ hne

theorem natDegree_jacobiMonicTau (μ ν k : ℕ) : (jacobiMonicTau μ ν k).natDegree = k := by
  have hne := jacobi_lead_ne_zero μ ν k
  have hd : (jacobiTau μ ν k).natDegree = k := by
    unfold jacobiTau
    rw [natDegree_comp, natDegree_linTau, jacobi_natDegree, mul_one]
  have : jacobiMonicTau μ ν k = C (((jacobi (μ : ℝ) (ν : ℝ) k).coeff k * (-2) ^ k)⁻¹) *
      jacobiTau μ ν k := rfl
  rw [this, natDegree_C_mul (inv_ne_zero hne), hd]

/-- The Jacobi form at `θ = arccos x`:
`c_k · √(((1-x)/2)^μ ((1+x)/2)^ν) · P_k^{(μ,ν)}(x)`. -/
lemma wignerJacobiForm_arccos (μ ν k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    wignerJacobiForm μ ν k (Real.arccos x) =
      wignerJacobiNorm μ ν k * Real.sqrt (((1 - x) / 2) ^ μ * ((1 + x) / 2) ^ ν) *
        (jacobi (μ : ℝ) (ν : ℝ) k).eval x := by
  have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have h0 : 0 ≤ Real.arccos x := Real.arccos_nonneg x
  have hpi : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
  have hs : Real.sin (Real.arccos x / 2) = Real.sqrt ((1 - x) / 2) := by
    have h2 : Real.sin (Real.arccos x / 2) ^ 2 = (1 - x) / 2 := by
      have := Real.cos_sq (Real.arccos x / 2)
      rw [show 2 * (Real.arccos x / 2) = Real.arccos x by ring, hc] at this
      nlinarith [Real.sin_sq_add_cos_sq (Real.arccos x / 2)]
    have hn : 0 ≤ Real.sin (Real.arccos x / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [← h2, Real.sqrt_sq hn]
  have hco : Real.cos (Real.arccos x / 2) = Real.sqrt ((1 + x) / 2) := by
    have h2 : Real.cos (Real.arccos x / 2) ^ 2 = (1 + x) / 2 := by
      have := Real.cos_sq (Real.arccos x / 2)
      rw [show 2 * (Real.arccos x / 2) = Real.arccos x by ring, hc] at this
      linarith
    have hn : 0 ≤ Real.cos (Real.arccos x / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    rw [← h2, Real.sqrt_sq hn]
  have hA : 0 ≤ (1 - x) / 2 := by linarith [hx.2]
  have hB : 0 ≤ (1 + x) / 2 := by linarith [hx.1]
  unfold wignerJacobiForm wignerJacobiNorm
  rw [hs, hco, hc, Real.sqrt_mul (pow_nonneg hA μ), br_sqrt_pow _ hA, br_sqrt_pow _ hB]
  ring

/-! ### The `3j` carrier -/

/-- The sign `ε(M,σ)` of Wigner's extremal value (= that of `seed3`): `(-1)^{|M-σ|}` for `σ ≤ M`,
`+1` for `σ > M`. -/
noncomputable def signE3 (M σ : ℚ) (α : ℕ) : ℝ := if σ ≤ M then (-1 : ℝ) ^ α else 1

/-- **Wigner `d` in the four chambers, all ranks**: `d^{L₀+k}_{Mσ}(θ) = ε(M,σ) · (Jacobi form with
`(μ,ν) = (|M-σ|,|M+σ|)`, degree `k`)(θ)`. -/
theorem wignerSmallD_eq_signE3 (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) (k : ℕ)
    (θ : ℝ) :
    wignerSmallD (max |M| |σ| + (k : ℚ)) M σ θ = signE3 M σ α * wignerJacobiForm α β k θ := by
  unfold signE3
  by_cases h1 : σ ≤ M
  · simp only [h1, ite_true]
    by_cases h2 : 0 ≤ M + σ
    · have hj : max |M| |σ| = M := by
        rw [abs_of_nonneg (by linarith : 0 ≤ M)]
        exact max_eq_left (abs_le.mpr ⟨by linarith, h1⟩)
      rw [hj, wignerSmallD_chamber_A (μ := α) (ν := β) (k := k)
        (by rw [← hα, abs_of_nonneg (by linarith)])
        (by rw [← hβ, abs_of_nonneg h2]) (by ring)]
    · push Not at h2
      have hj : max |M| |σ| = -σ := by
        rw [abs_of_nonpos (by linarith : σ ≤ 0)]
        exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hj, wignerSmallD_chamber_B (μ := α) (ν := β) (k := k)
        (by rw [← hα, abs_of_nonneg (by linarith)])
        (by rw [← hβ, abs_of_neg h2]) (by ring)]
  · push Not at h1
    simp only [not_le.mpr h1, ite_false, one_mul]
    by_cases h2 : 0 ≤ M + σ
    · have hj : max |M| |σ| = σ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ σ)]
        exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hj, wignerSmallD_chamber_C (μ := α) (ν := β) (k := k)
        (by rw [← hα, abs_of_neg (by linarith)]; ring)
        (by rw [← hβ, abs_of_nonneg h2]; ring) (by ring)]
    · push Not at h2
      have hj : max |M| |σ| = -M := by
        rw [abs_of_nonpos (by linarith : M ≤ 0)]
        exact max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hj, wignerSmallD_chamber_D (μ := α) (ν := β) (k := k)
        (by rw [← hα, abs_of_neg (by linarith)]; ring)
        (by rw [← hβ, abs_of_neg h2]; ring) (by ring)]

/-- The carrier `P̃_{L₀+k}(τ; 0)` as a real polynomial in `τ` (`t = 0`). -/
noncomputable def ptilde3Zero (M σ : ℚ) (k : ℕ) : ℝ[X] :=
  (ptilde3Poly M σ k).map (Polynomial.evalRingHom 0)

lemma eval_ptilde3Zero (M σ : ℚ) (k : ℕ) (τ : ℝ) :
    (ptilde3Zero M σ k).eval τ = ptilde3 M σ k τ 0 := by
  rw [ptilde3_eq_evalP]
  rfl

lemma coeff_ptilde3Zero_top (M σ : ℚ) (k : ℕ) : (ptilde3Zero M σ k).coeff k = lead3 M σ k := by
  unfold ptilde3Zero
  rw [coeff_map, ptilde3Poly_coeff_top]
  simp

/-- On `(0,1)`: `P̃_{L₀+k}(τ;0) = ε · c_k · P_k^{(p_+,p_-)}(1-2τ)`. -/
theorem ptilde3_zero_eq_jacobi (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) (k : ℕ)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ptilde3 M σ k τ 0 =
      signE3 M σ α * wignerJacobiNorm α β k * (jacobi (α : ℝ) (β : ℝ) k).eval (1 - 2 * τ) := by
  have hx : (1 - 2 * τ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have h := dZero3_eq_wignerD M σ α β hα hβ hx k
  have e1 : (1 - (1 - 2 * τ)) / 2 = τ := by ring
  have e2 : (1 + (1 - 2 * τ)) / 2 = 1 - τ := by ring
  unfold dZero3 wignerSmallDx at h
  rw [wignerSmallD_eq_signE3 M σ α β hα hβ k, wignerJacobiForm_arccos α β k hx,
    br3_pPlus hα, br3_pMinus hβ, e1, e2] at h
  have hpos : 0 < Real.sqrt (τ ^ α * (1 - τ) ^ β) :=
    Real.sqrt_pos.mpr (mul_pos (pow_pos hτ.1 _) (pow_pos (by linarith [hτ.2]) _))
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [h]; ring

/-- The polynomial identity in `τ`: `P̃_{L₀+k}(τ;0) = ε c_k P_k^{(p_+,p_-)}(1-2τ)`. -/
theorem ptilde3Zero_eq_jacobi (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (k : ℕ) :
    ptilde3Zero M σ k = C (signE3 M σ α * wignerJacobiNorm α β k) * jacobiTau α β k := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (fun τ hτ => ?_) (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1))
  show eval τ _ = eval τ _
  rw [eval_ptilde3Zero, ptilde3_zero_eq_jacobi M σ α β hα hβ k hτ, eval_mul, eval_C,
    eval_jacobiTau]

/-- **Leading coefficient of the `3j` carrier** (`lem:sqrtfreecarrier`, `eq:WignerJacobiMonic`):
`k_{3j} = lead3 M σ k = ε(M,σ) · c_k · (-2)^k · [X^k] P_k^{(p_+,p_-)}`, `c_k` the Wigner
normalisation `√(k!(k+p_++p_-)!/((k+p_+)!(k+p_-)!))` and `(-2)^k` from `x = 1 - 2τ`. -/
theorem lead3_eq_jacobi (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) (k : ℕ) :
    lead3 M σ k = signE3 M σ α * wignerJacobiNorm α β k *
      ((jacobi (α : ℝ) (β : ℝ) k).coeff k * (-2) ^ k) := by
  rw [← coeff_ptilde3Zero_top, ptilde3Zero_eq_jacobi M σ α β hα hβ k, coeff_C_mul,
    coeff_jacobiTau_top]

/-- Closed form: `lead3 M σ k = ε(M,σ) (-1)^k √(k!(k+α+β)!/((k+α)!(k+β)!)) (k+α+β+1)_k / k!`,
`α = |M-σ|`, `β = |M+σ|`. -/
theorem lead3_eq_closed (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) (k : ℕ) :
    lead3 M σ k = signE3 M σ α * wignerJacobiNorm α β k * (-1) ^ k *
      (ascPochhammer ℝ k).eval ((k : ℝ) + α + β + 1) / (k.factorial : ℝ) := by
  rw [lead3_eq_jacobi M σ α β hα hβ k, jacobi_coeff_self]
  have h2 : ((-2 : ℝ)) ^ k = (-1) ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [h2]
  field_simp

lemma ptilde3Zero_eq_lead_mul_monic (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (k : ℕ) : ptilde3Zero M σ k = C (lead3 M σ k) * jacobiMonicTau α β k := by
  have hne := jacobi_lead_ne_zero α β k
  rw [ptilde3Zero_eq_jacobi M σ α β hα hβ k, lead3_eq_jacobi M σ α β hα hβ k]
  unfold jacobiMonicTau
  change _ = _ * (C _ * jacobiTau α β k)
  rw [← mul_assoc, ← C_mul, mul_assoc (signE3 M σ α * wignerJacobiNorm α β k), mul_inv_cancel₀ hne,
    mul_one]

/-- **`eq:WignerJacobiMonic` for `3j`** with `k_{3j} = lead3 M σ k` (exact, all four chambers):
`d^{L₀+k}_{Mσ}(arccos x) = k_{3j} · W_{3j}(x) · P̂_k^{(p_+,p_-)}((1-x)/2)` on `[-1,1]`, with `P̂` the
monic Jacobi polynomial in `τ = (1-x)/2` (`jacobiMonicTau`, monic of degree `k`). -/
theorem wignerD3_eq_lead_mul_monic (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x =
      lead3 M σ k * Wedge α β x * (jacobiMonicTau α β k).eval ((1 - x) / 2) := by
  rw [← dZero3_eq_wignerD M σ α β hα hβ hx k, dZero3, br3_pPlus hα, br3_pMinus hβ,
    ← Wedge_eq_sqrt α β hx, ← eval_ptilde3Zero, ptilde3Zero_eq_lead_mul_monic M σ α β hα hβ k,
    eval_mul, eval_C]
  ring

/-! ### The `6j` carrier (canonical sector) -/

open FormalResearch.Racah.SixJ in
/-- The `6j` carrier `P̃_{m+d}(τ; 0,0,0)` as a real polynomial in `τ` (zero scale `u = v = w = 0`). -/
noncomputable def ptilde6Zero (m n : ℚ) (d : ℕ) : ℝ[X] :=
  (ptPoly m n d).map (MvPolynomial.eval ![(0 : ℝ), 0, 0])

lemma eval_ptilde6Zero (m n : ℚ) (d : ℕ) (τ : ℝ) :
    (ptilde6Zero m n d).eval τ = ptilde6 m n τ 0 0 0 d := by
  unfold ptilde6Zero ptilde6 evalC
  rw [eval_map, Polynomial.coe_eval₂RingHom]

lemma coeff_ptilde6Zero_top (m n : ℚ) (hmn : |n| ≤ m) (d : ℕ) :
    (ptilde6Zero m n d).coeff d = kLead m n d := by
  unfold ptilde6Zero
  rw [coeff_map, ptPoly_coeff_top m n hmn d]
  simp

/-- On `(0,1)`: `P̃_{m+d}(τ;0,0,0) = c_d P_d^{(m-n,m+n)}(1-2τ)` (no sign in the canonical sector). -/
theorem ptilde6_zero_eq_jacobi (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ptilde6 m n τ 0 0 0 d =
      wignerJacobiNorm p q d * (jacobi (p : ℝ) (q : ℝ) d).eval (1 - 2 * τ) := by
  have hx : (1 - 2 * τ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have h := dZero6c_eq_wignerD m n p q hp hq hx d
  obtain ⟨h1, h2, -⟩ := floor_labels m n p q hp hq
  have e1 : (1 - (1 - 2 * τ)) / 2 = τ := by ring
  have e2 : (1 + (1 - 2 * τ)) / 2 = 1 - τ := by ring
  unfold dZero6c wignerSmallDx at h
  rw [wignerSmallD_chamber_C (μ := p) (ν := q) (k := d) (by rw [hp]) (by rw [hq])
    (by ring), wignerJacobiForm_arccos p q d hx, h1, h2, e1, e2] at h
  have hpos : 0 < Real.sqrt (τ ^ p * (1 - τ) ^ q) :=
    Real.sqrt_pos.mpr (mul_pos (pow_pos hτ.1 _) (pow_pos (by linarith [hτ.2]) _))
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [h]; ring

theorem ptilde6Zero_eq_jacobi (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ) :
    ptilde6Zero m n d = C (wignerJacobiNorm p q d) * jacobiTau p q d := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (fun τ hτ => ?_) (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1))
  show eval τ _ = eval τ _
  rw [eval_ptilde6Zero, ptilde6_zero_eq_jacobi m n p q hp hq d hτ, eval_mul, eval_C,
    eval_jacobiTau]

lemma abs_le_of_labels {m n : ℚ} {p q : ℕ} (hp : m - n = p) (hq : m + n = q) : |n| ≤ m := by
  have h1 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have h2 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Leading coefficient of the `6j` carrier** (`lem:sqrtfreecarrier`, `eq:WignerJacobiMonic`):
`k_{6j} = kLead m n d = c_d · (-2)^d · [X^d] P_d^{(m-n,m+n)}`, `c_d = √(d!(d+2m)!/((d+m-n)!(d+m+n)!))`
(canonical sector `m ∓ n` natural; no sign). -/
theorem kLead_eq_jacobi (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ) :
    kLead m n d = wignerJacobiNorm p q d *
      ((jacobi (p : ℝ) (q : ℝ) d).coeff d * (-2) ^ d) := by
  rw [← coeff_ptilde6Zero_top m n (abs_le_of_labels hp hq), ptilde6Zero_eq_jacobi m n p q hp hq d,
    coeff_C_mul, coeff_jacobiTau_top]

/-- Closed form: `kLead m n d = (-1)^d √(d!(d+p+q)!/((d+p)!(d+q)!)) (d+p+q+1)_d / d!`,
`p = m-n`, `q = m+n`. -/
theorem kLead_eq_closed (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ) :
    kLead m n d = wignerJacobiNorm p q d * (-1) ^ d *
      (ascPochhammer ℝ d).eval ((d : ℝ) + p + q + 1) / (d.factorial : ℝ) := by
  rw [kLead_eq_jacobi m n p q hp hq d, jacobi_coeff_self]
  have h2 : ((-2 : ℝ)) ^ d = (-1) ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
  have hk : (d.factorial : ℝ) ≠ 0 := by positivity
  rw [h2]
  field_simp

lemma ptilde6Zero_eq_kLead_mul_monic (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ) :
    ptilde6Zero m n d = C (kLead m n d) * jacobiMonicTau p q d := by
  have hne := jacobi_lead_ne_zero p q d
  rw [ptilde6Zero_eq_jacobi m n p q hp hq d, kLead_eq_jacobi m n p q hp hq d]
  unfold jacobiMonicTau
  change _ = _ * (C _ * jacobiTau p q d)
  rw [← mul_assoc, ← C_mul, mul_assoc (wignerJacobiNorm p q d), mul_inv_cancel₀ hne, mul_one]

/-- **`eq:WignerJacobiMonic` for `6j`** with `k_{6j} = kLead m n d` (canonical sector, `m ∓ n`
natural, `p_min = m-n`, `p_max = m+n` in the paper's naming): for `x ∈ [-1,1]`,
`d^{m+d}_{nm}(arccos x) = k_{6j} · W_{6j}(x) · P̂_d^{(m-n,m+n)}((1-x)/2)`. -/
theorem wignerD6_eq_kLead_mul_monic (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    wignerSmallDx (m + (d : ℚ)) n m x =
      kLead m n d * Wedge p q x * (jacobiMonicTau p q d).eval ((1 - x) / 2) := by
  obtain ⟨h1, h2, -⟩ := floor_labels m n p q hp hq
  rw [← dZero6c_eq_wignerD m n p q hp hq hx d, dZero6c, h1, h2, ← Wedge_eq_sqrt p q hx,
    ← eval_ptilde6Zero, ptilde6Zero_eq_kLead_mul_monic m n p q hp hq d, eval_mul, eval_C]
  ring

/-- info: 'FormalResearch.Racah.lead3_eq_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lead3_eq_jacobi

/-- info: 'FormalResearch.Racah.lead3_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lead3_eq_closed

/-- info: 'FormalResearch.Racah.wignerD3_eq_lead_mul_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerD3_eq_lead_mul_monic

/-- info: 'FormalResearch.Racah.jacobiMonicTau_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobiMonicTau_monic

/-- info: 'FormalResearch.Racah.kLead_eq_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kLead_eq_jacobi

/-- info: 'FormalResearch.Racah.kLead_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kLead_eq_closed

/-- info: 'FormalResearch.Racah.wignerD6_eq_kLead_mul_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerD6_eq_kLead_mul_monic

end FormalResearch.Racah
