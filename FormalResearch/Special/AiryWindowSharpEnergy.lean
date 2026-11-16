module

public import Mathlib

/-!
# A quadratic (energy) Grönwall march for the discrete oscillator: the Airy-free core of the sharp window bound

`DiscreteJacobiExtrasGronwall` follows a perturbed three-term recurrence with the `ℓ¹` size `|y| + |Δy|/δ` and pays the factor
`exp(L δ n)`, `L ≈ 1 + 2 Sg/c_a`, `Sg ≈ A0`, i.e. `e^{O(A0²)}` over a window of length `A0`: the `ℓ¹` norm of the rotation
`[[1, θ], [-θ, 1]]` is `1 + θ`, although the rotation is an isometry of the Euclidean norm.  Here the recurrence in oscillatory
form is marched in the **adapted quadratic form**, which the symplectic-Euler step preserves *exactly*:

For `P' = P - δ α y + ρ`, `y' = y + δ β P'` (`α = (a_k + a_{k+1} - c_k)/δ² > 0` the local frequency squared, `β = 1/a_{k+1}`,
`P = a_k (y_k - y_{k-1})/δ` the flux, `ρ = r_k/δ` the forcing), put
`Q_{α,β}(y, P) = α y² + β P² - δ α β y P`.  Then (**all proved**):

* `enQ_step`: `Q(y', P') = Q(y, P)` when `ρ = 0` (polynomial identity) and `enQ_forcing`: `Q(δβρ, ρ) = βρ²`;
* `enQ_lower`, `enQ_upper`: `(αy² + βP²)/2 ≤ Q ≤ (3/2)(αy² + βP²)` when `δ²αβ ≤ 1`;
* `enQ_cs`: `B(u,v)² ≤ Q(u) Q(v)` (Lagrange identity with the factor `αβ(4 - δ²αβ)/4`), hence the triangle inequality
  `enQ_sqrt_add_le`;
* `enQ_change`: for a change of coefficients `α = α'(1+s)`, `β = β'(1+s')`: `Q_{α,β} ≤ (1 + 3(μ + μ' + μμ')) Q_{α',β'}` (`|s| ≤ μ`,
  `|s'| ≤ μ'`), so each step costs only the *relative variation of the coefficients*, not `Lδ`;
* **`energy_march_down`**: with `M_k = √(Q_{α_k,β_k}(y_k, P_k))` and `Σ_k (μ_k + μ'_k + μ_kμ'_k) ≤ V`,
  `M_k ≤ e^{3V/2} (√((3/2)(α_m y_{m+1}² + β_m P_{m+1}²)) + Σ_j √β_j |ρ_j|)` for all `k` of the window.

In the Airy lane `α_k ≈ |X_k|` is monotone on `[-A0, -1]` and `V ≈ ln A0 + O(1)`, so `e^{3V/2}` is polynomial in `A0` (the
`ℓ¹` march gave `e^{O(A0²)}`); mpmath check on the model chain `a = 1`, `c_k = 2 - δ²|X_k|`, `δ = 0.005`: the exact worst
amplification of `|y_k|` over `X ∈ [-A0, -1]` from unit data at `X = -1` is `1.345` for `A0 = 2, 5, 10, 20, 40, 80`
(the true amplitude decreases like `|X|^{-1/4}`), against the `ℓ¹` constant `exp((1 + 2A0)(A0 - 1)) = 148, 10^{19}, 10^{82}, …`.

**Not formalised** here: the translation from `jac a c y = r` to the oscillator form and the assembly into the window
theorem (`AiryWindowSharp`), and a lower bound (the energy bound is an upper bound on a quantity that is *conserved*, so it is
sharp up to the `e^{3V/2}` coefficient-variation factor).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- The adapted quadratic form `Q_{α,β}(y, P) = α y² + β P² - δ α β y P`. -/
noncomputable def enQ (α β δ y P : ℝ) : ℝ := α * y ^ 2 + β * P ^ 2 - δ * α * β * y * P

lemma enQ_lower {α β δ y P : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : δ ^ 2 * α * β ≤ 1) :
    (α * y ^ 2 + β * P ^ 2) / 2 ≤ enQ α β δ y P := by
  unfold enQ
  have h1 : 0 ≤ α * (y - δ * β * P) ^ 2 := by positivity
  have h2 : 0 ≤ β * P ^ 2 * (1 - δ ^ 2 * α * β) := mul_nonneg (by positivity) (by linarith)
  nlinarith

lemma enQ_upper {α β δ y P : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : δ ^ 2 * α * β ≤ 1) :
    enQ α β δ y P ≤ 3 / 2 * (α * y ^ 2 + β * P ^ 2) := by
  unfold enQ
  have h1 : 0 ≤ α * (y + δ * β * P) ^ 2 := by positivity
  have h2 : 0 ≤ β * P ^ 2 * (1 - δ ^ 2 * α * β) := mul_nonneg (by positivity) (by linarith)
  nlinarith

lemma enQ_nonneg {α β δ y P : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : δ ^ 2 * α * β ≤ 1) :
    0 ≤ enQ α β δ y P := by
  have := enQ_lower (y := y) (P := P) hα hβ hε
  have : 0 ≤ α * y ^ 2 + β * P ^ 2 := by positivity
  linarith

/-- **Exact invariance** of `Q` under the homogeneous step. -/
lemma enQ_step (α β δ y P : ℝ) :
    enQ α β δ (y + δ * β * (P - δ * α * y)) (P - δ * α * y) = enQ α β δ y P := by
  unfold enQ; ring

/-- The forcing vector `(δβρ, ρ)` has `Q`-size `β ρ²`. -/
lemma enQ_forcing (α β δ ρ : ℝ) : enQ α β δ (δ * β * ρ) ρ = β * ρ ^ 2 := by
  unfold enQ; ring

lemma enQ_neg (α β δ y P : ℝ) : enQ α β δ (-y) (-P) = enQ α β δ y P := by
  unfold enQ; ring

/-- Cauchy-Schwarz for `Q` (Lagrange identity): `B(u,v)² ≤ Q(u) Q(v)`. -/
lemma enQ_cs {α β δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : δ ^ 2 * α * β ≤ 1) (y1 P1 y2 P2 : ℝ) :
    (α * y1 * y2 + β * P1 * P2 - δ * α * β / 2 * (y1 * P2 + y2 * P1)) ^ 2 ≤
      enQ α β δ y1 P1 * enQ α β δ y2 P2 := by
  have e : enQ α β δ y1 P1 * enQ α β δ y2 P2 -
      (α * y1 * y2 + β * P1 * P2 - δ * α * β / 2 * (y1 * P2 + y2 * P1)) ^ 2 =
      α * β * (4 - δ ^ 2 * α * β) / 4 * (y1 * P2 - y2 * P1) ^ 2 := by
    unfold enQ; ring
  have : 0 ≤ α * β * (4 - δ ^ 2 * α * β) / 4 * (y1 * P2 - y2 * P1) ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hα hβ) (by linarith)) (by norm_num)) (sq_nonneg _)
  linarith

/-- **Triangle inequality** for the norm `√Q`. -/
lemma enQ_sqrt_add_le {α β δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : δ ^ 2 * α * β ≤ 1) (y1 P1 y2 P2 : ℝ) :
    √(enQ α β δ (y1 + y2) (P1 + P2)) ≤ √(enQ α β δ y1 P1) + √(enQ α β δ y2 P2) := by
  have h1 := enQ_nonneg (y := y1) (P := P1) hα hβ hε
  have h2 := enQ_nonneg (y := y2) (P := P2) hα hβ hε
  have hcs := enQ_cs hα hβ hε y1 P1 y2 P2
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  set B := α * y1 * y2 + β * P1 * P2 - δ * α * β / 2 * (y1 * P2 + y2 * P1) with hB
  have hBle : B ≤ √(enQ α β δ y1 P1) * √(enQ α β δ y2 P2) := by
    rw [← Real.sqrt_mul h1]
    exact Real.le_sqrt_of_sq_le hcs
  have e : enQ α β δ (y1 + y2) (P1 + P2) = enQ α β δ y1 P1 + enQ α β δ y2 P2 + 2 * B := by
    rw [hB]; unfold enQ; ring
  have s1 := Real.sq_sqrt h1
  have s2 := Real.sq_sqrt h2
  rw [e]
  nlinarith

/-- **Change of coefficients**: if `α = α'(1 + s)`, `β = β'(1 + s')` with `|s| ≤ μ`, `|s'| ≤ μ'` and `δ² α' β' ≤ 1`, then
`Q_{α,β}(y, P) ≤ (1 + 3(μ + μ' + μμ')) Q_{α',β'}(y, P)`. -/
lemma enQ_change {α β α' β' δ s s' μ μ' : ℝ} (hα' : 0 < α') (hβ' : 0 < β')
    (hε : δ ^ 2 * α' * β' ≤ 1) (hs : |s| ≤ μ) (hs' : |s'| ≤ μ') (hα : α = α' * (1 + s))
    (hβ : β = β' * (1 + s')) (y P : ℝ) :
    enQ α β δ y P ≤ (1 + 3 * (μ + μ' + μ * μ')) * enQ α' β' δ y P := by
  have hμ : 0 ≤ μ := (abs_nonneg _).trans hs
  have hμ' : 0 ≤ μ' := (abs_nonneg _).trans hs'
  set m := μ + μ' + μ * μ' with hm
  have hm0 : 0 ≤ m := by positivity
  have hlow := enQ_lower (y := y) (P := P) hα'.le hβ'.le hε
  -- difference
  have hdiff : enQ α β δ y P - enQ α' β' δ y P =
      α' * s * y ^ 2 + β' * s' * P ^ 2 - δ * α' * β' * (s + s' + s * s') * y * P := by
    rw [hα, hβ]; unfold enQ; ring
  have hss : |s + s' + s * s'| ≤ m := by
    calc |s + s' + s * s'| ≤ |s| + |s'| + |s| * |s'| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]; gcongr; exact abs_add_le _ _
      _ ≤ m := by rw [hm]; gcongr
  have c1 : α' * s * y ^ 2 ≤ m * (α' * y ^ 2) := by
    have : s ≤ m := by
      have := (abs_le.mp hs).2; nlinarith [mul_nonneg hμ hμ']
    nlinarith [mul_nonneg hα'.le (sq_nonneg y)]
  have c2 : β' * s' * P ^ 2 ≤ m * (β' * P ^ 2) := by
    have : s' ≤ m := by
      have := (abs_le.mp hs').2; nlinarith [mul_nonneg hμ hμ']
    nlinarith [mul_nonneg hβ'.le (sq_nonneg P)]
  -- cross term: |δ α' β' t y P| ≤ m (α' y² + β' P²)/2 with t = s+s'+ss'
  have c3 : -(δ * α' * β' * (s + s' + s * s') * y * P) ≤ m * ((α' * y ^ 2 + β' * P ^ 2) / 2) := by
    set t := s + s' + s * s' with ht
    have hcross : |δ * α' * β' * y * P| ≤ (α' * y ^ 2 + β' * P ^ 2) / 2 := by
      rw [abs_le]
      have h1 : 0 ≤ α' * (y - δ * β' * P) ^ 2 := by positivity
      have h2 : 0 ≤ α' * (y + δ * β' * P) ^ 2 := by positivity
      have h3 : 0 ≤ β' * P ^ 2 * (1 - δ ^ 2 * α' * β') := mul_nonneg (by positivity) (by linarith)
      constructor <;> nlinarith
    have e : δ * α' * β' * t * y * P = t * (δ * α' * β' * y * P) := by ring
    rw [e]
    have : |t * (δ * α' * β' * y * P)| ≤ m * ((α' * y ^ 2 + β' * P ^ 2) / 2) := by
      rw [abs_mul]; exact mul_le_mul hss hcross (abs_nonneg _) hm0
    have := neg_abs_le (t * (δ * α' * β' * y * P))
    linarith [abs_nonneg (t * (δ * α' * β' * y * P))]
  have hE : 0 ≤ α' * y ^ 2 + β' * P ^ 2 := by positivity
  have : enQ α β δ y P ≤ enQ α' β' δ y P + m * (α' * y ^ 2 + β' * P ^ 2) +
      m * ((α' * y ^ 2 + β' * P ^ 2) / 2) := by
    have := hdiff
    linarith
  have h4 : m * (α' * y ^ 2 + β' * P ^ 2) + m * ((α' * y ^ 2 + β' * P ^ 2) / 2) ≤
      3 * m * enQ α' β' δ y P := by
    have := mul_le_mul_of_nonneg_left hlow hm0
    nlinarith
  nlinarith

/-- **One step of the downward energy recursion.**  If `P' = P - δαy + ρ`, `y' = y + δβP'` (the step with coefficients
`(α, β)`) and the next step has coefficients `(α', β')` with `α = α'(1+s)`, `β = β'(1+s')`, `|s| ≤ μ`, `|s'| ≤ μ'`, then
`√Q_{α,β}(y,P) ≤ exp(3(μ+μ'+μμ')/2) √Q_{α',β'}(y',P') + √β |ρ|`. -/
lemma energy_step_down {α β α' β' δ s s' μ μ' y P y' P' ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hα' : 0 < α') (hβ' : 0 < β') (hε : δ ^ 2 * α * β ≤ 1) (hε' : δ ^ 2 * α' * β' ≤ 1)
    (hs : |s| ≤ μ) (hs' : |s'| ≤ μ') (hαs : α = α' * (1 + s)) (hβs : β = β' * (1 + s'))
    (hP : P' = P - δ * α * y + ρ) (hy : y' = y + δ * β * P') :
    √(enQ α β δ y P) ≤ Real.exp (3 * (μ + μ' + μ * μ') / 2) * √(enQ α' β' δ y' P') + √β * |ρ| := by
  have hμ : 0 ≤ μ := (abs_nonneg _).trans hs
  have hμ' : 0 ≤ μ' := (abs_nonneg _).trans hs'
  have hinv : enQ α β δ y P = enQ α β δ (y' - δ * β * ρ) (P' - ρ) := by
    rw [← enQ_step α β δ y P]
    congr 1
    · rw [hy, hP]; ring
    · rw [hP]; ring
  have htri := enQ_sqrt_add_le hα.le hβ.le hε y' P' (-(δ * β * ρ)) (-ρ)
  have hf : √(enQ α β δ (-(δ * β * ρ)) (-ρ)) = √β * |ρ| := by
    rw [enQ_neg, enQ_forcing, Real.sqrt_mul hβ.le, Real.sqrt_sq_eq_abs]
  have hchg := enQ_change hα' hβ' hε' hs hs' hαs hβs y' P'
  have hsq : √(enQ α β δ y' P') ≤ Real.exp (3 * (μ + μ' + μ * μ') / 2) * √(enQ α' β' δ y' P') := by
    have h1 : 1 + 3 * (μ + μ' + μ * μ') ≤ Real.exp (3 * (μ + μ' + μ * μ')) := by
      linarith [Real.add_one_le_exp (3 * (μ + μ' + μ * μ'))]
    have h2 : √(1 + 3 * (μ + μ' + μ * μ')) ≤ Real.exp (3 * (μ + μ' + μ * μ') / 2) := by
      rw [Real.sqrt_le_left (by positivity)]
      calc 1 + 3 * (μ + μ' + μ * μ') ≤ Real.exp (3 * (μ + μ' + μ * μ')) := h1
        _ = Real.exp (3 * (μ + μ' + μ * μ') / 2) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc √(enQ α β δ y' P') ≤ √((1 + 3 * (μ + μ' + μ * μ')) * enQ α' β' δ y' P') := Real.sqrt_le_sqrt hchg
      _ = √(1 + 3 * (μ + μ' + μ * μ')) * √(enQ α' β' δ y' P') := Real.sqrt_mul (by positivity) _
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  have e1 : y' - δ * β * ρ = y' + -(δ * β * ρ) := by ring
  have e2 : P' - ρ = P' + -ρ := by ring
  rw [hinv, e1, e2]
  linarith

lemma sum_Ico_split_bot (f : ℤ → ℝ) {k m : ℤ} (h : k < m) :
    ∑ j ∈ Ico k m, f j = f k + ∑ j ∈ Ico (k + 1) m, f j := by
  rw [← Finset.sum_insert (s := Ico (k + 1) m) (a := k) (by simp)]
  congr 1; ext j; simp only [mem_insert, mem_Ico]; omega

lemma sum_Icc_split_bot (f : ℤ → ℝ) {k m : ℤ} (h : k ≤ m) :
    ∑ j ∈ Icc k m, f j = f k + ∑ j ∈ Icc (k + 1) m, f j := by
  rw [← Finset.sum_insert (s := Icc (k + 1) m) (a := k) (by simp)]
  congr 1; ext j; simp only [mem_insert, mem_Icc]; omega

/-- **The energy march (downward).**  Rows `k ∈ [J+1, m]` of the oscillator
`P_{k+1} = P_k - δ α_k y_k + ρ_k`, `y_{k+1} = y_k + δ β_k P_{k+1}` with `δ² α_k β_k ≤ 1`, coefficient ratios
`α_k = α_{k+1}(1 + s_k)`, `β_k = β_{k+1}(1 + s'_k)`, `|s_k| ≤ μ_k`, `|s'_k| ≤ μ'_k`,
`Σ_{k ∈ [J+1, m)} (μ_k + μ'_k + μ_kμ'_k) ≤ V`.  Then for all `k ∈ [J+1, m]`
`√Q_k(y_k, P_k) ≤ e^{3V/2} (√((3/2)(α_m y_{m+1}² + β_m P_{m+1}²)) + Σ_{j ∈ [J+1, m]} √β_j |ρ_j|)`. -/
theorem energy_march_down (y P α β ρ s s' μ μ' : ℤ → ℝ) (δ V : ℝ) (J m : ℤ)
    (hα : ∀ k ∈ Icc (J + 1) m, 0 < α k) (hβ : ∀ k ∈ Icc (J + 1) m, 0 < β k)
    (hε : ∀ k ∈ Icc (J + 1) m, δ ^ 2 * α k * β k ≤ 1)
    (hP : ∀ k ∈ Icc (J + 1) m, P (k + 1) = P k - δ * α k * y k + ρ k)
    (hy : ∀ k ∈ Icc (J + 1) m, y (k + 1) = y k + δ * β k * P (k + 1))
    (hαs : ∀ k ∈ Ico (J + 1) m, α k = α (k + 1) * (1 + s k))
    (hβs : ∀ k ∈ Ico (J + 1) m, β k = β (k + 1) * (1 + s' k))
    (hs : ∀ k ∈ Ico (J + 1) m, |s k| ≤ μ k) (hs' : ∀ k ∈ Ico (J + 1) m, |s' k| ≤ μ' k)
    (hV : ∑ k ∈ Ico (J + 1) m, (μ k + μ' k + μ k * μ' k) ≤ V) :
    ∀ k ∈ Icc (J + 1) m, √(enQ (α k) (β k) δ (y k) (P k)) ≤ Real.exp (3 * V / 2) *
      (√(3 / 2 * (α m * y (m + 1) ^ 2 + β m * P (m + 1) ^ 2)) + ∑ j ∈ Icc (J + 1) m, √(β j) * |ρ j|) := by
  set T0 : ℝ := √(3 / 2 * (α m * y (m + 1) ^ 2 + β m * P (m + 1) ^ 2)) with hT0
  have hm3 : ∀ k ∈ Ico (J + 1) m, 0 ≤ μ k + μ' k + μ k * μ' k := by
    intro k hk
    have h1 : 0 ≤ μ k := (abs_nonneg _).trans (hs k hk)
    have h2 : 0 ≤ μ' k := (abs_nonneg _).trans (hs' k hk)
    positivity
  have hF : ∀ k ∈ Icc (J + 1) m, 0 ≤ √(β k) * |ρ k| := fun k _ => by positivity
  have hT00 : 0 ≤ T0 := Real.sqrt_nonneg _
  -- top step
  have htop : ∀ hm : J + 1 ≤ m, √(enQ (α m) (β m) δ (y m) (P m)) ≤ T0 + √(β m) * |ρ m| := by
    intro hm
    have hmm : m ∈ Icc (J + 1) m := by simp [hm]
    have h := energy_step_down (α := α m) (β := β m) (α' := α m) (β' := β m) (δ := δ) (s := 0) (s' := 0) (μ := 0)
      (μ' := 0) (y := y m) (P := P m) (y' := y (m + 1)) (P' := P (m + 1)) (ρ := ρ m) (hα m hmm) (hβ m hmm)
      (hα m hmm) (hβ m hmm) (hε m hmm) (hε m hmm) (by simp) (by simp) (by simp) (by simp)
      (by rw [hP m hmm]) (hy m hmm)
    simp only [mul_zero, add_zero, zero_div, Real.exp_zero, one_mul] at h
    refine h.trans (add_le_add_left ?_ _)
    refine Real.sqrt_le_sqrt ?_
    exact enQ_upper (hα m hmm).le (hβ m hmm).le (hε m hmm)
  have key : ∀ n : ℕ, ∀ k : ℤ, k + n = m → J + 1 ≤ k →
      √(enQ (α k) (β k) δ (y k) (P k)) ≤ Real.exp (3 / 2 * ∑ j ∈ Ico k m, (μ j + μ' j + μ j * μ' j)) *
        (T0 + ∑ j ∈ Icc k m, √(β j) * |ρ j|) := by
    intro n
    induction n with
    | zero =>
      intro k hk hJk
      have hkm : k = m := by simpa using hk
      subst hkm
      simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, Real.exp_zero, one_mul, Finset.Icc_self,
        Finset.sum_singleton]
      exact htop hJk
    | succ n ih =>
      intro k hk hJk
      have hkm : k < m := by omega
      have hk1 := ih (k + 1) (by push_cast at hk; omega) (by omega)
      have hkI : k ∈ Icc (J + 1) m := by simp only [mem_Icc]; omega
      have hk1I : k + 1 ∈ Icc (J + 1) m := by simp only [mem_Icc]; omega
      have hkIco : k ∈ Ico (J + 1) m := by simp only [mem_Ico]; omega
      have hstep := energy_step_down (α := α k) (β := β k) (α' := α (k + 1)) (β' := β (k + 1)) (δ := δ)
        (s := s k) (s' := s' k) (μ := μ k) (μ' := μ' k) (y := y k) (P := P k) (y' := y (k + 1))
        (P' := P (k + 1)) (ρ := ρ k) (hα k hkI) (hβ k hkI) (hα (k + 1) hk1I) (hβ (k + 1) hk1I) (hε k hkI)
        (hε (k + 1) hk1I) (hs k hkIco) (hs' k hkIco) (hαs k hkIco) (hβs k hkIco) (hP k hkI) (hy k hkI)
      rw [sum_Ico_split_bot _ hkm, sum_Icc_split_bot _ (by omega : k ≤ m)]
      set m3 := μ k + μ' k + μ k * μ' k with hm3k
      set S1 := ∑ j ∈ Ico (k + 1) m, (μ j + μ' j + μ j * μ' j) with hS1
      set S2 := ∑ j ∈ Icc (k + 1) m, √(β j) * |ρ j| with hS2
      have hm3k0 : 0 ≤ m3 := hm3 k hkIco
      have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun j hj => hm3 j (by
        simp only [mem_Ico] at hj ⊢; omega)
      have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun j hj => hF j (by
        simp only [mem_Icc] at hj ⊢; omega)
      have hFk := hF k hkI
      have e1 : Real.exp (3 / 2 * (m3 + S1)) = Real.exp (3 * m3 / 2) * Real.exp (3 / 2 * S1) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexp1 : 1 ≤ Real.exp (3 / 2 * S1) := Real.one_le_exp (by positivity)
      have hexp2 : 1 ≤ Real.exp (3 * m3 / 2) := Real.one_le_exp (by positivity)
      calc _ ≤ Real.exp (3 * m3 / 2) * √(enQ (α (k + 1)) (β (k + 1)) δ (y (k + 1)) (P (k + 1))) +
            √(β k) * |ρ k| := hstep
        _ ≤ Real.exp (3 * m3 / 2) * (Real.exp (3 / 2 * S1) * (T0 + S2)) + √(β k) * |ρ k| := by
            gcongr
        _ ≤ Real.exp (3 / 2 * (m3 + S1)) * (T0 + (√(β k) * |ρ k| + S2)) := by
            rw [e1]
            have h0 : 0 ≤ T0 + S2 := by positivity
            have hE : 0 ≤ Real.exp (3 * m3 / 2) * Real.exp (3 / 2 * S1) := by positivity
            nlinarith [mul_nonneg hE hFk, mul_nonneg (mul_nonneg hE hFk) (by norm_num : (0 : ℝ) ≤ 1),
              mul_le_mul_of_nonneg_left hexp1 (mul_nonneg (Real.exp_pos (3 * m3 / 2)).le hFk),
              mul_le_mul_of_nonneg_left hexp2 hFk]
  intro k hk
  rw [mem_Icc] at hk
  have := key (m - k).toNat k (by omega) hk.1
  have hsum : ∑ j ∈ Ico k m, (μ j + μ' j + μ j * μ' j) ≤ V := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hV
    · intro j hj; simp only [mem_Ico] at hj ⊢; omega
    · intro j hj _; exact hm3 j hj
  have hsum2 : ∑ j ∈ Icc k m, √(β j) * |ρ j| ≤ ∑ j ∈ Icc (J + 1) m, √(β j) * |ρ j| := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj; simp only [mem_Icc] at hj ⊢; omega
    · intro j hj _; exact hF j hj
  refine this.trans ?_
  have hE : Real.exp (3 / 2 * ∑ j ∈ Ico k m, (μ j + μ' j + μ j * μ' j)) ≤ Real.exp (3 * V / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h0 : 0 ≤ T0 + ∑ j ∈ Icc k m, √(β j) * |ρ j| := by
    have : 0 ≤ ∑ j ∈ Icc k m, √(β j) * |ρ j| := Finset.sum_nonneg fun j hj => hF j (by
      simp only [mem_Icc] at hj ⊢; omega)
    positivity
  calc _ ≤ Real.exp (3 * V / 2) * (T0 + ∑ j ∈ Icc k m, √(β j) * |ρ j|) :=
        mul_le_mul_of_nonneg_right hE h0
    _ ≤ _ := by gcongr

end FormalResearch.Special

/-- info: 'FormalResearch.Special.enQ_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.enQ_step

/-- info: 'FormalResearch.Special.enQ_sqrt_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.enQ_sqrt_add_le

/-- info: 'FormalResearch.Special.enQ_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.enQ_change

/-- info: 'FormalResearch.Special.energy_step_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.energy_step_down

/-- info: 'FormalResearch.Special.energy_march_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.energy_march_down

