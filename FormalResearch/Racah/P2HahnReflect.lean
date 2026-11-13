module

public import FormalResearch.Racah.P2HahnRec

/-!
# The Hahn reflection symmetry (Weyl P2)

`Q_n(D-u; β, α, D) = (-1)^n ((α+1)_n/(β+1)_n) Q_n(u; α, β, D)` for `0 ≤ n, u ≤ D`, proved from the
three-term recurrence in the degree (`hahnQ_rec`) by induction on `n`; consequently the normalized
Hahn functions `√(w_H/h_{H,n}) Q_n` of `(α,β)` and `(β,α)` agree up to `(-1)^n` under `u ↦ D-u`.
This is the finite Hahn counterpart of `P_n^{(α,β)}(-x) = (-1)^n P_n^{(β,α)}(x)`; it relates the
chambers of `eq:HahnAllChamberPhase` that exchange `α_H` and `β_H`.
-/

@[expose] public section

namespace FormalResearch.Racah

/-- `r_n = (α+1)_n/(β+1)_n`. -/
noncomputable def hahnR (α β : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => hahnR α β n * (((α : ℝ) + 1 + n) / ((β : ℝ) + 1 + n))

lemma hahnR_succ (α β n : ℕ) :
    hahnR α β (n + 1) = hahnR α β n * (((α : ℝ) + 1 + n) / ((β : ℝ) + 1 + n)) := rfl

lemma hahnR_pos (α β n : ℕ) : 0 < hahnR α β n := by
  induction n with
  | zero => simp [hahnR]
  | succ n ih => simp only [hahnR]; positivity

/-- Reflection of the weight. -/
lemma hahnW_reflect (α β D u : ℕ) (hu : u ≤ D) : hahnW β α D (D - u) = hahnW α β D u := by
  unfold hahnW
  rw [Nat.sub_sub_self hu, mul_comm]

lemma hahnA_reflect (α β D n : ℕ) :
    hahnA β α D n * hahnR α β (n + 1) = hahnA α β D n * hahnR α β n := by
  rw [hahnR_succ]
  unfold hahnA
  have h1 : (2 * (n : ℝ) + β + α + 1) ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + β + α + 2) ≠ 0 := by positivity
  have h3 : (2 * (n : ℝ) + α + β + 1) ≠ 0 := by positivity
  have h4 : (2 * (n : ℝ) + α + β + 2) ≠ 0 := by positivity
  have h5 : ((β : ℝ) + 1 + n) ≠ 0 := by positivity
  have e1 : 2 * (n : ℝ) + β + α + 1 = 2 * n + α + β + 1 := by ring
  have e2 : 2 * (n : ℝ) + β + α + 2 = 2 * n + α + β + 2 := by ring
  rw [e1, e2]
  field_simp
  ring

lemma hahnC_reflect (α β D n : ℕ) :
    hahnC β α D (n + 1) * hahnR α β n = hahnC α β D (n + 1) * hahnR α β (n + 1) := by
  rw [hahnR_succ]
  unfold hahnC
  have h1 : (2 * ((n : ℝ) + 1) + β + α) ≠ 0 := by positivity
  have h2 : (2 * ((n : ℝ) + 1) + β + α + 1) ≠ 0 := by positivity
  have h3 : (2 * ((n : ℝ) + 1) + α + β) ≠ 0 := by positivity
  have h4 : (2 * ((n : ℝ) + 1) + α + β + 1) ≠ 0 := by positivity
  have h5 : ((β : ℝ) + 1 + n) ≠ 0 := by positivity
  have e1 : 2 * ((n : ℝ) + 1) + β + α = 2 * ((n : ℝ) + 1) + α + β := by ring
  have e2 : 2 * ((n : ℝ) + 1) + β + α + 1 = 2 * ((n : ℝ) + 1) + α + β + 1 := by ring
  push_cast
  rw [e1]
  field_simp
  ring

lemma hahnAC_sum (α β D n : ℕ) :
    hahnA β α D n + hahnC β α D n + (hahnA α β D n + hahnC α β D n) = D := by
  unfold hahnA hahnC
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : (α : ℝ) + β + 1 ≠ 0 := by positivity
    have h2 : (β : ℝ) + α + 1 ≠ 0 := by positivity
    have h3 : (α : ℝ) + β + 2 ≠ 0 := by positivity
    have h4 : (β : ℝ) + α + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (2 * (n : ℝ) + β + α + 1) ≠ 0 := by positivity
    have h2 : (2 * (n : ℝ) + β + α + 2) ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + α + β + 1) ≠ 0 := by positivity
    have h4 : (2 * (n : ℝ) + α + β + 2) ≠ 0 := by positivity
    have h5 : (2 * (n : ℝ) + β + α) ≠ 0 := by positivity
    have h6 : (2 * (n : ℝ) + α + β) ≠ 0 := by positivity
    field_simp
    ring

lemma hahnC_zero (α β D : ℕ) : hahnC α β D 0 = 0 := by simp [hahnC]

/-- The `C`-term of the recurrence under reflection. -/
lemma hahnC_term (α β D n u : ℕ)
    (IH : n ≠ 0 → hahnQ β α D (n - 1) (D - u) =
      (-1) ^ (n - 1) * hahnR α β (n - 1) * hahnQ α β D (n - 1) u) :
    hahnC β α D n * hahnQ β α D (n - 1) (D - u) =
      -((-1 : ℝ) ^ n) * hahnC α β D n * hahnR α β n * hahnQ α β D (n - 1) u := by
  rcases n with _ | j
  · simp [hahnC_zero]
  · have h := IH (Nat.succ_ne_zero j)
    simp only [Nat.add_sub_cancel] at h ⊢
    rw [h]
    have := hahnC_reflect α β D j
    calc hahnC β α D (j + 1) * ((-1) ^ j * hahnR α β j * hahnQ α β D j u)
        = (hahnC β α D (j + 1) * hahnR α β j) * ((-1) ^ j * hahnQ α β D j u) := by ring
      _ = (hahnC α β D (j + 1) * hahnR α β (j + 1)) * ((-1) ^ j * hahnQ α β D j u) := by rw [this]
      _ = _ := by rw [pow_succ]; ring

/-- **Hahn reflection**: `Q_n(D-u; β, α, D) = (-1)^n ((α+1)_n/(β+1)_n) Q_n(u; α, β, D)`. -/
theorem hahnQ_reflect (α β D u : ℕ) (hu : u ≤ D) :
    ∀ n : ℕ, n ≤ D →
      hahnQ β α D n (D - u) = (-1) ^ n * hahnR α β n * hahnQ α β D n u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases n with _ | k
  · simp [hahnQ_zero, hahnR]
  · have hk : k + 1 ≤ D := hn
    have hq := hahnQ_rec α β D k u hk
    have ht := hahnQ_rec β α D k (D - u) hk
    have IH0 := ih k (by omega) (by omega)
    have hCrel := hahnC_term α β D k u (fun h => ih (k - 1) (by omega) (by omega))
    have hA1 := hahnA_reflect α β D k
    have hS := hahnAC_sum α β D k
    have hAne : hahnA β α D k ≠ 0 := by
      unfold hahnA
      have h1 : (k : ℝ) + 1 ≤ D := by exact_mod_cast hk
      have : (0 : ℝ) < (D : ℝ) - k := by linarith
      positivity
    rw [Nat.cast_sub hu] at ht
    apply mul_left_cancel₀ hAne
    rw [pow_succ]
    generalize hahnQ β α D (k + 1) (D - u) = t1 at *
    generalize hahnQ α β D (k + 1) u = q1 at *
    generalize hahnQ β α D (k - 1) (D - u) = tm at *
    generalize hahnQ α β D (k - 1) u = qm at *
    generalize hahnQ β α D k (D - u) = t0 at *
    generalize hahnQ α β D k u = q0 at *
    generalize hahnA β α D k = At at *
    generalize hahnC β α D k = Ct at *
    generalize hahnA α β D k = A at *
    generalize hahnC α β D k = C at *
    generalize hahnR α β (k + 1) = r1 at *
    generalize hahnR α β k = r0 at *
    generalize ((-1 : ℝ) ^ k) = e at *
    linear_combination (-1 : ℝ) * ht + (-((D : ℝ) - u) + At + Ct) * IH0 - hCrel +
      (e * r0 * q0) * hS + (e * q1) * hA1 - (e * r0) * hq

/-- info: 'FormalResearch.Racah.hahnQ_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahnQ_reflect

/-- Reflection of the Hahn norm: `h_{H,n}(β,α) = ((α+1)_n/(β+1)_n)² h_{H,n}(α,β)`. -/
theorem hahnNorm_reflect (α β D n : ℕ) (hn : n ≤ D) :
    hahnNorm β α D n = hahnR α β n ^ 2 * hahnNorm α β D n := by
  unfold hahnNorm
  rw [← Finset.sum_range_reflect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ D := by simp only [Finset.mem_range] at hj; omega
  rw [show D + 1 - 1 - j = D - j by omega, hahnQ_reflect α β D j hjD n hn]
  have hw := hahnW_reflect α β D j hjD
  rw [hw]
  have h1 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination ((hahnW α β D j : ℝ) * hahnR α β n ^ 2 * hahnQ α β D n j ^ 2) * h1

/-- **Reflection of the normalized Hahn function**: for `n, u ≤ D`,
`√(w_H^{(β,α)}(D-u)/h_{H,n}^{(β,α)}) Q_n(D-u;β,α,D) = (-1)^n √(w_H^{(α,β)}(u)/h_{H,n}^{(α,β)}) Q_n(u;α,β,D)`. -/
theorem hahn_normalized_reflect (α β D n u : ℕ) (hn : n ≤ D) (hu : u ≤ D) :
    Real.sqrt ((hahnW β α D (D - u) : ℝ) / hahnNorm β α D n) * hahnQ β α D n (D - u) =
      (-1 : ℝ) ^ n * (Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u) := by
  rw [hahnQ_reflect α β D u hu n hn, hahnW_reflect α β D u hu, hahnNorm_reflect α β D n hn]
  have hr := hahnR_pos α β n
  have e : (hahnW α β D u : ℝ) / (hahnR α β n ^ 2 * hahnNorm α β D n) =
      ((hahnW α β D u : ℝ) / hahnNorm α β D n) / hahnR α β n ^ 2 := by
    rw [div_div, mul_comm]
  rw [e, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hr.le]
  field_simp

/-- info: 'FormalResearch.Racah.hahn_normalized_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_normalized_reflect

end FormalResearch.Racah
