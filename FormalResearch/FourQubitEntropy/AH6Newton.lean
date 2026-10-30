import Mathlib

/-!
# Newton form of the quintic Hermite interpolant on three double nodes, and its remainder for `1/(ρ t + σ)`

Nodes `n₁ n₁ n₂ n₂ n₃ n₃` (so `q² = π₆`); the data are `vᵢ = g(nᵢ)`, `wᵢ = g'(nᵢ)`.  `newtonP` is the Newton
polynomial `∑ₖ C_k π_k(e)`, `π_k = ∏_{j<k}(e - x_j)`, with `C_k` the divided differences computed by the tableau
(`tab`; the inverse node differences are parameters `i21 = 1/(n₂-n₁)`, `i31`, `i32`).

For the function `φ(t) = 1/(ρ t + σ)` the divided differences are `(-ρ)^{j-i} / ∏_{k=i}^{j} D(x_k)`
(`tab_phi`), and the Newton remainder is `ρ⁶ q(e)² / (D(e) D(n₁)² D(n₂)² D(n₃)²)` (`phi_remainder`).
This is the Hermite remainder identity of the Stieltjes representation in
`joint_entropy_analytic_proof.tex` (eq. `seven-joint-stieltjes`), proved by an elementary induction.
-/

namespace FormalResearch.FourQubitEntropy.AH6

/-- One divided-difference step `(a - b)/(x_j - x_i)`, with `i = 1/(x_j - x_i)`. -/
def step (a b i : ℝ) : ℝ := (a - b) * i

/-- The divided-difference tableau: `(d₀₂, d₀₃, d₀₄, d₀₅)` for the data `(v₁,w₁,v₂,w₂,v₃,w₃)`. -/
def tab (i21 i31 i32 v1 w1 v2 w2 v3 w3 : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  let d12 := step v2 v1 i21
  let d34 := step v3 v2 i32
  let d02 := step d12 w1 i21
  let d13 := step w2 d12 i21
  let d24 := step d34 w2 i32
  let d35 := step w3 d34 i32
  let d03 := step d13 d02 i21
  let d14 := step d24 d13 i31
  let d25 := step d35 d24 i32
  let d04 := step d14 d03 i31
  let d15 := step d25 d14 i31
  (d02, d03, d04, step d15 d04 i31)

/-- The Newton polynomial. -/
def newtonP (n1 n2 n3 i21 i31 i32 v1 w1 v2 w2 v3 w3 e : ℝ) : ℝ :=
  let t := tab i21 i31 i32 v1 w1 v2 w2 v3 w3
  v1 + w1 * (e - n1) + t.1 * (e - n1) ^ 2 + t.2.1 * ((e - n1) ^ 2 * (e - n2))
    + t.2.2.1 * ((e - n1) ^ 2 * (e - n2) ^ 2) + t.2.2.2 * ((e - n1) ^ 2 * (e - n2) ^ 2 * (e - n3))

/-- The Newton polynomial is linear in the data. -/
theorem newtonP_lin (n1 n2 n3 i21 i31 i32 v1 w1 v2 w2 v3 w3 e : ℝ) :
    newtonP n1 n2 n3 i21 i31 i32 v1 w1 v2 w2 v3 w3 e =
      v1 * newtonP n1 n2 n3 i21 i31 i32 1 0 0 0 0 0 e + w1 * newtonP n1 n2 n3 i21 i31 i32 0 1 0 0 0 0 e
      + v2 * newtonP n1 n2 n3 i21 i31 i32 0 0 1 0 0 0 e + w2 * newtonP n1 n2 n3 i21 i31 i32 0 0 0 1 0 0 e
      + v3 * newtonP n1 n2 n3 i21 i31 i32 0 0 0 0 1 0 e + w3 * newtonP n1 n2 n3 i21 i31 i32 0 0 0 0 0 1 e := by
  simp only [newtonP, tab, step]
  ring


/-- The divided-difference step for `1/D`: `D_j - D_i = ρ (x_j - x_i)`. -/
theorem step_phi {ρ c M Di Dj dx i A B R : ℝ} (hi : Di ≠ 0) (hj : Dj ≠ 0) (hM : M ≠ 0)
    (hx : dx * i = 1) (hD : Dj - Di = ρ * dx)
    (hA : A = c / (M * Dj)) (hB : B = c / (Di * M)) (hR : R = -ρ * c / (Di * M * Dj)) :
    step A B i = R := by
  have hdx : dx ≠ 0 := left_ne_zero_of_mul_eq_one hx
  have hi' : i = dx⁻¹ := eq_inv_of_mul_eq_one_right hx
  have hDi : Di = Dj - ρ * dx := by linarith
  subst hA hB hR hi'
  unfold step
  rw [hDi] at hi ⊢
  field_simp
  ring


/-- Remainder step: `R - C = (-ρ s) π (e-x) / (P D_x D_e)` when `R = s π/(P D_e)` and `C = s π/(P D_x)`. -/
theorem rem_step {ρ s π P Dx De e x R C : ℝ} (hDe : De ≠ 0) (hDx : Dx ≠ 0) (hP : P ≠ 0)
    (hD : De - Dx = ρ * (e - x)) (hR : R = s * π / (P * De)) (hC : C = s * π / (P * Dx)) :
    R - C = (-ρ * s) * (π * (e - x)) / ((P * Dx) * De) := by
  have hDe' : De = Dx + ρ * (e - x) := by linarith
  subst hR hC
  rw [hDe'] at hDe ⊢
  field_simp
  ring

section PhiTableau

variable {ρ D1 D2 D3 n1 n2 n3 i21 i31 i32 : ℝ}

theorem tab_phi (hD1 : D1 ≠ 0) (hD2 : D2 ≠ 0) (hD3 : D3 ≠ 0)
    (h21 : (n2 - n1) * i21 = 1) (h31 : (n3 - n1) * i31 = 1) (h32 : (n3 - n2) * i32 = 1)
    (hD21 : D2 - D1 = ρ * (n2 - n1)) (hD31 : D3 - D1 = ρ * (n3 - n1))
    (hD32 : D3 - D2 = ρ * (n3 - n2)) :
    tab i21 i31 i32 (1 / D1) (-ρ / (D1 * D1)) (1 / D2) (-ρ / (D2 * D2)) (1 / D3) (-ρ / (D3 * D3)) =
      (ρ ^ 2 / (D1 ^ 2 * D2), -ρ ^ 3 / (D1 ^ 2 * D2 ^ 2), ρ ^ 4 / (D1 ^ 2 * D2 ^ 2 * D3),
        -ρ ^ 5 / (D1 ^ 2 * D2 ^ 2 * D3 ^ 2)) := by
  have one : (1 : ℝ) ≠ 0 := one_ne_zero
  have e12 : step (1 / D2) (1 / D1) i21 = -ρ * 1 / (D1 * 1 * D2) :=
    step_phi hD1 hD2 one h21 hD21 (by ring) (by ring) rfl
  have e34 : step (1 / D3) (1 / D2) i32 = -ρ * 1 / (D2 * 1 * D3) :=
    step_phi hD2 hD3 one h32 hD32 (by ring) (by ring) rfl
  have e02 : step (-ρ * 1 / (D1 * 1 * D2)) (-ρ / (D1 * D1)) i21 = -ρ * (-ρ) / (D1 * D1 * D2) :=
    step_phi (c := -ρ) hD1 hD2 hD1 h21 hD21 (by ring) (by ring) rfl
  have e13 : step (-ρ / (D2 * D2)) (-ρ * 1 / (D1 * 1 * D2)) i21 = -ρ * (-ρ) / (D1 * D2 * D2) :=
    step_phi (c := -ρ) (M := D2) hD1 hD2 hD2 h21 hD21 (by ring) (by ring) (by ring)
  have e24 : step (-ρ * 1 / (D2 * 1 * D3)) (-ρ / (D2 * D2)) i32 = -ρ * (-ρ) / (D2 * D2 * D3) :=
    step_phi (c := -ρ) (M := D2) hD2 hD3 hD2 h32 hD32 (by ring) (by ring) (by ring)
  have e35 : step (-ρ / (D3 * D3)) (-ρ * 1 / (D2 * 1 * D3)) i32 = -ρ * (-ρ) / (D2 * D3 * D3) :=
    step_phi (c := -ρ) (M := D3) hD2 hD3 hD3 h32 hD32 (by ring) (by ring) (by ring)
  have e03 : step (-ρ * (-ρ) / (D1 * D2 * D2)) (-ρ * (-ρ) / (D1 * D1 * D2)) i21 =
      -ρ * (-ρ) ^ 2 / (D1 * (D1 * D2) * D2) :=
    step_phi (c := (-ρ) ^ 2) (M := D1 * D2) hD1 hD2 (mul_ne_zero hD1 hD2) h21 hD21
      (by ring) (by ring) rfl
  have e14 : step (-ρ * (-ρ) / (D2 * D2 * D3)) (-ρ * (-ρ) / (D1 * D2 * D2)) i31 =
      -ρ * (-ρ) ^ 2 / (D1 * (D2 * D2) * D3) :=
    step_phi (c := (-ρ) ^ 2) (M := D2 * D2) hD1 hD3 (mul_ne_zero hD2 hD2) h31 hD31
      (by ring) (by ring) rfl
  have e25 : step (-ρ * (-ρ) / (D2 * D3 * D3)) (-ρ * (-ρ) / (D2 * D2 * D3)) i32 =
      -ρ * (-ρ) ^ 2 / (D2 * (D2 * D3) * D3) :=
    step_phi (c := (-ρ) ^ 2) (M := D2 * D3) hD2 hD3 (mul_ne_zero hD2 hD3) h32 hD32
      (by ring) (by ring) rfl
  have e04 : step (-ρ * (-ρ) ^ 2 / (D1 * (D2 * D2) * D3)) (-ρ * (-ρ) ^ 2 / (D1 * (D1 * D2) * D2)) i31 =
      -ρ * (-ρ) ^ 3 / (D1 * (D1 * D2 * D2) * D3) :=
    step_phi (c := (-ρ) ^ 3) (M := D1 * D2 * D2) hD1 hD3 (mul_ne_zero (mul_ne_zero hD1 hD2) hD2) h31 hD31
      (by ring) (by ring) rfl
  have e15 : step (-ρ * (-ρ) ^ 2 / (D2 * (D2 * D3) * D3)) (-ρ * (-ρ) ^ 2 / (D1 * (D2 * D2) * D3)) i31 =
      -ρ * (-ρ) ^ 3 / (D1 * (D2 * D2 * D3) * D3) :=
    step_phi (c := (-ρ) ^ 3) (M := D2 * D2 * D3) hD1 hD3 (mul_ne_zero (mul_ne_zero hD2 hD2) hD3) h31 hD31
      (by ring) (by ring) rfl
  have e05 : step (-ρ * (-ρ) ^ 3 / (D1 * (D2 * D2 * D3) * D3)) (-ρ * (-ρ) ^ 3 / (D1 * (D1 * D2 * D2) * D3)) i31 =
      -ρ * (-ρ) ^ 4 / (D1 * (D1 * D2 * D2 * D3) * D3) :=
    step_phi (c := (-ρ) ^ 4) (M := D1 * D2 * D2 * D3) hD1 hD3
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hD1 hD2) hD2) hD3) h31 hD31 (by ring) (by ring) rfl
  simp only [tab]
  rw [e12, e34, e02, e13, e24, e35, e03, e14, e25, e04, e15, e05]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> field_simp


/-- **Newton remainder for `1/D`.** -/
theorem phi_remainder {De e : ℝ} (hD1 : D1 ≠ 0) (hD2 : D2 ≠ 0) (hD3 : D3 ≠ 0) (hDe : De ≠ 0)
    (h21 : (n2 - n1) * i21 = 1) (h31 : (n3 - n1) * i31 = 1) (h32 : (n3 - n2) * i32 = 1)
    (hD21 : D2 - D1 = ρ * (n2 - n1)) (hD31 : D3 - D1 = ρ * (n3 - n1))
    (hD32 : D3 - D2 = ρ * (n3 - n2))
    (hE1 : De - D1 = ρ * (e - n1)) (hE2 : De - D2 = ρ * (e - n2)) (hE3 : De - D3 = ρ * (e - n3)) :
    1 / De - newtonP n1 n2 n3 i21 i31 i32 (1 / D1) (-ρ / (D1 * D1)) (1 / D2) (-ρ / (D2 * D2))
        (1 / D3) (-ρ / (D3 * D3)) e =
      ρ ^ 6 * ((e - n1) ^ 2 * (e - n2) ^ 2 * (e - n3) ^ 2) / (De * D1 ^ 2 * D2 ^ 2 * D3 ^ 2) := by
  have one : (1 : ℝ) ≠ 0 := one_ne_zero
  have r1 := rem_step (ρ := ρ) (s := 1) (π := 1) (P := 1) (Dx := D1) (De := De) (e := e) (x := n1)
    (R := 1 / De) (C := 1 / D1) hDe hD1 one hE1
    (by ring) (by ring)
  have r2 := rem_step (ρ := ρ) (s := (-ρ * 1)) (π := (1 * (e - n1))) (P := (1 * D1)) (Dx := D1) (De := De) (e := e) (x := n1)
    (R := (1 / De - 1 / D1)) (C := -ρ / (D1 * D1) * (e - n1)) hDe hD1 (mul_ne_zero one hD1) hE1
    (r1) (by ring)
  have r3 := rem_step (ρ := ρ) (s := (-ρ * (-ρ * 1))) (π := ((1 * (e - n1)) * (e - n1))) (P := ((1 * D1) * D1)) (Dx := D2) (De := De) (e := e) (x := n2)
    (R := ((1 / De - 1 / D1) - -ρ / (D1 * D1) * (e - n1))) (C := ρ ^ 2 / (D1 ^ 2 * D2) * (e - n1) ^ 2) hDe hD2 (mul_ne_zero (mul_ne_zero one hD1) hD1) hE2
    (r2) (by ring)
  have r4 := rem_step (ρ := ρ) (s := (-ρ * (-ρ * (-ρ * 1)))) (π := (((1 * (e - n1)) * (e - n1)) * (e - n2))) (P := (((1 * D1) * D1) * D2)) (Dx := D2) (De := De) (e := e) (x := n2)
    (R := (((1 / De - 1 / D1) - -ρ / (D1 * D1) * (e - n1)) - ρ ^ 2 / (D1 ^ 2 * D2) * (e - n1) ^ 2)) (C := -ρ ^ 3 / (D1 ^ 2 * D2 ^ 2) * ((e - n1) ^ 2 * (e - n2))) hDe hD2 (mul_ne_zero (mul_ne_zero (mul_ne_zero one hD1) hD1) hD2) hE2
    (r3) (by ring)
  have r5 := rem_step (ρ := ρ) (s := (-ρ * (-ρ * (-ρ * (-ρ * 1))))) (π := ((((1 * (e - n1)) * (e - n1)) * (e - n2)) * (e - n2))) (P := ((((1 * D1) * D1) * D2) * D2)) (Dx := D3) (De := De) (e := e) (x := n3)
    (R := ((((1 / De - 1 / D1) - -ρ / (D1 * D1) * (e - n1)) - ρ ^ 2 / (D1 ^ 2 * D2) * (e - n1) ^ 2) - -ρ ^ 3 / (D1 ^ 2 * D2 ^ 2) * ((e - n1) ^ 2 * (e - n2)))) (C := ρ ^ 4 / (D1 ^ 2 * D2 ^ 2 * D3) * ((e - n1) ^ 2 * (e - n2) ^ 2)) hDe hD3 (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero one hD1) hD1) hD2) hD2) hE3
    (r4) (by ring)
  have r6 := rem_step (ρ := ρ) (s := (-ρ * (-ρ * (-ρ * (-ρ * (-ρ * 1)))))) (π := (((((1 * (e - n1)) * (e - n1)) * (e - n2)) * (e - n2)) * (e - n3))) (P := (((((1 * D1) * D1) * D2) * D2) * D3)) (Dx := D3) (De := De) (e := e) (x := n3)
    (R := (((((1 / De - 1 / D1) - -ρ / (D1 * D1) * (e - n1)) - ρ ^ 2 / (D1 ^ 2 * D2) * (e - n1) ^ 2) - -ρ ^ 3 / (D1 ^ 2 * D2 ^ 2) * ((e - n1) ^ 2 * (e - n2))) - ρ ^ 4 / (D1 ^ 2 * D2 ^ 2 * D3) * ((e - n1) ^ 2 * (e - n2) ^ 2))) (C := -ρ ^ 5 / (D1 ^ 2 * D2 ^ 2 * D3 ^ 2) * ((e - n1) ^ 2 * (e - n2) ^ 2 * (e - n3))) hDe hD3 (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero one hD1) hD1) hD2) hD2) hD3) hE3
    (r5) (by ring)
  have ht := tab_phi hD1 hD2 hD3 h21 h31 h32 hD21 hD31 hD32
  simp only [newtonP, ht]
  linear_combination r6

end PhiTableau

end FormalResearch.FourQubitEntropy.AH6
