module

public import FormalResearch.ModularBootstrap.Integrality.MidpointGrid
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Euclidean angle-shift inverse (`int:cheb-explicit`, first half of its proof)

`CFT/modular_bootstrap/paper/integrality.tex`, Lemma INT-M.exp (`int:cheb-explicit`): on the midpoint
grid of size `N = M + 1`, every target `v ∈ ℝ^M` of the nonconstant cosine moments with
`‖B v‖₂ ≤ 1/(4M)` (`B = -2 Sᵗ D⁻¹ / N`, `S_{mj} = sin(m θ_j)`, `D = diag(1,…,M)`) is realised by an
angle shift `h` with `‖h‖₂ ≤ 1/(2M)`: `∑_j (cos(m(θ_j + h_j)) - cos(m θ_j)) = v_m`.

The proof here is the paper's fixed-Jacobian contraction, written with the unknown
`z ∈ ℝ^M` of `h = -(2/N) Sᵗ z` (so that `‖h‖₂² = (2/N) ‖z‖²`, the Jacobian is `D`, and the map
`z ↦ D⁻¹ F(z)` approximates the identity); the contraction step is Mathlib's
`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`.  **Proved.**
-/

@[expose] public section

open Real Finset

namespace FormalResearch.ModularBootstrap.Integrality

section Algebra

variable {M : ℕ}

/-- The angle shift `h_j(z) = -(2/N) ∑_m sin(mθ_j) z_m` (`N = M + 1`). -/
noncomputable def angleShift (M : ℕ) (z : Fin M → ℝ) (j : ℕ) : ℝ :=
  -(2 / ((M : ℝ) + 1)) *
    ∑ i : Fin M, sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) * z i

lemma angleShift_sub (z z' : Fin M → ℝ) (j : ℕ) :
    angleShift M z j - angleShift M z' j = angleShift M (z - z') j := by
  unfold angleShift
  simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]

lemma angleShift_add_smul (z z' : Fin M → ℝ) (t : ℝ) (j : ℕ) :
    angleShift M z' j + t * angleShift M (z - z') j = angleShift M (z' + t • (z - z')) j := by
  unfold angleShift
  have : ∑ i : Fin M, sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) * (z' + t • (z - z')) i =
      ∑ i : Fin M, sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) * z' i +
        t * ∑ i : Fin M, sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) * (z - z') i := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [this]
  ring

/-- Orthogonality of the sine rows: `∑_j sin(mθ_j) sin(kθ_j) = (N/2) δ_{mk}`. -/
lemma sin_orth (i k : Fin M) :
    ∑ j ∈ range (M + 1), sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) *
      sin ((((k : ℕ) : ℝ) + 1) * midAngle (M + 1) j) =
      if i = k then ((M : ℝ) + 1) / 2 else 0 := by
  have := sum_sin_mul_sin (n := M + 1) (a := (i : ℕ) + 1) (b := (k : ℕ) + 1) (by omega)
    (by have := i.2; omega) (by have := k.2; omega) (by omega) (by omega)
  push_cast at this
  rw [this]
  by_cases hik : i = k
  · simp [hik]
  · have : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    simp [hik, this]

/-- Orthogonality: `∑_j h_j(z)^2 = (2/N) ∑_m z_m^2`. -/
lemma sum_angleShift_sq (z : Fin M → ℝ) :
    ∑ j ∈ range (M + 1), angleShift M z j ^ 2 = (2 / ((M : ℝ) + 1)) * ∑ i : Fin M, z i ^ 2 := by
  have hN : (M : ℝ) + 1 ≠ 0 := by positivity
  set s : Fin M → ℕ → ℝ := fun i j => sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) with hs
  have key : ∀ j : ℕ, angleShift M z j ^ 2 =
      (2 / ((M : ℝ) + 1)) ^ 2 * ∑ i : Fin M, ∑ k : Fin M, (z i * z k) * (s i j * s k j) := by
    intro j
    unfold angleShift
    rw [mul_pow, neg_sq, sq (∑ i : Fin M, sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) * z i),
      sum_mul_sum]
    congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
    simp only [hs]; ring
  simp_rw [key]
  rw [← mul_sum, sum_comm]
  have h2 : ∀ i : Fin M, ∑ j ∈ range (M + 1), ∑ k : Fin M, (z i * z k) * (s i j * s k j) =
      ((M : ℝ) + 1) / 2 * z i ^ 2 := by
    intro i
    rw [sum_comm]
    have h3 : ∀ k : Fin M, ∑ j ∈ range (M + 1), (z i * z k) * (s i j * s k j) =
        if i = k then ((M : ℝ) + 1) / 2 * z i ^ 2 else 0 := by
      intro k
      rw [← mul_sum]
      simp only [hs]
      rw [sin_orth i k]
      by_cases hik : i = k
      · subst hik; simp; ring
      · simp [hik]
    simp_rw [h3]
    simp
  simp_rw [h2]
  rw [← mul_sum]
  field_simp

/-- The linear part: `∑_j sin(mθ_j) h_j(z) = -z_m`. -/
lemma sum_sin_angleShift (z : Fin M → ℝ) (i : Fin M) :
    ∑ j ∈ range (M + 1), sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) * angleShift M z j =
      -z i := by
  have hN : (M : ℝ) + 1 ≠ 0 := by positivity
  unfold angleShift
  have h1 : ∀ j ∈ range (M + 1), sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) *
      (-(2 / ((M : ℝ) + 1)) *
        ∑ k : Fin M, sin ((((k : ℕ) : ℝ) + 1) * midAngle (M + 1) j) * z k) =
      -(2 / ((M : ℝ) + 1)) * ∑ k : Fin M, z k * (sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) *
        sin ((((k : ℕ) : ℝ) + 1) * midAngle (M + 1) j)) := by
    intro j _
    simp only [mul_sum]
    refine sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl h1, ← mul_sum, sum_comm]
  have h2 : ∀ k : Fin M, ∑ j ∈ range (M + 1), z k * (sin ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j) *
      sin ((((k : ℕ) : ℝ) + 1) * midAngle (M + 1) j)) =
      if i = k then z k * (((M : ℝ) + 1) / 2) else 0 := by
    intro k
    rw [← mul_sum, sin_orth i k]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik]
  simp_rw [h2]
  simp
  field_simp

/-- The cosine-moment increments `∑_j (cos(m(θ_j + h_j(z))) - cos(mθ_j))`, `m = i + 1`. -/
noncomputable def momentMap (M : ℕ) (z : Fin M → ℝ) (i : Fin M) : ℝ :=
  ∑ j ∈ range (M + 1), (cos ((((i : ℕ) : ℝ) + 1) * (midAngle (M + 1) j + angleShift M z j)) -
    cos ((((i : ℕ) : ℝ) + 1) * midAngle (M + 1) j))

lemma momentMap_zero (i : Fin M) : momentMap M 0 i = 0 := by
  unfold momentMap angleShift
  simp

/-- **Error of the fixed Jacobian**: for two shifts with `‖h‖₂, ‖h'‖₂ ≤ ρ`,
`|F_m(z) - F_m(z') - m (z_m - z'_m)| ≤ m² ρ ‖h(z - z')‖₂`. -/
lemma momentMap_err (z z' : Fin M → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hz : ∑ j ∈ range (M + 1), angleShift M z j ^ 2 ≤ ρ ^ 2)
    (hz' : ∑ j ∈ range (M + 1), angleShift M z' j ^ 2 ≤ ρ ^ 2) (i : Fin M) :
    |momentMap M z i - momentMap M z' i - (((i : ℕ) : ℝ) + 1) * (z i - z' i)| ≤
      (((i : ℕ) : ℝ) + 1) ^ 2 * ρ *
        Real.sqrt (∑ j ∈ range (M + 1), angleShift M (z - z') j ^ 2) := by
  set m : ℝ := ((i : ℕ) : ℝ) + 1 with hm
  have hm0 : 0 ≤ m := by positivity
  set θ : ℕ → ℝ := fun j => midAngle (M + 1) j with hθ
  set a : ℕ → ℝ := fun j => angleShift M z j with ha
  set b : ℕ → ℝ := fun j => angleShift M z' j with hb
  set δ : ℕ → ℝ := fun j => angleShift M (z - z') j with hδ
  have hδab : ∀ j, δ j = a j - b j := fun j => (angleShift_sub z z' j).symm
  let ψ : ℝ → ℝ := fun t => ∑ j ∈ range (M + 1),
    (cos (m * (θ j + b j + t * δ j)) + m * sin (m * θ j) * (t * δ j))
  let ψ' : ℝ → ℝ := fun t => ∑ j ∈ range (M + 1),
    (-sin (m * (θ j + b j + t * δ j)) * (m * δ j) + m * sin (m * θ j) * δ j)
  have hderiv : ∀ t, HasDerivAt ψ (ψ' t) t := by
    intro t
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => m * (θ j + b j + t * δ j)) (m * δ j) t := by
      have := ((hasDerivAt_id t).mul_const (δ j)).const_add (θ j + b j) |>.const_mul m
      simpa using this
    have h2 := h1.cos
    have h3 : HasDerivAt (fun t : ℝ => m * sin (m * θ j) * (t * δ j)) (m * sin (m * θ j) * δ j) t := by
      have := ((hasDerivAt_id t).mul_const (δ j)).const_mul (m * sin (m * θ j))
      simpa using this
    exact h2.add h3
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖ψ' t‖ ≤
      m ^ 2 * ρ * Real.sqrt (∑ j ∈ range (M + 1), δ j ^ 2) := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hξ : ∑ j ∈ range (M + 1), (b j + t * δ j) ^ 2 ≤ ρ ^ 2 := by
      calc ∑ j ∈ range (M + 1), (b j + t * δ j) ^ 2
          ≤ ∑ j ∈ range (M + 1), ((1 - t) * b j ^ 2 + t * a j ^ 2) := by
            refine sum_le_sum fun j _ => ?_
            rw [hδab j]
            nlinarith [mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1.le)) (sq_nonneg (a j - b j))]
        _ = (1 - t) * ∑ j ∈ range (M + 1), b j ^ 2 + t * ∑ j ∈ range (M + 1), a j ^ 2 := by
            rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ ρ ^ 2 := by
            have h1 : (1 - t) * ∑ j ∈ range (M + 1), b j ^ 2 ≤ (1 - t) * ρ ^ 2 :=
              mul_le_mul_of_nonneg_left hz' (by linarith)
            have h2 : t * ∑ j ∈ range (M + 1), a j ^ 2 ≤ t * ρ ^ 2 :=
              mul_le_mul_of_nonneg_left hz ht0
            nlinarith
    have hterm : ∀ j ∈ range (M + 1),
        |-sin (m * (θ j + b j + t * δ j)) * (m * δ j) + m * sin (m * θ j) * δ j| ≤
          m ^ 2 * (|δ j| * |b j + t * δ j|) := by
      intro j _
      have e : -sin (m * (θ j + b j + t * δ j)) * (m * δ j) + m * sin (m * θ j) * δ j =
          m * δ j * (sin (m * θ j) - sin (m * θ j + m * (b j + t * δ j))) := by
        have : m * (θ j + b j + t * δ j) = m * θ j + m * (b j + t * δ j) := by ring
        rw [this]; ring
      rw [e, abs_mul, abs_mul, abs_of_nonneg hm0]
      have h := Real.abs_sin_sub_sin_le (m * θ j) (m * θ j + m * (b j + t * δ j))
      have h' : |m * θ j - (m * θ j + m * (b j + t * δ j))| = m * |b j + t * δ j| := by
        rw [show m * θ j - (m * θ j + m * (b j + t * δ j)) = -(m * (b j + t * δ j)) by ring,
          abs_neg, abs_mul, abs_of_nonneg hm0]
      rw [h'] at h
      have := mul_le_mul_of_nonneg_left h (mul_nonneg hm0 (abs_nonneg (δ j)))
      nlinarith [this, abs_nonneg (δ j), abs_nonneg (b j + t * δ j)]
    calc ‖ψ' t‖ = |ψ' t| := Real.norm_eq_abs _
      _ ≤ ∑ j ∈ range (M + 1),
          |-sin (m * (θ j + b j + t * δ j)) * (m * δ j) + m * sin (m * θ j) * δ j| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (M + 1), m ^ 2 * (|δ j| * |b j + t * δ j|) := sum_le_sum hterm
      _ = m ^ 2 * ∑ j ∈ range (M + 1), |δ j| * |b j + t * δ j| := by rw [← mul_sum]
      _ ≤ m ^ 2 * (Real.sqrt (∑ j ∈ range (M + 1), |δ j| ^ 2) *
            Real.sqrt (∑ j ∈ range (M + 1), |b j + t * δ j| ^ 2)) :=
            mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (sq_nonneg m)
      _ ≤ m ^ 2 * (Real.sqrt (∑ j ∈ range (M + 1), δ j ^ 2) * ρ) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul (le_of_eq ?_) ?_ (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)) (sq_nonneg m)
            · simp_rw [sq_abs]
            · simp_rw [sq_abs]
              exact Real.sqrt_le_iff.2 ⟨hρ, hξ⟩
      _ = m ^ 2 * ρ * Real.sqrt (∑ j ∈ range (M + 1), δ j ^ 2) := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := ψ) (f' := ψ') (a := 0) (b := 1)
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound 1 (Set.right_mem_Icc.2 zero_le_one)
  have hψ : ψ 1 - ψ 0 = momentMap M z i - momentMap M z' i - m * (z i - z' i) := by
    have hlin := sum_sin_angleShift (z - z') i
    simp only [Pi.sub_apply] at hlin
    simp only [ψ, momentMap]
    have e1 : ∑ j ∈ range (M + 1), (cos (m * (θ j + b j + 1 * δ j)) + m * sin (m * θ j) * (1 * δ j)) -
        ∑ j ∈ range (M + 1), (cos (m * (θ j + b j + 0 * δ j)) + m * sin (m * θ j) * (0 * δ j)) =
        ∑ j ∈ range (M + 1), (cos (m * (θ j + a j)) - cos (m * (θ j + b j))) +
          m * ∑ j ∈ range (M + 1), sin (m * θ j) * δ j := by
      rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      have : θ j + b j + 1 * δ j = θ j + a j := by rw [hδab j]; ring
      rw [this]
      have : θ j + b j + 0 * δ j = θ j + b j := by ring
      rw [this]; ring
    rw [e1]
    have hsum : ∑ j ∈ range (M + 1), sin (m * θ j) * δ j = -(z i - z' i) := hlin
    rw [hsum]
    have e2 : ∑ j ∈ range (M + 1), (cos (m * (θ j + a j)) - cos (m * (θ j + b j))) =
        ∑ j ∈ range (M + 1), (cos (m * (θ j + a j)) - cos (m * θ j)) -
          ∑ j ∈ range (M + 1), (cos (m * (θ j + b j)) - cos (m * θ j)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [e2]
    ring
  rw [hψ, sub_zero, Real.norm_eq_abs] at hmvt
  rw [mul_one] at hmvt
  exact hmvt

/-- `∑_{m=1}^M m² ≤ M²(M+1)/2` for `M ≥ 1`. -/
lemma sum_sq_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ i ∈ range M, (((i : ℕ) : ℝ) + 1) ^ 2 ≤ (M : ℝ) ^ 2 * ((M : ℝ) + 1) / 2 := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [sum_range_succ]
    push_cast
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [ih]

end Algebra

section Banach

variable {M : ℕ}

open Metric in
/-- **Euclidean angle-shift inverse** (`int:cheb-explicit`).  If the moment target `v ∈ ℝ^M`
satisfies `(2/N) ∑_m (v_m/m)² ≤ 1/(16 M²)` (`N = M+1`, i.e. `‖B v‖₂ ≤ 1/(4M)`), then there is a
shift `z` with `‖h(z)‖₂ ≤ 1/(2M)` realising `∑_j (cos(m(θ_j + h_j)) - cos(mθ_j)) = v_m` for all
`1 ≤ m ≤ M`. -/
theorem exists_angleShift (hM : 1 ≤ M) (v : Fin M → ℝ)
    (hv : (2 / ((M : ℝ) + 1)) * ∑ i : Fin M, (v i / (((i : ℕ) : ℝ) + 1)) ^ 2 ≤
      1 / (16 * (M : ℝ) ^ 2)) :
    ∃ z : Fin M → ℝ, ∑ j ∈ range (M + 1), angleShift M z j ^ 2 ≤ (1 / (2 * (M : ℝ))) ^ 2 ∧
      ∀ i, momentMap M z i = v i := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hM0 : (0 : ℝ) < M := by linarith
  set ρ : ℝ := 1 / (2 * (M : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  let f : EuclideanSpace ℝ (Fin M) → EuclideanSpace ℝ (Fin M) := fun z =>
    WithLp.toLp 2 (fun i => momentMap M z.ofLp i / (((i : ℕ) : ℝ) + 1))
  let y : EuclideanSpace ℝ (Fin M) := WithLp.toLp 2 (fun i => v i / (((i : ℕ) : ℝ) + 1))
  have hynorm : ‖y‖ ^ 2 = ∑ i : Fin M, (v i / (((i : ℕ) : ℝ) + 1)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, y]
  have hy2 : ‖y‖ ^ 2 ≤ ((M : ℝ) + 1) / 2 * (1 / (16 * (M : ℝ) ^ 2)) := by
    rw [hynorm]
    have h := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ ((M : ℝ) + 1) / 2)
    have e : ((M : ℝ) + 1) / 2 * (2 / ((M : ℝ) + 1) *
        ∑ i : Fin M, (v i / (((i : ℕ) : ℝ) + 1)) ^ 2) =
        ∑ i : Fin M, (v i / (((i : ℕ) : ℝ) + 1)) ^ 2 := by field_simp
    rw [e] at h
    exact h
  set ε : ℝ := 2 * ‖y‖ with hε
  have hε0 : 0 ≤ ε := by positivity
  -- inside the ball the shift has Euclidean norm at most `ρ`
  have hball : ∀ z : EuclideanSpace ℝ (Fin M), ‖z‖ ≤ ε →
      ∑ j ∈ range (M + 1), angleShift M z.ofLp j ^ 2 ≤ ρ ^ 2 := by
    intro z hz
    rw [sum_angleShift_sq]
    have h1 : ∑ i : Fin M, z.ofLp i ^ 2 = ‖z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp
    rw [h1]
    have h2 : ‖z‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have h3 : ε ^ 2 = 4 * ‖y‖ ^ 2 := by rw [hε]; ring
    have h4 : 2 / ((M : ℝ) + 1) * ‖z‖ ^ 2 ≤ 2 / ((M : ℝ) + 1) *
        (4 * (((M : ℝ) + 1) / 2 * (1 / (16 * (M : ℝ) ^ 2)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [h3] at h2
      linarith [hy2]
    refine h4.trans (le_of_eq ?_)
    rw [hρdef]
    field_simp
    ring
  -- approximation of the identity on the ball
  have happ : ApproximatesLinearOn f (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin M)))
      (closedBall 0 ε) (1 / 2) := by
    intro x hx w hw
    have hxb := hball x (by simpa using mem_closedBall_zero_iff.1 hx)
    have hwb := hball w (by simpa using mem_closedBall_zero_iff.1 hw)
    simp only [ContinuousLinearMap.id_apply]
    have hD : ∑ j ∈ range (M + 1), angleShift M (x.ofLp - w.ofLp) j ^ 2 =
        2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2 := by
      rw [sum_angleShift_sq]
      congr 1
      rw [EuclideanSpace.norm_sq_eq]; simp
    have hterm : ∀ i : Fin M, ((f x - f w - (x - w)).ofLp i) ^ 2 ≤
        (((i : ℕ) : ℝ) + 1) ^ 2 * ρ ^ 2 * (2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2) := by
      intro i
      have hm : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
      have herr := momentMap_err x.ofLp w.ofLp hρ0 hxb hwb i
      rw [hD] at herr
      have hsq : (momentMap M x.ofLp i - momentMap M w.ofLp i -
          (((i : ℕ) : ℝ) + 1) * (x.ofLp i - w.ofLp i)) ^ 2 ≤
          ((((i : ℕ) : ℝ) + 1) ^ 2) ^ 2 * ρ ^ 2 * (2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2) := by
        have h0 : (0 : ℝ) ≤ 2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2 := by positivity
        calc _ = |momentMap M x.ofLp i - momentMap M w.ofLp i -
              (((i : ℕ) : ℝ) + 1) * (x.ofLp i - w.ofLp i)| ^ 2 := (sq_abs _).symm
          _ ≤ ((((i : ℕ) : ℝ) + 1) ^ 2 * ρ *
              Real.sqrt (2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) herr 2
          _ = ((((i : ℕ) : ℝ) + 1) ^ 2) ^ 2 * ρ ^ 2 * (2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2) := by
              rw [mul_pow, mul_pow, Real.sq_sqrt h0]
      have e : (f x - f w - (x - w)).ofLp i =
          (momentMap M x.ofLp i - momentMap M w.ofLp i -
            (((i : ℕ) : ℝ) + 1) * (x.ofLp i - w.ofLp i)) / (((i : ℕ) : ℝ) + 1) := by
        simp only [f, WithLp.ofLp_sub, Pi.sub_apply]
        field_simp
      rw [e, div_pow, div_le_iff₀ (by positivity)]
      calc _ ≤ _ := hsq
        _ = _ := by ring
    have hsum : ‖f x - f w - (x - w)‖ ^ 2 ≤ (1 / 2) ^ 2 * ‖x - w‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      calc ∑ i : Fin M, (f x - f w - (x - w)).ofLp i ^ 2
          ≤ ∑ i : Fin M, (((i : ℕ) : ℝ) + 1) ^ 2 * ρ ^ 2 * (2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2) :=
            sum_le_sum fun i _ => hterm i
        _ = (∑ i : Fin M, (((i : ℕ) : ℝ) + 1) ^ 2) * (ρ ^ 2 * (2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2)) := by
            rw [sum_mul]; refine sum_congr rfl fun i _ => by ring
        _ ≤ ((M : ℝ) ^ 2 * ((M : ℝ) + 1) / 2) * (ρ ^ 2 * (2 / ((M : ℝ) + 1) * ‖x - w‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have := sum_sq_le M hM
            rwa [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i : ℝ) + 1) ^ 2) M]
        _ = (1 / 2) ^ 2 * ‖x - w‖ ^ 2 := by
            rw [hρdef]; field_simp
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity : 0 ≤ (1 / 2 : ℝ) * ‖x - w‖)
      (two_ne_zero)).1 (by rw [mul_pow]; exact hsum)
    simpa using this
  let f'symm : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin M))).NonlinearRightInverse :=
    { toFun := fun w => w
      nnNorm := 1
      bound' := fun w => by simp
      right_inv' := fun w => rfl }
  have hf0 : f 0 = 0 := by
    ext i
    simp [f, momentMap_zero]
  have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse f'symm hε0 (subset_refl _)
  have hy : y ∈ closedBall (f 0) (((f'symm.nnNorm : ℝ)⁻¹ - ((1 / 2 : NNReal) : ℝ)) * ε) := by
    rw [hf0, mem_closedBall_zero_iff]
    have : (f'symm.nnNorm : ℝ) = 1 := rfl
    rw [this, hε]
    simp
    linarith
  obtain ⟨z, hz, hfz⟩ := hsurj hy
  refine ⟨z.ofLp, hball z (mem_closedBall_zero_iff.1 hz), fun i => ?_⟩
  have h1 := congrArg (fun u : EuclideanSpace ℝ (Fin M) => u.ofLp i) hfz
  simp only [f, y] at h1
  have hm : (((i : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  field_simp at h1
  exact h1

end Banach

end FormalResearch.ModularBootstrap.Integrality
