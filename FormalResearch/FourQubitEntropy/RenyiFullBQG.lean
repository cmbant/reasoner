module

public import FormalResearch.FourQubitEntropy.RenyiFullBQOde

/-!
# Binary quartic lemma: the derivative formulas (BQ-1)

With `s = tanh φ`, `x = tanh(qφ)`, `f = ln m_q`, `v = s²`: `f' = q(x-s)/(2s(1-s²))`, `G = f''`,
and `G'(s)`, `G''(s) = -q M(x,s) / (2 s⁵ (1-s²)⁴)` as rational functions of `(s, x(s))` along the
Riccati equation.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

/-- `f'(v)` at `v = s²`, as a function of `s`: `q (x - s)/(2 s (1 - s²))`. -/
noncomputable def bqF1 (q s : ℝ) : ℝ := q * (bqx q s - s) / (2 * s * (1 - s ^ 2))

/-- `G(s) = f''(s²)`. -/
noncomputable def bqG (q s : ℝ) : ℝ :=
  q * (q * s - bqx q s + 3 * s ^ 2 * bqx q s - q * s * bqx q s ^ 2 - 2 * s ^ 3) /
    (4 * s ^ 3 * (1 - s ^ 2) ^ 2)

/-- The numerator `N₁(s,x)` of `G'`. -/
noncomputable def bqN1 (q s x : ℝ) : ℝ :=
  2 * q ^ 2 * s ^ 2 * x ^ 3 - 2 * q ^ 2 * s ^ 2 * x - 9 * q * s ^ 3 * x ^ 2 + 9 * q * s ^ 3
    + 3 * q * s * x ^ 2 - 3 * q * s - 8 * s ^ 5 + 15 * s ^ 4 * x - 10 * s ^ 2 * x + 3 * x

/-- `G'(s) = q N₁(s, x(s)) / (4 s⁴ (1-s²)³)`. -/
noncomputable def bqG1 (q s : ℝ) : ℝ :=
  q * bqN1 q s (bqx q s) / (4 * s ^ 4 * (1 - s ^ 2) ^ 3)

/-- The numerator `M(x,s)` of `G''` (BQ-1). -/
noncomputable def bqM (q s x : ℝ) : ℝ :=
  3 * q ^ 3 * s ^ 3 * x ^ 4 + q ^ 2 * s ^ 2 * (5 - 17 * s ^ 2) * x ^ 3
    + q * s * (6 - 23 * s ^ 2 - 4 * q ^ 2 * s ^ 2 + 39 * s ^ 4) * x ^ 2
    + (6 - 25 * s ^ 2 - 5 * q ^ 2 * s ^ 2 + 40 * s ^ 4 + 17 * q ^ 2 * s ^ 4 - 45 * s ^ 6) * x
    - 6 * q * s + (23 * q + q ^ 3) * s ^ 3 + (4 - 39 * q) * s ^ 5 + 20 * s ^ 7

/-- `G''(s) = -q M(x(s), s) / (2 s⁵ (1-s²)⁴)`. -/
noncomputable def bqG2 (q s : ℝ) : ℝ :=
  -(q * bqM q s (bqx q s)) / (2 * s ^ 5 * (1 - s ^ 2) ^ 4)

theorem hasDerivAt_bqF1 {q s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (bqF1 q) (2 * s * bqG q s) s := by
  have hs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hx := hasDerivAt_bqx (q := q) hs
  have hxd := hx.differentiableAt
  have hxd' := hx.deriv
  have hs2 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hnum : HasDerivAt (fun s => q * (bqx q s - s))
      (q * (q * (1 - bqx q s ^ 2) / (1 - s ^ 2) - 1)) s := by
    have := (hx.sub (hasDerivAt_id s)).const_mul q
    exact this.congr_deriv (by simp)
  have hden : HasDerivAt (fun s : ℝ => 2 * s * (1 - s ^ 2)) (2 * (1 - s ^ 2) + 2 * s * (-(2 * s))) s := by
    have h : HasDerivAt (fun s : ℝ => 2 * s * (1 - s ^ 2)) (deriv (fun s : ℝ => 2 * s * (1 - s ^ 2)) s) s :=
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => 2 * s * (1 - s ^ 2)) s).hasDerivAt
    refine h.congr_deriv ?_
    simp (disch := fun_prop)
  have := hnum.div hden (by positivity)
  refine this.congr_deriv ?_
  unfold bqG
  have : s ≠ 0 := hs0.ne'
  field_simp
  ring


theorem hasDerivAt_bqG {q s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (bqG q) (bqG1 q s) s := by
  have hs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hx := hasDerivAt_bqx (q := q) hs
  have hxd := hx.differentiableAt
  have hxd' := hx.deriv
  have hs2 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hnum : HasDerivAt (fun s => q * (q * s - bqx q s + 3 * s ^ 2 * bqx q s - q * s * bqx q s ^ 2 - 2 * s ^ 3))
      (deriv (fun s => q * (q * s - bqx q s + 3 * s ^ 2 * bqx q s - q * s * bqx q s ^ 2 - 2 * s ^ 3)) s) s :=
    (by fun_prop : DifferentiableAt ℝ (fun s => q * (q * s - bqx q s + 3 * s ^ 2 * bqx q s - q * s * bqx q s ^ 2 - 2 * s ^ 3)) s).hasDerivAt
  have hden : HasDerivAt (fun s : ℝ => 4 * s ^ 3 * (1 - s ^ 2) ^ 2)
      (deriv (fun s : ℝ => 4 * s ^ 3 * (1 - s ^ 2) ^ 2) s) s :=
    (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => 4 * s ^ 3 * (1 - s ^ 2) ^ 2) s).hasDerivAt
  have := hnum.div hden (by positivity)
  refine this.congr_deriv ?_
  simp (disch := fun_prop) [hxd']
  unfold bqG1 bqN1
  have : s ≠ 0 := hs0.ne'
  field_simp
  ring

theorem hasDerivAt_bqG1 {q s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (bqG1 q) (bqG2 q s) s := by
  have hs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hx := hasDerivAt_bqx (q := q) hs
  have hxd := hx.differentiableAt
  have hxd' := hx.deriv
  have hs2 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hnum : HasDerivAt (fun s => q * bqN1 q s (bqx q s))
      (deriv (fun s => q * bqN1 q s (bqx q s)) s) s :=
    (by unfold bqN1; fun_prop : DifferentiableAt ℝ (fun s => q * bqN1 q s (bqx q s)) s).hasDerivAt
  have hden : HasDerivAt (fun s : ℝ => 4 * s ^ 4 * (1 - s ^ 2) ^ 3)
      (deriv (fun s : ℝ => 4 * s ^ 4 * (1 - s ^ 2) ^ 3) s) s :=
    (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => 4 * s ^ 4 * (1 - s ^ 2) ^ 3) s).hasDerivAt
  have := hnum.div hden (by positivity)
  refine this.congr_deriv ?_
  unfold bqN1
  simp (disch := fun_prop) [hxd']
  unfold bqG2 bqM
  have : s ≠ 0 := hs0.ne'
  field_simp
  ring

end FormalResearch.FourQubitEntropy.RenyiFull
