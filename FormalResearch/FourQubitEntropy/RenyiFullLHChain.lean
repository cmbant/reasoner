module

public import FormalResearch.FourQubitEntropy.RenyiFullLHHermite
public import FormalResearch.FourQubitEntropy.RenyiFullProps

/-!
# The derivative chain of `h(a,K) = -ln(a^q + K(1-a)^q)/((q-1) ln 2)`

Paper E, `lem:fqe-large-head-curvature`.  With `x = 2a - 1` and
`y = (a^q - K(1-a)^q)/(a^q + K(1-a)^q)` one has `y' = 2q(1-y²)/(1-x²)`, and the successive
derivatives of `ln Z`, `Z = a^q + K(1-a)^q`, are the explicit rational functions `lhm1 … lhm4` of `(x, y)`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def lhZ (q K a : ℝ) : ℝ := a ^ q + K * (1 - a) ^ q

noncomputable def lhY (q K a : ℝ) : ℝ := (a ^ q - K * (1 - a) ^ q) / lhZ q K a

/-- `d/da ln Z`. -/
noncomputable def lhm1 (q x y : ℝ) : ℝ := 2 * q * (y - x) / (1 - x ^ 2)

noncomputable def lhm2 (q x y : ℝ) : ℝ :=
  -4 * q * (q * y ^ 2 - q + x ^ 2 - 2 * x * y + 1) / (1 - x ^ 2) ^ 2

noncomputable def lhm3 (q x y : ℝ) : ℝ :=
  16 * q * (q ^ 2 * y ^ 3 - q ^ 2 * y - 3 * q * x * y ^ 2 + 3 * q * x - x ^ 3 + 3 * x ^ 2 * y - 3 * x + y)
    / (1 - x ^ 2) ^ 3

/-- The numerator of the fourth derivative of `ln Z`; `lhm4 = -16 q J / (1-x²)^4`. -/
noncomputable def lhJ (q x y : ℝ) : ℝ :=
  6 * q ^ 3 * y ^ 4 - 24 * q ^ 2 * x * y ^ 3 + (-8 * q ^ 3 + 36 * q * x ^ 2 + 8 * q) * y ^ 2
    + (24 * q ^ 2 * x - 24 * x ^ 3 - 24 * x) * y + 2 * q ^ 3 - 36 * q * x ^ 2 - 8 * q + 6 * x ^ 4
    + 36 * x ^ 2 + 6

noncomputable def lhm4 (q x y : ℝ) : ℝ := -16 * q * lhJ q x y / (1 - x ^ 2) ^ 4

theorem hasDerivAt_lhZ {q K a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (lhZ q K) (q * a ^ q / a - K * (q * (1 - a) ^ q / (1 - a))) a := by
  have h1a : 0 < 1 - a := by linarith
  have e1 : HasDerivAt (fun a : ℝ => a ^ q) (q * a ^ q / a) a := by
    have := (hasDerivAt_id a).rpow_const (p := q) (Or.inl ha.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one ha.ne']
    ring
  have e2 : HasDerivAt (fun a : ℝ => (1 - a) ^ q) (-(q * (1 - a) ^ q / (1 - a))) a := by
    have := ((hasDerivAt_id a).const_sub 1).rpow_const (p := q) (Or.inl h1a.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one h1a.ne']
    ring
  have := e1.add (e2.const_mul K)
  refine this.congr_deriv ?_
  ring

theorem lhZ_pos {q K a : ℝ} (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) : 0 < lhZ q K a := by
  unfold lhZ
  have : 0 < (1 - a) := by linarith
  have := Real.rpow_pos_of_pos ha q
  have := Real.rpow_pos_of_pos (show 0 < 1 - a by linarith) q
  positivity

theorem lhm1_eq {q K a : ℝ} (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    q * a ^ q / a - K * (q * (1 - a) ^ q / (1 - a)) = lhZ q K a * lhm1 q (2 * a - 1) (lhY q K a) := by
  have hZ := lhZ_pos (q := q) hK ha ha1
  have h1a : 0 < 1 - a := by linarith
  unfold lhm1 lhY
  have hx : (1 - (2 * a - 1) ^ 2) = 4 * a * (1 - a) := by ring
  rw [hx]
  have : lhZ q K a ≠ 0 := hZ.ne'
  unfold lhZ at this ⊢
  field_simp
  ring

theorem hasDerivAt_log_lhZ {q K a : ℝ} (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun a => Real.log (lhZ q K a)) (lhm1 q (2 * a - 1) (lhY q K a)) a := by
  have hZ := lhZ_pos (q := q) hK ha ha1
  have := (hasDerivAt_lhZ (q := q) (K := K) ha ha1).log hZ.ne'
  refine this.congr_deriv ?_
  rw [lhm1_eq hK ha ha1]
  field_simp

theorem hasDerivAt_lhY {q K a : ℝ} (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (lhY q K) (2 * q * (1 - lhY q K a ^ 2) / (1 - (2 * a - 1) ^ 2)) a := by
  have hZ := lhZ_pos (q := q) hK ha ha1
  have h1a : 0 < 1 - a := by linarith
  have e1 : HasDerivAt (fun a : ℝ => a ^ q) (q * a ^ q / a) a := by
    have := (hasDerivAt_id a).rpow_const (p := q) (Or.inl ha.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one ha.ne']
    ring
  have e2 : HasDerivAt (fun a : ℝ => (1 - a) ^ q) (-(q * (1 - a) ^ q / (1 - a))) a := by
    have := ((hasDerivAt_id a).const_sub 1).rpow_const (p := q) (Or.inl h1a.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one h1a.ne']
    ring
  have hn := e1.sub (e2.const_mul K)
  have hd := e1.add (e2.const_mul K)
  have := hn.div hd hZ.ne'
  unfold lhY
  refine this.congr_deriv ?_
  have hx : (1 - (2 * a - 1) ^ 2) = 4 * a * (1 - a) := by ring
  rw [hx]
  have hu := Real.rpow_pos_of_pos ha q
  have hv := Real.rpow_pos_of_pos h1a q
  unfold lhZ at hZ ⊢
  simp only [Pi.add_apply, Pi.sub_apply]
  field_simp
  ring


/-! ### The algebraic steps `m1 → m2 → m3 → m4` along the ODE -/

section Steps

variable {q a : ℝ} {X Y : ℝ → ℝ}

theorem step12 (hX : HasDerivAt X 2 a) (hY : HasDerivAt Y (2 * q * (1 - Y a ^ 2) / (1 - X a ^ 2)) a)
    (h : 1 - X a ^ 2 ≠ 0) :
    HasDerivAt (fun a => lhm1 q (X a) (Y a)) (lhm2 q (X a) (Y a)) a := by
  have hn := (hY.sub hX).const_mul (2 * q)
  have hd := (hX.fun_pow 2).const_sub 1
  have := hn.fun_div hd h
  convert this using 1
  · funext a'
    simp [lhm1]
  · simp [lhm2]
    field_simp
    ring

theorem step23 (hX : HasDerivAt X 2 a) (hY : HasDerivAt Y (2 * q * (1 - Y a ^ 2) / (1 - X a ^ 2)) a)
    (h : 1 - X a ^ 2 ≠ 0) :
    HasDerivAt (fun a => lhm2 q (X a) (Y a)) (lhm3 q (X a) (Y a)) a := by
  have hn := ((((((hY.fun_pow 2).const_mul q).sub_const q).fun_add (hX.fun_pow 2)).fun_sub
    ((hX.fun_mul hY).const_mul 2)).add_const 1).const_mul (-4 * q)
  have hd := (((hX.fun_pow 2).const_sub 1).fun_pow 2)
  have := hn.fun_div hd (pow_ne_zero 2 h)
  convert this using 1
  · funext a'
    simp only [lhm2]
    ring
  · simp [lhm3]
    field_simp
    ring

theorem step34 (hX : HasDerivAt X 2 a) (hY : HasDerivAt Y (2 * q * (1 - Y a ^ 2) / (1 - X a ^ 2)) a)
    (h : 1 - X a ^ 2 ≠ 0) :
    HasDerivAt (fun a => lhm3 q (X a) (Y a)) (lhm4 q (X a) (Y a)) a := by
  have t1 := (hY.fun_pow 3).const_mul (q ^ 2)
  have t2 := hY.const_mul (q ^ 2)
  have t3 := (hX.fun_mul (hY.fun_pow 2)).const_mul (3 * q)
  have t4 := hX.const_mul (3 * q)
  have t5 := hX.fun_pow 3
  have t6 := ((hX.fun_pow 2).fun_mul hY).const_mul 3
  have t7 := hX.const_mul 3
  have hn := ((((((t1.fun_sub t2).fun_sub t3).fun_add t4).fun_sub t5).fun_add t6).fun_sub t7).fun_add hY
  have hn := hn.const_mul (16 * q)
  have hd := (((hX.fun_pow 2).const_sub 1).fun_pow 3)
  have := hn.fun_div hd (pow_ne_zero 3 h)
  convert this using 1
  · funext a'
    simp only [lhm3]
    ring
  · simp [lhm4, lhJ]
    field_simp
    ring

end Steps


/-! ### `h` and its derivatives -/

noncomputable def hfun (q K a : ℝ) : ℝ := -Real.log (lhZ q K a) / ((q - 1) * Real.log 2)

noncomputable def hd1 (q K a : ℝ) : ℝ := -lhm1 q (2 * a - 1) (lhY q K a) / ((q - 1) * Real.log 2)
noncomputable def hd2 (q K a : ℝ) : ℝ := -lhm2 q (2 * a - 1) (lhY q K a) / ((q - 1) * Real.log 2)
noncomputable def hd3 (q K a : ℝ) : ℝ := -lhm3 q (2 * a - 1) (lhY q K a) / ((q - 1) * Real.log 2)
noncomputable def hd4 (q K a : ℝ) : ℝ := -lhm4 q (2 * a - 1) (lhY q K a) / ((q - 1) * Real.log 2)

section HChain

variable {q K a : ℝ}

theorem hX_deriv (a : ℝ) : HasDerivAt (fun a : ℝ => 2 * a - 1) 2 a := by
  have := ((hasDerivAt_id a).const_mul 2).sub_const 1
  simpa using this

theorem one_sub_x_sq_ne {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 1 - (2 * a - 1) ^ 2 ≠ 0 := by
  nlinarith

theorem hasDerivAt_hfun (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (hfun q K) (hd1 q K a) a := by
  have := (hasDerivAt_log_lhZ (q := q) hK ha ha1).neg.div_const ((q - 1) * Real.log 2)
  exact this

theorem hasDerivAt_hd1 (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (hd1 q K) (hd2 q K a) a := by
  have := (step12 (q := q) (hX_deriv a) (hasDerivAt_lhY (q := q) hK ha ha1) (one_sub_x_sq_ne ha ha1)).neg.div_const
    ((q - 1) * Real.log 2)
  exact this

theorem hasDerivAt_hd2 (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (hd2 q K) (hd3 q K a) a := by
  have := (step23 (q := q) (hX_deriv a) (hasDerivAt_lhY (q := q) hK ha ha1) (one_sub_x_sq_ne ha ha1)).neg.div_const
    ((q - 1) * Real.log 2)
  exact this

theorem hasDerivAt_hd3 (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (hd3 q K) (hd4 q K a) a := by
  have := (step34 (q := q) (hX_deriv a) (hasDerivAt_lhY (q := q) hK ha ha1) (one_sub_x_sq_ne ha ha1)).neg.div_const
    ((q - 1) * Real.log 2)
  exact this

end HChain

/-! ### The polynomial part -/

/-- `P(a) = (α+17β) p - 12β t - γ p² - α/3 - 4β + γ/9` with `p = a² + B(1-a)²`, `t = a³ + C(1-a)³`. -/
noncomputable def Pgen (α β γ B C a : ℝ) : ℝ :=
  (α + 17 * β) * (a ^ 2 + B * (1 - a) ^ 2) - 12 * β * (a ^ 3 + C * (1 - a) ^ 3)
    - γ * (a ^ 2 + B * (1 - a) ^ 2) ^ 2 - α / 3 - 4 * β + γ / 9

noncomputable def Pg1 (α β γ B C a : ℝ) : ℝ :=
  (α + 17 * β) * (2 * a - 2 * B * (1 - a)) - 12 * β * (3 * a ^ 2 - 3 * C * (1 - a) ^ 2)
    - 2 * γ * (a ^ 2 + B * (1 - a) ^ 2) * (2 * a - 2 * B * (1 - a))

noncomputable def Pg2 (α β γ B C a : ℝ) : ℝ :=
  (α + 17 * β) * (2 + 2 * B) - 12 * β * (6 * a + 6 * C * (1 - a))
    - 2 * γ * ((2 * a - 2 * B * (1 - a)) ^ 2 + (a ^ 2 + B * (1 - a) ^ 2) * (2 + 2 * B))

noncomputable def Pg3 (_α β γ B C a : ℝ) : ℝ :=
  -12 * β * (6 - 6 * C) - 6 * γ * (2 * a - 2 * B * (1 - a)) * (2 + 2 * B)

noncomputable def Pg4 (γ B : ℝ) : ℝ := -6 * γ * (2 + 2 * B) ^ 2

section PChain

variable {α β γ B C : ℝ}

theorem hasDerivAt_Pgen (a : ℝ) : HasDerivAt (Pgen α β γ B C) (Pg1 α β γ B C a) a := by
  have h : HasDerivAt (Pgen α β γ B C) (deriv (Pgen α β γ B C) a) a :=
    (by unfold Pgen; fun_prop : DifferentiableAt ℝ (Pgen α β γ B C) a).hasDerivAt
  refine h.congr_deriv ?_
  unfold Pgen Pg1
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_Pg1 (a : ℝ) : HasDerivAt (Pg1 α β γ B C) (Pg2 α β γ B C a) a := by
  have h : HasDerivAt (Pg1 α β γ B C) (deriv (Pg1 α β γ B C) a) a :=
    (by unfold Pg1; fun_prop : DifferentiableAt ℝ (Pg1 α β γ B C) a).hasDerivAt
  refine h.congr_deriv ?_
  unfold Pg1 Pg2
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_Pg2 (a : ℝ) : HasDerivAt (Pg2 α β γ B C) (Pg3 α β γ B C a) a := by
  have h : HasDerivAt (Pg2 α β γ B C) (deriv (Pg2 α β γ B C) a) a :=
    (by unfold Pg2; fun_prop : DifferentiableAt ℝ (Pg2 α β γ B C) a).hasDerivAt
  refine h.congr_deriv ?_
  unfold Pg2 Pg3
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_Pg3 (a : ℝ) : HasDerivAt (Pg3 α β γ B C) (Pg4 γ B) a := by
  have h : HasDerivAt (Pg3 α β γ B C) (deriv (Pg3 α β γ B C) a) a :=
    (by unfold Pg3; fun_prop : DifferentiableAt ℝ (Pg3 α β γ B C) a).hasDerivAt
  refine h.congr_deriv ?_
  unfold Pg3 Pg4
  simp (disch := fun_prop)
  ring

end PChain

end FormalResearch.FourQubitEntropy.RenyiFull
