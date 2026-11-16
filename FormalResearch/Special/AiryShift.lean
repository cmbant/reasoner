module

public import FormalResearch.Special.AiryBridge
public import FormalResearch.Special.AiryValues
public import FormalResearch.Special.AiryBiReal

/-!
# The Airy shift identity

For a solution `(y, y')` of `y'' = x y` on `ℝ` and `X, s ∈ ℝ`,
```
y(X+s)  = y(X) C(X,s)  + y'(X) S(X,s),
y'(X+s) = y(X) C_s(X,s) + y'(X) S_s(X,s),
```
where `s ↦ C(X,s)`, `s ↦ S(X,s)` are the solutions of `Y'' = (X+s) Y` with Cauchy data `(1, 0)`,
`(0, 1)` at `s = 0` and `C_s`, `S_s` are their `s`-derivatives.  This is Lemma `airy2-shift-parity` (i)
of the P3 appendices (`weyl_midpoint_semiclassics_appendices.tex`, `A:1068`) and the shift step behind
`lem:ec-defect` of `Weyl/free_fermion/notes/edge_crossover.tex` (`EC:78-86`), in the unscaled variable
(the paper's `C(s; ζ, h)`, `S(s; ζ, h)` are `C(X, h^{1/3} s)` and `h^{-1/3} S(X, h^{1/3} s)` with
`X = h^{-2/3} ζ`).

## Definition (the cheapest rigorous route)

`C`, `S` are *defined* by the Wronskian-type combinations of `Ai`, `Bi` (with `W(Ai, Bi) = 1/π`,
`airyAiC_wronskian_airyBiC_eq`):
```
S(X,s) = π (Ai(X) Bi(X+s) − Bi(X) Ai(X+s)),      C(X,s) = π (Bi'(X) Ai(X+s) − Ai'(X) Bi(X+s)),
```
and `S_s`, `C_s` are the formal `s`-derivatives (`hasDerivAt_airyShiftS` ...).  In particular the identity
`Ai(X+s) Bi(X) − Ai(X) Bi(X+s) = −S(X,s)/π` (`A:1121`) holds by definition
(`airyShift_wronskian_shift`).  The shift identity for an arbitrary solution is then *uniqueness* for the
ODE `Y'' = (X+s) Y` (`SturmAiry.IsSol.eq_zero_of_zero_data`).  Being combinations of the entire functions
`Ai(X+·)`, `Bi(X+·)`, `C(X,·)` and `S(X,·)` are entire in `s`; the power series
`C = 1 + X s²/2 + s³/6 + X² s⁴/24 + X s⁵/30 + …`, `S = s + X s³/6 + s⁴/12 + …`
(coefficients `c_{n+2} = (X c_n + c_{n-1})/((n+2)(n+1))`) was checked against these definitions with
`mpmath` (30 digits, `X ∈ {-3,-1,0,0.7,2,5.5}`, `s ∈ {-1,-0.3,0.2,0.9}`; max discrepancy `4e-15`, which is
float input rounding), but the recurrence is *not* formalised as a power series; the low-order Taylor
coefficients with remainder are `AiryShiftTaylor.airyShiftC_taylor`, `airyShiftS_taylor` (applying the Taylor
lemma for solutions to `C(X, · - X)`, `S(X, · - X)`).

Not formalised: the power series / recurrence for the coefficients of `C`, `S`; the dependence of
`C(s; ζ, h)`, `S(s; ζ, h)` on the parameters `(ζ, h)` (analyticity, parity under `h ↦ -h`).
-/

@[expose] public section

open Set

namespace FormalResearch.Special

open SturmAiry

/-! ### The real `Bi'`

`Bi'` on the real axis is `airyBiDeriv` (`AiryBiReal`): `hasDerivAt_airyBi`, `hasDerivAt_airyBiDeriv`,
`airyWronskian_real` (`Ai Bi' - Ai' Bi = 1/π`). -/

/-- `(Bi, Bi')` is a real solution of `y'' = x y`. -/
theorem isAirySol_airyBi_shift : IsAirySol airyBi airyBiDeriv :=
  fun x => ⟨hasDerivAt_airyBi x, hasDerivAt_airyBiDeriv x⟩

/-! ### The functions `C`, `S` -/

/-- `S(X, s) = π (Ai(X) Bi(X+s) − Bi(X) Ai(X+s))`: the solution of `Y'' = (X+s) Y` with `(Y, Y')(0) = (0, 1)`. -/
noncomputable def airyShiftS (X s : ℝ) : ℝ :=
  Real.pi * (airyAi X * airyBi (X + s) - airyBi X * airyAi (X + s))

/-- `C(X, s) = π (Bi'(X) Ai(X+s) − Ai'(X) Bi(X+s))`: the solution of `Y'' = (X+s) Y` with
`(Y, Y')(0) = (1, 0)`. -/
noncomputable def airyShiftC (X s : ℝ) : ℝ :=
  Real.pi * (airyBiDeriv X * airyAi (X + s) - airyAi' X * airyBi (X + s))

/-- `S_s(X, s) = ∂_s S(X, s)`. -/
noncomputable def airyShiftSd (X s : ℝ) : ℝ :=
  Real.pi * (airyAi X * airyBiDeriv (X + s) - airyBi X * airyAi' (X + s))

/-- `C_s(X, s) = ∂_s C(X, s)`. -/
noncomputable def airyShiftCd (X s : ℝ) : ℝ :=
  Real.pi * (airyBiDeriv X * airyAi' (X + s) - airyAi' X * airyBiDeriv (X + s))

private lemma pi_mul_w (x : ℝ) :
    Real.pi * (airyAi x * airyBiDeriv x - airyAi' x * airyBi x) = 1 := by
  rw [airyWronskian_real]; field_simp [Real.pi_pos.ne']

/-- Initial data: `C(X,0) = 1`, `C_s(X,0) = 0`, `S(X,0) = 0`, `S_s(X,0) = 1`. -/
theorem airyShift_initial (X : ℝ) :
    airyShiftC X 0 = 1 ∧ airyShiftCd X 0 = 0 ∧ airyShiftS X 0 = 0 ∧ airyShiftSd X 0 = 1 := by
  have h := pi_mul_w X
  simp only [airyShiftC, airyShiftCd, airyShiftS, airyShiftSd, add_zero]
  refine ⟨by linarith, by ring, by ring, by linarith⟩

/-- Shifting a solution of `y'' = x y` by `X` gives a solution of `Y'' = (X+s) Y`. -/
theorem isSol_shift {y y' : ℝ → ℝ} (h : IsAirySol y y') (X : ℝ) :
    IsSol (fun s => X + s) (fun s => y (X + s)) (fun s => y' (X + s)) where
  hasDerivAt s := (h (X + s)).1.comp_const_add X s
  hasDerivAt' s := (h (X + s)).2.comp_const_add X s

/-- Linear combinations of solutions of the same equation are solutions. -/
theorem isSol_lin {q y y' w w' : ℝ → ℝ} (h1 : IsSol q y y') (h2 : IsSol q w w') (a b : ℝ) :
    IsSol q (fun x => a * y x + b * w x) (fun x => a * y' x + b * w' x) where
  hasDerivAt x := ((h1.hasDerivAt x).const_mul a).add ((h2.hasDerivAt x).const_mul b)
  hasDerivAt' x := (((h1.hasDerivAt' x).const_mul a).add ((h2.hasDerivAt' x).const_mul b)).congr_deriv
    (by ring)

theorem isSol_airyShiftC (X : ℝ) :
    IsSol (fun s => X + s) (airyShiftC X) (airyShiftCd X) := by
  have := isSol_lin (isSol_shift isAirySol_airyAi X) (isSol_shift isAirySol_airyBi_shift X)
    (Real.pi * airyBiDeriv X) (-(Real.pi * airyAi' X))
  convert this using 2 <;> (simp only [airyShiftC, airyShiftCd]; ring)

theorem isSol_airyShiftS (X : ℝ) :
    IsSol (fun s => X + s) (airyShiftS X) (airyShiftSd X) := by
  have := isSol_lin (isSol_shift isAirySol_airyAi X) (isSol_shift isAirySol_airyBi_shift X)
    (-(Real.pi * airyBi X)) (Real.pi * airyAi X)
  convert this using 2 <;> (simp only [airyShiftS, airyShiftSd]; ring)

theorem hasDerivAt_airyShiftC (X s : ℝ) : HasDerivAt (airyShiftC X) (airyShiftCd X s) s :=
  (isSol_airyShiftC X).hasDerivAt s

theorem hasDerivAt_airyShiftCd (X s : ℝ) :
    HasDerivAt (airyShiftCd X) ((X + s) * airyShiftC X s) s :=
  (isSol_airyShiftC X).hasDerivAt' s

theorem hasDerivAt_airyShiftS (X s : ℝ) : HasDerivAt (airyShiftS X) (airyShiftSd X s) s :=
  (isSol_airyShiftS X).hasDerivAt s

theorem hasDerivAt_airyShiftSd (X s : ℝ) :
    HasDerivAt (airyShiftSd X) ((X + s) * airyShiftS X s) s :=
  (isSol_airyShiftS X).hasDerivAt' s

/-- **The Airy shift identity.**  For every solution `(y, y')` of `y'' = x y` on `ℝ`,
`y(X+s) = y(X) C(X,s) + y'(X) S(X,s)` and `y'(X+s) = y(X) C_s(X,s) + y'(X) S_s(X,s)`
(P3 appendices `A:1068`, `lem:airy2-shift-parity` (i)). -/
theorem airy_shift {y y' : ℝ → ℝ} (hy : IsAirySol y y') (X s : ℝ) :
    y (X + s) = y X * airyShiftC X s + y' X * airyShiftS X s ∧
      y' (X + s) = y X * airyShiftCd X s + y' X * airyShiftSd X s := by
  obtain ⟨h1, h2, h3, h4⟩ := airyShift_initial X
  have hsol := (isSol_shift hy X).sub
    (isSol_lin (isSol_airyShiftC X) (isSol_airyShiftS X) (y X) (y' X))
  have hq : Continuous fun s : ℝ => X + s := continuous_const.add continuous_id
  have := hsol.eq_zero_of_zero_data hq (a := 0)
    (by simp [h1, h3]) (by simp [h2, h4]) s
  constructor <;> linarith [this.1, this.2]

/-- **`A:1121`**: `Ai(X+s) Bi(X) − Ai(X) Bi(X+s) = −S(X,s)/π`. -/
theorem airyShift_wronskian_shift (X s : ℝ) :
    airyAi (X + s) * airyBi X - airyAi X * airyBi (X + s) = -(airyShiftS X s / Real.pi) := by
  unfold airyShiftS
  field_simp [Real.pi_pos.ne']
  ring

/-- `Ai(X+s) = Ai(X) C(X,s) + Ai'(X) S(X,s)`. -/
theorem airyAi_shift (X s : ℝ) :
    airyAi (X + s) = airyAi X * airyShiftC X s + airyAi' X * airyShiftS X s :=
  (airy_shift isAirySol_airyAi X s).1

/-- `Ai'(X+s) = Ai(X) C_s(X,s) + Ai'(X) S_s(X,s)`. -/
theorem airyAi'_shift (X s : ℝ) :
    airyAi' (X + s) = airyAi X * airyShiftCd X s + airyAi' X * airyShiftSd X s :=
  (airy_shift isAirySol_airyAi X s).2

/-- `Bi(X+s) = Bi(X) C(X,s) + Bi'(X) S(X,s)`. -/
theorem airyBi_shift (X s : ℝ) :
    airyBi (X + s) = airyBi X * airyShiftC X s + airyBiDeriv X * airyShiftS X s :=
  (airy_shift isAirySol_airyBi_shift X s).1

/-- The shift matrix has determinant one: `C S_s − C_s S = 1` (Wronskian of `C`, `S`). -/
theorem airyShift_det (X s : ℝ) :
    airyShiftC X s * airyShiftSd X s - airyShiftCd X s * airyShiftS X s = 1 := by
  have h1 := pi_mul_w X
  have h2 := pi_mul_w (X + s)
  have : airyShiftC X s * airyShiftSd X s - airyShiftCd X s * airyShiftS X s =
      (Real.pi * (airyAi X * airyBiDeriv X - airyAi' X * airyBi X)) *
        (Real.pi * (airyAi (X + s) * airyBiDeriv (X + s) - airyAi' (X + s) * airyBi (X + s))) := by
    unfold airyShiftC airyShiftSd airyShiftCd airyShiftS
    ring
  rw [this, h1, h2, one_mul]

/-- info: 'FormalResearch.Special.airy_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_shift

/-- info: 'FormalResearch.Special.airyShift_wronskian_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyShift_wronskian_shift

/-- info: 'FormalResearch.Special.airyShift_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyShift_det

/-- info: 'FormalResearch.Special.airyShift_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyShift_initial

/-- info: 'FormalResearch.Special.airyAi_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_shift

/-- info: 'FormalResearch.Special.airyBi_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_shift

end FormalResearch.Special
