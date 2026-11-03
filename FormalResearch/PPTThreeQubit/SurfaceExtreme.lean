module

public import FormalResearch.PPTThreeQubit.Surface

/-!
# The explicit rational member `σ = N / 16323219`: GME

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/rank_five_surface.tex`,
`cor:ppt3-extreme5` (`eq:ppt3-sigma5`), GME part.

`σ = N / 16323219` with `N = 825000 ũũ† + 1440000 ww† + 2021184 vv† + 145200 (wv† + vw†)
+ 951720 ee† + 450625 oo†`, `ũ = 2|000⟩ - |011⟩ - |101⟩ - |110⟩ = 2 u_{1/2}`.  Covered:
* `sigma5_eq`: `σ = B_{1/2} X_σ B_{1/2}†` with the coefficient matrix `X_σ` of the paper;
* `sigma5_gme`: `tr(H_{1/2} X_σ) = -493577/32646438 < 0` and hence `σ` is GME, by the support
  criterion `trace_Hs_nonneg_of_biseparable` at `s = 1/2`
  (`H_{1/2} = diag(-3/2, 1, 11/4, -3, 7/2)`);
* `sigma5_eq_member`: `N = 30000 ρ(55, 48, 110)`, the member `(α, W, A) = (55, 48, 110)`
  of the surface (`τ = 48/55`, `s = 1/2`, `h = 73`).
Not covered: rank, cyclic/parity invariance, PPT of the three cuts, extremality (exact-rank
computation), the level-two witness and the white-noise threshold.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- `ũ = 2|000⟩ - |011⟩ - |101⟩ - |110⟩`. -/
def uTilde : Fin 8 → ℂ := ![2, 0, 0, -1, 0, -1, -1, 0]

/-- The unnormalised matrix `N` of `eq:ppt3-sigma5`. -/
def Nsigma : Matrix (Fin 8) (Fin 8) ℂ :=
  (825000 : ℂ) • vecMulVec uTilde (star uTilde) + (1440000 : ℂ) • vecMulVec wVec (star wVec) +
    (2021184 : ℂ) • vecMulVec vVec (star vVec) +
    (145200 : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) +
    (951720 : ℂ) • vecMulVec eVec (star eVec) + (450625 : ℂ) • vecMulVec oVec (star oVec)

/-- `σ = N / 16323219`. -/
def sigma5 : Matrix (Fin 8) (Fin 8) ℂ := (1 / 16323219 : ℂ) • Nsigma

/-- The coefficient matrix `X_σ` of `σ` in the basis `(u_{1/2}, v, w, e, o)`: `16323219 X_σ` has
diagonal `(4·825000, 2021184, 1440000, 951720, 450625)` and `vw` entry `145200`. -/
def Xsigma : Matrix (Fin 5) (Fin 5) ℂ :=
  surfXw (4 * 825000 / 16323219) (2021184 / 16323219) (145200 / 16323219) (1440000 / 16323219)
    (951720 / 16323219) (450625 / 16323219)

theorem sigma5_eq : sigma5 = Bs (1 / 2) * Xsigma * (Bs (1 / 2))ᴴ := by
  rw [Xsigma, Bs_surfXw_Bs]
  have hu : uTilde = (2 : ℂ) • uVec (1 / 2) := by
    ext i; fin_cases i <;> simp [uTilde, uVec]
  ext i j
  simp only [sigma5, Nsigma, hu, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', star_ofNat]
  push_cast
  ring

/-- `tr(H_{1/2} X_σ) = -493577/32646438`. -/
theorem trace_H_half_Xsigma : (Hs (1 / 2) * Xsigma).trace = ((-493577 / 32646438 : ℝ) : ℂ) := by
  rw [Xsigma, trace_Hs_surfXw]
  simp only [hDiag]
  norm_num

/-- **`cor:ppt3-extreme5`, GME part.**  `σ = N/16323219` is genuinely multipartite entangled:
`H_{1/2} = diag(-3/2, 1, 11/4, -3, 7/2)` is nonnegative on cut-product vectors of `R_{1/2}`
(`trace_Hs_nonneg_of_biseparable`) while `tr(H_{1/2} X_σ) = -493577/32646438 < 0`. -/
theorem sigma5_gme : IsGME sigma5 := by
  intro hb
  rw [sigma5_eq] at hb
  have h := trace_Hs_nonneg_of_biseparable (s := 1 / 2) (by norm_num) Xsigma hb
  rw [trace_H_half_Xsigma, Complex.ofReal_re] at h
  norm_num at h

/-- `N = 30000 ρ(55, 48, 110)`: `σ` is the member `(α, W, A) = (55, 48, 110)` of the surface
(`τ = 48/55`, in the window of `thm:ppt3-orbit`). -/
theorem sigma5_eq_member :
    sigma5 = ((30000 / 16323219 : ℝ) : ℂ) • rhoSurface 55 48 110 := by
  have h73 : surfH 55 48 = 73 := by
    unfold surfH
    rw [show (55 : ℝ) ^ 2 + 48 ^ 2 = 73 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hs : (55 : ℝ) / 110 = 1 / 2 := by norm_num
  have hE : wE 55 48 110 = 951720 / 30000 := by
    unfold wE; rw [h73]; norm_num
  have hG : wG 55 48 110 = 145200 / 30000 := by
    unfold wG; rw [hE, hs]; norm_num
  have hV : wV 55 48 110 = 2021184 / 30000 := by
    unfold wV; rw [hE, hs]; norm_num
  have hO : wO 55 48 = 450625 / 30000 := by
    unfold wO; norm_num
  have hX : Xsigma = ((30000 / 16323219 : ℝ) : ℂ) •
      surfXw 110 (2021184 / 30000) (145200 / 30000) 48 (951720 / 30000) (450625 / 30000) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xsigma, surfXw] <;> norm_num
  rw [sigma5_eq, hX, rhoSurface, hs, surfX, hE, hG, hV, hO]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end

/-- info: 'FormalResearch.PPTThreeQubit.sigma5_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma5_gme

/-- info: 'FormalResearch.PPTThreeQubit.sigma5_eq_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma5_eq_member

end FormalResearch.PPTThreeQubit
