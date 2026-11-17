module

public import Mathlib
public import FormalResearch.Special.HermiteBulkRot

/-!
# The Liouville–Green profile of the Weber equation

For `L > 0` write `w(x) = √(L - x²)`, `E = √w`.  A solution `f` of the Weber equation
`f'' = (x² - L) f` gives, on `x² < L`, the Liouville-Green variables
`U = E f`, `V = f'/E - x f / (2 E⁵)` with `U' = w V`, `V' = -w (1 + ψ) U`,
`ψ = (3x² + 2L) / (4 w⁶) ≥ 0`.  The primitive of `w` is
`S(x) = (x w + L arcsin(x/√L)) / 2`.  This is the first-order system needed by `hbk_rot`;
all statements are exact calculus identities (no asymptotics).
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- `w(x) = √(L - x²)`. -/
noncomputable def hbk_w (L x : ℝ) : ℝ := √(L - x ^ 2)
/-- `E(x) = √(w(x))`. -/
noncomputable def hbk_E (L x : ℝ) : ℝ := √(hbk_w L x)
/-- The perturbation `ψ = (3x² + 2L) / (4 w⁶)`. -/
noncomputable def hbk_psi (L x : ℝ) : ℝ := (3 * x ^ 2 + 2 * L) / (4 * hbk_w L x ^ 6)
/-- The primitive `S(x) = (x w + L arcsin(x/√L))/2` of `w`, `S 0 = 0`. -/
noncomputable def hbk_S (L x : ℝ) : ℝ := (x * hbk_w L x + L * Real.arcsin (x / √L)) / 2
/-- `U = E f`. -/
noncomputable def hbk_U (L : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := hbk_E L x * f x
/-- `V = f'/E - x f/(2 E⁵)`. -/
noncomputable def hbk_V (L : ℝ) (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f' x / hbk_E L x - x * f x / (2 * hbk_E L x ^ 5)

lemma hbk_w_pos {L x : ℝ} (hx : x ^ 2 < L) : 0 < hbk_w L x :=
  Real.sqrt_pos.2 (by linarith)

lemma hbk_E_pos {L x : ℝ} (hx : x ^ 2 < L) : 0 < hbk_E L x :=
  Real.sqrt_pos.2 (hbk_w_pos hx)

lemma hbk_E_sq {L x : ℝ} (hx : x ^ 2 < L) : hbk_E L x ^ 2 = hbk_w L x :=
  Real.sq_sqrt (hbk_w_pos hx).le

lemma hbk_E_four {L x : ℝ} (hx : x ^ 2 < L) : hbk_E L x ^ 4 = L - x ^ 2 := by
  have h1 := hbk_E_sq hx
  have h2 : hbk_w L x ^ 2 = L - x ^ 2 := Real.sq_sqrt (by linarith)
  calc hbk_E L x ^ 4 = (hbk_E L x ^ 2) ^ 2 := by ring
    _ = _ := by rw [h1, h2]

lemma hbk_hasDerivAt_E {L x : ℝ} (hx : x ^ 2 < L) :
    HasDerivAt (hbk_E L) (-x / (2 * hbk_E L x ^ 3)) x := by
  have hwp := hbk_w_pos hx
  have hEp := hbk_E_pos hx
  have h1 : HasDerivAt (fun y : ℝ => L - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub L
  have h2 := h1.sqrt (by linarith)
  have h3 := h2.sqrt hwp.ne'
  have e2 := hbk_E_sq hx
  refine (h3 : HasDerivAt (hbk_E L) _ x).congr_deriv ?_
  change -(2 * x) / (2 * hbk_w L x) / (2 * hbk_E L x) = _
  rw [← e2]
  field_simp

lemma hbk_hasDerivAt_w {L x : ℝ} (hx : x ^ 2 < L) :
    HasDerivAt (hbk_w L) (-x / hbk_w L x) x := by
  have h1 : HasDerivAt (fun y : ℝ => L - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub L
  refine ((h1.sqrt (by linarith)) : HasDerivAt (hbk_w L) _ x).congr_deriv ?_
  change -(2 * x) / (2 * hbk_w L x) = _
  field_simp

/-- `U' = w V`. -/
theorem hbk_hasDerivAt_U {L x : ℝ} (hx : x ^ 2 < L) (f f' : ℝ → ℝ)
    (hf : HasDerivAt f (f' x) x) :
    HasDerivAt (hbk_U L f) (hbk_w L x * hbk_V L f f' x) x := by
  have hEp := hbk_E_pos hx
  have e2 := hbk_E_sq hx
  refine ((hbk_hasDerivAt_E hx).mul hf).congr_deriv ?_
  unfold hbk_V
  rw [← e2]
  field_simp
  ring

/-- `V' = -w (1 + ψ) U` for solutions of the Weber equation. -/
theorem hbk_hasDerivAt_V {L x : ℝ} (hx : x ^ 2 < L) (f f' : ℝ → ℝ)
    (hf : HasDerivAt f (f' x) x) (hf' : HasDerivAt f' ((x ^ 2 - L) * f x) x) :
    HasDerivAt (hbk_V L f f') (-(hbk_w L x * (1 + hbk_psi L x)) * hbk_U L f x) x := by
  have hEp := hbk_E_pos hx
  have e2 := hbk_E_sq hx
  have e4 := hbk_E_four hx
  have hEd := hbk_hasDerivAt_E hx
  have hE5 : HasDerivAt (fun y => 2 * hbk_E L y ^ 5)
      (2 * (5 * hbk_E L x ^ 4 * (-x / (2 * hbk_E L x ^ 3)))) x := by
    simpa using (hEd.pow 5).const_mul 2
  have hA := hf'.div hEd hEp.ne'
  have hB : HasDerivAt (fun y => y * f y) (1 * f x + x * f' x) x :=
    (hasDerivAt_id x).mul hf
  have hC := hB.div hE5 (by positivity)
  refine (hA.sub hC).congr_deriv ?_
  have hL : L = hbk_E L x ^ 4 + x ^ 2 := by rw [e4]; ring
  unfold hbk_psi hbk_U
  rw [← e2]
  generalize hbk_E L x = e at *
  subst hL
  field_simp
  ring

/-- `S' = w`. -/
theorem hbk_hasDerivAt_S {L x : ℝ} (hx : x ^ 2 < L) :
    HasDerivAt (hbk_S L) (hbk_w L x) x := by
  have hL : 0 < L := lt_of_le_of_lt (sq_nonneg x) hx
  have hsL : 0 < √L := Real.sqrt_pos.2 hL
  have hsL2 : √L ^ 2 = L := Real.sq_sqrt hL.le
  have hwp := hbk_w_pos hx
  have hw2 : hbk_w L x ^ 2 = L - x ^ 2 := Real.sq_sqrt (by linarith)
  have hz : HasDerivAt (fun y : ℝ => y / √L) (1 / √L) x := by
    simpa using (hasDerivAt_id x).div_const (√L)
  have hlt : |x / √L| < 1 := by
    rw [abs_div, abs_of_pos hsL, div_lt_one hsL]
    exact abs_lt_of_sq_lt_sq (by rw [hsL2]; exact hx) hsL.le
  have hab := abs_lt.1 hlt
  have har := (Real.hasDerivAt_arcsin hab.1.ne' hab.2.ne).comp x hz
  have hxw := (hasDerivAt_id x).mul (hbk_hasDerivAt_w hx)
  have hm := (hxw.add (har.const_mul L)).div_const 2
  refine hm.congr_deriv ?_
  have h1 : 1 - (x / √L) ^ 2 = (hbk_w L x / √L) ^ 2 := by
    rw [div_pow, div_pow, hw2, hsL2]; field_simp
  rw [h1, Real.sqrt_sq (by positivity)]
  simp only [id]
  field_simp
  nlinarith [hw2]

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hbk_hasDerivAt_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hbk_hasDerivAt_V

/-- info: 'FormalResearch.Special.hbk_hasDerivAt_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hbk_hasDerivAt_S
