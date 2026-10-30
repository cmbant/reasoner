import FormalResearch.FourQubitEntropy.AH6Sound
import FormalResearch.FourQubitEntropy.AH6Kmin
import FormalResearch.FourQubitEntropy.AH6Flat
import FormalResearch.FourQubitEntropy.AH6Contact

/-!
# The joint scalar majorant `lem:seven-joint-scalar-majorant` (AH-6), for the explicit polynomial `H`

Connects the real computation `stageA .. stageD3` (`AH6Model`) to the analytic ingredients: the kernel minorant
(`AH6Kmin`), the binary minorant (`AH6Binary`), the double factor (`AH6Flat`, `AH6Contact`), the assembly
(`AH6Assembly`) and the kernel certificate (`AH6Sound`).
-/

namespace FormalResearch.FourQubitEntropy.AH6

/-! ### Evaluation of the model lists -/

theorem evalL_stageB_P (s : StA ℝ) (e : ℝ) :
    evalL (stageB s).P e = newtonP s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 s.G1 s.W1 s.G2 s.W2 s.G3 s.W3 e := by
  simp only [stageB, evalL_addL, evalL_scaleL, evalL_mulL, evalL, ic_real, newtonP, tab, step]
  push_cast
  ring

theorem evalL_stageB_q (s : StA ℝ) (e : ℝ) :
    evalL (stageB s).q e = (e - s.n1) * (e - s.n2) * (e - s.n3) := by
  simp only [stageB, evalL_mulL, evalL, ic_real]
  push_cast
  ring


/-! ### The majorant data of the real computation -/

noncomputable section

/-- The data of `MajData` extracted from the real computation. -/
def majD (p : Par ℝ) : MajData where
  P := fun e => evalL (rB p).P e
  q := fun e => evalL (rB p).q e
  k0 := (rC2 p).k0
  gam := (rC2 p).gam
  e0 := (rC1 p).e0
  A := fun e => evalL [(rC2 p).a0, (rC2 p).a1, (rC1 p).a2, (rC1 p).a3] e
  B := fun e => evalL [(rC2 p).b0, (rC1 p).b1] e
  Pi := fun e => evalL (rD3 p).Pi e

end

section Eval

variable (p : Par ℝ)

theorem eval_L (e : ℝ) : evalL (rD1 p).L e = (majD p).L e := by
  simp only [rD1, stageD1, evalL, ic_real, majD, MajData.L]
  ring

theorem eval_AA (e : ℝ) : evalL (rD1 p).AA e = (majD p).U e := by
  simp only [rD1, stageD1, evalL_scaleL, evalL_powL, majD, MajData.U, ic_real]
  push_cast; ring

theorem eval_BB (e : ℝ) : evalL (rD1 p).BB e = (majD p).V e := by
  simp only [rD1, stageD1, evalL_addL, evalL_scaleL, evalL, rat_real, ic_real, majD, MajData.V]
  push_cast; ring

theorem eval_CC (hη2 : (rC1 p).eta2 = eta2R) (e : ℝ) : evalL (rD1 p).CC e = (majD p).W e := by
  simp only [rD1, stageD1, evalL_addL, evalL_scaleL, evalL, ic_real, majD, MajData.W]
  rw [hη2]; push_cast; ring

theorem eval_EL (e : ℝ) : evalL (rD1 p).EL e = e * (majD p).L e := by
  simp only [rD1, stageD1, evalL_mulL, evalL, ic_real, majD, MajData.L]
  push_cast; ring

theorem eval_R (hη2 : (rC1 p).eta2 = eta2R) (hη3 : (rC1 p).eta3 = eta3R) (e : ℝ) :
    evalL (rR p) e = (majD p).R e := by
  simp only [rR, stageD2, evalL_addL, evalL_scaleL, evalL_mulL, evalL_powL, eval_AA, eval_BB,
    eval_CC p hη2, eval_EL, ic_real, hη3, MajData.R]
  push_cast; ring

end Eval


/-! ### The concrete parameters -/

section Concrete

variable {x : ℝ}

theorem eta2_eq (x : ℝ) : (rC1 (parR x)).eta2 = eta2R := by
  simp only [rC1, stageC1, parR, eta2R, rat_real, ic_real]
  push_cast; ring

theorem eta3_eq (x : ℝ) : (rC1 (parR x)).eta3 = eta3R := by
  simp only [rC1, stageC1, parR, eta3R, rat_real, ic_real]
  push_cast; ring


/-- `ln c + ln 3 - ln 2 = ln (e₀/8)` for the concrete parameters. -/
theorem ln6_eq (hb : InBracket x) :
    (parR x).lc + (parR x).l3 + -(parR x).l2 = Real.log ((rC1 (parR x)).e0 / 8) := by
  have hu := uOf_pos hb
  have hc : 0 < ic 4 * uOf x := by simp only [ic_real]; positivity
  have h1 : (rC1 (parR x)).e0 / 8 = (ic 4 * uOf x) * 3 / 2 := by
    simp only [rC1, stageC1, rA, stageA, parR, uOf, ic_real]; push_cast; ring
  rw [h1, Real.log_div (by positivity) (by norm_num), Real.log_mul hc.ne' (by norm_num)]
  simp only [parR]; ring

theorem G_eq (hb : InBracket x) :
    (rA (parR x)).G1 = Real.negMulLog ((rA (parR x)).n1 / 8) ∧
    (rA (parR x)).G2 = Real.negMulLog ((rA (parR x)).n2 / 8) ∧
    (rA (parR x)).G3 = Real.negMulLog ((rA (parR x)).n3 / 8) ∧
    (rA (parR x)).W1 = -(Real.log ((rA (parR x)).n1 / 8) + 1) / 8 ∧
    (rA (parR x)).W2 = -(Real.log ((rA (parR x)).n2 / 8) + 1) / 8 ∧
    (rA (parR x)).W3 = -(Real.log ((rA (parR x)).n3 / 8) + 1) / 8 := by
  have h1 : (rA (parR x)).n1 / 8 = ic 4 * uOf x := by
    simp only [rA, stageA, parR, uOf, ic_real]; push_cast; ring
  have h2 : (rA (parR x)).n2 / 8 = ic 3 * uOf x + x := by
    simp only [rA, stageA, parR, uOf, ic_real]; push_cast; ring
  have h3 : (rA (parR x)).n3 / 8 = uOf x + x := by
    simp only [rA, stageA, parR, uOf, ic_real]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; simp only [rA, stageA, parR, uOf, ic_real, Real.negMulLog]; ring
  · rw [h2]; simp only [rA, stageA, parR, uOf, ic_real, Real.negMulLog]; ring
  · rw [h3]; simp only [rA, stageA, parR, uOf, ic_real, Real.negMulLog]; ring
  · rw [h1]; simp only [rA, stageA, parR, uOf, rat_real, ic_real]; push_cast; ring
  · rw [h2]; simp only [rA, stageA, parR, uOf, rat_real, ic_real]; push_cast; ring
  · rw [h3]; simp only [rA, stageA, parR, uOf, rat_real, ic_real]; push_cast; ring


theorem kmin_model (hb : InBracket x) :
    ∀ e : ℝ, 0 < e → (rC2 (parR x)).k0 * ((majD (parR x)).q e) ^ 2 ≤
      ((majD (parR x)).P e - Real.negMulLog (e / 8)) * (majD (parR x)).L e := by
  have F := cert_sound (parR x) (parR_enc hb)
  obtain ⟨hG1, hG2, hG3, hW1, hW2, hW3⟩ := G_eq hb
  set p := parR x with hp
  set s := rA p with hs
  set c1 := rC1 p with hc1
  set c2 := rC2 p with hc2
  have hn1 : 0 < s.n1 := mul_pos (by simp only [ic_real]; norm_num) F.c_pos
  have hn2 : 0 < s.n2 := mul_pos (by simp only [ic_real]; norm_num) F.a_pos
  have hn3 : 0 < s.n3 := mul_pos (by simp only [ic_real]; norm_num) F.d_pos
  have hi21 : s.i21 = (s.n2 + -s.n1)⁻¹ := rfl
  have hi31 : s.i31 = (s.n3 + -s.n1)⁻¹ := rfl
  have hi32 : s.i32 = (s.n3 + -s.n2)⁻¹ := rfl
  have h21 : (s.n2 - s.n1) * s.i21 = 1 := by
    rw [hi21, ← sub_eq_add_neg]; exact mul_inv_cancel₀ (by rw [sub_eq_add_neg]; exact F.n21)
  have h31 : (s.n3 - s.n1) * s.i31 = 1 := by
    rw [hi31, ← sub_eq_add_neg]; exact mul_inv_cancel₀ (by rw [sub_eq_add_neg]; exact F.n31)
  have h32 : (s.n3 - s.n2) * s.i32 = 1 := by
    rw [hi32, ← sub_eq_add_neg]; exact mul_inv_cancel₀ (by rw [sub_eq_add_neg]; exact F.n32)
  have hPfun : ∀ e, evalL (rB p).P e = Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 e := by
    intro e
    rw [rB, evalL_stageB_P, Pfun, hG1, hG2, hG3, hW1, hW2, hW3]
  have hqfun : ∀ e, evalL (rB p).q e = (e - s.n1) * (e - s.n2) * (e - s.n3) := fun e => by
    rw [rB, evalL_stageB_q]
  have he0pos : 0 < c1.e0 := by
    have : c1.e0 = ic 48 * s.u := rfl
    rw [this]; exact mul_pos (by simp only [ic_real]; norm_num) F.u_pos
  have hq0 : (c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3) ≠ 0 := by
    have := F.q0_ne
    have e : c1.q0 = (c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3) := by
      show evalL (rB p).q c1.e0 = _
      rw [hqfun]
    rwa [e] at this
  have hP' : HasDerivAt (Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32) c1.Pd0 c1.e0 := by
    have h := hasDerivAt_evalL (rB p).P c1.e0
    have e : evalL (rB p).P = Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 := funext hPfun
    rw [e] at h
    exact h
  have hq1 : HasDerivAt (fun e => (e - s.n1) * (e - s.n2) * (e - s.n3)) c1.q1 c1.e0 := by
    have h := hasDerivAt_evalL (rB p).q c1.e0
    have e : evalL (rB p).q = fun e => (e - s.n1) * (e - s.n2) * (e - s.n3) := funext hqfun
    rw [e] at h
    exact h
  have key := kmin hn1 hn2 hn3 h21 h31 h32 he0pos hq0 hP' hq1
  simp only at key
  obtain ⟨-, -, -, hK⟩ := key
  -- identification of `k₀` and `γ`
  have hln6 := ln6_eq hb
  have hg0 : c1.g0 = Real.negMulLog (c1.e0 / 8) := by
    have h1 : c1.g0 = -(ic 6 * (s.u * (p.lc + p.l3 + -p.l2))) := rfl
    rw [h1, hln6]
    have : c1.e0 / 8 = ic 6 * s.u := by
      show (ic 48 * s.u) / 8 = _
      simp only [ic_real]; push_cast; ring
    rw [this]; unfold Real.negMulLog; simp only [ic_real]; ring
  have hg1 : c1.g1 = -(Real.log (c1.e0 / 8) + 1) / 8 := by
    have h1 : c1.g1 = -((p.lc + p.l3 + -p.l2) + ic 1) * rat 1 8 := rfl
    rw [h1, hln6]; simp only [ic_real, rat_real]; push_cast; ring
  have hPe0 : c1.Pe0 = Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 c1.e0 := hPfun c1.e0
  have hq0e : c1.q0 = (c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3) := by
    show evalL (rB p).q c1.e0 = _
    rw [hqfun]
  have hk0 : c2.k0 = (Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 c1.e0 - Real.negMulLog (c1.e0 / 8)) /
      ((c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3)) ^ 2 := by
    have h1 : c2.k0 = (c1.Pe0 + -c1.g0) * (c1.q0 * c1.q0)⁻¹ := rfl
    rw [h1, hPe0, hg0, hq0e]
    field_simp
    ring
  have hgam : c2.gam = -(((c1.Pd0 - (-(Real.log (c1.e0 / 8) + 1) / 8)) /
        ((c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3)) ^ 2 -
      2 * (((Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 c1.e0 - Real.negMulLog (c1.e0 / 8)) /
          ((c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3)) ^ 2) *
        (c1.q1 / ((c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3))))) /
      ((Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 c1.e0 - Real.negMulLog (c1.e0 / 8)) /
        ((c1.e0 - s.n1) * (c1.e0 - s.n2) * (c1.e0 - s.n3)) ^ 2)) := by
    have h1 : c2.gam = -(c2.k1 * c2.k0⁻¹) := rfl
    have h2 : c2.k1 = (c1.Pd0 + -c1.g1) * (c1.q0 * c1.q0)⁻¹ + -(2 * (c2.k0 * (c1.q1 * c1.q0⁻¹))) := rfl
    rw [h1, h2, hk0, hg1, hq0e, div_eq_mul_inv]
    simp only [sub_eq_add_neg, div_eq_mul_inv]
    ring_nf
  intro e he
  have hfin := hK e he
  show c2.k0 * (evalL (rB p).q e) ^ 2 ≤
    (evalL (rB p).P e - Real.negMulLog (e / 8)) * (1 + c2.gam * (e - c1.e0))
  rw [hqfun, hPfun]
  rw [hgam, hk0]
  exact hfin


theorem dl2_spec (R : List ℝ) (e0 e : ℝ) :
    evalL R e = (e - e0) ^ 2 * evalL (dl (dl R e0).1 e0).1 e + (dl (dl R e0).1 e0).2 * (e - e0) +
      (dl R e0).2 := by
  rw [dl_spec R e0 e, dl_spec (dl R e0).1 e0 e]; ring

/-- A function that equals `evalL R`, vanishes to second order at `e₀`, is `(e - e₀)²` times the double quotient. -/
theorem factor_of_flat (R : List ℝ) (e0 : ℝ) (f : ℝ → ℝ) (hf : ∀ e, f e = evalL R e)
    (h0 : f e0 = 0) (hd : HasDerivAt f 0 e0) :
    ∀ e, f e = (e - e0) ^ 2 * evalL (dl (dl R e0).1 e0).1 e := by
  obtain ⟨r0, hr0⟩ : ∃ r0, r0 = (dl R e0).2 := ⟨_, rfl⟩
  obtain ⟨r1, hr1⟩ : ∃ r1, r1 = (dl (dl R e0).1 e0).2 := ⟨_, rfl⟩
  have hd2 : ∀ e, evalL R e = (e - e0) ^ 2 * evalL (dl (dl R e0).1 e0).1 e + r1 * (e - e0) + r0 := by
    intro e; rw [hr0, hr1]; exact dl2_spec R e0 e
  have hr0z : r0 = 0 := by
    have := hd2 e0
    rw [← hf] at this
    simp at this
    linarith
  have hfun : f = fun e => (e - e0) ^ 2 * evalL (dl (dl R e0).1 e0).1 e + r1 * (e - e0) + r0 := by
    funext e; rw [hf, hd2]
  have hderiv : HasDerivAt (fun e => (e - e0) ^ 2 * evalL (dl (dl R e0).1 e0).1 e + r1 * (e - e0) + r0)
      r1 e0 := by
    have h1 := (((hasDerivAt_id e0).sub_const e0).pow 2).mul (hasDerivAt_evalL (dl (dl R e0).1 e0).1 e0)
    have h2 := (((hasDerivAt_id e0).sub_const e0).const_mul r1)
    have h3 := (h1.add h2).add_const r0
    refine HasDerivAt.congr_deriv h3 ?_
    simp
  rw [hfun] at hd
  have hr1z : r1 = 0 := hderiv.unique hd
  intro e
  rw [hfun, hr0z, hr1z]
  ring

/-- The factorisation `R(e) = (e - e₀)² Π(e)` of the degree-twenty polynomial. -/
theorem R_factor (hb : InBracket x) :
    ∀ e : ℝ, (majD (parR x)).R e = (e - (majD (parR x)).e0) ^ 2 * (majD (parR x)).Pi e := by
  have F := cert_sound (parR x) (parR_enc hb)
  have hη2 := eta2_eq x
  have hη3 := eta3_eq x
  set p := parR x with hp
  set s := rA p with hs
  set c1 := rC1 p with hc1
  set c2 := rC2 p with hc2
  have hqfun : ∀ e, evalL (rB p).q e = (e - s.n1) * (e - s.n2) * (e - s.n3) := fun e => by
    rw [rB, evalL_stageB_q]
  have he0pos : 0 < c1.e0 := by
    have : c1.e0 = ic 48 * s.u := rfl
    rw [this]; exact mul_pos (by simp only [ic_real]; norm_num) F.u_pos
  have hk0ne : c2.k0 ≠ 0 := F.k0_pos.ne'
  -- the model equations
  have he0 : c1.e0 = 48 * s.u := by
    show ic 48 * s.u = _
    simp only [ic_real]; push_cast; ring
  have hv0 : c1.v0 = c1.e0 * c1.e0 / 9 := by
    show (c1.e0 * c1.e0) * rat 1 9 = _
    simp only [rat_real]; push_cast; ring
  have hhh : c1.hh = (-(8 * s.u * (p.lc + p.l2)) + -(4 * s.u * p.lc)) / 2 := by
    show (-(ic 8 * s.u * (p.lc + p.l2)) + -(s.c * p.lc)) * rat 1 2 = _
    have : s.c = ic 4 * s.u := rfl
    rw [this]; simp only [ic_real, rat_real]; push_cast; ring
  have hhe : c1.he = (-((p.lc + p.l2) + 1) + -(p.lc + 1)) / 16 := by
    show (-((p.lc + p.l2) + ic 1) + -(p.lc + ic 1)) * rat 1 16 = _
    simp only [ic_real, rat_real]; push_cast; ring
  have hhv : c1.hv = (-((p.lc + p.l2) + 1) + (p.lc + 1)) / (512 * s.u) := by
    show (-((p.lc + p.l2) + ic 1) + (p.lc + ic 1)) * (ic 512 * s.u)⁻¹ = _
    simp only [ic_real]; push_cast; ring
  have ha2 : c1.a2 = p.l2 * (-115001089107 / 1000000000000) := by
    show p.l2 * rat (-115001089107) 1000000000000 = _
    simp only [rat_real]; push_cast; ring
  have ha3 : c1.a3 = p.l2 * (18166193766 / 1000000000000) := by
    show p.l2 * rat 18166193766 1000000000000 = _
    simp only [rat_real]; push_cast; ring
  have hb1 : c1.b1 = p.l2 * (14438812336 / 1000000000000) := by
    show p.l2 * rat 14438812336 1000000000000 = _
    simp only [rat_real]; push_cast; ring
  have hg0 : c1.g0 = -(6 * (s.u * (p.lc + p.l3 - p.l2))) := by
    show -(ic 6 * (s.u * (p.lc + p.l3 + -p.l2))) = _
    simp only [ic_real]; push_cast; ring
  have hg1 : c1.g1 = -((p.lc + p.l3 - p.l2) + 1) / 8 := by
    show -((p.lc + p.l3 + -p.l2) + ic 1) * rat 1 8 = _
    simp only [ic_real, rat_real]; push_cast; ring
  have hq0e : c1.q0 = evalL (rB p).q c1.e0 := rfl
  have hq0ne : c1.q0 ≠ 0 := F.q0_ne
  have hk0def : c2.k0 = (c1.Pe0 + -c1.g0) * (c1.q0 * c1.q0)⁻¹ := rfl
  have hPe0 : c1.Pe0 = c1.g0 + c2.k0 * c1.q0 ^ 2 := by
    rw [hk0def]; field_simp; ring
  have hPd0 : c1.Pd0 = c1.g1 - c1.q0 ^ 2 * c2.gam * c2.k0 + 2 * c2.k0 * c1.q0 * c1.q1 := by
    have h1 : c2.gam = -(c2.k1 * c2.k0⁻¹) := rfl
    have h2 : c2.k1 = (c1.Pd0 + -c1.g1) * (c1.q0 * c1.q0)⁻¹ + -(2 * (c2.k0 * (c1.q1 * c1.q0⁻¹))) := rfl
    have h3 : c2.gam * c2.k0 = -c2.k1 := by rw [h1]; field_simp
    rw [h2] at h3
    field_simp at h3
    nlinarith [h3]
  have hb0 : c2.b0 = (c1.v0 * c1.hv + -c1.hh + c1.Pe0) / (c1.v0 * c1.v0) + -(c1.b1 * c1.e0) := by
    show (c1.v0 * c1.hv + -c1.hh + c1.Pe0) * (c1.v0 * c1.v0)⁻¹ + -(c1.b1 * c1.e0) = _
    rw [div_eq_mul_inv]
  have ha1 : c2.a1 = (c1.he + -c1.Pd0 + -(c1.v0 * (c1.v0 * c1.b1))) / c1.v0 +
      -(2 * (c1.a2 * c1.e0)) + -(3 * (c1.a3 * (c1.e0 * c1.e0))) := by
    show (c1.he + -c1.Pd0 + -(c1.v0 * (c1.v0 * c1.b1))) * c1.v0⁻¹ + -(ic 2 * (c1.a2 * c1.e0))
      + -(ic 3 * (c1.a3 * (c1.e0 * c1.e0))) = _
    simp only [ic_real, div_eq_mul_inv]; push_cast; ring
  have ha0 : c2.a0 = c1.hv + -(2 * (c1.v0 * (c2.b0 + c1.b1 * c1.e0))) + -(c2.a1 * c1.e0) +
      -(c1.a2 * (c1.e0 * c1.e0)) + -(c1.a3 * (c1.e0 * (c1.e0 * c1.e0))) := by
    show c1.hv + -(ic 2 * (c1.v0 * (c2.b0 + c1.b1 * c1.e0))) + -(c2.a1 * c1.e0) +
      -(c1.a2 * (c1.e0 * c1.e0)) + -(c1.a3 * (c1.e0 * (c1.e0 * c1.e0))) = _
    simp only [ic_real]; push_cast; ring
  have heta2 : c1.eta2 = 1593 / 4 * p.l2 + -(243 * p.l3) + -9 := by
    show rat 1593 4 * p.l2 + -(ic 243 * p.l3) + ic (-9) = _
    simp only [ic_real, rat_real]; push_cast; ring
  have heta3 : c1.eta3 = 81 / 2 + -(9477 / 4 * p.l2) + 1458 * p.l3 := by
    show rat 81 2 + -(rat 9477 4 * p.l2) + ic 1458 * p.l3 = _
    simp only [ic_real, rat_real]; push_cast; ring
  have hcon := contact_algebra (u := s.u) (lc := p.lc) (l2 := p.l2) (l3 := p.l3) (k0 := c2.k0)
    (gam := c2.gam) (q0 := c1.q0) (q1 := c1.q1) (Pe0 := c1.Pe0) (Pd0 := c1.Pd0) (e0 := c1.e0)
    (v0 := c1.v0) (hh := c1.hh) (he := c1.he) (hv := c1.hv) (a2 := c1.a2) (a3 := c1.a3)
    (b1 := c1.b1) (g0 := c1.g0) (g1 := c1.g1) (b0 := c2.b0) (a1 := c2.a1) (a0 := c2.a0)
    (eta2 := c1.eta2) (eta3 := c1.eta3) F.u_pos.ne' hq0ne he0 hv0 hhh hhe hhv ha2 ha3 hb1 hg0 hg1
    hPe0 hPd0 hb0 ha1 ha0 heta2 heta3
  simp only at hcon
  obtain ⟨C0, Cv, Ce⟩ := hcon
  -- derivatives of the polynomial pieces
  have hAd : HasDerivAt (majD p).A (evalL (derL [c2.a0, c2.a1, c1.a2, c1.a3]) c1.e0) c1.e0 :=
    hasDerivAt_evalL _ _
  have hBd : HasDerivAt (majD p).B (evalL (derL [c2.b0, c1.b1]) c1.e0) c1.e0 :=
    hasDerivAt_evalL _ _
  have hqd : HasDerivAt (majD p).q c1.q1 c1.e0 := hasDerivAt_evalL _ _
  have hA1 : evalL (derL [c2.a0, c2.a1, c1.a2, c1.a3]) c1.e0 =
      c2.a1 + 2 * c1.a2 * c1.e0 + 3 * c1.a3 * c1.e0 ^ 2 := by
    simp only [derL, evalL, addL, ic_real]; push_cast; ring
  have hB1 : evalL (derL [c2.b0, c1.b1]) c1.e0 = c1.b1 := by
    simp only [derL, evalL, addL, ic_real]; push_cast; ring
  rw [hA1] at hAd
  rw [hB1] at hBd
  have hq0e' : evalL (rB p).q c1.e0 = c1.q0 := rfl
  have hDq : (majD p).q c1.e0 = c1.q0 := rfl
  have hDe0 : (majD p).e0 = c1.e0 := rfl
  have hDk : (majD p).k0 = c2.k0 := rfl
  have hDg : (majD p).gam = c2.gam := rfl
  have hDA : (majD p).A c1.e0 = c2.a0 + c2.a1 * c1.e0 + c1.a2 * c1.e0 ^ 2 + c1.a3 * c1.e0 ^ 3 := by
    simp only [majD, evalL, ic_real]; push_cast; ring
  have hDB : (majD p).B c1.e0 = c2.b0 + c1.b1 * c1.e0 := by
    simp only [majD, evalL, ic_real]; push_cast; ring
  have hDL : (majD p).L c1.e0 = 1 := by simp only [MajData.L, hDe0]; ring
  have hDU : (majD p).U c1.e0 = 8 * c2.k0 * c1.q0 ^ 2 := by
    unfold MajData.U; rw [hDq]; rfl
  have hDV : (majD p).V c1.e0 = 1 / 2 + 8 * c1.e0 * (c2.a0 + c2.a1 * c1.e0 + c1.a2 * c1.e0 ^ 2 + c1.a3 * c1.e0 ^ 3) := by
    unfold MajData.V; rw [hDA]
  have hDW : (majD p).W c1.e0 = c1.eta2 + 8 * c1.e0 ^ 3 * (c2.b0 + c1.b1 * c1.e0) := by
    unfold MajData.W; rw [hDB, hη2]
  have hC0 : (majD p).F (majD p).e0 c1.v0 = 0 := by
    rw [hDe0]; unfold MajData.F
    rw [hDU, hDV, hDW, hDL, ← hη3]
    linear_combination C0
  have hCv : (majD p).e0 ^ 4 * (majD p).V (majD p).e0 + 2 * (majD p).e0 ^ 2 * (majD p).W (majD p).e0 * c1.v0 +
      3 * eta3R * c1.v0 ^ 2 = 0 := by
    rw [hDe0, hDV, hDW, ← hη3]
    linear_combination Cv
  have hCe : 5 * (majD p).e0 ^ 4 * (majD p).U (majD p).e0 +
      (majD p).e0 ^ 5 * (8 * (majD p).k0 * (2 * (majD p).q (majD p).e0 * c1.q1)) +
      (4 * (majD p).e0 ^ 3 * (majD p).V (majD p).e0 + (majD p).gam * (majD p).e0 ^ 4 * (majD p).V (majD p).e0 +
        (majD p).e0 ^ 4 * (8 * ((majD p).A (majD p).e0 + (majD p).e0 * (c2.a1 + 2 * c1.a2 * c1.e0 + 3 * c1.a3 * c1.e0 ^ 2)))) *
        c1.v0 +
      (2 * (majD p).e0 * (majD p).W (majD p).e0 + (majD p).gam * (majD p).e0 ^ 2 * (majD p).W (majD p).e0 +
        (majD p).e0 ^ 2 * (8 * (3 * (majD p).e0 ^ 2 * (majD p).B (majD p).e0 + (majD p).e0 ^ 3 * c1.b1))) * c1.v0 ^ 2 +
      eta3R * (majD p).gam * c1.v0 ^ 3 = 0 := by
    rw [hDe0, hDU, hDV, hDW, hDA, hDB, hDq, hDk, hDg, ← hη3]
    linear_combination Ce
  have hflat := R_flat (majD p) (A1 := c2.a1 + 2 * c1.a2 * c1.e0 + 3 * c1.a3 * c1.e0 ^ 2)
    (B1 := c1.b1) (q1 := c1.q1) (v0 := c1.v0) (by rw [hDe0]; exact he0pos) hAd hBd hqd hC0 hCv hCe
  obtain ⟨hR0, hRd⟩ := hflat
  have hRe : ∀ e, (majD p).R e = evalL (rR p) e := fun e => (eval_R p hη2 hη3 e).symm
  have hR0' : (majD p).R c1.e0 = 0 := by rw [← hDe0]; exact hR0
  have hRd' : HasDerivAt (majD p).R 0 c1.e0 := by rw [← hDe0]; exact hRd
  have hfac := factor_of_flat (rR p) c1.e0 (majD p).R hRe hR0' hRd'
  intro e
  have hPi : (majD p).Pi e = evalL (dl (dl (rR p) c1.e0).1 c1.e0).1 e := by
    exact congrArg (fun l => evalL l e) (stageD3_Pi (rC1 p) (rR p))
  rw [hPi, hDe0]
  exact hfac e

end Concrete

end FormalResearch.FourQubitEntropy.AH6
