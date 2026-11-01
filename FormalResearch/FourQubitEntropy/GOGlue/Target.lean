import FormalResearch.FourQubitEntropy.PaperEGoSlice
import FormalResearch.FourQubitEntropy.GOProbe.Remainders
import FormalResearch.FourQubitEntropy.GOGlue.PQ

/-!
# GO glue: the slice target as a sparse polynomial

`pTarget : PQ 6` is `sliceTarget` (`PaperEGoSlice.lean`) transcribed to the computable `PQ` calculus
(matrices of rational polynomials, `PQ.lean`), and `pRem : PQ 6` is `R_sq + R_ax` of
`GOProbe/Remainders.lean`.  `pTarget_val`, `pRem_val` prove that their values at a point `x : ℕ → ℝ`
are `sliceTarget (restr x)` and `Rsq x + Rax x`.  The comparison of these polynomials with the generated
`lit` is the decidable check of `GOGlue/DataCheck.lean`.  Claim class: proved.
-/

open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.GO
open GOProbe GOProbe.PQ

noncomputable section

/-- The slice point of the first 19 coordinates of `x`. -/
def restr (x : ℕ → ℝ) : SV := fun i => x i.1

@[simp] theorem restr_apply (x : ℕ → ℝ) (i : Fin 19) : restr x i = x i.1 := rfl

end

/-- The coordinate `i` as a polynomial. -/
def pv (i : Fin 19) : PQ 1 := PQ.var i.1 i.2

def pX : PM 1 4 4 :=
  !![pv 0, pv 13, pv 14, pv 15;
     smul (1 / 3) (pv 16), pv 1, add (pv 7) (pv 10), add (pv 8) (pv 11);
     smul (1 / 3) (pv 17), sub (pv 7) (pv 10), pv 2, add (pv 9) (pv 12);
     smul (1 / 3) (pv 18), sub (pv 8) (pv 11), sub (pv 9) (pv 12), pv 3]

def pY : PM 1 4 4 :=
  !![add (add (pv 1) (pv 2)) (pv 3), pv 16, pv 17, pv 18;
     smul 3 (pv 13), add (pv 0) (pv 4), smul (-1 / 2) (pv 7), smul (-1 / 2) (pv 8);
     smul 3 (pv 14), smul (-1 / 2) (pv 7), add (pv 0) (pv 5), smul (-1 / 2) (pv 9);
     smul 3 (pv 15), smul (-1 / 2) (pv 8), smul (-1 / 2) (pv 9), add (pv 0) (pv 6)]

def pH0 : PQ 1 := add (add (add (smul 6 (pv 0)) (pv 4)) (pv 5)) (pv 6)

/-- `n = 3‖X‖² + ‖Y‖²`. -/
def pN : PQ 2 := add (smul 3 (pfn pX)) (pfn pY)

/-- `e = n - h₀²/6`. -/
def pE : PQ 2 := sub pN (smul (1 / 6) (mul pH0 pH0))

def pA : PM 2 4 4 := tab (padd (psmul 3 (pmul pX (ptrans pX))) (pmul pY (ptrans pY)))
def pB : PM 2 4 4 := tab (psub (pmul pY (ptrans pX)) (pmul pX (ptrans pY)))
def pC : PM 2 4 4 := tab (psub (psmul 3 (pmul (ptrans pX) pX)) (pmul (ptrans pY) pY))
def pD : PM 2 4 4 := tab (padd (pmul (ptrans pX) pY) (pmul (ptrans pY) pX))
def pR : PQ 2 := ptr pC
def pI : PQ 2 := smul 2 (sumF fun i => sumF fun j => mul (pX i j) (pY i j))

def pNr : PM 3 4 4 := tab (padd (psub (pmul pX pC) (pmul pY pD))
  (padd (psmul (-1 / 2) (pscal pR pX)) (psmul (1 / 2) (pscal pI pY))))

def pNi : PM 3 4 4 := tab (psub (padd (psmul 3 (pmul pX pD)) (pmul pY pC))
  (padd (psmul (1 / 2) (pscal pR pY)) (psmul (3 / 2) (pscal pI pX))))

def pQ : PQ 6 :=
  sub (sub (smul 27 (mul pN (sub (ptr (pmul pA pA)) (smul 3 (ptr (pmul pB pB))))))
        (smul 18 (sub (ptr (pmul (pmul pA pA) pA)) (smul 9 (ptr (pmul (pmul pA pB) pB))))))
    (add (smul 54 (pfn pNr)) (add (smul 18 (pfn pNi)) (smul 4 (mul pN (mul pN pN)))))

def pTarget : PQ 6 := smul (1 / 36) (sub pQ (mul (mul pN pN) pE))

/-! ### Soundness -/

section Sound
variable (x : ℕ → ℝ)

theorem pv_val (i : Fin 19) : (pv i).val x = restr x i := by
  simp [pv, val_var]

theorem rel_pX : Rel x pX (sX (restr x)) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pX, sX, pv_val, val_smul, val_add, val_sub] <;> ring

theorem rel_pY : Rel x pY (sY (restr x)) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pY, sY, pv_val, val_smul, val_add] <;> ring

theorem pH0_val : pH0.val x = sH0 (restr x) := by
  simp [pH0, sH0, pv_val, val_smul, val_add]

theorem pN_val : pN.val x = sN (restr x) := by
  rw [pN, val_add, val_smul, val_pfn (rel_pX x) (by norm_num), val_pfn (rel_pY x) (by norm_num)]
  simp [sN, fn4]

theorem pE_val : pE.val x = sE (restr x) := by
  rw [pE, val_sub, val_smul, val_mul, pN_val, pH0_val]
  simp [sE]; ring

theorem rel_pA : Rel x pA (sA (restr x)) := by
  have hX := rel_pX x
  have hY := rel_pY x
  exact ((((hX.mul hX.trans).smul 3).add (hY.mul hY.trans))).tab

theorem rel_pB : Rel x pB (sB (restr x)) := by
  have hX := rel_pX x
  have hY := rel_pY x
  exact (((hY.mul hX.trans).sub (hX.mul hY.trans))).tab

theorem rel_pC : Rel x pC (sC (restr x)) := by
  have hX := rel_pX x
  have hY := rel_pY x
  exact (((hX.trans.mul hX).smul 3).sub (hY.trans.mul hY)).tab

theorem rel_pD : Rel x pD (sD (restr x)) := by
  have hX := rel_pX x
  have hY := rel_pY x
  exact ((hX.trans.mul hY).add (hY.trans.mul hX)).tab

theorem pR_val : pR.val x = sR (restr x) := by
  rw [pR, val_ptr (rel_pC x)]; rfl

theorem pI_val : pI.val x = sI (restr x) := by
  rw [pI, val_smul]
  simp only [val_sumF, val_mul, rel_pX x _ _, rel_pY x _ _]
  simp [sI]

theorem rel_pNr : Rel x pNr (sNr (restr x)) := by
  have hX := rel_pX x
  have hY := rel_pY x
  have hR := pR_val x
  have hI := pI_val x
  have e := (((hX.mul (rel_pC x)).sub (hY.mul (rel_pD x))).add
    (((hX.scal (s := pR)).smul (-1 / 2)).add ((hY.scal (s := pI)).smul (1 / 2)))).tab
  intro i j
  have := e i j
  rw [hR, hI] at this
  unfold pNr
  rw [this]
  simp [sNr, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

theorem rel_pNi : Rel x pNi (sNi (restr x)) := by
  have hX := rel_pX x
  have hY := rel_pY x
  have hR := pR_val x
  have hI := pI_val x
  have e := ((((hX.mul (rel_pD x)).smul 3).add (hY.mul (rel_pC x))).sub
    (((hY.scal (s := pR)).smul (1 / 2)).add ((hX.scal (s := pI)).smul (3 / 2)))).tab
  intro i j
  have := e i j
  rw [hR, hI] at this
  unfold pNi
  rw [this]
  simp [sNi, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

theorem pQ_val : pQ.val x = sliceQ (restr x) := by
  have hA := rel_pA x
  have hB := rel_pB x
  have e1 := val_ptr (hA.mul hA)
  have e2 := val_ptr (hB.mul hB)
  have e3 := val_ptr ((hA.mul hA).mul hA)
  have e4 := val_ptr ((hA.mul hB).mul hB)
  have e5 := val_pfn (rel_pNr x) (by norm_num)
  have e6 := val_pfn (rel_pNi x) (by norm_num)
  simp only [pQ, val_sub, val_add, val_smul, val_mul, e1, e2, e3, e4, e5, e6, pN_val]
  unfold sliceQ
  simp only [fn4]
  push_cast
  ring

theorem pTarget_val : pTarget.val x = sliceTarget (restr x) := by
  simp only [pTarget, val_smul, val_sub, val_mul, pQ_val, pN_val, pE_val]
  unfold sliceTarget
  push_cast
  ring

end Sound

/-! ### The lower-frame matrices and the remainders -/

def pS (j k : Fin 3) : PQ 1 := smul (1 / 2) (add (pX j.succ k.succ) (pX k.succ j.succ))
def pY3 (j k : Fin 3) : PQ 1 := pY j.succ k.succ

/-- The lower-frame matrix `L_{σ₀,σ,c,s}` (`sL`) with rational parameters. -/
def pL (σ₀ σ c s : ℚ) : PM 1 3 3 := fun j k =>
  sub (sub
    (if j = k then
      sub (sub pH0 (smul c (add (smul σ₀ (pY 0 0)) (smul σ (sumF fun i => pY3 i i)))))
        (smul (3 * s) (sub (smul (-σ₀) (pX 0 0)) (smul σ (sumF fun i => pS i i))))
    else zero)
    (smul c (sub (smul 3 (pS j k)) (smul σ (pY3 j k)))))
    (smul (3 * s) (add (pY3 j k) (smul σ (pS j k))))

def pJ : PQ 2 :=
  add (smul 5 (add (sumF fun j : Fin 3 => add (mul (pv ⟨13 + j.1, by omega⟩) (pv ⟨13 + j.1, by omega⟩))
        (mul (pv ⟨16 + j.1, by omega⟩) (pv ⟨16 + j.1, by omega⟩)))
      (sumF fun k : Fin 3 => add (mul (pv ⟨7 + k.1, by omega⟩) (pv ⟨7 + k.1, by omega⟩))
        (mul (pv ⟨10 + k.1, by omega⟩) (pv ⟨10 + k.1, by omega⟩)))))
    (smul 2 (add (add (add (mul (sub (pv 1) (pv 2)) (sub (pv 1) (pv 2)))
      (mul (sub (pv 1) (pv 3)) (sub (pv 1) (pv 3))))
      (add (mul (sub (pv 2) (pv 3)) (sub (pv 2) (pv 3)))
        (mul (sub (pv 4) (pv 5)) (sub (pv 4) (pv 5)))))
      (add (mul (sub (pv 4) (pv 6)) (sub (pv 4) (pv 6))) (mul (sub (pv 5) (pv 6)) (sub (pv 5) (pv 6))))))

/-- `R_sq`, scaled. -/
def pRsq : PQ 6 := smul ((1 / 10 ^ 7 : ℚ) / 27) (mul (mul pN (mul pH0 pH0)) pJ)

def pZax : Fin 3 → PQ 1 := ![pv 12, smul (-1) (pv 11), pv 10]

def pZLZ : PQ 3 := sumF fun i => sumF fun j => mul (mul (pZax i) (pL (-1) (-1) (-1 / 2) (1 / 2) i j)) (pZax j)

/-- `R_ax`. -/
def pRax : PQ 6 := smul ((794424 / 10 ^ 12 : ℚ) / 216) (mul (mul pN pH0) pZLZ)

def pRem : PQ 6 := add pRsq pRax

section Sound2
variable (x : ℕ → ℝ)

theorem Xm_eq (a b : ℕ) (ha : a < 4) (hb : b < 4) : Xm x a b = sX (restr x) ⟨a, ha⟩ ⟨b, hb⟩ := by
  interval_cases a <;> interval_cases b <;> simp [Xm, sX, pidx]

theorem Ym_eq (a b : ℕ) (ha : a < 4) (hb : b < 4) : Ym x a b = sY (restr x) ⟨a, ha⟩ ⟨b, hb⟩ := by
  interval_cases a <;> interval_cases b <;> simp [Ym, sY, pidx]

theorem nn_eq : nn x = sN (restr x) := by
  unfold nn sN fn4
  simp only [Finset.sum_range, Xm_eq x _ _ (Fin.is_lt _) (Fin.is_lt _), Ym_eq x _ _ (Fin.is_lt _) (Fin.is_lt _)]

theorem h0_eq : h0 x = sH0 (restr x) := by simp [h0, sH0]

theorem Lstar_eq (i j : Fin 3) :
    Lstar x i j = sL (restr x) (-1) (-1) (-1 / 2) (1 / 2) i j := by
  have hXs : ∀ a b : Fin 4, Xm x a.1 b.1 = sX (restr x) a b := fun a b => Xm_eq x a.1 b.1 a.2 b.2
  have hYs : ∀ a b : Fin 4, Ym x a.1 b.1 = sY (restr x) a b := fun a b => Ym_eq x a.1 b.1 a.2 b.2
  have e : ∀ a b : Fin 3, Xm x (a.1 + 1) (b.1 + 1) = sX (restr x) a.succ b.succ :=
    fun a b => hXs a.succ b.succ
  have f : ∀ a b : Fin 3, Ym x (a.1 + 1) (b.1 + 1) = sY (restr x) a.succ b.succ :=
    fun a b => hYs a.succ b.succ
  have X00 : Xm x 0 0 = sX (restr x) 0 0 := hXs 0 0
  have Y00 : Ym x 0 0 = sY (restr x) 0 0 := hYs 0 0
  have X11 : Xm x 1 1 = sX (restr x) (Fin.succ 0) (Fin.succ 0) := hXs (Fin.succ 0) (Fin.succ 0)
  have X22 : Xm x 2 2 = sX (restr x) (Fin.succ 1) (Fin.succ 1) := hXs (Fin.succ 1) (Fin.succ 1)
  have X33 : Xm x 3 3 = sX (restr x) (Fin.succ 2) (Fin.succ 2) := hXs (Fin.succ 2) (Fin.succ 2)
  have Y11 : Ym x 1 1 = sY (restr x) (Fin.succ 0) (Fin.succ 0) := hYs (Fin.succ 0) (Fin.succ 0)
  have Y22 : Ym x 2 2 = sY (restr x) (Fin.succ 1) (Fin.succ 1) := hYs (Fin.succ 1) (Fin.succ 1)
  have Y33 : Ym x 3 3 = sY (restr x) (Fin.succ 2) (Fin.succ 2) := hYs (Fin.succ 2) (Fin.succ 2)
  unfold Lstar sL sY3 sS
  simp only [Fin.sum_univ_three, h0_eq, e, f, X00, Y00, X11, X22, X33, Y11, Y22, Y33, Fin.val_inj]
  split_ifs <;> ring


theorem pL_rel (σ₀ σ c s : ℚ) : Rel x (pL σ₀ σ c s) (Matrix.of (sL (restr x) σ₀ σ c s)) := by
  have hX := rel_pX x
  have hY := rel_pY x
  have hS : ∀ j k, (pS j k).val x = sS (restr x) j k := fun j k => by
    simp [pS, sS, val_smul, val_add, hX _ _]; ring
  have hY3 : ∀ j k, (pY3 j k).val x = sY3 (restr x) j k := fun j k => by
    simp [pY3, sY3, hY _ _]
  intro j k
  simp only [pL, Matrix.of_apply, sL, val_sub, val_smul, val_add, hS, hY3]
  by_cases h : j = k
  · simp only [h, ite_true, val_sub, val_smul, val_add, val_sumF, hS, hY3, hX _ _, hY _ _, pH0_val]
    push_cast; ring
  · simp only [h, ite_false, val_zero]
    push_cast; ring

theorem pJ_val : pJ.val x = Jsq x := by
  simp [pJ, Jsq, val_smul, val_add, val_sub, val_mul, val_sumF, pv_val, Fin.sum_univ_three,
    Finset.sum_range_succ]
  ring

theorem pRsq_val : pRsq.val x = Rsq x := by
  rw [pRsq, val_smul, val_mul, val_mul, val_mul, pN_val, pH0_val, pJ_val, Rsq, nn_eq, h0_eq]
  push_cast
  ring

theorem pRax_val : pRax.val x = Rax x := by
  have hz : ∀ i : Fin 3, (pZax i).val x = zax x i := fun i => by
    fin_cases i <;> simp [pZax, zax, pv_val, val_smul]
  have hL := pL_rel x (-1) (-1) (-1 / 2) (1 / 2)
  have hLz : ∀ i j : Fin 3, (pL (-1) (-1) (-1 / 2) (1 / 2) i j).val x = Lstar x i j := fun i j => by
    rw [hL i j, Matrix.of_apply, Lstar_eq]; push_cast; rfl
  have hZ : pZLZ.val x = ∑ i ∈ range 3, ∑ j ∈ range 3, zax x i * Lstar x i j * zax x j := by
    simp only [pZLZ, val_sumF, val_mul, hz, hLz, Finset.sum_range]
  rw [pRax, val_smul, val_mul, val_mul, pN_val, pH0_val, hZ, Rax, nn_eq, h0_eq]
  push_cast
  ring

theorem pRem_val : pRem.val x = Rsq x + Rax x := by
  rw [pRem, val_add, pRsq_val, pRax_val]

end Sound2

end FormalResearch.FourQubitEntropy.GO
