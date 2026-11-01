import FormalResearch.FourQubitEntropy.QVCheck.CBlock
import FormalResearch.FourQubitEntropy.QVFrame.Gram
import FormalResearch.FourQubitEntropy.QVFrame.Twist

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace QVCheck

/-- the checker's `C` rows are the six-copy intertwiner `rowC` of `QVCert` -/
theorem cArr_rowC : ∀ j < 4, ∀ k ≤ 2 * j, ∀ μ < mult j, ∀ w < 64,
    gt cArr ((off j + k * mult j + μ) * 64 + w) = QVCert.rowC (2 * j) k μ w := by
  native_decide


theorem weight_omega : ∀ j < 4, ∀ k ≤ 2 * j, (QVCert.weight (2 * j) k : ℤ) = omegaT j k := by
  native_decide

theorem numOf_revW : ∀ α : Wd 6, numOf (revW α) = 63 - numOf α := by decide +kernel

theorem numOf_mixW : ∀ a ∈ ({3, 4} : Finset ℕ), ∀ u v : Wd 6, numOf (mixW a u v) = mixIdx a (numOf u) (numOf v) := by
  native_decide

theorem tauSgn_eq : ∀ a ∈ ({3, 4} : Finset ℕ), ∀ α β : Wd 6,
    tauSgn a α β = if (popPar (numOf α &&& ((1 <<< (6 - a)) - 1)) + popPar (numOf β &&& ((1 <<< (6 - a)) - 1))) % 2 = 0
      then 1 else -1 := by
  native_decide


theorem gt_eMat (j mu mup : ℕ) (β α : ℕ) (hβ : β < 64) (hα : α < 64) :
    gt (eMat j mu mup) (β * 64 + α) =
      ∑ k ∈ range (2 * j + 1), omegaT j k * gt cArr ((off j + k * mult j + mu) * 64 + β) *
        gt cArr ((off j + k * mult j + mup) * 64 + α) := by
  unfold eMat
  rw [gt_tab, if_pos (by omega), sumTo_eq]
  have e1 : (β * 64 + α) / 64 = β := by omega
  have e2 : (β * 64 + α) % 64 = α := by omega
  rw [e1, e2]

theorem Eop_entry (jx : Spin) (mu mup : ℕ) (hmu : mu < mult jx.val) (hmup : mup < mult jx.val) (w w' : Wd 6) :
    Eop (2 * jx.val) mu mup w w' = gt (eMat jx.val mu mup) (numOf w * 64 + numOf w') := by
  rw [gt_eMat _ _ _ _ _ (numOf_lt64 w) (numOf_lt64 w')]
  have h2 : 2 * jx.val + 1 = (2 * jx.val) + 1 := rfl
  show ∑ m ∈ range (2 * jx.val + 1), (QVCert.weight (2 * jx.val) m : ℤ) * rowW (2 * jx.val) m mu w *
      rowW (2 * jx.val) m mup w' = _
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ 2 * jx.val := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hj := jx.2
  rw [weight_omega jx.val hj m hm']
  have e1 := cArr_rowC jx.val hj m hm' mu hmu (numOf w) (numOf_lt64 w)
  have e2 := cArr_rowC jx.val hj m hm' mup hmup (numOf w') (numOf_lt64 w')
  unfold rowW
  rw [← e1, ← e2]


theorem tau_Eop_entry (a : ℕ) (ha : a ∈ ({3, 4} : Finset ℕ)) (jx : Spin) (mu mup : ℕ) (hmu : mu < mult jx.val)
    (hmup : mup < mult jx.val) (β α : Wd 6) :
    tau a (Eop (2 * jx.val) mu mup) β α = gt (tauMat a (eMat jx.val mu mup)) (numOf β * 64 + numOf α) := by
  rw [tau_apply, Eop_entry jx mu mup hmu hmup, tauSgn_eq a ha]
  unfold tauMat
  have hlt : numOf β * 64 + numOf α < 4096 := by have := numOf_lt64 β; have := numOf_lt64 α; omega
  rw [gt_tab, if_pos hlt]
  have e1 : (numOf β * 64 + numOf α) / 64 = numOf β := by have := numOf_lt64 α; omega
  have e2 : (numOf β * 64 + numOf α) % 64 = numOf α := by have := numOf_lt64 α; omega
  simp only [e1, e2]
  rw [numOf_mixW a ha, numOf_mixW a ha, numOf_revW, numOf_revW]
  have hb := numOf_lt64 β
  have hα := numOf_lt64 α
  generalize popPar (numOf α &&& 1 <<< (6 - a) - 1) + popPar (numOf β &&& 1 <<< (6 - a) - 1) = S
  by_cases hc : S % 2 = 0
  · simp [hc]
  · simp [hc]


/-- the block of `Ψ` as a matrix -/
def psiMat (a : ℕ) (jx j' : Spin) (mu mup : ℕ) : Matrix (Fin (multF j')) (Fin (multF j')) ℤ :=
  Matrix.of fun ν ν' => psiAt (a - 3) jx.val j'.val mu mup ν.val ν'.val

theorem checkPsiOne_spec (h : checkPsi () = true) (ai : ℕ) (hai : ai < 2) (j mu mup : ℕ) (hj : j < 4)
    (hmu : mu < mult j) (hmup : mup < mult j) : checkPsiOne ai j mu mup = true := by
  unfold checkPsi at h
  have h1 := (allTo_iff _ _).1 h ai (by rw [hide_eq]; exact hai)
  have h2 := (allTo_iff _ _).1 h1 j hj
  have h3 := (allTo_iff _ _).1 h2 mu hmu
  exact (allTo_iff _ _).1 h3 mup hmup


theorem hPsi_of_check (h : checkPsi () = true) (a : ℕ) (ha : a ∈ ({3, 4} : Finset ℕ)) (jx : Spin) (mu mup : ℕ)
    (hmu : mu < mult jx.val) (hmup : mup < mult jx.val) :
    Cmat * tau a (Eop (2 * jx.val) mu mup) = blk dimF (fun j' => psiMat a jx j' mu mup) * Cmat := by
  refine Matrix.ext fun r w => ?_
  obtain ⟨j, k, ν⟩ := r
  rw [blk_Cmat_apply (fun j' => psiMat a jx j' mu mup) (fun j' ν ν' => psiAt (a - 3) jx.val j'.val mu mup ν ν') (fun _ _ _ => rfl)]
  have hai : a - 3 < 2 := by simp at ha; omega
  have hspec := checkPsiOne_spec h (a - 3) hai jx.val mu mup jx.2 hmu hmup
  have ha3 : 3 + (a - 3) = a := by simp at ha; omega
  unfold checkPsiOne at hspec
  rw [ha3] at hspec
  have hr := rowNum_lt ⟨j, (k, ν)⟩
  have h1 := (allTo_iff _ _).1 hspec (rowNum ⟨j, (k, ν)⟩) hr
  have h2 := (allTo_iff _ _).1 h1 (numOf w) (numOf_lt64 w)
  simp only [beq_iff_eq, sumTo_eq] at h2
  obtain ⟨e1, e2, e3⟩ := rowSpin_rowNum ⟨j, (k, ν)⟩
  rw [e1, e2] at h2
  have hL : (Cmat * tau a (Eop (2 * jx.val) mu mup)) ⟨j, (k, ν)⟩ w =
      ∑ x ∈ range 64, gt cArr (rowNum ⟨j, (k, ν)⟩ * 64 + x) *
        gt (tauMat a (eMat jx.val mu mup)) (x * 64 + numOf w) := by
    rw [Matrix.mul_apply]
    refine (Finset.sum_congr rfl fun w' _ => ?_).trans
      (sum_wd (fun x => gt cArr (rowNum ⟨j, (k, ν)⟩ * 64 + x) * gt (tauMat a (eMat jx.val mu mup)) (x * 64 + numOf w)))
    rw [tau_Eop_entry a ha jx mu mup hmu hmup]
    rfl
  rw [hL, h2]

end QVCheck
