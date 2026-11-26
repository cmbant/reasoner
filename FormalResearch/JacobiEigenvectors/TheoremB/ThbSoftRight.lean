module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftLeft
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftOverlapRight

/-!
# Paper J, Theorem B, L3.5c, part 12: the right half chart of a soft block (generic over the soft chart pair)

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`, the soft charts: (I1)--(I4) for the right half collar (the left half of the mirror chain).

`softRightChart` has the global rows `g_0 .. b - 1` (`g_0 = N - nearestRow (L - u_c)`, `b = ceil((u_c + eta/2)/h - 1/2)`), the mirror chain rows `N - i` (direction `+1`, `tau = true`), the half-window `P_k = softPk` of the mirror chain
`{chain row <= nearestRow u_c^R}` (covered by the rows since `g_0` is the global row of `nearestRow u_c^R`), and `used = {rows > n_c}`.  The rows `g_0 .. n_c` (at most two, both within `h/2` of `u_c`) are not used by `hat G`; the host of the chart
on them is the right sewing `hat kappa psi-hat^R_{N-i}/hat N` (`softHost0R`), which differs from the final matrix there by `<= C_d h^m` (`soft_entry_diff`), so the host column bound only changes by the constant `2 C_d`.

## Proved here

* `jbL2_add_le`, `jbL2_support_le`: the triangle inequality and the bound of a vector supported on at most two rows.
* `soft_right_ok`: constants `cs, N_0, h_0` such that the right chart is `Chart.Ok`, matches `G0, G1` on its used rows and covers the rows `n_c + 1 .. b - 1` with used rows.

## Differences from the paper

The right half starts at `g_0` and has a modified host on the rows `<= n_c` (see above); the paper does not distinguish the fold row of the left and right chains.

## Not formalised

The block assembly and the cover bound (`ThbSoftUp.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine FormalResearch.JB

open scoped Classical

theorem jbL2_add_le {ι : Type*} (S : Finset ι) (a b : ι → ℝ) :
    jbL2 S (fun i => a i + b i) ≤ jbL2 S a + jbL2 S b := by
  unfold jbL2
  set A := ∑ i ∈ S, a i ^ 2 with hA
  set B := ∑ i ∈ S, b i ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : (∑ i ∈ S, a i * b i) ^ 2 ≤ A * B := by
    have := Finset.sum_mul_sq_le_sq_mul_sq S a b
    exact this
  have hab : ∑ i ∈ S, a i * b i ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_mul hA0]
    exact Real.le_sqrt_of_sq_le hcs
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ i ∈ S, (a i + b i) ^ 2 = A + B + 2 * ∑ i ∈ S, a i * b i := by
    rw [hA, hB, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  have h1 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have h2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  nlinarith

theorem jbL2_support_le {ι : Type*} [Fintype ι] (d : ι → ℝ) (S : Finset ι) (hS : S.card ≤ 2) {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ i, i ∉ S → d i = 0) (h1 : ∀ i, |d i| ≤ c) : jbL2 Finset.univ d ≤ 2 * c := by
  unfold jbL2
  rw [Real.sqrt_le_left (by positivity)]
  have : ∑ i, d i ^ 2 = ∑ i ∈ S, d i ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
    rw [h0 i hi]; ring
  rw [this]
  calc ∑ i ∈ S, d i ^ 2 ≤ ∑ i ∈ S, c ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc d i ^ 2 = |d i| ^ 2 := (sq_abs _).symm
          _ ≤ c ^ 2 := by gcongr; exact h1 i
    _ = (S.card : ℝ) * c ^ 2 := by simp
    _ ≤ 2 * c ^ 2 := by
        have : (S.card : ℝ) ≤ 2 := by exact_mod_cast hS
        nlinarith [sq_nonneg c]
    _ ≤ (2 * c) ^ 2 := by nlinarith [sq_nonneg c]

section Defs

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

/-- First global row of the right chart: the global row of the fold row of the mirror chain. -/
def softLoR (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (p : Par × ℝ) (N : ℕ) : ℕ :=
  ((N : ℤ) - nearestRow (Fz.step N) (CR.uc p)).toNat

/-- Number of rows `g_0 .. b - 1` of the right chart. -/
def softRR (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (p : Par × ℝ) (N : ℕ) : ℕ :=
  ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉.toNat - softLoR CR p N

/-- The host (order `m`) of the right chart: the right sewing on the rows `g_0 .. n_c`, the final matrix elsewhere. -/
def softHost0R {m' : ℕ} (CL : SoftEdgeChart Fz P m' q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m' q U V (fun _ => 1))
    (lo : ℕ) (p : Par × ℝ) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (G0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => if j ∈ cols ∧ lo ≤ (i : ℕ) ∧ ((i : ℕ) : ℤ) ≤ nearestRow (Fz.step N) (CL.uc p) then
    softKappa CL CR p (Xs j) N * CR.psiHatL p (Xs j) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL CR p (Xs j) N else G0 i j

/-- The right half chart of the soft block. -/
def softRightChart {Jlo Jhi ulo uhi : (Par × ℝ) → ℝ}
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (TIR : TransferInputsDn (mirrorFamily Fz) P Jlo Jhi m CR.chain CR1.chain 2 ulo uhi)
    (p : Par × ℝ) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1)))
    (G0 G1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hlo : softLoR CR p N + softRR CL CR p N ≤ N + 1) :
    Chart (N + 1) (softRR CL CR p N) cols :=
  softJBChart CR CR1 TIR p N Xs cols (softLoR CR p N) (softRR CL CR p N) hlo true
    (Finset.univ.filter (fun n : Fin (softRR CL CR p N) => nearestRow (Fz.step N) (CL.uc p) < ((softLoR CR p N : ℕ) : ℤ) + n))
    (fun k => softPk N (softLoR CR p N) (softRR CL CR p N) true
      ((softWindow CR p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p))))
    (fun k => softKappa CL CR p (Xs k) N * CR.lamL p (Xs k) N / (kappaBal (CR.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
    (fun k => softKappa CL1 CR1 p (Xs k) N * CR1.lamL p (Xs k) N / (kappaBal (CR1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N))
    (softHost0R CL CR (softLoR CR p N) p N Xs cols G0) (softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1)

end Defs


theorem card_row_le_one {N : ℕ} (c : ℤ) : (Finset.univ.filter (fun i : Fin (N + 1) => ((i : ℕ) : ℤ) = c)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := (Finset.mem_filter.mp ha).2
  have h2 := (Finset.mem_filter.mp hb).2
  exact Fin.ext (by omega)

theorem fold_between {h uc : ℝ} (hh : 0 < h) {a b i : ℤ} (ha : |uNode h a - uc| ≤ h / 2) (hb : |uNode h b - uc| ≤ h / 2)
    (h1 : a ≤ i) (h2 : i ≤ b) : |uNode h i - uc| ≤ h / 2 := by
  have a1 : (a : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
  have a2 : (i : ℝ) ≤ (b : ℝ) := by exact_mod_cast h2
  have e5 := abs_le.mp ha
  have e6 := abs_le.mp hb
  unfold uNode at e5 e6 ⊢
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 a1) hh.le, mul_nonneg (sub_nonneg.2 a2) hh.le]

/-- The column bound of a host that differs from `G` on at most two rows `g0 .. nc` (`nc <= g0 + 1`) of the columns in `cols` only, by at most `c`. -/
theorem host_col_gen {N : ℕ} (cols : Finset (Fin (N + 1))) (g0 nc : ℤ) (hnc : nc ≤ g0 + 1)
    (host G Um ex : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hhost : ∀ i j, host i j = if j ∈ cols ∧ g0 ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) ≤ nc then ex i j else G i j)
    {c : ℝ} (hc : 0 ≤ c) (hdiff : ∀ j ∈ cols, ∀ i : Fin (N + 1), g0 ≤ ((i : ℕ) : ℤ) → ((i : ℕ) : ℤ) ≤ nc → |ex i j - G i j| ≤ c)
    (j : Fin (N + 1)) : jbL2 Finset.univ (fun i => host i j - Um i j) ≤ 2 * c + jbL2 Finset.univ (fun i => G i j - Um i j) := by
  by_cases hj : j ∈ cols
  · have hSc : (Finset.univ.filter (fun i : Fin (N + 1) => g0 ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) ≤ nc)).card ≤ 2 := by
      refine (Finset.card_le_card (t := (Finset.univ.filter (fun i : Fin (N + 1) => ((i : ℕ) : ℤ) = g0)) ∪
        (Finset.univ.filter (fun i : Fin (N + 1) => ((i : ℕ) : ℤ) = g0 + 1))) ?_).trans ?_
      · intro i hi
        have := (Finset.mem_filter.mp hi).2
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · exact (Finset.card_union_le _ _).trans (by have := card_row_le_one (N := N) g0; have := card_row_le_one (N := N) (g0 + 1); omega)
    have hd : jbL2 Finset.univ (fun i => host i j - G i j) ≤ 2 * c := by
      refine jbL2_support_le _ _ hSc hc ?_ ?_
      · intro i hi
        have hi' : ¬ (g0 ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) ≤ nc) := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [hhost, ite_eq_right (fun h => hi' h.2)]
        ring
      · intro i
        by_cases hi : g0 ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) ≤ nc
        · rw [hhost, ite_eq_left ⟨hj, hi⟩]
          exact hdiff j hj i hi.1 hi.2
        · rw [hhost, ite_eq_right (fun h => hi h.2), sub_self, abs_zero]
          exact hc
    have hsum := jbL2_add_le Finset.univ (fun i => host i j - G i j) (fun i => G i j - Um i j)
    have e : (fun i => host i j - Um i j) = fun i => (host i j - G i j) + (G i j - Um i j) := by
      funext i; ring
    rw [e]
    linarith
  · have e : (fun i => host i j - Um i j) = fun i => G i j - Um i j := by
      funext i
      rw [hhost, ite_eq_right (fun h => hj h.1)]
    rw [e]
    linarith [jbL2_nonneg (S := (Finset.univ : Finset (Fin (N + 1)))) (fun i => G i j - Um i j)]

section Right

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem soft_right_ok (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hM1 : SoftMirror CL1 CR1)
    (hz : CL1.zeta = CL.zeta) (hmu : CL1.muS = CL.muS) (huc : CL1.uc = CL.uc) (hδ1 : CL1.δ0 = CL.δ0) (hη1 : CL1.η = CL.η)
    (hm : 1 ≤ m) (r : ℕ) (hr : StdAssump Fz P (q / 2) r)
    (TIR : TransferInputsDn (mirrorFamily Fz) P (fun p => Fz.bandHi p - CL.δ0) (fun p => Fz.bandHi p + CL.δ0) m CR.chain CR1.chain 2
      (fun p => CR.uc p - CR.η / 2) (fun p => CR.uc p + CR.η / 2))
    (Ch : ℝ) (hCh : 0 ≤ Ch) :
    ∃ (cs : OneStepConsts) (N0 : ℕ) (h0 : ℝ), 0 < h0 ∧ h0 ≤ 1 ∧ ∀ p ∈ P, ∀ N : ℕ, N0 ≤ N → Fz.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
      ∀ cols : Finset (Fin (N + 1)), (∀ k ∈ cols, |Xs k - Fz.bandHi p| ≤ CL.δ0) →
      ∀ G0 G1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
        (∀ k ∈ cols, ∀ i : Fin (N + 1), G0 i k =
          if ((i : ℕ) : ℤ) ≤ nearestRow (Fz.step N) (CL.uc p) then CL.psiHatL p (Xs k) N ((i : ℕ) : ℤ) / softNorm CL CR p (Xs k) N
          else softKappa CL CR p (Xs k) N * CR.psiHatL p (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL CR p (Xs k) N) →
        (∀ k ∈ cols, ∀ i : Fin (N + 1), G1 i k =
          if ((i : ℕ) : ℤ) ≤ nearestRow (Fz.step N) (CL1.uc p) then CL1.psiHatL p (Xs k) N ((i : ℕ) : ℤ) / softNorm CL1 CR1 p (Xs k) N
          else softKappa CL1 CR1 p (Xs k) N * CR1.psiHatL p (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL1 CR1 p (Xs k) N) →
        (∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => G0 i j - Um i j) ≤ Ch * Fz.step N ^ m) →
        (∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => G1 i j - Um i j) ≤ Ch * Fz.step N ^ (m + 1) * Real.log (1 / Fz.step N)) →
        ∃ hlo : softLoR CR p N + softRR CL CR p N ≤ N + 1,
          (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).Ok cs m (Fz.step N) Um ∧
          (∀ n ∈ (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).used, ∀ k : cols,
            G0 ((softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).row n) k =
              (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).H0 (Fz.step N) n k) ∧
          (∀ n ∈ (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).used, ∀ k : cols,
            G1 ((softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).row n) k =
              (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).H1 (Fz.step N) n k) ∧
          (∀ i : Fin (N + 1), nearestRow (Fz.step N) (CL.uc p) < ((i : ℕ) : ℤ) →
            ((i : ℕ) : ℤ) < ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ →
            ∃ n ∈ (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).used,
              (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).row n = i) := by
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero Fz P (q / 2) r hr
  have hδR : CR.δ0 = CL.δ0 := hM.2.2.2.2.1
  have hδR1 : CR1.δ0 = CR.δ0 := by rw [hM1.2.2.2.2.1, hδR, hδ1]
  have hηR : CR.η = CL.η := hM.2.2.2.1
  have hηR1 : CR1.η = CR.η := by rw [hM1.2.2.2.1, hη1, hηR]
  obtain ⟨hE1, hhE1, HEXT⟩ := softJBChart_ext_row (Jlo := fun p => Fz.bandHi p - CL.δ0) (Jhi := fun p => Fz.bandHi p + CL.δ0)
    (ulo := fun p => CR.uc p - CR.η / 2) (uhi := fun p => CR.uc p + CR.η / 2) hf CL CR CL1 CR1 hM hM1 hδ1 r hr
  obtain ⟨C4, hu1, hC40, hupos, HUB⟩ := softJBChart_overlap_ub_P (Jlo := fun p => Fz.bandHi p - CL.δ0) (Jhi := fun p => Fz.bandHi p + CL.δ0)
    (ulo := fun p => CR.uc p - CR.η / 2) (uhi := fun p => CR.uc p + CR.η / 2) hf CR CR1 hδR1
  obtain ⟨c0, hl1, hc0pos, hlpos, HLB⟩ := softJBChart_overlap_lb_right (Jlo := fun p => Fz.bandHi p - CL.δ0) (Jhi := fun p => Fz.bandHi p + CL.δ0)
    (ulo := fun p => CR.uc p - CR.η / 2) (uhi := fun p => CR.uc p + CR.η / 2) hf CL CR CR1 hM hm Cs
  obtain ⟨hA, hhA, HA⟩ := soft_a_data hf CL CR hm hM r hr
  obtain ⟨Cd, hd1, hCd0, hd1p, Hd⟩ := soft_entry_diff hf CL CR hm hM
  obtain ⟨Cd1, hd2, hCd10, hd2p, Hd1⟩ := soft_entry_diff hf CL1 CR1 (by omega) hM1
  obtain ⟨hf0, hhf0, Hf0⟩ := soft_fold_rows CL
  obtain ⟨hf1, hhf1, Hf1⟩ := soft_fold_rows CL1
  have hηpos : 0 < CL.η := CL.consts_pos.2.1
  have hδpos : 0 < CL.δ0 := CL.consts_pos.1
  obtain ⟨hrect, hcTp, hcαp, hS0, hωp⟩ := TIR.consts_pos
  obtain ⟨h0, hh0pos, hle⟩ : ∃ h0 : ℝ, 0 < h0 ∧ ∀ x : ℝ, x ≤ h0 → x ≤ 1 ∧ x ≤ CL.η / 4 ∧ x ≤ hE1 ∧ x ≤ hu1 ∧ x ≤ hl1 ∧ x ≤ hs0 ∧ x ≤ hA ∧
      x ≤ asmH0 CL ∧ x ≤ asmH0 CR ∧ x ≤ hd1 ∧ x ≤ hd2 ∧ x ≤ hf0 ∧ x ≤ hf1 ∧ x ≤ Real.exp (-1) := by
    refine ⟨min 1 (min (CL.η / 4) (min hE1 (min hu1 (min hl1 (min hs0 (min hA (min (asmH0 CL) (min (asmH0 CR)
      (min hd1 (min hd2 (min hf0 (min hf1 (Real.exp (-1)))))))))))))), ?_, fun x hx => ?_⟩
    · simp only [lt_min_iff]
      exact ⟨one_pos, by linarith, hhE1, hupos, hlpos, hs0p, hhA, asmH0_pos CL, asmH0_pos CR, hd1p, hd2p, hhf0, hhf1, Real.exp_pos _⟩
    · simp only [le_min_iff] at hx
      exact hx
  set cs : OneStepConsts :=
    ⟨0, Ch + 2 * Cd + 2 * Cd1, max (chartSchurK 0 CL.η 0 (2 * CL.δ0) TIR.S TIR.cT TIR.cα 1) 0, TIR.ωmax, TIR.cT, TIR.cα, c0, C4, 1,
      by positivity, le_max_right _ _, hωp, hcTp, hcαp, hc0pos, hC40, zero_le_one⟩ with hcs
  refine ⟨cs, max CL.N0 (max CR.N0 (max CL1.N0 (max CR1.N0 TIR.N0))), h0, hh0pos, (hle h0 le_rfl).1, ?_⟩
  intro p hp N hN hstep Xs Um hE cols hwin G0 G1 hG0 hG1 hc0 hc1
  simp only [max_le_iff] at hN
  obtain ⟨hN0L, hN0R, hN1L, hN1R, hNT⟩ := hN
  have hst : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  obtain ⟨hh1, hsη, hsE, hsu, hsl, hss0, hsA, hsasm, hsasmR, hsd1, hsd2, hsf0, hsf1, hsexp⟩ := hle _ hstep
  obtain ⟨hu1', hu2'⟩ := CL.ucη_in p hp
  have hucR : CR.uc p = Fz.L - CL.uc p := hM.1 p hp
  have hucR1 : CR1.uc p = Fz.L - CL.uc p := by rw [hM1.1 p hp, huc]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ :=
    soft_geom (N := N) hst hηpos hsη hLs hu1' hu2'
  set nc : ℤ := nearestRow (Fz.step N) (CL.uc p) with hncdef
  set g0 : ℤ := (N : ℤ) - nearestRow (Fz.step N) (Fz.L - CL.uc p) with hg0def
  set b : ℤ := ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ with hbdef
  have hloR : (softLoR CR p N : ℤ) = g0 := by
    unfold softLoR; rw [hucR]; omega
  have hRR : (softRR CL CR p N : ℤ) = b - g0 := by
    unfold softRR
    have : (b.toNat : ℤ) = b := by omega
    have h2 : softLoR CR p N ≤ b.toNat := by
      have : (softLoR CR p N : ℤ) ≤ (b.toNat : ℤ) := by omega
      exact_mod_cast this
    omega
  have hlo : softLoR CR p N + softRR CL CR p N ≤ N + 1 := by
    have : ((softLoR CR p N + softRR CL CR p N : ℕ) : ℤ) ≤ ((N + 1 : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast this
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) := fun k => by
    have := hwin k k.2
    rw [abs_le] at this
    exact ⟨by linarith, by linarith⟩
  have hX' : ∀ k : cols, |Xs k - Fz.bandHi p| ≤ CL.δ0 := fun k => hwin k k.2
  have hXR : ∀ k : cols, |Xs k - (mirrorFamily Fz).bandHi p| ≤ CR.δ0 := fun k => by
    rw [bandHi_mirror, hδR]; exact hX' k
  have hsame : ∀ k : cols, (CR.chain p (Xs k) N).wf 2 = (CR1.chain p (Xs k) N).wf 2 :=
    fun k => (TIR.same_ladder p hp (Xs k) (hX k) N hNT).2.1
  have haL1 : ∀ k : cols, CL.aOf p (Xs k) N ≤ 1 := fun k =>
    ((HA p hp N (max_le hN0L hN0R) hsA Xs Um hE k (hX' k)).trans zero_le_one)
  have hzP : ∀ α x, CL1.zeta p α x = CL.zeta p α x := fun α x => by rw [hz]
  have hmuP : ∀ r α, CL1.muS r p α = CL.muS r p α := fun r α => by rw [hmu]
  have hucP : CL1.uc p = CL.uc p := by rw [huc]
  have haL1' : ∀ k : cols, CL1.aOf p (Xs k) N ≤ 1 := fun k => by
    rw [(softChart_data_eq_P CL CL1 hzP hmuP hucP (Xs k) N).1]
    exact haL1 k
  have haR : ∀ k : cols, CR.aOf p (Xs k) N ≤ 1 := fun k => by rw [aOf_mirror hM hp]; exact haL1 k
  have haR1 : ∀ k : cols, CR1.aOf p (Xs k) N ≤ 1 := fun k => by rw [aOf_mirror hM1 hp]; exact haL1' k
  have hzR : ∀ α x, CR1.zeta p α x = CR.zeta p α x := fun α x => by
    have h1 := hM.2.1 p hp α (-x)
    have h2 := hM1.2.1 p hp α (-x)
    rw [neg_neg] at h1 h2
    rw [h1, h2, hz]
  have hmuR : ∀ r α, CR1.muS r p α = CR.muS r p α := fun r α => by
    rw [hM1.2.2.1 r p hp α, hM.2.2.1 r p hp α, hmu]
  have hmir : ∀ i : ℤ, uNode (Fz.step N) ((N : ℤ) - i) = Fz.L - uNode (Fz.step N) i := fun i => uNode_mirror Fz.L (Fz.step N) N i hLs
  have hrows : ∀ n : Fin (softRR CL CR p N), 1 ≤ chartRowDn N (softLoR CR p N) (softRR CL CR p N) true n ∧
      CR.uc p - CR.η / 2 ≤ uNode (Fz.step N) (chartRowDn N (softLoR CR p N) (softRR CL CR p N) true n) ∧
      uNode (Fz.step N) (chartRowDn N (softLoR CR p N) (softRR CL CR p N) true n) ≤ CR.uc p + CR.η / 2 := by
    intro n
    have hn : n.val < softRR CL CR p N := n.isLt
    have hnz : (n.val : ℤ) < b - g0 := by rw [← hRR]; exact_mod_cast hn
    have hr' : chartRowDn N (softLoR CR p N) (softRR CL CR p N) true n = (N : ℤ) - ((softLoR CR p N : ℤ) + n.val) := by simp [chartRowDn]
    rw [hr', hmir, hucR, hηR]
    refine ⟨by omega, ?_, ?_⟩
    · have := g12 ((softLoR CR p N : ℤ) + n.val) (by omega)
      linarith
    · have h1 := (uNode_le_iff hst g0 ((softLoR CR p N : ℤ) + n.val)).mpr (by omega)
      have h2 := (abs_le.mp g5).1
      linarith
  have hcov : ∀ k : cols, ∀ j ∈ (softWindow CR p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p)),
      ∃ n : Fin (softRR CL CR p N), chartRowDn N (softLoR CR p N) (softRR CL CR p N) true n = j := by
    intro k j hj
    have hj' := Finset.mem_filter.mp hj
    have hloc := soft_win_loc CR hp (hXR k) hsasmR hj'.1
    have hj0 : 0 ≤ j := by
      have := (Finset.mem_filter.mp hj'.1).1
      unfold rowsOf at this
      exact (Finset.mem_Icc.mp this).1
    have hjN : j ≤ (N : ℤ) := by
      have := (Finset.mem_filter.mp hj'.1).1
      unfold rowsOf at this
      exact (Finset.mem_Icc.mp this).2
    have hjn : j ≤ (N : ℤ) - g0 := by
      have := hj'.2
      rw [hucR] at this
      omega
    have hjb : (N : ℤ) - j < b := by
      by_contra hcon
      have h1 := g13 ((N : ℤ) - j) (by omega)
      rw [hmir] at h1
      have h2 := (abs_lt.mp hloc).1
      rw [hucR, hηR] at h2
      have h2' : -(CL.η / 4) < uNode (Fz.step N) j - (Fz.L - CL.uc p) := h2
      have h3 : uNode (Fz.step N) j > Fz.L - CL.uc p - CL.η / 4 := by linarith
      linarith
    refine ⟨⟨((N : ℤ) - (softLoR CR p N : ℤ) - j).toNat, ?_⟩, ?_⟩
    · have : (((N : ℤ) - (softLoR CR p N : ℤ) - j).toNat : ℤ) < (softRR CL CR p N : ℤ) := by omega
      exact_mod_cast this
    · simp only [chartRowDn, ite_true]
      omega
  have hnc1 : nearestRow (Fz.step N) (CL1.uc p) = nc := by rw [hucP]
  -- the host entries on the rows `>= g_0`
  have hHR0 : ∀ (i : Fin (N + 1)), softLoR CR p N ≤ (i : ℕ) → ∀ k ∈ cols,
      softHost0R CL CR (softLoR CR p N) p N Xs cols G0 i k =
        softKappa CL CR p (Xs k) N * CR.psiHatL p (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL CR p (Xs k) N := by
    intro i hi k hk
    unfold softHost0R
    by_cases hle' : ((i : ℕ) : ℤ) ≤ nc
    · rw [ite_eq_left ⟨hk, hi, hle'⟩]
    · rw [ite_eq_right (fun h => hle' h.2.2), hG0 k hk i, ite_eq_right hle']
  have hHR1 : ∀ (i : Fin (N + 1)), softLoR CR p N ≤ (i : ℕ) → ∀ k ∈ cols,
      softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1 i k =
        softKappa CL1 CR1 p (Xs k) N * CR1.psiHatL p (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL1 CR1 p (Xs k) N := by
    intro i hi k hk
    unfold softHost0R
    by_cases hle' : ((i : ℕ) : ℤ) ≤ nc
    · rw [ite_eq_left ⟨hk, hi, by rw [hnc1]; exact hle'⟩]
    · rw [ite_eq_right (fun h => hle' (by have h2 := h.2.2; rwa [hnc1] at h2)), hG1 k hk i, ite_eq_right (by rw [hnc1]; exact hle')]
  have hmono : ∀ i : ℤ, g0 ≤ i → i ≤ nc → |uNode (Fz.step N) i - CL.uc p| ≤ Fz.step N / 2 :=
    fun i h1 h2 => fold_between hst g5 g6 h1 h2
  have hX1' : ∀ k ∈ cols, |Xs k - Fz.bandHi p| ≤ CL1.δ0 := fun k hk => by rw [hδ1]; exact hwin k hk
  have hdiff0 : ∀ k ∈ cols, ∀ i : ℤ, g0 ≤ i → i ≤ nc →
      |softKappa CL CR p (Xs k) N * CR.psiHatL p (Xs k) N ((N : ℤ) - i) / softNorm CL CR p (Xs k) N -
        CL.psiHatL p (Xs k) N i / softNorm CL CR p (Xs k) N| ≤ Cd * Fz.step N ^ m := by
    intro k hk i h1 h2
    exact Hd p hp N (max_le hN0L hN0R) hsd1 Xs Um hE k (hwin k hk) (haL1 ⟨k, hk⟩) i
      (Hf0 p hp (Xs k) (hwin k hk) N hN0L hsf0 (haL1 ⟨k, hk⟩) i (hmono i h1 h2))
  have hdiff1 : ∀ k ∈ cols, ∀ i : ℤ, g0 ≤ i → i ≤ nc →
      |softKappa CL1 CR1 p (Xs k) N * CR1.psiHatL p (Xs k) N ((N : ℤ) - i) / softNorm CL1 CR1 p (Xs k) N -
        CL1.psiHatL p (Xs k) N i / softNorm CL1 CR1 p (Xs k) N| ≤ Cd1 * Fz.step N ^ (m + 1) := by
    intro k hk i h1 h2
    have hmono1 : |uNode (Fz.step N) i - CL1.uc p| ≤ Fz.step N / 2 := by rw [hucP]; exact hmono i h1 h2
    exact Hd1 p hp N (max_le hN1L hN1R) hsd2 Xs Um hE k (hX1' k hk) (haL1' ⟨k, hk⟩) i
      (Hf1 p hp (Xs k) (hX1' k hk) N hN1L hsf1 (haL1' ⟨k, hk⟩) i hmono1)
  have hlogge : 1 ≤ Real.log (1 / Fz.step N) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    rw [le_div_iff₀ hst]
    calc Real.exp 1 * Fz.step N ≤ Real.exp 1 * Real.exp (-1) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hlogge : 1 ≤ Real.log (1 / Fz.step N) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    rw [le_div_iff₀ hst]
    calc Real.exp 1 * Fz.step N ≤ Real.exp 1 * Real.exp (-1) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hhost0 : ∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => softHost0R CL CR (softLoR CR p N) p N Xs cols G0 i j - Um i j) ≤ cs.C * Fz.step N ^ m := by
    intro j
    have hh := host_col_gen cols g0 nc g4 (softHost0R CL CR (softLoR CR p N) p N Xs cols G0) G0 Um
      (fun i j => softKappa CL CR p (Xs j) N * CR.psiHatL p (Xs j) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL CR p (Xs j) N)
      (fun i j => by
        unfold softHost0R
        exact if_congr ⟨fun h => ⟨h.1, by omega, h.2.2⟩, fun h => ⟨h.1, by omega, h.2.2⟩⟩ rfl rfl)
      (mul_nonneg hCd0 (pow_nonneg hst.le _))
      (fun j hj i h1 h2 => by
        rw [hG0 j hj i, ite_eq_left h2]
        exact hdiff0 j hj _ h1 h2) j
    have := hc0 j
    have hC : cs.C = Ch + 2 * Cd + 2 * Cd1 := rfl
    rw [hC]
    linarith [mul_nonneg hCd0 (pow_nonneg hst.le m), mul_nonneg hCd10 (pow_nonneg hst.le m)]
  have hhost1 : ∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1 i j - Um i j) ≤
      cs.C * Fz.step N ^ (m + 1) * Real.log (1 / Fz.step N) := by
    intro j
    have hh := host_col_gen cols g0 nc g4 (softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1) G1 Um
      (fun i j => softKappa CL1 CR1 p (Xs j) N * CR1.psiHatL p (Xs j) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL1 CR1 p (Xs j) N)
      (fun i j => by
        unfold softHost0R
        exact if_congr ⟨fun h => ⟨h.1, by omega, by rw [← hnc1]; exact h.2.2⟩, fun h => ⟨h.1, by omega, by rw [hnc1]; exact h.2.2⟩⟩ rfl rfl)
      (mul_nonneg hCd10 (pow_nonneg hst.le _))
      (fun j hj i h1 h2 => by
        rw [hG1 j hj i, ite_eq_left (by rw [hnc1]; exact h2)]
        exact hdiff1 j hj _ h1 h2) j
    have := hc1 j
    have hC : cs.C = Ch + 2 * Cd + 2 * Cd1 := rfl
    rw [hC]
    have hp1 : 0 ≤ Fz.step N ^ (m + 1) := pow_nonneg hst.le _
    have hL0 : 0 ≤ Fz.step N ^ (m + 1) * Real.log (1 / Fz.step N) := mul_nonneg hp1 (by linarith)
    have hLge : Fz.step N ^ (m + 1) ≤ Fz.step N ^ (m + 1) * Real.log (1 / Fz.step N) := le_mul_of_one_le_right hp1 hlogge
    linarith [mul_nonneg hCd0 hL0, mul_nonneg hCd10 hL0, mul_nonneg hCh hL0, mul_nonneg hCd10 (sub_nonneg.2 hLge)]
  have hpP : ∀ n : Fin (softRR CL CR p N), (softLoR CR p N : ℤ) + n.val < b := by
    intro n
    have hn : n.val < softRR CL CR p N := n.isLt
    have hnz : (n.val : ℤ) < b - g0 := by rw [← hRR]; exact_mod_cast hn
    omega
  have hH0 : ∀ (n : Fin (softRR CL CR p N)) (k : cols),
      (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).H0 (Fz.step N) n k =
        softHost0R CL CR (softLoR CR p N) p N Xs cols G0
          ((softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).row n) k := by
    intro n k
    unfold softRightChart
    erw [softJBChart_H0]
    simp only [FormalResearch.JB.Chart.row, softJBChart]
    have hn : n.val < softRR CL CR p N := n.isLt
    have hi := hHR0 ⟨softLoR CR p N + n.val, by omega⟩ (by simp) k k.2
    simp only [Fin.val_mk] at hi
    rw [hi]
    have hcr : chartRowDn N (softLoR CR p N) (softRR CL CR p N) true n = (N : ℤ) - (((softLoR CR p N + n.val : ℕ) : ℤ)) := by
      simp [chartRowDn]
    rw [hcr]
    have hg : CR.uc p - CR.η / 2 < uNode (Fz.step N) ((N : ℤ) - (((softLoR CR p N + n.val : ℕ) : ℤ))) := by
      rw [hmir, hucR, hηR]
      have := g12 (((softLoR CR p N + n.val : ℕ) : ℤ)) (by push_cast; exact hpP n)
      linarith
    rw [psiHatL_of_gt _ _ _ _ hg]
    ring
  have hH1 : ∀ (n : Fin (softRR CL CR p N)) (k : cols),
      (softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).H1 (Fz.step N) n k =
        softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1
          ((softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo).row n) k := by
    intro n k
    unfold softRightChart
    erw [softJBChart_H1 CR CR1 TIR p hp N hNT Xs cols (softLoR CR p N) (softRR CL CR p N) hlo true _ _ _ _ _ _ hX n k]
    simp only [FormalResearch.JB.Chart.row, softJBChart]
    have hn : n.val < softRR CL CR p N := n.isLt
    have hi := hHR1 ⟨softLoR CR p N + n.val, by omega⟩ (by simp) k k.2
    simp only [Fin.val_mk] at hi
    rw [hi]
    have hcr : chartRowDn N (softLoR CR p N) (softRR CL CR p N) true n = (N : ℤ) - (((softLoR CR p N + n.val : ℕ) : ℤ)) := by
      simp [chartRowDn]
    rw [hcr]
    have hg : CR1.uc p - CR1.η / 2 < uNode (Fz.step N) ((N : ℤ) - (((softLoR CR p N + n.val : ℕ) : ℤ))) := by
      rw [hucR1, hηR1, hmir, hηR]
      have := g12 (((softLoR CR p N + n.val : ℕ) : ℤ)) (by push_cast; exact hpP n)
      linarith
    rw [psiHatL_of_gt _ _ _ _ hg]
    ring
  have hcoeff := softJBChart_coeff CR CR1 TIR cs hp N (max_le hN0R hN1R) hNT Xs cols (softLoR CR p N) (softRR CL CR p N) hlo true
    (Finset.univ.filter (fun n : Fin (softRR CL CR p N) => nearestRow (Fz.step N) (CL.uc p) < ((softLoR CR p N : ℕ) : ℤ) + n))
    (fun k => softPk N (softLoR CR p N) (softRR CL CR p N) true
      ((softWindow CR p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p))))
    (fun k => softKappa CL CR p (Xs k) N * CR.lamL p (Xs k) N / (kappaBal (CR.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
    (fun k => softKappa CL1 CR1 p (Xs k) N * CR1.lamL p (Xs k) N / (kappaBal (CR1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N))
    (softHost0R CL CR (softLoR CR p N) p N Xs cols G0) (softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1)
    hX (fun X hX0 => by
      obtain ⟨h1, h2⟩ := hX0
      rw [bandHi_mirror, hδR]
      exact abs_le.mpr ⟨by linarith, by linarith⟩) hrows 1
    (by show |Fz.step N| ≤ 1; rw [abs_of_pos hst]; exact hh1) le_rfl le_rfl le_rfl
    (by
      show chartSchurK (CR.uc p - CR.η / 2) (CR.uc p + CR.η / 2) (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) TIR.S TIR.cT TIR.cα 1 ≤
        max (chartSchurK 0 CL.η 0 (2 * CL.δ0) TIR.S TIR.cT TIR.cα 1) 0
      rw [chartSchurK_congr (a' := 0) (b' := CL.η) (c' := 0) (d' := 2 * CL.δ0) _ _ _ _ (by rw [hηR]; ring) (by ring)]
      exact le_max_left _ _)
  have hlo' : ((softLoR CR p N + softRR CL CR p N : ℕ) : ℤ) = b := by push_cast; omega
  refine ⟨hlo, ?_, ?_, ?_, ?_⟩
  · refine ChartOkCoeff.ok (c := softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hlo) hcoeff (fun n k => hH0 n k) (fun n k => hH1 n k)
      (fun j => hhost0 j) (fun j => hhost1 j) ?_ ?_ ?_
    · intro n hn0' _
      have hn1 : n.val + 1 = softRR CL CR p N := hn0' rfl
      exact (HEXT p hp N (max_le hN0L hN1L) hsE Xs cols hX' haL1').2 TIR (softLoR CR p N) (softRR CL CR p N) hlo _
        (fun k => softPk N (softLoR CR p N) (softRR CL CR p N) true
          ((softWindow CR p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p))))
        (fun k => softKappa CL CR p (Xs k) N * CR.lamL p (Xs k) N / (kappaBal (CR.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
        (fun k => softKappa CL1 CR1 p (Xs k) N * CR1.lamL p (Xs k) N / (kappaBal (CR1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N))
        (softHost0R CL CR (softLoR CR p N) p N Xs cols G0) (softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1)
        hlo' (fun k => rfl) n hn1
    · intro k
      exact HLB p hp N (max_le hN0L hN0R) hsl Xs Um hE (fun i => (hsp p hp N hss0 Xs Um hE i).2) TIR cols (softLoR CR p N) (softRR CL CR p N) hlo
        _
        (fun k => softKappa CL CR p (Xs k) N * CR.lamL p (Xs k) N / (kappaBal (CR.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
        (fun k => softKappa CL1 CR1 p (Xs k) N * CR1.lamL p (Xs k) N / (kappaBal (CR1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N))
        (softHost0R CL CR (softLoR CR p N) p N Xs cols G0) (softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1)
        Xs id Um (fun k => rfl) (fun n k => rfl) hX' haL1 hcov k
    · intro k
      exact HUB p hp hzR hmuR (by rw [hucR1, hucR]) N (max_le hN0R hN1R) hsu TIR Xs cols (softLoR CR p N) (softRR CL CR p N) hlo true _
        (fun k => softKappa CL CR p (Xs k) N * CR.lamL p (Xs k) N / (kappaBal (CR.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
        (fun k => softKappa CL1 CR1 p (Xs k) N * CR1.lamL p (Xs k) N / (kappaBal (CR1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N))
        (softHost0R CL CR (softLoR CR p N) p N Xs cols G0) (softHost0R CL1 CR1 (softLoR CR p N) p N Xs cols G1)
        hXR haR hsame hcov k
  · intro n hn k
    have hn' := (Finset.mem_filter.mp hn).2
    rw [hH0 n k]
    unfold softHost0R
    rw [ite_eq_right (fun h => by have := h.2.2; simp only [FormalResearch.JB.Chart.row, softRightChart, softJBChart] at this; omega)]
  · intro n hn k
    have hn' := (Finset.mem_filter.mp hn).2
    rw [hH1 n k]
    unfold softHost0R
    rw [ite_eq_right (fun h => by have := h.2.2; rw [hnc1] at this; simp only [FormalResearch.JB.Chart.row, softRightChart, softJBChart] at this; omega)]
  · intro i hi1 hi2
    have hn : ((i : ℕ) : ℤ) - (softLoR CR p N : ℤ) ≥ 0 := by omega
    have hlt : (((i : ℕ) : ℤ) - (softLoR CR p N : ℤ)).toNat < softRR CL CR p N := by
      have : (((((i : ℕ) : ℤ) - (softLoR CR p N : ℤ)).toNat : ℕ) : ℤ) < (softRR CL CR p N : ℤ) := by omega
      exact_mod_cast this
    refine ⟨⟨(((i : ℕ) : ℤ) - (softLoR CR p N : ℤ)).toNat, hlt⟩, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only
      omega
    · apply Fin.ext
      simp only [FormalResearch.JB.Chart.row, softRightChart, softJBChart]
      omega

end Right

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_right_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_right_ok

end FormalResearch.JacobiEigenvectors.TheoremB

end
