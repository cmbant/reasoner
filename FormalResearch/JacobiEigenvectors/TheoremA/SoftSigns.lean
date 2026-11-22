module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Count
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkNormalisation
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftEigen

/-!
# Paper J, Layer 2 (L2.C7): the sign analysis of app_thmA Step 6, part 1: abstract lemmas (`SoftSigns.lean`)

Source: `app_thmA.tex`, proof of prop:tha-W2, Step 6 ("counting"): hypotheses (ii), (iii) of `lem:tha-count`.  The statements are those of `SoftCountHyps`
(`TheoremA/SoftCountHyps.lean`); they are proved in `SoftSigns2.lean` (item (ii)), `SoftSigns3.lean` (item (iii)) and assembled in `SoftSigns4.lean`.

## Proved here (all axiom-pinned; no chart, no special function)

* `sign_const_of_cont`: a function that is continuous and non-vanishing on an order-connected set has a constant sign there (intermediate value theorem).  This is the paper's
  "`lambda_L`, `lambda_R` are real, continuous and non-vanishing in `X`, so `sigma_0` is constant" (Step 6, first paragraph).
* `pq_exact`: the exact solutions of the proof of Step 4 from the two solutions of `lem:tha-count`: for `bondA > 0`, `c_0 p_n` solves the recurrence of `F` on the rows `0 <= n < N_L <= N`
  (seed `c_0`), and `m |-> c_0' q_{N-m}` solves that of the mirror family on the rows `0 <= m < N_R <= N` (seed `c_0'`).
* `casD_row`: the Casoratian `casD` of `lem:tha-count` is `cas A p q` at every bond `k in [0, N-1]` (Green).
* `sign_core_alg`: the elementary comparison behind Step 6 (ii): if `L_j = c f_j (1 + O(theta))` at two consecutive rows with `f_0 <= (1+G) f_1`, `f_j > 0`, and `R_j > 0` decays,
  `(1 + nu) R_1 <= R_0`, then `c (L_0 R_1 - L_1 R_0) < 0` (all of `theta, G` small against `nu`).
* `casD_sign_of_rows`: the same, as a statement about `casD`: `sign casD = sign c`.

## Differences from the paper

None (the lemmas are general; the paper's argument is the Casoratian of `psi^L`, `psi^R` at a row on the right forbidden side).

## Not formalised here

The chart-level inputs (the rows, item (1), the growth of `psi^R`), in `SoftSigns2.lean`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

/-- A continuous, non-vanishing function on an order-connected set has a constant sign. -/
theorem sign_const_of_cont {S : Set ℝ} (hS : S.OrdConnected) {f : ℝ → ℝ} (hc : ContinuousOn f S)
    (hne : ∀ x ∈ S, f x ≠ 0) : (∀ x ∈ S, 0 < f x) ∨ (∀ x ∈ S, f x < 0) := by
  by_cases hpos : ∀ x ∈ S, 0 < f x
  · exact Or.inl hpos
  · right
    push_neg at hpos
    obtain ⟨a, haS, ha⟩ := hpos
    have ha' : f a < 0 := lt_of_le_of_ne ha (hne a haS)
    intro b hbS
    by_contra hb
    have hb' : 0 < f b := lt_of_le_of_ne (not_lt.mp hb) (Ne.symm (hne b hbS))
    rcases le_total a b with hab | hab
    · have hsub : Set.Icc a b ⊆ S := hS.out haS hbS
      have := intermediate_value_Icc hab (hc.mono hsub)
      obtain ⟨x, hx, hx0⟩ := this ⟨ha'.le, hb'.le⟩
      exact hne x (hsub hx) hx0
    · have hsub : Set.Icc b a ⊆ S := hS.out hbS haS
      have := intermediate_value_Icc' hab (hc.mono hsub)
      obtain ⟨x, hx, hx0⟩ := this ⟨ha'.le, hb'.le⟩
      exact hne x (hsub hx) hx0

section Exact

variable {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ)

/-- Row equation of `q` transported to the mirror family: for `0 <= k < N`, `Lop` of the mirror recurrence at `k` of `i |-> q_{N-i}` is `Lop` of `q` at row `N - k in [1, N]`. -/
lemma lop_mirror_qZ (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) (c : ℝ)
    (k : ℤ) (hk0 : 0 ≤ k) (hkN : k < (N : ℤ)) :
    Lop ((mirrorFamily F).bondA μ N) ((mirrorFamily F).diagQ μ N X) (fun i => c * qZ F μ N X ((N : ℤ) - i)) k = 0 := by
  have h := Lop_qZ hpos hN X ((N : ℤ) - k) (by omega) (by omega)
  unfold Lop at h ⊢
  simp only [bondA_mirror, diagQ_mirror]
  simp only [SymbolFamily.diagQ]
  have e1 : (N : ℤ) - 1 - k = (N : ℤ) - k - 1 := by ring
  have e2 : (N : ℤ) - 1 - (k - 1) = (N : ℤ) - k := by ring
  have e3 : (N : ℤ) - (k + 1) = (N : ℤ) - k - 1 := by ring
  have e4 : (N : ℤ) - (k - 1) = (N : ℤ) - k + 1 := by ring
  rw [e1, e2, e3, e4]
  linear_combination c * h

/-- **The exact solutions from `p`, `q`**: `c_0 p_n` solves the recurrence of `F` on the rows `0 <= n < N_L <= N`, and `m |-> c_0' q_{N-m}` that of the mirror family on the rows
`0 <= m < N_R <= N`; their seeds are `c_0`, `c_0'`. -/
theorem pq_exact (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) (c0 c0' : ℝ) (NL NR : ℤ)
    (hL : NL ≤ N) (hR : NR ≤ N) :
    JacSol F μ N X NL (fun n => c0 * pZ F μ N X n) ∧ c0 * pZ F μ N X 0 = c0 ∧
      JacSol (mirrorFamily F) μ N X NR (fun m => c0' * qZ F μ N X ((N : ℤ) - m)) ∧
      c0' * qZ F μ N X ((N : ℤ) - 0) = c0' := by
  refine ⟨?_, by rw [pZ_zero, mul_one], ?_, by simp [qZ_N]⟩
  · intro n hn0 hn1
    have h := Lop_pZ hpos hN X n hn0 (by omega)
    have h2 := Lop_smul' (F.bondA μ N) (fun n => X - F.entryB μ N n) (pZ F μ N X) c0 n
    show Lop (F.bondA μ N) (F.diagQ μ N X) (fun k => c0 * pZ F μ N X k) n = 0
    have e : F.diagQ μ N X = fun n => X - F.entryB μ N n := rfl
    rw [e, h2, h, mul_zero]
  · intro m hm0 hm1
    exact lop_mirror_qZ F μ N hpos hN X c0' m hm0 (by omega)

/-- The Casoratian `casD` of `lem:tha-count` is `cas A p q` at every bond `k in [0, N-1]` (Green). -/
theorem casD_row (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) (k : ℤ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ (N : ℤ) - 1) :
    casD F μ N X = cas (F.bondA μ N) (pZ F μ N X) (qZ F μ N X) k := by
  have hc := green_cas_const (F.bondA μ N) (F.entryB μ N) X (N : ℤ)
    (pZ F μ N X) (qZ F μ N X)
    (fun i hi => Lop_pZ hpos hN X i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2)
    (fun i hi => Lop_qZ hpos hN X i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2)
  rw [casD_eq_cas, ← hc k (mem_Icc.2 ⟨hk0, hk1⟩)]

end Exact

/-- **The comparison of Step 6 (ii)** (pure algebra).  `L_j = c f_j (1 + O(theta))` at two consecutive rows, `f_j > 0`, `f_0 <= (1+G) f_1`; `R_j > 0` with `(1+nu) R_1 <= R_0`; and
`(1+theta)(1+G) < (1-theta)(1+nu)`.  Then `c (L_0 R_1 - L_1 R_0) < 0`. -/
theorem sign_core_alg (c L0 L1 R0 R1 f0 f1 θ G ν : ℝ) (hf0 : 0 < f0) (hf1 : 0 < f1) (hff : f0 ≤ (1 + G) * f1)
    (hθ : 0 ≤ θ) (hG : 0 ≤ G) (hL0 : |L0 - c * f0| ≤ θ * |c| * f0) (hL1 : |L1 - c * f1| ≤ θ * |c| * f1)
    (hR0 : 0 < R0) (hR1 : 0 < R1) (hR : (1 + ν) * R1 ≤ R0) (hν : 0 < ν)
    (hsmall : (1 + θ) * (1 + G) < (1 - θ) * (1 + ν)) (hc : c ≠ 0) :
    c * (L0 * R1 - L1 * R0) < 0 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hcabs : |c| * |c| = c ^ 2 := by rw [← abs_mul, abs_mul_self]; ring
  -- `c L_j` against `c^2 f_j`
  have hcL0 : c * L0 ≤ (1 + θ) * (c ^ 2 * f0) := by
    have h1 : |c * (L0 - c * f0)| ≤ θ * (c ^ 2 * f0) := by
      rw [abs_mul]
      calc |c| * |L0 - c * f0| ≤ |c| * (θ * |c| * f0) := mul_le_mul_of_nonneg_left hL0 (abs_nonneg _)
        _ = θ * (|c| * |c|) * f0 := by ring
        _ = θ * (c ^ 2 * f0) := by rw [hcabs]; ring
    have h2 := (abs_le.mp h1).2
    nlinarith
  have hcL1 : (1 - θ) * (c ^ 2 * f1) ≤ c * L1 := by
    have h1 : |c * (L1 - c * f1)| ≤ θ * (c ^ 2 * f1) := by
      rw [abs_mul]
      calc |c| * |L1 - c * f1| ≤ |c| * (θ * |c| * f1) := mul_le_mul_of_nonneg_left hL1 (abs_nonneg _)
        _ = θ * (|c| * |c|) * f1 := by ring
        _ = θ * (c ^ 2 * f1) := by rw [hcabs]; ring
    have h2 := (abs_le.mp h1).1
    nlinarith
  have hθ1 : θ < 1 := by
    by_contra hcon
    have : 1 ≤ θ := not_lt.mp hcon
    nlinarith
  have hstep : (1 + θ) * f0 * R1 ≤ (1 + θ) * (1 + G) * f1 * R1 := by
    have := mul_le_mul_of_nonneg_left hff (by linarith : 0 ≤ 1 + θ)
    nlinarith [hR1]
  have hstep2 : (1 + θ) * (1 + G) * f1 * ((1 + ν) * R1) < (1 - θ) * (1 + ν) * f1 * R0 := by
    have h1 : (1 + θ) * (1 + G) * f1 * ((1 + ν) * R1) = ((1 + θ) * (1 + G)) * (1 + ν) * (f1 * R1) := by ring
    have h2 : (1 - θ) * (1 + ν) * f1 * R0 ≥ (1 - θ) * (1 + ν) * f1 * ((1 + ν) * R1) := by
      have : 0 ≤ (1 - θ) * (1 + ν) * f1 := by
        have : 0 ≤ 1 - θ := by linarith
        positivity
      exact mul_le_mul_of_nonneg_left hR this
    have h3 : (1 - θ) * (1 + ν) * f1 * ((1 + ν) * R1) = ((1 - θ) * (1 + ν)) * (1 + ν) * (f1 * R1) := by ring
    have h4 : 0 < (1 + ν) * (f1 * R1) := by positivity
    have h5 : ((1 + θ) * (1 + G)) * ((1 + ν) * (f1 * R1)) < ((1 - θ) * (1 + ν)) * ((1 + ν) * (f1 * R1)) :=
      mul_lt_mul_of_pos_right hsmall h4
    calc (1 + θ) * (1 + G) * f1 * ((1 + ν) * R1) = ((1 + θ) * (1 + G)) * ((1 + ν) * (f1 * R1)) := by ring
      _ < ((1 - θ) * (1 + ν)) * ((1 + ν) * (f1 * R1)) := h5
      _ = (1 - θ) * (1 + ν) * f1 * ((1 + ν) * R1) := by ring
      _ ≤ _ := h2
  have hpos1 : 0 < 1 + ν := by linarith
  have hstep3 : (1 + θ) * (1 + G) * f1 * R1 < (1 - θ) * f1 * R0 := by
    have : (1 + ν) * ((1 + θ) * (1 + G) * f1 * R1) < (1 + ν) * ((1 - θ) * f1 * R0) := by
      calc (1 + ν) * ((1 + θ) * (1 + G) * f1 * R1) = (1 + θ) * (1 + G) * f1 * ((1 + ν) * R1) := by ring
        _ < (1 - θ) * (1 + ν) * f1 * R0 := hstep2
        _ = (1 + ν) * ((1 - θ) * f1 * R0) := by ring
    exact lt_of_mul_lt_mul_left this hpos1.le
  have hfin : c * (L0 * R1 - L1 * R0) = (c * L0) * R1 - (c * L1) * R0 := by ring
  rw [hfin]
  have h1 : (c * L0) * R1 ≤ (1 + θ) * (c ^ 2 * f0) * R1 := mul_le_mul_of_nonneg_right hcL0 hR1.le
  have h2 : (1 - θ) * (c ^ 2 * f1) * R0 ≤ (c * L1) * R0 := mul_le_mul_of_nonneg_right hcL1 hR0.le
  have h3 : c ^ 2 * ((1 + θ) * (1 + G) * f1 * R1) < c ^ 2 * ((1 - θ) * f1 * R0) := mul_lt_mul_of_pos_left hstep3 hc2
  have h4 : c ^ 2 * ((1 + θ) * f0 * R1) ≤ c ^ 2 * ((1 + θ) * (1 + G) * f1 * R1) := mul_le_mul_of_nonneg_left hstep hc2.le
  nlinarith

/-- **`sign casD = sign c`** (Step 6 (ii), as a statement about `casD`): `psi^L = c_0 p`, `psi^R = c_0' q` positive multiples; at the bond `k` the rows satisfy the hypotheses of
`sign_core_alg`; then `sign casD = sign c`. -/
theorem casD_sign_of_rows {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ)
    (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) (c0 c0' : ℝ) (hc0 : 0 < c0) (hc0' : 0 < c0')
    (k : ℤ) (hk0 : 0 ≤ k) (hk1 : k ≤ (N : ℤ) - 1) (c f0 f1 θ G ν : ℝ) (hf0 : 0 < f0) (hf1 : 0 < f1) (hff : f0 ≤ (1 + G) * f1)
    (hθ : 0 ≤ θ) (hG : 0 ≤ G)
    (hL0 : |c0 * pZ F μ N X k - c * f0| ≤ θ * |c| * f0) (hL1 : |c0 * pZ F μ N X (k + 1) - c * f1| ≤ θ * |c| * f1)
    (hR0 : 0 < c0' * qZ F μ N X k) (hR1 : 0 < c0' * qZ F μ N X (k + 1)) (hR : (1 + ν) * (c0' * qZ F μ N X (k + 1)) ≤ c0' * qZ F μ N X k)
    (hν : 0 < ν) (hsmall : (1 + θ) * (1 + G) < (1 - θ) * (1 + ν)) (hc : c ≠ 0) :
    SignType.sign (casD F μ N X) = SignType.sign c := by
  have hA : 0 < F.bondA μ N k := hpos k hk0 (by omega)
  have hcore := sign_core_alg c (c0 * pZ F μ N X k) (c0 * pZ F μ N X (k + 1)) (c0' * qZ F μ N X k) (c0' * qZ F μ N X (k + 1))
    f0 f1 θ G ν hf0 hf1 hff hθ hG hL0 hL1 hR0 hR1 hR hν hsmall hc
  rw [casD_row F μ N hpos hN X k hk0 hk1]
  have hcas : cas (F.bondA μ N) (pZ F μ N X) (qZ F μ N X) k =
      -(F.bondA μ N k / (c0 * c0')) * ((c0 * pZ F μ N X k) * (c0' * qZ F μ N X (k + 1)) -
        (c0 * pZ F μ N X (k + 1)) * (c0' * qZ F μ N X k)) := by
    unfold cas
    field_simp
    ring
  rw [hcas]
  have hP : 0 < F.bondA μ N k / (c0 * c0') := by positivity
  set B : ℝ := (c0 * pZ F μ N X k) * (c0' * qZ F μ N X (k + 1)) - (c0 * pZ F μ N X (k + 1)) * (c0' * qZ F μ N X k) with hB
  have hcB : c * B < 0 := hcore
  rcases lt_or_gt_of_ne hc with hneg | hposc
  · have hBp : 0 < B := by nlinarith
    have : -(F.bondA μ N k / (c0 * c0')) * B < 0 := by nlinarith
    rw [sign_neg this, sign_neg hneg]
  · have hBn : B < 0 := by nlinarith
    have : 0 < -(F.bondA μ N k / (c0 * c0')) * B := by nlinarith
    rw [sign_pos this, sign_pos hposc]

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.sign_const_of_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_const_of_cont

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.pq_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pq_exact

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.casD_sign_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms casD_sign_of_rows

end FormalResearch.JacobiEigenvectors.TheoremA

end
