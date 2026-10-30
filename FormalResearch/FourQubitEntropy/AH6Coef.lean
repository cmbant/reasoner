import FormalResearch.FourQubitEntropy.AH6Joint
import FormalResearch.FourQubitEntropy.SevenQubitJointMajorant

/-!
# The coefficients `h_{kl}` of `H` and the statement for `polyH`

`H(λ,μ) = P(e) + v A(e) + v² B(e) = ∑_{k+l ≤ 5} h_{kl} λ^k μ^l` (`e = 4(λ+μ)`, `v = 16(λ-μ)²`).  `hcoef` is the
explicit table of the 21 coefficients in terms of the coefficients `P₀..P₅` of the Hermite polynomial, `α₀..α₃` and
`β₀, β₁` (computed by expanding the binomials); `polyH_jointCoef` is the identity
`polyH degFive (jointCoef x) = H`.
-/

namespace FormalResearch.FourQubitEntropy.AH6

open FormalResearch.FourQubitEntropy.SevenQubitConseq.JointMajorant

/-- The table of the 21 coefficients `h_{kl}`, `k + l ≤ 5`. -/
def hcoef (P0 P1 P2 P3 P4 P5 a0 a1 a2 a3 b0 b1 : ℝ) (k l : ℕ) : ℝ :=
  match k, l with
  | 0, 0 => P0
  | 0, 1 => 4*P1
  | 0, 2 => 16*P2 + 16*a0
  | 0, 3 => 64*P3 + 64*a1
  | 0, 4 => 256*P4 + 256*a2 + 256*b0
  | 0, 5 => 1024*P5 + 1024*a3 + 1024*b1
  | 1, 0 => 4*P1
  | 1, 1 => 32*P2 - 32*a0
  | 1, 2 => 192*P3 - 64*a1
  | 1, 3 => 1024*P4 - 1024*b0
  | 1, 4 => 5120*P5 + 1024*a3 - 3072*b1
  | 2, 0 => 16*P2 + 16*a0
  | 2, 1 => 192*P3 - 64*a1
  | 2, 2 => 1536*P4 - 512*a2 + 1536*b0
  | 2, 3 => 10240*P5 - 2048*a3 + 2048*b1
  | 3, 0 => 64*P3 + 64*a1
  | 3, 1 => 1024*P4 - 1024*b0
  | 3, 2 => 10240*P5 - 2048*a3 + 2048*b1
  | 4, 0 => 256*P4 + 256*a2 + 256*b0
  | 4, 1 => 5120*P5 + 1024*a3 - 3072*b1
  | 5, 0 => 1024*P5 + 1024*a3 + 1024*b1
  | _, _ => 0

theorem polyH_hcoef (P0 P1 P2 P3 P4 P5 a0 a1 a2 a3 b0 b1 l m : ℝ) :
    polyH degFive (hcoef P0 P1 P2 P3 P4 P5 a0 a1 a2 a3 b0 b1) l m =
      (P0 + P1 * (4 * (l + m)) + P2 * (4 * (l + m)) ^ 2 + P3 * (4 * (l + m)) ^ 3 +
        P4 * (4 * (l + m)) ^ 4 + P5 * (4 * (l + m)) ^ 5) +
      16 * (l - m) ^ 2 * (a0 + a1 * (4 * (l + m)) + a2 * (4 * (l + m)) ^ 2 + a3 * (4 * (l + m)) ^ 3) +
      (16 * (l - m) ^ 2) ^ 2 * (b0 + b1 * (4 * (l + m))) := by
  have hK : degFive = ({(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
      (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (5, 0)} : Finset (ℕ × ℕ)) := by
    decide
  rw [polyH, hK]
  simp [Finset.sum_insert, hcoef]
  ring


theorem length_scaleL (c : ℝ) (p : List ℝ) : (scaleL c p).length = p.length := by simp [scaleL]

theorem length_addL (p q : List ℝ) : (addL p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [addL]
  | cons a p ih =>
    cases q with
    | nil => simp [addL]
    | cons b q => simp [addL, ih]

theorem length_mulL (p q : List ℝ) (hp : p ≠ []) (hq : q ≠ []) :
    (mulL p q).length = p.length + q.length - 1 := by
  induction p with
  | nil => exact absurd rfl hp
  | cons a p ih =>
    by_cases hp' : p = []
    · subst hp'
      have hql : 0 < q.length := List.length_pos_iff.2 hq
      simp [mulL, length_addL, length_scaleL]
      omega
    · have := ih hp'
      have hpl : 0 < p.length := List.length_pos_iff.2 hp'
      have hql : 0 < q.length := List.length_pos_iff.2 hq
      simp [mulL, length_addL, length_scaleL, this]
      omega

theorem length_stageB_P (s : StA ℝ) : (stageB s).P.length = 6 := by
  have h1 : ([-s.n1, ic 1] : List ℝ).length = 2 := rfl
  have h2 : (mulL [-s.n1, ic 1] [-s.n1, ic 1]).length = 3 := by
    rw [length_mulL _ _ (by simp) (by simp)]; rfl
  have h3 : (mulL (mulL [-s.n1, ic 1] [-s.n1, ic 1]) [-s.n2, ic 1]).length = 4 := by
    rw [length_mulL _ _ (by intro h; rw [h] at h2; simp at h2) (by simp), h2]; rfl
  have h4 : (mulL (mulL (mulL [-s.n1, ic 1] [-s.n1, ic 1]) [-s.n2, ic 1]) [-s.n2, ic 1]).length = 5 := by
    rw [length_mulL _ _ (by intro h; rw [h] at h3; simp at h3) (by simp), h3]; rfl
  have h5 : (mulL (mulL (mulL (mulL [-s.n1, ic 1] [-s.n1, ic 1]) [-s.n2, ic 1]) [-s.n2, ic 1])
      [-s.n3, ic 1]).length = 6 := by
    rw [length_mulL _ _ (by intro h; rw [h] at h4; simp at h4) (by simp), h4]; rfl
  simp only [stageB, length_addL, length_scaleL, h1, h2, h3, h4, h5]
  simp

theorem eval6 (l : List ℝ) (h : l.length = 6) (e : ℝ) :
    evalL l e = l.getD 0 0 + l.getD 1 0 * e + l.getD 2 0 * e ^ 2 + l.getD 3 0 * e ^ 3 +
      l.getD 4 0 * e ^ 4 + l.getD 5 0 * e ^ 5 := by
  match l, h with
  | [a, b, c, d, f, g], _ =>
    simp only [evalL, ic_real, List.getD_cons_zero, List.getD_cons_succ]
    push_cast; ring

/-- The coefficients `h_{kl}` of `H` for the parameter `x` (in nats). -/
noncomputable def jointCoef (x : ℝ) : ℕ → ℕ → ℝ :=
  hcoef ((rB (parR x)).P.getD 0 0) ((rB (parR x)).P.getD 1 0) ((rB (parR x)).P.getD 2 0)
    ((rB (parR x)).P.getD 3 0) ((rB (parR x)).P.getD 4 0) ((rB (parR x)).P.getD 5 0)
    (rC2 (parR x)).a0 (rC2 (parR x)).a1 (rC1 (parR x)).a2 (rC1 (parR x)).a3
    (rC2 (parR x)).b0 (rC1 (parR x)).b1

theorem polyH_jointCoef (x l m : ℝ) :
    polyH degFive (jointCoef x) l m = (majD (parR x)).H l m := by
  unfold jointCoef
  rw [polyH_hcoef]
  have hP : ∀ e, (majD (parR x)).P e = (rB (parR x)).P.getD 0 0 + (rB (parR x)).P.getD 1 0 * e +
      (rB (parR x)).P.getD 2 0 * e ^ 2 + (rB (parR x)).P.getD 3 0 * e ^ 3 +
      (rB (parR x)).P.getD 4 0 * e ^ 4 + (rB (parR x)).P.getD 5 0 * e ^ 5 := fun e =>
    eval6 _ (length_stageB_P _) e
  unfold MajData.H
  rw [hP]
  simp only [majD, evalL, ic_real]
  push_cast
  ring

end FormalResearch.FourQubitEntropy.AH6
