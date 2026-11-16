module

public import FormalResearch.Racah.P2AnalyticLeading6jChambers
public import FormalResearch.Racah.P2AnalyticBridge6j

/-!
# `eq:WignerJacobiMonic6j` in every chamber (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:WignerJacobiMonic6j`:
`d^f_{nm}(arccos x) = k_{6j} W_{6j}(x) P̂^{(p_min,p_max)}_{f-f_0}(ς)`, `k_{6j} = ε(n,m) κ_{f-f_0}(p_min,p_max)`
(the paper states "in the canonical chamber `m ≥ |n|` one has `ε(n,m) = 1`").

`wignerD6_eq_kLead_mul_monic` (`P2AnalyticLeading`) is the canonical chamber.  Here `dZero6` (the `t = 0`
carrier, all chambers) is written as the chamber sign times the canonical one (`dZero6_eq_chamberSign_mul`) and
`wignerD6_eq_kLeadAll_mul_monic` gives the all-chamber statement with `k_{6j} = kLeadAll m n f = ε(n,m) κ_d(p,q)`
(`kLeadAll_eq_signE3_mul_kappa`), `p = |m-n|`, `q = |m+n|`, `d = ⌊f - max(|m|,|n|)⌋₊`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

/-- The `t = 0` carrier of every chamber is the chamber sign times that of the canonically reduced data. -/
theorem dZero6_eq_chamberSign_mul (f m n : ℚ) (x : ℝ) :
    dZero6 f m n x = chamberSign m n * dZero6c (chamberM m n) (chamberN m n) ⌊f - chamberM m n⌋₊ x := by
  unfold dZero6 chamberSign chamberM chamberN
  by_cases c1 : |n| ≤ m
  · simp [c1]
  by_cases c2 : |n| ≤ -m
  · simp [c1, c2, sub_neg_eq_add]
  by_cases c3 : |m| ≤ n
  · simp [c1, c2, c3]
  · simp [c1, c2, c3, sub_neg_eq_add]

/-- **`eq:WignerJacobiMonic6j`, every chamber.**  For `f ± m`, `f ± n` natural, `p = |m-n|`, `q = |m+n|`,
`x ∈ [-1,1]`: `d^f_{nm}(arccos x) = k_{6j} W_{6j}(x) P̂_d^{(p,q)}((1-x)/2)`, `k_{6j} = kLeadAll m n f
= ε(n,m) κ_d(p,q)`, `d = ⌊f - max(|m|,|n|)⌋₊`, `W_{6j} = Wedge p q`. -/
theorem wignerD6_eq_kLeadAll_mul_monic (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    wignerSmallDx f n m x =
      kLeadAll m n f * Wedge p q x *
        (jacobiMonicTau p q ⌊f - chamberM m n⌋₊).eval ((1 - x) / 2) := by
  obtain ⟨h1, h2⟩ := chamber_labels m n p q hp hq
  rw [← dZero6_eq_wignerD f m n n1 n2 n3 n4 hx, dZero6_eq_chamberSign_mul,
    dZero6c_eq_wignerD _ _ p q h1 h2 hx, wignerD6_eq_kLead_mul_monic _ _ p q h1 h2 _ hx]
  unfold kLeadAll
  ring

/-- The same with the paper's `k_{6j} = ε(n,m) κ_d(p,q)` written out (`eq:kconstants`). -/
theorem wignerD6_eq_signE3_mul_kappa (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    wignerSmallDx f n m x =
      signE3 n m p * kappaJac p q ⌊f - max |m| |n|⌋₊ * Wedge p q x *
        (jacobiMonicTau p q ⌊f - max |m| |n|⌋₊).eval ((1 - x) / 2) := by
  rw [wignerD6_eq_kLeadAll_mul_monic f m n n1 n2 n3 n4 p q hp hq hx,
    kLeadAll_eq_signE3_mul_kappa m n f p q hp hq, chamberM_eq_max]

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.wignerD6_eq_kLeadAll_mul_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.wignerD6_eq_kLeadAll_mul_monic

/-- info: 'FormalResearch.Racah.wignerD6_eq_signE3_mul_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.wignerD6_eq_signE3_mul_kappa
