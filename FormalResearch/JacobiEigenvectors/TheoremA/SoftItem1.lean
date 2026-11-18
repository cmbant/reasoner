module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftLower

/-!
# Paper J, Layer 2 (L2.C6): `prop:tha-W2` item (1) on the corrected soft-edge chain (`PropThaW2Item1`, `propThaW2_item1`)

Source: Paper J `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Steps 1--3 (`eq:tha-W2-1`, `eq:tha-connect`, `eq:tha-S4grow`) and the statement `prop:tha-W2` (1) as frozen in `TheoremA/Statements.lean`.

## Proved here

* `PropThaW2Item1`: the item-(1) fragment of `PropThaW2` for the left chart `CL` (the Weber bound on `u_n <= u_c - eta/2`, the PC bound `C h^m Lm |lambda_L| M_Olv(a,-Z_n)` on `u_c - eta/2 < u_n <= u_c + 2 eta`,
  and `clam lambda kappa_bal <= |lambda_L| <= Clam lambda kappa_bal`), with the same quantifier structure as in `PropThaW2` (`Cc, h0, clam, Clam` outside `p, N`; `X` inside).
* `propThaW2_item1`: `ParabolicCylinderFacts U V cPC CPC` implies `PropThaW2Item1` for every `SoftEdgeChart` (the engine part `soft_through_edge`, the absorption and the `M_Olv` conversion `soft_pc_bound`, and the lower
  bound of `lambda_L` `soft_lamL_lower`).  Both signs of `a` are covered (the three-patch chain has `P = 3` for every `a`).

## Differences from the paper and from the frozen statement

* `ParabolicCylinderFacts U V cPC CPC` is a **hypothesis** (the frozen `PropThaW2` has none): the two-sided `M_Olv` bounds, `V_growth` (the facts that the paper takes from Olver) enter `M_-(a)`, the Casoratian of the PC pair and `eq:cha-MolvEquiv`.
* The chart has the new fields `bondA_le`, `grow_gap`, `collar_lbW`, `ratio2`, `ratioM` (see `Charts/SoftParabolicCylinder.lean`, F-W2-7, F-W2-11); the absorption threshold is `h <= softH2` (`d_+ h <= sqrt(c_{z1})/2`).
* `a <= a_+` is not assumed (the paper's Step 3 implicitly bounds `mu_0`): `muS_bd` for `r = 0` does it.
* `PropThaW2Item1` drops the hypotheses `StdAssump Fz P (q/2) r` and the right chart `CR` of `PropThaW2` (item (1) uses neither).

## Not formalised

Items (2)--(4) of `PropThaW2` (L2.C7); the chart-level derivations of the chart fields.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-- **`prop:tha-W2` (1)** for the left chart (the item-(1) fragment of `PropThaW2`). -/
def PropThaW2Item1 (Fz : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (m q : ℕ) (U V : ℝ → ℝ → ℝ)
    (CL : SoftEdgeChart Fz P m q U V) (Lm : ℝ → ℝ) : Prop :=
  1 ≤ m → (∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) →
    ∃ Cc h0 clam Clam : ℝ, 0 < h0 ∧ 0 < clam ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      (∀ ψ : ℤ → ℝ, JacSol Fz p N X (CL.chain p X N).NR ψ → ψ 0 = CL.psiHatL p X N 0 →
        (∀ k ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, uNode (Fz.step N) k ≤ CL.uc p - CL.η / 2 →
          |ψ k - CL.psiHatL p X N k| ≤ Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnvWeb CL p X N k) ∧
        (∀ k ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, CL.uc p - CL.η / 2 < uNode (Fz.step N) k → uNode (Fz.step N) k ≤ CL.uc p + 2 * CL.η →
          |ψ k - CL.psiHatL p X N k| ≤ Cc * Fz.step N ^ m * Lm (Fz.step N) * |CL.lamL p X N| * Molv U V (CL.aOf p X N) (-(CL.Zof p X N k)))) ∧
      clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) ≤ |CL.lamL p X N| ∧
      |CL.lamL p X N| ≤ Clam * (softLam CL p X N * kappaBal (CL.aOf p X N))

section Item1

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V)

/-- `M_Olv >= 0` (from the lower bound `molv_lower` and the positivity of `W_mol`). -/
lemma molv_nonneg {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (a z : ℝ) : 0 ≤ Molv U V a z := by
  have h := molv_lower hf a z
  have hW : 0 < Wmol a z := by
    by_cases hz : 0 ≤ z
    · have := Wmol_neg_of_nonpos a (z := -z) (by linarith)
      rw [neg_neg] at this
      rw [this]; exact Eminus_pos _ _
    · have := Wmol_neg_of_pos a (z := -z) (by linarith)
      rw [neg_neg] at this
      rw [this]; exact Eswap_pos _ _
  have hκ := kappaBal_pos a
  have hc := hf.cPC_pos
  have : 0 ≤ cPC * (kappaBal a)⁻¹ * Wmol a z * Mbal a z :=
    mul_nonneg (mul_nonneg (mul_nonneg hc.le (inv_nonneg.mpr hκ.le)) hW.le) (Mbal_pos a z).le
  linarith

/-- **L2.C6: `prop:tha-W2` (1) on the corrected soft-edge chain.** -/
theorem propThaW2_item1 {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (Lm : ℝ → ℝ) :
    PropThaW2Item1 Fz P m q U V C Lm := by
  intro hm hLm
  obtain ⟨Cw, h0, h0pos, H⟩ := soft_through_edge C hf hm
  obtain ⟨Cb, hb0, hb0pos, HB⟩ := soft_pc_bound C hf hm
  obtain ⟨clam, hl0, hclam, hl0pos, HL⟩ := soft_lamL_lower C hf hm
  set Cf : ℝ := max (max Cw 0) (Cb / clam) with hCf
  have hCf0 : 0 ≤ Cf := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨Cf, min (min h0 hb0) (min hl0 1), clam, C.softLamC, lt_min (lt_min h0pos hb0pos) (lt_min hl0pos one_pos), hclam, ?_⟩
  intro p hp N hN hstep X hX
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs0 : Fz.step N ≤ h0 := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsb : Fz.step N ≤ hb0 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsl : Fz.step N ≤ hl0 := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 : Fz.step N ≤ 1 := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLm1 : 1 ≤ Lm (Fz.step N) := hLm _ hh0 hs1
  obtain ⟨hlam, hup, H2⟩ := H p hp X hX N hN hs0
  have hlow := HL p hp X hX N hN hsl
  have hhm : 0 ≤ Fz.step N ^ m := pow_nonneg hh0.le m
  have hκ := kappaBal_pos (C.aOf p X N)
  refine ⟨fun ψ hJ hseed => ⟨?_, ?_⟩, hlow, hup⟩
  · intro k hk hku
    refine le_trans ((H2 ψ hJ hseed).1 k hk hku) ?_
    have hE := softEnvWeb_nonneg C p X N k
    have h1 : Cw ≤ Cf := le_trans (le_max_left _ _) (le_max_left _ _)
    have h2 : Cw * Fz.step N ^ m * softEnvWeb C p X N k ≤ Cf * Fz.step N ^ m * softEnvWeb C p X N k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hhm) hE
    have h3 : Cf * Fz.step N ^ m * softEnvWeb C p X N k ≤ Cf * Fz.step N ^ m * Lm (Fz.step N) * softEnvWeb C p X N k := by
      have : 0 ≤ Cf * Fz.step N ^ m * softEnvWeb C p X N k := mul_nonneg (mul_nonneg hCf0 hhm) hE
      nlinarith [this, hLm1]
    exact h2.trans h3
  · intro k hk hku1 hku2
    refine le_trans (HB p hp X hX N hN hsb ψ hJ hseed k hk hku1) ?_
    have hMo := molv_nonneg hf (C.aOf p X N) (-(C.Zof p X N k))
    have hlk : softLam C p X N * kappaBal (C.aOf p X N) ≤ |C.lamL p X N| / clam := by
      rw [le_div_iff₀ hclam]; linarith
    have hCb : Cb ≤ Cf * clam := by
      have : Cb / clam ≤ Cf := le_max_right _ _
      rwa [div_le_iff₀ hclam] at this
    have hT : 0 ≤ Fz.step N ^ m * Molv U V (C.aOf p X N) (-(C.Zof p X N k)) := mul_nonneg hhm hMo
    have hlam0 : 0 ≤ softLam C p X N * kappaBal (C.aOf p X N) := mul_nonneg hlam.le hκ.le
    have hlamL0 : 0 ≤ |C.lamL p X N| := abs_nonneg _
    calc Cb * Fz.step N ^ m * (softLam C p X N * kappaBal (C.aOf p X N)) * Molv U V (C.aOf p X N) (-(C.Zof p X N k))
        = Cb * (softLam C p X N * kappaBal (C.aOf p X N)) * (Fz.step N ^ m * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) := by ring
      _ ≤ (Cf * clam) * (|C.lamL p X N| / clam) * (Fz.step N ^ m * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) := by
          refine mul_le_mul_of_nonneg_right ?_ hT
          calc Cb * (softLam C p X N * kappaBal (C.aOf p X N)) ≤ (Cf * clam) * (softLam C p X N * kappaBal (C.aOf p X N)) :=
                mul_le_mul_of_nonneg_right hCb hlam0
            _ ≤ _ := mul_le_mul_of_nonneg_left hlk (by positivity)
      _ = Cf * |C.lamL p X N| * (Fz.step N ^ m * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) := by field_simp
      _ ≤ Cf * |C.lamL p X N| * Lm (Fz.step N) * (Fz.step N ^ m * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) := by
          have : 0 ≤ Cf * |C.lamL p X N| * (Fz.step N ^ m * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) :=
            mul_nonneg (mul_nonneg hCf0 hlamL0) hT
          nlinarith [this, hLm1]
      _ = _ := by ring

end Item1

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.propThaW2_item1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms propThaW2_item1

end FormalResearch.JacobiEigenvectors.TheoremA

end
