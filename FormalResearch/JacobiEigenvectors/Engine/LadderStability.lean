module

public import FormalResearch.JacobiEigenvectors.Charts.LadderChain
public import FormalResearch.JacobiEigenvectors.Engine.VolterraMulti
public import FormalResearch.JacobiEigenvectors.Engine.VolterraLadder

/-!
# Paper J engine, L1.1: stability of a chain of ladder pairs (`LadderData.Stability`)

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/engine.tex`, `thm:eng-volterra` (a) (multi-patch Casoratian--Volterra
stability, `volterra_multi`) and (b) (ladder pairs: `ladder_S1`, `ladder_S2`, `ladder_residual_interior`, `ladder_residual_hard`),
for per-patch ladders as in the chain of `Charts/LadderChain.lean`.  The statement proved is the frozen `LadderData.Stability`.

## Statement proved

`FormalResearch.JacobiEigenvectors.Charts.LadderData.stability D cs h m : D.Stability cs h m`.  For `D.Valid cs h m`, every `ψ` with
`Lh h D.A D.Q ψ k = 0` on `[s0, NR-1]`, the seed `ψ j = D.phi h 0 1 j` on `[0, s0]` and `2 K_𝔇 K_w h^m Θ ≤ c_*`, the conclusion
`D.Concl cs h m ψ` holds.

## Proof

`volterra_multi` is applied to the **common** operator `(D.A, D.Q)` and the comparison pairs `D.phi h 0`, `D.phi h 1`, with
`ω := |ω_1(h)|`, `ε := 2 K_𝔇 K_w h^m`, `K := (K_A+K_B) K_w`.  Its hypotheses are obtained patch by patch:
* (S1) and (S2) and the residuals (R) of patch `p` come from the per-patch lemmas `ladder_S1`, `ladder_S2`,
  `ladder_residual_interior` and, at the hard-edge site `k = 0` of patch `1`, `ladder_residual_hard`, applied to the ladder
  `Valid.ladder p` with its own `dd, pp, qq, Π±, w` and its own rows `AA p, BB p`;
* the bond and diagonal of patch `p`'s ladder agree with the common `D.A`, `D.Q` on the window (`Valid.A_eq`, `Valid.Q_eq`), so the
  Casoratians (`cas`) and the operators (`Lh`) of the pair agree with those of the common operator (`cas_congr_site`, `Lh_congr_site`);
* `|ω_p(h)| = |ω_1(h)|` on every patch (`Valid.omega_eq`), and `ω_1(h) ≠ 0` (`SymplecticLadder.wronsk_ne`);
* the transfer condition (S3) is `Valid.transfer` verbatim.

## Ranges (checked; no field of `Valid` had to be changed)

The bonds `[jj(p-1), jj p]` of (S1), the windows `[jj(p-1), jj p+1]` of (S2) and `Valid.cas_lb`, `Valid.A_bd`, `Valid.B_bd`, `Valid.env`
(all stated on `Icc (max (jj(p-1)) 0) (jj p + 1)`, which equals `Icc (jj(p-1)) (jj p + 1)` as `jj(p-1) ≥ 0`), the equation sites
`[eqLo s0 jj p, jj p]` of (R) (`Valid.defect0/1`), the rows `[-1, NR]` of `A_eq` and `[0, NR]` of `Q_eq` (the residual at `k` reads
`A(k-1), A(k), Q(k)` with `0 ≤ k ≤ jj p ≤ NR-1`), and `[0, NR]` for `M_pos`, `W_pos`, `W_mono` all cover what `volterra_multi` reads.

## Differences from the paper

None in the statement.  The chain is the one of `Charts/LadderChain.lean`: per-patch ladders and rows, one common operator `(A, Q)`,
one envelope family `(M, W)`, and the seed of patch 1.  `CE ≥ 0` is not a field of `ChainConsts` and is not needed by `volterra_multi`.

## Not formalised

The defect bounds `Valid.defect0/1`, the envelopes `Valid.env`, the Casoratian bound `Valid.cas_lb` and the transfer bounds
`Valid.transfer` are hypotheses (the charts of Section 3 and `thm:eng-corr`).  The bounded-overlap derivation of (S3) is not formalised.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Engine

/-- The residual operator at a site depends only on the bonds `A j`, `A (j-1)` and the diagonal `Q j`. -/
lemma Lh_congr_site {h : ℝ} {A A' Q Q' f : ℤ → ℝ} {j : ℤ} (hA : A j = A' j) (hA1 : A (j - 1) = A' (j - 1))
    (hQ : Q j = Q' j) : Lh h A Q f j = Lh h A' Q' f j := by
  unfold Lh Lop
  rw [hA, hA1, hQ]

/-- The Casoratian across the bond `j` depends only on the bond `A j`. -/
lemma cas_congr_site {A A' f g : ℤ → ℝ} {j : ℤ} (hA : A j = A' j) : cas A f g j = cas A' f g j := by
  unfold cas
  rw [hA]

namespace LadderData

/-- **Stability of a chain of ladder pairs** (`thm:eng-volterra`(a)+(b) for per-patch ladders): the frozen statement
`LadderData.Stability`, proved from `volterra_multi` and the per-patch ladder lemmas (see the module docstring). -/
theorem stability (D : LadderData) (cs : ChainConsts) (h : ℝ) (m : ℕ) : D.Stability cs h m := by
  unfold LadderData.Stability
  intro hV ψ hsol hseed hsmall
  have hh : 0 < h := hV.h_pos
  have hP : 1 ≤ D.P := hV.P_pos
  have hjj0 : D.jj 0 = 0 := hV.jj0
  have hjjmono := hV.jj_mono
  have hjjP : D.jj D.P = D.NR - 1 := hV.jj_last
  have hs0 : D.s0 = 0 ∨ D.s0 = 1 := hV.s0_cases
  have hs0nn : 0 ≤ D.s0 := by
    rcases hs0 with h0 | h0 <;> omega
  -- breakpoints
  have hjjge : ∀ p : ℕ, p ≤ D.P → 0 ≤ D.jj p := fun p hp => by
    have := jj_mono_le D.jj D.P hjjmono 0 p (Nat.zero_le _) hp
    rw [hjj0] at this
    exact this
  have hjjle : ∀ p : ℕ, p ≤ D.P → D.jj p ≤ D.NR - 1 := fun p hp => by
    have := jj_mono_le D.jj D.P hjjmono p D.P hp le_rfl
    rw [hjjP] at this
    exact this
  have hjjNR : ∀ p : ℕ, p ≤ D.P → D.jj p + 1 ≤ D.NR := fun p hp => by
    have := hjjle p hp
    omega
  have hleft : ∀ p : ℕ, 1 ≤ p → p ≤ D.P → 0 ≤ D.jj (p - 1) := fun p _ hp => hjjge (p - 1) (by omega)
  -- the window `[jj(p-1), jj p + 1]` lies in `[0, NR]`, and the max in the frozen hypotheses is `jj(p-1)`
  have hwin : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (D.jj (p - 1)) (D.jj p + 1),
      k ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1) := by
    intro p hp k hk
    have hpP := mem_Icc.mp hp
    rw [max_eq_left (hleft p hpP.1 hpP.2)]
    exact hk
  have hwinNR : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (D.jj (p - 1)) (D.jj p + 1), 0 ≤ k ∧ k ≤ D.NR := by
    intro p hp k hk
    have hpP := mem_Icc.mp hp
    have hkm := mem_Icc.mp hk
    exact ⟨le_trans (hleft p hpP.1 hpP.2) hkm.1, le_trans hkm.2 (hjjNR p hpP.2)⟩
  -- the frequency of patch 1 is nonzero
  have hωpos : 0 < |D.ω 1 h| :=
    abs_pos.mpr ((hV.ladder 1 (mem_Icc.mpr ⟨le_rfl, hP⟩)).wronsk_ne h hh)
  -- transfer of the per-patch coefficients to the common operator
  have hAeq : ∀ p ∈ Icc 1 D.P, ∀ k : ℤ, -1 ≤ k → k ≤ D.NR →
      ladderA (D.dd p) (D.pp p) (1 / 2) h k = D.A k :=
    fun p hp k h1 h2 => hV.A_eq p hp k (mem_Icc.mpr ⟨h1, h2⟩)
  have hQeq : ∀ p ∈ Icc 1 D.P, ∀ k : ℤ, 0 ≤ k → k ≤ D.NR →
      ladderQ (D.qq p) (1 / 2) h k = D.Q k :=
    fun p hp k h1 h2 => hV.Q_eq p hp k (mem_Icc.mpr ⟨h1, h2⟩)
  have hLhc : ∀ p ∈ Icc 1 D.P, ∀ (α : Fin 2) (k : ℤ), 0 ≤ k → k ≤ D.jj p →
      Lh h D.A D.Q (D.phi h α p) k
        = Lh h (ladderA (D.dd p) (D.pp p) (1 / 2) h) (ladderQ (D.qq p) (1 / 2) h) (D.phi h α p) k := by
    intro p hp α k hk0 hkj
    have hjn := hjjle p (mem_Icc.mp hp).2
    exact Lh_congr_site (hAeq p hp k (by omega) (by omega)).symm
      (hAeq p hp (k - 1) (by omega) (by omega)).symm (hQeq p hp k hk0 (by omega)).symm
  -- (S1): the Casoratian lower bound on the bonds of patch p
  have hS1 : ∀ p ∈ Icc 1 D.P, ∀ j ∈ Icc (D.jj (p - 1)) (D.jj p),
      cs.cm * |D.ω 1 h| ≤ |cas D.A (D.phi h 0 p) (D.phi h 1 p) j| := by
    intro p hp j hj
    have hpP := mem_Icc.mp hp
    have hjm := mem_Icc.mp hj
    have hj0 : 0 ≤ j := le_trans (hleft p hpP.1 hpP.2) hjm.1
    have hjN : j ≤ D.NR - 1 := le_trans hjm.2 (hjjle p hpP.2)
    have hwj : j ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1) :=
      hwin p hp j (mem_Icc.mpr ⟨hjm.1, by omega⟩)
    have hS := ladder_S1 (hV.ladder p hp) (D.AA p) (D.BB p) hh j hj0 (hV.cas_lb p hp j hwj)
    have hc := cas_congr_site (f := D.phi h 0 p) (g := D.phi h 1 p) (hAeq p hp j (by omega) (by omega))
    have hω := hV.omega_eq p hp
    rw [← hω, ← hc, mul_comm]
    exact hS
  -- (S2): envelopes of the comparison pairs
  have hφ1 : ∀ p ∈ Icc 1 D.P, ∀ j ∈ Icc (D.jj (p - 1)) (D.jj p + 1),
      |D.phi h 0 p j| ≤ (cs.KA + cs.KB) * cs.Kw * D.W j * D.M j := by
    intro p hp j hj
    have hjn := hwinNR p hp j hj
    have hWj := hV.W_pos j (mem_Icc.mpr hjn)
    have hMj := hV.M_pos j (mem_Icc.mpr hjn)
    obtain ⟨e0, -, e2, -⟩ := hV.env p hp j (hwin p hp j hj)
    exact ladder_S2 (D.AA p) (D.BB p) (D.wf p) (1 / 2) h 0 j cs.KA cs.KB cs.Kw (D.W j) (D.M j) (D.ρ j) (D.ρt j)
      cs.Kw_nonneg hWj.le hMj.le (hV.ρ_nonneg j) (hV.ρt_pos j hjn.1)
      (hV.A_bd p hp j (hwin p hp j hj)) (hV.B_bd p hp j (hwin p hp j hj)) e0 e2
  have hφ2 : ∀ p ∈ Icc 1 D.P, ∀ j ∈ Icc (D.jj (p - 1)) (D.jj p + 1),
      |D.phi h 1 p j| ≤ (cs.KA + cs.KB) * cs.Kw * (D.W j)⁻¹ * D.M j := by
    intro p hp j hj
    have hjn := hwinNR p hp j hj
    have hWj := hV.W_pos j (mem_Icc.mpr hjn)
    have hMj := hV.M_pos j (mem_Icc.mpr hjn)
    obtain ⟨-, e1, -, e3⟩ := hV.env p hp j (hwin p hp j hj)
    exact ladder_S2 (D.AA p) (D.BB p) (D.wf p) (1 / 2) h 1 j cs.KA cs.KB cs.Kw ((D.W j)⁻¹) (D.M j) (D.ρ j) (D.ρt j)
      cs.Kw_nonneg (inv_nonneg.mpr hWj.le) hMj.le (hV.ρ_nonneg j) (hV.ρt_pos j hjn.1)
      (hV.A_bd p hp j (hwin p hp j hj)) (hV.B_bd p hp j (hwin p hp j hj)) e1 e3
  -- the equation sites lie in the window of their patch
  have hkwin : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (eqLo D.s0 D.jj p) (D.jj p), k ∈ Icc (D.jj (p - 1)) (D.jj p + 1) := by
    intro p hp k hk
    have hpP := mem_Icc.mp hp
    obtain ⟨hkl, hku⟩ := mem_Icc.mp hk
    have hlo := eqLo_ge_jj_of D.s0 D.jj p hs0nn hjj0 (hleft p hpP.1 hpP.2)
    have hjn := hjjle p hpP.2
    exact mem_Icc.mpr ⟨le_trans hlo hkl, by omega⟩
  -- (R): residuals of both pairs on the equation sites
  have hr1 : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (eqLo D.s0 D.jj p) (D.jj p),
      |Lh h D.A D.Q (D.phi h 0 p) k| ≤ 2 * cs.KD * cs.Kw * h ^ m * D.ρ k * D.W k * D.M k := by
    intro p hp k hk
    have hpP := mem_Icc.mp hp
    obtain ⟨hkl, hku⟩ := mem_Icc.mp hk
    obtain ⟨hk0, hkNR⟩ := hwinNR p hp k (hkwin p hp k hk)
    have hWk := hV.W_pos k (mem_Icc.mpr ⟨hk0, hkNR⟩)
    have hMk := hV.M_pos k (mem_Icc.mpr ⟨hk0, hkNR⟩)
    obtain ⟨e0, -, e2, -⟩ := hV.env p hp k (hwin p hp k (hkwin p hp k hk))
    rw [hLhc p hp 0 k hk0 hku]
    by_cases hk1 : 1 ≤ k
    · have hpart := ladder_residual_interior (hV.ladder p hp) (D.AA p) (D.BB p) 0 k hk1 hh m cs.KD cs.Kw
        (D.ρ k) (D.ρt k) (D.W k) (D.M k) cs.KD_nonneg cs.Kw_nonneg (hV.ρ_nonneg k) hWk.le hMk.le
        (hV.defect0 p hp k hk) (hV.defect1 p hp k hk) e0 e2
      exact le_of_le_of_eq hpart (by ring)
    · have hk00 : k = 0 := by omega
      subst hk00
      have hp1 : p = 1 := by
        by_contra hne
        have h1 := eqLo_ge_one_of D.s0 D.jj p hne (hleft p hpP.1 hpP.2)
        omega
      subst hp1
      have hs0z : D.s0 = 0 := by
        rw [eqLo_one] at hkl
        omega
      have e00 : (((0 : ℤ) : ℝ) + 1 / 2) * h = 1 / 2 * h := by simp
      have hD0 := hV.defect0 1 hp 0 hk
      have hD1 := hV.defect1 1 hp 0 hk
      rw [e00] at hD0 hD1 e0 e2
      have hW0 := hV.W_pos 0 (mem_Icc.mpr ⟨le_rfl, by have := hjjNR 1 hP; have := hjjge 1 hP; omega⟩)
      have hM0 := hV.M_pos 0 (mem_Icc.mpr ⟨le_rfl, by have := hjjNR 1 hP; have := hjjge 1 hP; omega⟩)
      have hpart := ladder_residual_hard (hV.ladder 1 hp) (D.AA 1) (D.BB 1) hh m cs.KD cs.Kw (D.ρ 0) (D.ρt 0)
        (D.W 0) (D.M 0) cs.KD_nonneg cs.Kw_nonneg (hV.ρ_nonneg 0) hW0.le hM0.le (hV.D_hard hs0z) (hV.annih hs0z)
        hD0 hD1 e0 e2
      exact le_of_le_of_eq hpart (by ring)
  have hr2 : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (eqLo D.s0 D.jj p) (D.jj p), k ≠ 0 →
      |Lh h D.A D.Q (D.phi h 1 p) k| ≤ 2 * cs.KD * cs.Kw * h ^ m * D.ρ k * (D.W k)⁻¹ * D.M k := by
    intro p hp k hk hk0'
    have hpP := mem_Icc.mp hp
    obtain ⟨hkl, hku⟩ := mem_Icc.mp hk
    have hlo0 := eqLo_nonneg_of D.s0 D.jj p hs0nn (hleft p hpP.1 hpP.2)
    have hk0 : 0 ≤ k := le_trans hlo0 hkl
    have hk1 : 1 ≤ k := by omega
    obtain ⟨-, hkNR⟩ := hwinNR p hp k (hkwin p hp k hk)
    have hWk := hV.W_pos k (mem_Icc.mpr ⟨hk0, hkNR⟩)
    have hMk := hV.M_pos k (mem_Icc.mpr ⟨hk0, hkNR⟩)
    obtain ⟨-, e1, -, e3⟩ := hV.env p hp k (hwin p hp k (hkwin p hp k hk))
    rw [hLhc p hp 1 k hk0 hku]
    have hpart := ladder_residual_interior (hV.ladder p hp) (D.AA p) (D.BB p) 1 k hk1 hh m cs.KD cs.Kw
      (D.ρ k) (D.ρt k) ((D.W k)⁻¹) (D.M k) cs.KD_nonneg cs.Kw_nonneg (hV.ρ_nonneg k) (inv_nonneg.mpr hWk.le) hMk.le
      (hV.defect0 p hp k hk) (hV.defect1 p hp k hk) e1 e3
    exact le_of_le_of_eq hpart (by ring)
  -- apply the multi-patch theorem
  have hK : 0 ≤ (cs.KA + cs.KB) * cs.Kw := mul_nonneg (add_nonneg cs.KA_nonneg cs.KB_nonneg) cs.Kw_nonneg
  have hε : 0 ≤ 2 * cs.KD * cs.Kw * h ^ m :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two cs.KD_nonneg) cs.Kw_nonneg) (pow_nonneg hh.le m)
  obtain ⟨c1, c2, c3⟩ := volterra_multi h (|D.ω 1 h|) cs.cm cs.CE ((cs.KA + cs.KB) * cs.Kw)
    (2 * cs.KD * cs.Kw * h ^ m) cs.Λ D.A D.Q ψ D.ρ D.M D.W D.s0 D.NR D.P D.jj (D.phi h 0) (D.phi h 1)
    hh hωpos cs.cm_pos hK hε cs.Λ_ge hP hjj0 hjjmono hjjP hs0 hV.A_hard hS1 hV.M_pos hV.W_pos hV.W_mono
    hφ1 hφ2 hV.ρ_nonneg hr1 hr2 hV.transfer hsol hseed hsmall
  unfold LadderData.Concl
  exact ⟨c1, c2, c3⟩

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.LadderData.stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.LadderData.stability

end LadderData

end FormalResearch.JacobiEigenvectors.Charts

end
