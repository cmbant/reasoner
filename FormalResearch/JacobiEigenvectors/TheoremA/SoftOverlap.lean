module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftRescale

/-!
# Paper J, Layer 2 (L2.C6, engine part): (S3) at an overlap, derived (`PreValid`)

Source: Paper J `engine.tex`, `thm:eng-volterra` and the remark after (S3): case (i) (*bounded* overlap, the transfer matrix is an explicit bounded matrix) and case (ii)
(*forbidden* overlap: comparable weights and `A M M <= C_omega omega`); `app_thmA.tex`, "The soft edges", Steps 2--3.

## Proved here (all unconditional statements about `LadderData`; no chart hypothesis)

* `TransferAtΛ.mono`, `PreValid.withΛ`, `PreValid.toValid`: (S3) with a larger constant; `PreValid` does not mention `cs.Λ`, so `Valid` for the constants `{cs with Λ := Λ'}` is `PreValid` plus (S3) at every overlap.
* `PreValid.transferAt_forbidden` (case (ii)): from `PreValid` and, at one overlap bond `j_p`, `A_{j_p} > 0`, `W_{j_p+1} <= C_w W_{j_p}` and `A_{j_p} M_{j_p} M_{j_p+1} <= C_omega omega_*`, the transfer condition (S3) at `p`
  with `Lambda = max 1 (2 K^2 max(C_w, C_E) C_omega / c_-)` (this is `Engine.transfer_of_forbidden_overlap`, whose envelope and Casoratian inputs are the `PreValid` fields `env`, `A_bd`, `B_bd`, `cas_lb`).
* `transMat_of_linear`, `TransferAtΛ_of_linear` (case (i)): if the pair of patch `p+1` is a constant-coefficient combination `(a, b; c, d)` of the pair of patch `p` at the two sites of the overlap bond, with `a d - b c = 1`, then
  `transMat = [[d, -b], [-c, a]]` (the inverse matrix), hence (S3) holds as soon as `|a|, |d| <= Lambda`, `|b| <= Lambda W^{-2}`, `|c| <= Lambda W^2`.

## Differences from the paper

`Lambda` is derived with the explicit constant of `transfer_of_forbidden_overlap` (the paper only says `Lambda` depends on the stated constants).  Nothing is added to `PreValid`.

## Not formalised

The chart-level verification of the hypotheses (`TheoremA/SoftTransfer.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Engine

namespace LadderData

variable {D : LadderData}

lemma TransferAtΛ.mono {Λ Λ' h : ℝ} {p : ℕ} (hΛ : 0 < Λ) (hle : Λ ≤ Λ') (hT : D.TransferAtΛ Λ h p) :
    D.TransferAtΛ Λ' h p := by
  obtain ⟨a, b, c, d, e⟩ := hT
  refine ⟨(inv_anti₀ hΛ hle).trans a, b.trans hle, c.trans hle, ?_, ?_⟩
  · exact d.trans (mul_le_mul_of_nonneg_right hle (by positivity))
  · exact e.trans (mul_le_mul_of_nonneg_right hle (by positivity))

/-- `PreValid` does not mention `cs.Λ`. -/
lemma PreValid.withΛ {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.PreValid cs h m) (Λ' : ℝ) (hΛ : 1 ≤ Λ') :
    D.PreValid { cs with Λ := Λ', Λ_ge := hΛ } h m := { hV with }

/-- `Valid` for the constants with `Λ` replaced by `Λ'`: `PreValid` and (S3) with `Λ'` at every overlap. -/
lemma PreValid.toValid {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.PreValid cs h m) (Λ' : ℝ) (hΛ : 1 ≤ Λ')
    (hT : ∀ p, 1 ≤ p → p < D.P → D.TransferAtΛ Λ' h p) :
    D.Valid { cs with Λ := Λ', Λ_ge := hΛ } h m :=
  { hV.withΛ Λ' hΛ with transfer := hT }

/-- The bond is non-zero where the Casoratian of the pair of patch `p` is bounded below (`(S1)`: `A_j = 0` would force `cas = 0`). -/
lemma PreValid.A_ne_zero {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.PreValid cs h m) {p : ℕ} (hp : p ∈ Icc 1 D.P) {j : ℤ}
    (hj : j ∈ Icc (D.jj (p - 1)) (D.jj p)) : D.A j ≠ 0 := by
  intro h0
  have hωpos : 0 < |D.ω 1 h| :=
    abs_pos.mpr ((hV.ladder 1 (mem_Icc.mpr ⟨le_rfl, by have := (mem_Icc.mp hp).1; have := (mem_Icc.mp hp).2; omega⟩)).wronsk_ne h hV.h_pos)
  have h1 := hV.cas_lb_site hp hj
  have hc0 : cas D.A (D.phi h 0 p) (D.phi h 1 p) j = 0 := by
    unfold cas
    rw [h0]
    ring
  rw [hc0, abs_zero] at h1
  exact absurd h1 (not_le.mpr (mul_pos cs.cm_pos hωpos))

/-- The `2 x 2` determinant of the pair of patch `p` at the sites `j, j+1` is non-zero where `(S1)` holds. -/
lemma PreValid.det_ne_zero {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.PreValid cs h m) {p : ℕ} (hp : p ∈ Icc 1 D.P) {j : ℤ}
    (hj : j ∈ Icc (D.jj (p - 1)) (D.jj p)) :
    D.phi h 0 p j * D.phi h 1 p (j + 1) - D.phi h 1 p j * D.phi h 0 p (j + 1) ≠ 0 := by
  intro h0
  have hωpos : 0 < |D.ω 1 h| :=
    abs_pos.mpr ((hV.ladder 1 (mem_Icc.mpr ⟨le_rfl, by have := (mem_Icc.mp hp).1; have := (mem_Icc.mp hp).2; omega⟩)).wronsk_ne h hV.h_pos)
  have h1 := hV.cas_lb_site hp hj
  have hc0 : cas D.A (D.phi h 0 p) (D.phi h 1 p) j = 0 := by
    unfold cas
    have : D.phi h 0 p (j + 1) * D.phi h 1 p j - D.phi h 0 p j * D.phi h 1 p (j + 1) = 0 := by linarith
    rw [this, mul_zero]
  rw [hc0, abs_zero] at h1
  exact absurd h1 (not_le.mpr (mul_pos cs.cm_pos hωpos))

/-- **Case (ii) of (S3): a forbidden overlap** (`engine.tex` after `thm:eng-volterra`), from `PreValid` and the three overlap conditions at the bond `j_p`. -/
theorem PreValid.transferAt_forbidden {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.PreValid cs h m)
    {p : ℕ} (hp1 : 1 ≤ p) (hpP : p < D.P) (Cw Cω : ℝ)
    (hA : 0 < D.A (D.jj p)) (hw : D.W (D.jj p + 1) ≤ Cw * D.W (D.jj p))
    (hAM : D.A (D.jj p) * (D.M (D.jj p) * D.M (D.jj p + 1)) ≤ Cω * |D.ω 1 h|) :
    D.TransferAtΛ (max 1 (2 * ((cs.KA + cs.KB) * cs.Kw) ^ 2 * max Cw cs.CE * Cω / cs.cm)) h p := by
  have hjmono := hV.jj_mono
  have hj0 : 0 ≤ D.jj p := hV.jj_nonneg hpP.le
  have hjle : D.jj p ≤ D.NR - 1 := hV.jj_le hpP.le
  have hjm : D.jj p < D.jj (p + 1) := hjmono p hpP
  have hjm' : D.jj (p - 1) ≤ D.jj p := jj_mono_le D.jj D.P hjmono (p - 1) p (by omega) hpP.le
  have hmemj : D.jj p ∈ Icc (0 : ℤ) D.NR := mem_Icc.mpr ⟨hj0, by omega⟩
  have hmemj1 : D.jj p + 1 ∈ Icc (0 : ℤ) D.NR := mem_Icc.mpr ⟨by omega, by omega⟩
  have hWj := hV.W_pos _ hmemj
  have hW1 := hV.W_pos _ hmemj1
  have hK : 0 ≤ (cs.KA + cs.KB) * cs.Kw := mul_nonneg (add_nonneg cs.KA_nonneg cs.KB_nonneg) cs.Kw_nonneg
  have hωpos : 0 < |D.ω 1 h| :=
    abs_pos.mpr ((hV.ladder 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)).wronsk_ne h hV.h_pos)
  have hw1 : D.W (D.jj p + 1) ≤ max Cw cs.CE * D.W (D.jj p) :=
    hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWj.le)
  have hw2 : D.W (D.jj p) ≤ max Cw cs.CE * D.W (D.jj p + 1) :=
    (hV.W_mono _ hmemj _ hmemj1 (by omega)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hW1.le)
  have hpP' : p ∈ Icc 1 D.P := mem_Icc.mpr ⟨hp1, hpP.le⟩
  have hp1P : p + 1 ∈ Icc 1 D.P := mem_Icc.mpr ⟨by omega, hpP⟩
  have e : (p + 1 - 1) = p := by omega
  have hmain := transfer_of_forbidden_overlap (D.phi h 0) (D.phi h 1) D.jj p D.A D.W D.M |D.ω 1 h| cs.cm
    ((cs.KA + cs.KB) * cs.Kw) (max Cw cs.CE) Cω hA hωpos cs.cm_pos hK hWj hW1 (hV.M_pos _ hmemj) (hV.M_pos _ hmemj1)
    hw1 hw2 hAM
    (by
      intro q hq
      rcases hq with rfl | rfl
      · obtain ⟨a1, a2⟩ := hV.phi_bd hpP' (j := D.jj q) (mem_Icc.mpr ⟨hjm', by omega⟩)
        obtain ⟨b1, b2⟩ := hV.phi_bd hpP' (j := D.jj q + 1) (mem_Icc.mpr ⟨by omega, le_rfl⟩)
        exact ⟨a1, a2, b1, b2⟩
      · obtain ⟨a1, a2⟩ := hV.phi_bd hp1P (j := D.jj p) (mem_Icc.mpr ⟨by rw [e], by omega⟩)
        obtain ⟨b1, b2⟩ := hV.phi_bd hp1P (j := D.jj p + 1) (mem_Icc.mpr ⟨by rw [e]; omega, by omega⟩)
        exact ⟨a1, a2, b1, b2⟩)
    (by
      intro q hq
      rcases hq with rfl | rfl
      · exact hV.cas_lb_site hpP' (j := D.jj q) (mem_Icc.mpr ⟨hjm', le_rfl⟩)
      · exact hV.cas_lb_site hp1P (j := D.jj p) (mem_Icc.mpr ⟨by rw [e], hjm.le⟩))
  exact hmain

/-- **Case (i) of (S3), algebra**: if the pair of patch `p+1` is the constant combination `(a, b; c, d)` (`det = 1`) of the pair of patch `p` at the two sites `j_p, j_p+1`, then the transfer matrix is
the inverse matrix `[[d, -b], [-c, a]]`. -/
lemma transMat_of_linear (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ) (a b c d : ℝ) (hdet : a * d - b * c = 1)
    (h0 : φ1 (p + 1) (jj p) = a * φ1 p (jj p) + c * φ2 p (jj p))
    (h0' : φ1 (p + 1) (jj p + 1) = a * φ1 p (jj p + 1) + c * φ2 p (jj p + 1))
    (h1 : φ2 (p + 1) (jj p) = b * φ1 p (jj p) + d * φ2 p (jj p))
    (h1' : φ2 (p + 1) (jj p + 1) = b * φ1 p (jj p + 1) + d * φ2 p (jj p + 1))
    (hne : φ1 p (jj p) * φ2 p (jj p + 1) - φ2 p (jj p) * φ1 p (jj p + 1) ≠ 0) :
    transMat φ1 φ2 jj p 0 0 = d ∧ transMat φ1 φ2 jj p 0 1 = -b ∧ transMat φ1 φ2 jj p 1 0 = -c ∧
      transMat φ1 φ2 jj p 1 1 = a ∧ (transMat φ1 φ2 jj p).det = 1 := by
  obtain ⟨e00, e01, e10, e11, edet⟩ := transMat_entries φ1 φ2 jj p
  set x1 := φ1 p (jj p)
  set x2 := φ1 p (jj p + 1)
  set y1 := φ2 p (jj p)
  set y2 := φ2 p (jj p + 1)
  have hD : φ1 (p + 1) (jj p) * φ2 (p + 1) (jj p + 1) - φ2 (p + 1) (jj p) * φ1 (p + 1) (jj p + 1)
      = x1 * y2 - y1 * x2 := by
    rw [h0, h0', h1, h1']
    linear_combination (x1 * y2 - y1 * x2) * hdet
  rw [hD] at e00 e01 e10 e11 edet
  simp only [h0, h0', h1, h1'] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e00, div_eq_iff hne]; ring
  · rw [e01, div_eq_iff hne]; ring
  · rw [e10, div_eq_iff hne]; ring
  · rw [e11, div_eq_iff hne]; ring
  · rw [edet, div_eq_one_iff_eq hne]

/-- **Case (i) of (S3)**: the algebra of `transMat_of_linear` and the bounds on the coefficients give (S3) at the overlap `p`. -/
lemma TransferAtΛ_of_linear {h : ℝ} {p : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) (a b c d : ℝ) (hdet : a * d - b * c = 1)
    (h0 : D.phi h 0 (p + 1) (D.jj p) = a * D.phi h 0 p (D.jj p) + c * D.phi h 1 p (D.jj p))
    (h0' : D.phi h 0 (p + 1) (D.jj p + 1) = a * D.phi h 0 p (D.jj p + 1) + c * D.phi h 1 p (D.jj p + 1))
    (h1 : D.phi h 1 (p + 1) (D.jj p) = b * D.phi h 0 p (D.jj p) + d * D.phi h 1 p (D.jj p))
    (h1' : D.phi h 1 (p + 1) (D.jj p + 1) = b * D.phi h 0 p (D.jj p + 1) + d * D.phi h 1 p (D.jj p + 1))
    (hne : D.phi h 0 p (D.jj p) * D.phi h 1 p (D.jj p + 1) - D.phi h 1 p (D.jj p) * D.phi h 0 p (D.jj p + 1) ≠ 0)
    (ha : |a| ≤ Λ) (hb : |b| ≤ Λ * (D.W (D.jj p) ^ 2)⁻¹) (hc : |c| ≤ Λ * D.W (D.jj p) ^ 2) (hd : |d| ≤ Λ) :
    D.TransferAtΛ Λ h p := by
  obtain ⟨t00, t01, t10, t11, tdet⟩ := transMat_of_linear (D.phi h 0) (D.phi h 1) D.jj p a b c d hdet h0 h0' h1 h1' hne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [tdet, abs_one]
    exact inv_le_one_of_one_le₀ hΛ
  · rw [t00]; exact hd
  · rw [t11]; exact ha
  · rw [t01, abs_neg]; exact hb
  · rw [t10, abs_neg]; exact hc

/-- **The comparison sequences of two patches that differ by a constant unimodular combination agree** (`psi-hat_3 = psi-hat_2`, R2): if the pair of patch `3` is the combination `(a, b; c, d)`, `a d - b c = 1`, of the pair of
patch `2` at the sites `j_2, j_2 + 1` and at the site `j`, then `psi-hat_3(j) = psi-hat_2(j)` (`c_3 = M_2 c_2`, `M_2 = [[d, -b], [-c, a]]`). -/
lemma psiHat_three_of_linear (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (a b c d : ℝ) (hdet : a * d - b * c = 1)
    (h0 : φ1 3 (jj 2) = a * φ1 2 (jj 2) + c * φ2 2 (jj 2))
    (h0' : φ1 3 (jj 2 + 1) = a * φ1 2 (jj 2 + 1) + c * φ2 2 (jj 2 + 1))
    (h1 : φ2 3 (jj 2) = b * φ1 2 (jj 2) + d * φ2 2 (jj 2))
    (h1' : φ2 3 (jj 2 + 1) = b * φ1 2 (jj 2 + 1) + d * φ2 2 (jj 2 + 1))
    (hne : φ1 2 (jj 2) * φ2 2 (jj 2 + 1) - φ2 2 (jj 2) * φ1 2 (jj 2 + 1) ≠ 0) (j : ℤ)
    (hj0 : φ1 3 j = a * φ1 2 j + c * φ2 2 j) (hj1 : φ2 3 j = b * φ1 2 j + d * φ2 2 j) :
    Engine.psiHat φ1 φ2 jj 3 j = Engine.psiHat φ1 φ2 jj 2 j := by
  obtain ⟨t00, t01, t10, t11, -⟩ := transMat_of_linear φ1 φ2 jj 2 a b c d hdet h0 h0' h1 h1' hne
  have hc : cvec φ1 φ2 jj 3 = mulMV (transMat φ1 φ2 jj 2) (cvec φ1 φ2 jj 2) := cvec_succ_succ φ1 φ2 jj 1
  unfold Engine.psiHat
  rw [hc, hj0, hj1]
  simp only [mulMV, Matrix.cons_val_zero, Matrix.cons_val_one, t00, t01, t10, t11]
  linear_combination (cvec φ1 φ2 jj 2 0 * φ1 2 j + cvec φ1 φ2 jj 2 1 * φ2 2 j) * hdet

end LadderData

end FormalResearch.JacobiEigenvectors.Charts
