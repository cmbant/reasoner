module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ODEFlow
public import FormalResearch.JacobiEigenvectors.Charts.PCActual
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvelopeAssembled
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Engine.Defect

/-!
# Paper J, charts (WP1a): the parabolic-cylinder symplectic ladder and envelopes

Formalises:
* `charts.tex` `eq:cha-PC`: `pc_symplecticLadder` for any interior coordinate `ζ : ℝ → ℝ`,
  even shift `μh : ℝ → ℝ` (`μh(-h) = μh(h)`), and Wronskian-1 `(w0, w1)` solution pair of
  `w'' = (z^2/4 + a) w`, matching `pcMinus pcU pcV` (`a ≤ 0` and `a > 0`), `pcSwap pcU pcV`,
  and `(pcU, √(π/2) pcV)`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Engine

def ddPC (_ _ : ℝ) : ℝ := 1
def d2PC (_ _ : ℝ) : ℝ := 1

def qPC (ζ : ℝ → ℝ) (μh : ℝ → ℝ) (u h s : ℝ) : ℝ :=
  (ζ u + h * s) ^ 2 / 4 - μh h

lemma continuous_qPC (ζ μh : ℝ → ℝ) (u h : ℝ) : Continuous (qPC ζ μh u h) := by
  unfold qPC; fun_prop

def pcStepUp (ζ : ℝ → ℝ) (u h : ℝ) : ℝ := if h = 0 then deriv ζ u else (ζ (u + h) - ζ u) / h
def pcStepDn (ζ : ℝ → ℝ) (u h : ℝ) : ℝ := if h = 0 then -deriv ζ u else (ζ (u - h) - ζ u) / h

def pcPiP (ζ : ℝ → ℝ) (μh : ℝ → ℝ) (u h : ℝ) : M2 :=
  odeFund (qPC ζ μh u h) (continuous_qPC ζ μh u h) 0 (pcStepUp ζ u h)

def pcPiM (ζ : ℝ → ℝ) (μh : ℝ → ℝ) (u h : ℝ) : M2 :=
  odeFund (qPC ζ μh u h) (continuous_qPC ζ μh u h) 0 (pcStepDn ζ u h)

/-- PC vector along `(ζ, μh)` from a balanced pair `wBranch : Fin 2 → ℝ → ℝ → ℝ` (at parameter `a(h) = -μh(h) / h`). -/
def wPC (wBranch : Fin 2 → ℝ → ℝ → ℝ) (ζ : ℝ → ℝ) (μh : ℝ → ℝ) : Fin 2 → ℝ → ℝ → V2
  | α => fun u h => if h ≤ 0 then ![0, 0] else
      ![wBranch α (-(μh h / h)) (ζ u / Real.sqrt h),
        Real.sqrt h * deriv (wBranch α (-(μh h / h))) (ζ u / Real.sqrt h)]

/-- Model even shift `μ(h²) = μ₀ + ∑_{r=1}^{q/2} h^{2r} μ_{2r}`. -/
def muEvenPoly (muS : ℕ → ℝ) (q : ℕ) (h : ℝ) : ℝ :=
  muS 0 + ∑ r ∈ Finset.Icc 1 (q / 2), h ^ (2 * r) * muS r

lemma muEvenPoly_neg (muS : ℕ → ℝ) (q : ℕ) (h : ℝ) :
    muEvenPoly muS q (-h) = muEvenPoly muS q h := by
  unfold muEvenPoly
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_mul, neg_sq, ← pow_mul]

lemma neg_muEvenPoly_div_eq_aPC (muS : ℕ → ℝ → ℝ) (q : ℕ) (h α : ℝ) (hh : h ≠ 0) :
    -(muEvenPoly (fun r => muS r α) q h / h) = aPC muS q h α := by
  unfold muEvenPoly aPC
  field_simp [hh]

lemma pc_symplecticLadder {γ : ℝ} (ζ μh : ℝ → ℝ) (hμ_even : ∀ h, μh (-h) = μh h)
    {pp qq : ℝ → ℝ → ℝ} (wBranch : Fin 2 → ℝ → ℝ → ℝ)
    (hderiv : ∀ α a z, HasDerivAt (wBranch α a) (deriv (wBranch α a) z) z)
    (hode : ∀ α a z, HasDerivAt (deriv (wBranch α a)) ((z ^ 2 / 4 + a) * wBranch α a z) z)
    (hwr : ∀ a z, wBranch 0 a z * deriv (wBranch 1 a) z - deriv (wBranch 0 a) z * wBranch 1 a z = 1) :
    SymplecticLadder γ ddPC d2PC pp qq (pcPiP ζ μh) (pcPiM ζ μh) (wPC wBranch ζ μh) Real.sqrt where
  wronsk := fun h hh j => by
    have hn : ¬ h ≤ 0 := not_le.mpr hh
    simp only [wPC, hn, ↓reduceIte, colDet, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 := hwr (-(μh h / h)) (ζ (((j : ℝ) + γ) * h) / Real.sqrt h)
    calc wBranch 0 _ _ * (Real.sqrt h * deriv (wBranch 1 _) _) -
          Real.sqrt h * deriv (wBranch 0 _) _ * wBranch 1 _ _
        = Real.sqrt h * (wBranch 0 _ _ * deriv (wBranch 1 _) _ -
            deriv (wBranch 0 _) _ * wBranch 1 _ _) := by ring
      _ = Real.sqrt h := by rw [h0, mul_one]
  wronsk_ne := fun h hh => (Real.sqrt_pos.mpr hh).ne'
  shift_up := fun α h hh j => by
    have hn : ¬ h ≤ 0 := not_le.mpr hh
    let u := ((j : ℝ) + γ) * h
    have hv : μh h = -(-(μh h / h)) * h := by field_simp [hh.ne']
    have hs := odeFund_pc_step hh hv (hderiv α _) (hode α _) (Z₀ := ζ u) (Z₁ := ζ (u + h))
    have hD : Dp ddPC u h = 1 := rfl
    rw [hD, one_smul]
    dsimp [wPC, pcPiP, pcStepUp]
    simp only [hn, hh.ne', ↓reduceIte]
    exact hs
  shift_dn := fun α h hh j _ => by
    have hn : ¬ h ≤ 0 := not_le.mpr hh
    let u := ((j : ℝ) + γ) * h
    have hv : μh h = -(-(μh h / h)) * h := by field_simp [hh.ne']
    have hs := odeFund_pc_step hh hv (hderiv α _) (hode α _) (Z₀ := ζ u) (Z₁ := ζ (u - h))
    have hD : Dm ddPC u h = 1 := rfl
    rw [hD, one_smul]
    dsimp [wPC, pcPiM, pcStepDn]
    simp only [hn, hh.ne', ↓reduceIte]
    exact hs
  d2_up := fun _ _ _ => by simp [Dp, d2PC, ddPC]
  d2_dn := fun _ _ _ _ => by simp [Dm, d2PC, ddPC]
  det_up := fun u h => by
    simpa [pcPiP, Dp, d2PC] using odeFund_det (qPC ζ μh u h) (continuous_qPC ζ μh u h) 0 (pcStepUp ζ u h)
  det_dn := fun u h => by
    simpa [pcPiM, Dm, d2PC] using odeFund_det (qPC ζ μh u h) (continuous_qPC ζ μh u h) 0 (pcStepDn ζ u h)
  prod := fun u h => by
    have heq : ∀ t, qPC ζ μh (u + h) h t = qPC ζ μh u h (t + pcStepUp ζ u h) := fun t => by
      dsimp [qPC, pcStepUp]
      by_cases hh : h = 0
      · simp [hh]
      · simp only [hh, ↓reduceIte]
        have : ζ (u + h) + h * t = ζ u + h * (t + (ζ (u + h) - ζ u) / h) := by
          field_simp [hh]; ring
        rw [this]
    have hstep : pcStepDn ζ (u + h) h = -pcStepUp ζ u h := by
      dsimp [pcStepDn, pcStepUp]
      by_cases hh : h = 0
      · simp [hh]
      · simp [hh, add_sub_cancel_right]; ring
    rw [pcPiM, pcPiP, hstep]
    simpa [Dp, d2PC] using odeFund_shift_mul_cancel
      (continuous_qPC ζ μh u h) (continuous_qPC ζ μh (u + h) h) (pcStepUp ζ u h) heq
  par_D := fun u h => by rfl
  par_Pi := fun u h => by
    have heq : ∀ s, qPC ζ μh u (-h) (-s) = qPC ζ μh u h s := fun s => by
      dsimp [qPC]; rw [hμ_even h]; ring
    have hstep : -pcStepDn ζ u h = pcStepUp ζ u (-h) := by
      dsimp [pcStepDn, pcStepUp]
      by_cases hh : h = 0
      · simp [hh]
      · have hh' : -h ≠ 0 := neg_ne_zero.mpr hh
        simp only [hh, hh', ↓reduceIte]
        rw [← sub_eq_add_neg]; ring
    rw [pcPiP, pcPiM, ← hstep]
    exact (odeFund_conj_sg (continuous_qPC ζ μh u (-h)) (continuous_qPC ζ μh u h) heq (pcStepDn ζ u h)).symm

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_symplecticLadder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pc_symplecticLadder

end FormalResearch.JacobiEigenvectors.Charts
