import Mathlib
import FormalResearch.QIB.BlockRealCond
import FormalResearch.QIB.RealCoordsCoord
import FormalResearch.QIB.RealCoordsWeights

/-!
# Real isotypic coordinates for the frame group (unconditional)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

* `frame_realMin`: the frame commutant `C = frameAlg n k` satisfies `RealMin C`.  A nonzero
  conjugation-closed `C`/`C'`-invariant subspace `U` contains a real vector `g`; a weight projector
  `P ∈ C'` and a sector projector (real, in `C`) cut it to a real `f ∈ U`, `P f = f`, supported on one
  isotypic sector.  `P C' P` is commutative (`weightProj_comm`: block-preserving involutions, Gelfand),
  so `f` is a pure tensor in the sector (`pure_of_comm`), hence `C f` is minimal (`isMinInv_cyc`).
* `realIsotypicCoords n k`: `RealIsotypicCoords n k` holds for **all** `n k`
  (`exists_real_isotypic_coordinates`).
* `Pe_antiunitary_all`, `Pe_ge_blind_all`: the unconditional `prop:antiunitary`, `prop:blind` for
  `Helstrom.Pe`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (qf Pe rotK copies Copies)
open FormalResearch.FrameFree.NQubit (Ψ Θ eps cj)

section Frame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonzero vector is a real multiple of a unit vector. -/
theorem exists_unit_smul (f : ι → ℂ) (hf0 : f ≠ 0) :
    ∃ c : ℝ, star ((c : ℂ) • f) ⬝ᵥ ((c : ℂ) • f) = 1 := by
  set t : ℝ := ∑ i, Complex.normSq (f i) with ht
  have h1 : star f ⬝ᵥ f = (t : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, ht]
    push_cast
    exact Finset.sum_congr rfl fun i _ => (Complex.normSq_eq_conj_mul_self).symm
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have ht1 : t ≠ 0 := by
    intro h
    apply hf0
    apply dotProduct_star_self_eq_zero.1
    rw [h1, h]; simp
  have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht1)
  refine ⟨(Real.sqrt t)⁻¹, ?_⟩
  rw [star_smul_vec, smul_dotProduct, dotProduct_smul, h1, Complex.conj_ofReal]
  simp only [smul_eq_mul]
  have : ((Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * t) : ℝ) = 1 := by
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt ht0]
    exact inv_mul_cancel₀ ht1
  exact_mod_cast this

end Frame

section RealMinFrame

variable {n k : ℕ}

theorem exists_real_vec_of_ne_bot {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Submodule ℂ (ι → ℂ))
    (hU : ConjClosed U) (hU0 : U ≠ ⊥) : ∃ g ∈ U, g ≠ 0 ∧ star g = g := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have h1 : u + star u ∈ U := U.add_mem huU (hU u huU)
  have h2 : Complex.I • (u - star u) ∈ U := U.smul_mem _ (U.sub_mem huU (hU u huU))
  have r1 : star (u + star u) = u + star u := by rw [star_add, star_star, add_comm]
  have r2 : star (Complex.I • (u - star u)) = Complex.I • (u - star u) := by
    rw [star_smul_vec, star_sub, star_star]
    have : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
    rw [this, neg_smul, ← smul_neg, neg_sub]
  by_cases h : u + star u = 0
  · refine ⟨Complex.I • (u - star u), h2, ?_, r2⟩
    intro h0
    apply hu0
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h3 : u - star u = 0 := by
      rcases smul_eq_zero.1 h0 with h' | h'
      · exact absurd h' hI
      · exact h'
    have : (2 : ℂ) • u = 0 := by
      calc (2 : ℂ) • u = (u + star u) + (u - star u) := by rw [two_smul]; abel
        _ = 0 := by rw [h, h3, add_zero]
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' two_ne_zero
    · exact h'
  · exact ⟨u + star u, h1, h, r1⟩


theorem weightProj_facts (m : Fin n → ℕ) :
    weightProj (k := k) m ∈ frameDual n k ∧ weightProj (k := k) m * weightProj m = weightProj m ∧
    (weightProj (k := k) m).map conj = weightProj m ∧
    (∀ Z₁ ∈ comm (frameAlg n k), ∀ Z₂ ∈ comm (frameAlg n k),
      (weightProj m * Z₁ * weightProj m) * (weightProj m * Z₂ * weightProj m) =
        (weightProj m * Z₂ * weightProj m) * (weightProj m * Z₁ * weightProj m)) :=
  ⟨weightProj_mem_frameDual m, weightProj_idem m, weightProj_map_conj m,
    fun _ h₁ _ h₂ => weightProj_comm m h₁ h₂⟩

/-- **The frame commutant satisfies `RealMin`.** -/
theorem frame_realMin (n k : ℕ) : RealMin (frameAlg n k) := by
  intro U hUc hUC hUD hU0
  obtain ⟨r, a, b, W, ha, hW1, hW2, hG⟩ :=
    exists_isotypic_invariants (frameGroup n k) (frameGroup_star_closed n k)
  have : ∀ l, Nonempty (Fin (a l)) := fun l => ⟨⟨0, ha l⟩⟩
  have hCW : ∀ M, M ∈ frameAlg n k ↔
      ∃ Y : ∀ l : Fin r, Matrix (Fin (b l)) (Fin (b l)) ℂ,
        M = W * blockOp (fun l : Fin r => Fin (a l)) Y * Wᴴ := fun M => by
    rw [mem_frameAlg, ← mem_commSub]; exact mem_commSub_iff hW1 hW2 hG M
  obtain ⟨hSC, hCS, hreal, hconj⟩ := frame_real_data n k
  -- a nonzero real vector of `U`, cut down by a weight projector
  obtain ⟨g, hgU, hg0, hgr⟩ := exists_real_vec_of_ne_bot U hUc hU0
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hg0
  have hPx : (weightProj (k := k) (wtc x) *ᵥ g) x = g x := by
    simp [weightProj, Matrix.mulVec_diagonal]
  obtain ⟨hPD, hPP, hPr, hcomm⟩ := weightProj_facts (n := n) (k := k) (wtc x)
  generalize weightProj (k := k) (wtc x) = P at hPD hPP hPr hcomm hPx
  have hPg : P *ᵥ g ∈ U := hUD P hPD g hgU
  have hPgr : star (P *ᵥ g) = P *ᵥ g := by rw [star_mulVec_map, hPr, hgr]
  have hPg0 : P *ᵥ g ≠ 0 := by
    intro h
    apply hx
    rw [← hPx, h]
  have hPfix : P *ᵥ (P *ᵥ g) = P *ᵥ g := by rw [Matrix.mulVec_mulVec, hPP]
  generalize P *ᵥ g = g1 at hPg hPgr hPg0 hPfix
  -- coordinates and a sector on which `g1` is nonzero
  obtain ⟨⟨l, α0, b0⟩, hi⟩ : ∃ i, (Wᴴ *ᵥ g1) i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hPg0
    have h0 : Wᴴ *ᵥ g1 = 0 := funext hcon
    rw [coord_back hW2 g1, h0, Matrix.mulVec_zero]
  have hSpC : sectorProj (fun l : Fin r => Fin (a l)) W l ∈ frameAlg n k := by
    rw [mem_frameAlg, ← mem_commSub]; exact sectorProj_mem hW1 hW2 hG l
  have : Nonempty (Fin (b l)) := ⟨b0⟩
  have hSpr := sectorProj_real (A := fun l : Fin r => Fin (a l)) hW1 hW2 hG l (frameS n k) hSC hCS
    hreal hconj
  obtain ⟨f, hfdef⟩ : ∃ f, f = sectorProj (fun l : Fin r => Fin (a l)) W l *ᵥ g1 := ⟨_, rfl⟩
  have hfU : f ∈ U := by rw [hfdef]; exact hUC _ hSpC g1 hPg
  have hfr : star f = f := by rw [hfdef, star_mulVec_map, hSpr, hPgr]
  have hPf : P *ᵥ f = f := by
    rw [hfdef, Matrix.mulVec_mulVec, ← (mem_comm.1 hPD _ hSpC), ← Matrix.mulVec_mulVec, hPfix]
  have hWf : Wᴴ *ᵥ f = blockOp (fun l : Fin r => Fin (a l)) (sectorDelta (fun l : Fin r => Fin (b l)) l) *ᵥ
      (Wᴴ *ᵥ g1) := by
    rw [hfdef]; exact coord_conj_mulVec hW1 _ g1
  have hsupp : ∀ l' ≠ l, ∀ p, (Wᴴ *ᵥ f) ⟨l', p⟩ = 0 := by
    intro l' hl' p
    obtain ⟨α', b'⟩ := p
    rw [hWf, blockOp_mulVec_apply]
    simp [sectorDelta, hl']
  have hfi : (Wᴴ *ᵥ f) ⟨l, (α0, b0)⟩ = (Wᴴ *ᵥ g1) ⟨l, (α0, b0)⟩ := by
    rw [hWf, blockOp_mulVec_apply]
    simp [sectorDelta, slice]
  have hf0 : f ≠ 0 := by
    intro h
    apply hi
    rw [← hfi, h, Matrix.mulVec_zero]; rfl
  have hfΦ := eq_lift_of_supp (Wᴴ *ᵥ f) hsupp
  obtain ⟨v, m, hv, hm, hΦ⟩ := pure_of_comm hW1 hW2 hCW hPD hcomm hPf hfΦ hf0
  rw [hΦ] at hfΦ
  have hmin := isMinInv_cyc hW1 hW2 hCW hv hm hfΦ
  obtain ⟨c, hc⟩ := exists_unit_smul f hf0
  refine ⟨cycSub (frameAlg n k) f, ?_, hmin, (c : ℂ) • f, ?_, ?_, hc⟩
  · rintro _ ⟨c', hc', rfl⟩
    exact hUC c' hc' f hfU
  · exact (cycSub (frameAlg n k) f).smul_mem _ (mem_cycSub_self _ f)
  · rw [star_smul_vec, hfr, Complex.conj_ofReal]

end RealMinFrame

/-- **`RealIsotypicCoords n k` holds for all `n k`.**  The frame group has isotypic coordinates by a
unitary `W` with real entries. -/
theorem realIsotypicCoords (n k : ℕ) : RealIsotypicCoords n k := by
  obtain ⟨r, a, b, W, ha, hW1, hW2, hreal, hM⟩ :=
    exists_real_isotypic_coordinates (C := frameAlg n k) frameAlg_star frameAlg_conj
      (frame_realMin n k)
  refine ⟨r, a, b, W, ha, hW1, hW2, hreal, fun M' => ?_⟩
  have h1 : (∀ U' ∈ transportSet W (frameGroup n k), U' * M' = M' * U') ↔
      W * M' * Wᴴ ∈ frameAlg n k := by
    rw [mem_frameAlg]
    constructor
    · intro h g hg
      exact (comm_conj_iff hW1 hW2 g M').1 (h _ ⟨g, hg, rfl⟩)
    · rintro h _ ⟨g, hg, rfl⟩
      exact (comm_conj_iff hW1 hW2 g M').2 (h g hg)
  rw [h1, hM]
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, by rw [← conj_back hW1 M']; exact hX⟩
  · rintro ⟨X, rfl⟩
    exact ⟨X, by rw [conj_back hW1]⟩

/-- **Unconditional `prop:antiunitary` and sector-blindness criterion** for `Helstrom.Pe`. -/
theorem Pe_antiunitary_all (n k : ℕ) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W (frameGroup n k)) ∧
      ∀ ψ : Ψ n, star (copies k ψ) ⬝ᵥ copies k ψ = 1 →
        (1 - 2 * Pe k ψ = ∑ l, imNorm (tau (Wᴴ *ᵥ copies k ψ) l)) ∧
        ∀ l, (tau (Wᴴ *ᵥ copies k ψ) l = tau (Wᴴ *ᵥ copies k (Θ ψ)) l ↔
          imNorm (tau (Wᴴ *ᵥ copies k ψ) l) = 0) :=
  (realIsotypicCoords n k).antiunitary

/-- **Unconditional `prop:blind`** for `Helstrom.Pe`: in real isotypic coordinates `W` for the frame group,
any set `T` of sectors whose multiplicity blocks `τ_l(ψ^{⊗k})` are real is blind,
`½ Σ_{l ∈ T} Tr τ_l ≤ P_e`. -/
theorem Pe_ge_blind_all (n k : ℕ) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ W.map conj = W ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W (frameGroup n k)) ∧
      ∀ (ψ : Ψ n) (T : Finset (Fin r)),
        (∀ l ∈ T, (tau (Wᴴ *ᵥ copies k ψ) l).map conj = tau (Wᴴ *ᵥ copies k ψ) l) →
        (1 / 2) * ∑ l ∈ T, (tau (Wᴴ *ᵥ copies k ψ) l).trace.re ≤ Pe k ψ := by
  obtain ⟨r, a, b, W, ha, hW1, hW2, hreal, hG⟩ := realIsotypicCoords n k
  exact ⟨r, a, b, W, ha, hW1, hW2, hreal, hG, fun ψ T hT => Pe_ge_blind ha hW1 hW2 hreal hG ψ T hT⟩



end FormalResearch.QIB
