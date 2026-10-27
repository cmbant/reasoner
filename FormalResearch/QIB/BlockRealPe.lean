import Mathlib
import FormalResearch.QIB.BlockRealFrame
import FormalResearch.QIB.BlockAntiunitary

/-!
# Unconditional sector-mass equality and the multiplicity-one blind bound for `Helstrom.Pe`

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

In the unitary isotypic coordinates `W` of `Pe_blockdecomp` (`BlockCoordinates.lean`):

* `copies_theta`: `(Θψ)^{⊗k} = R ψ̄^{⊗k}` with `R = rotK k (ε,…,ε)` an element of the frame group.
* `sector_mass_theta`: for every sector `l` with nonempty multiplicity space,
  `Tr τ_l((Θψ)^{⊗k}) = Tr τ_l(ψ^{⊗k})` (real sector projectors, `sectorProj_real`).
* `Pe_ge_multiplicity_one`: `P_e(k) ≥ ½ Σ_{l : dim M_l = 1} Tr τ_l(ψ^{⊗k})`, i.e. `prop:blind`
  (multiplicity-one form) for `Helstrom.Pe`, in the coordinates `W` of `Pe_blockdecomp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (qf Pe rotK copies Copies)
open FormalResearch.FrameFree.NQubit (Ψ Θ SU2 SU2_eps eps cj nsq)

section Frame

theorem copies_cj {n : ℕ} (k : ℕ) (ψ : Ψ n) :
    copies k (cj ψ) = star (copies k ψ) := by
  funext x
  simp [copies, cj, Pi.star_apply, star_prod, Complex.star_def, map_prod]

/-- `(Θψ)^{⊗k} = R ψ̄^{⊗k}` with `R = rotK k (ε,…,ε)`. -/
theorem copies_theta {n : ℕ} (k : ℕ) (ψ : Ψ n) :
    copies k (Θ ψ) = rotK k (fun _ : Fin n => eps) *ᵥ star (copies k ψ) := by
  rw [FormalResearch.FrameFree.NQubit.Θ_eq_rot, FormalResearch.FrameFree.Helstrom.copies_rot, copies_cj]

theorem rotEps_mem (n k : ℕ) : rotK k (fun _ : Fin n => eps) ∈ frameGroup n k :=
  ⟨fun _ => eps, fun _ => SU2_eps, rfl⟩

theorem rotEps_unitary (n k : ℕ) : (rotK k (fun _ : Fin n => eps))ᴴ * rotK k (fun _ : Fin n => eps) = 1 :=
  FormalResearch.FrameFree.Helstrom.rotK_unitary k _ fun _ => SU2_eps

end Frame

section QF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qf_mulVec_mulVec (M U : Matrix ι ι ℂ) (v w : ι → ℂ) :
    qf M (U *ᵥ v) (U *ᵥ w) = qf (Uᴴ * M * U) v w := by
  unfold qf
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem qf_star_star (M : Matrix ι ι ℂ) (c : ι → ℂ) :
    qf M (star c) (star c) = conj (qf (M.map conj) c c) := by
  simp [qf, dotProduct, Matrix.mulVec, map_sum, Pi.star_apply, mul_comm, mul_left_comm]

theorem qf_real_of_psd {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (c : ι → ℂ) :
    conj (qf M c c) = qf M c c := by
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hM).2 c
  have him : (qf M c c).im = 0 := by
    have := (Complex.nonneg_iff.1 this).2
    simpa [qf] using this.symm
  exact Complex.conj_eq_iff_im.2 him

end QF

section Main

variable {n k r : ℕ} {a b : Fin r → ℕ}
  {W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ}

/-- **Sector masses of `ψ^{⊗k}` and `(Θψ)^{⊗k}` agree** in every sector of the isotypic coordinates `W`
of the frame group (the sector projectors are real, `sectorProj_real`, and `Θ` is `ε^{⊗nk} ∘ conj`). -/
theorem sector_mass_theta (ha : ∀ l, 0 < a l) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hG : IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
      (transportSet W (frameGroup n k))) (ψ : Ψ n) (l : Fin r) (hb : 0 < b l) :
    (tau (Wᴴ *ᵥ copies k (Θ ψ)) l).trace = (tau (Wᴴ *ᵥ copies k ψ) l).trace := by
  haveI : ∀ l, Nonempty (Fin (a l)) := fun l => ⟨⟨0, ha l⟩⟩
  haveI : Nonempty (Fin (b l)) := ⟨⟨0, hb⟩⟩
  obtain ⟨hSC, hCS, hreal, hconj⟩ := frame_real_data n k
  have hZreal := sectorProj_real hW1 hW2 hG l (frameS n k) hSC hCS hreal hconj
  have hZC := sectorProj_mem hW1 hW2 hG l
  set Z := sectorProj (fun l : Fin r => Fin (a l)) W l with hZ
  have hZh : Zᴴ = Z := sectorProj_conjTranspose l
  have hZi : Z * Z = Z := sectorProj_idem hW1 l
  have hZpsd : Z.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self Z
    rwa [hZh, hZi] at this
  set R := rotK k (fun _ : Fin n => eps) with hR
  have hRZ : R * Z = Z * R := mem_commSub.1 hZC R (rotEps_mem n k)
  have hRZR : Rᴴ * Z * R = Z := by
    rw [Matrix.mul_assoc, ← hRZ, ← Matrix.mul_assoc, rotEps_unitary, Matrix.one_mul]
  rw [trace_tau_eq hW1 hW2, trace_tau_eq hW1 hW2, copies_theta, qf_mulVec_mulVec, hRZR,
    qf_star_star, hZreal, qf_real_of_psd hZpsd]

theorem Pe_eq_invErr_coords (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (ψ : Ψ n) :
    Pe k ψ = invErr (transportSet W (frameGroup n k)) (Wᴴ *ᵥ copies k ψ) (Wᴴ *ᵥ copies k (Θ ψ)) := by
  rw [invErr_transport hW1 hW2, Pe_eq_invErr]

end Main

section Blind

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- In a one-dimensional multiplicity space `τ` is determined by its trace. -/
theorem tau_eq_of_trace_eq (a b : Idx A B → ℂ) (l : Λ) [Subsingleton (B l)]
    (h : (tau a l).trace = (tau b l).trace) : tau a l = tau b l := by
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  have e : ∀ v : Idx A B → ℂ, (tau v l).trace = tau v l i i := fun v => by
    simp [Matrix.trace, Matrix.diag, Fintype.sum_subsingleton _ i]
  rw [e, e] at h
  exact h

/-- `P_e ≥ ½ Σ_{l ∈ T} Tr τ_l` over any set `T` of sectors in which the two multiplicity blocks agree. -/
theorem invErr_ge_of_eq [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (a b : Idx A B → ℂ) (T : Finset Λ)
    (hT : ∀ l ∈ T, tau a l = tau b l) :
    (1 / 2) * ∑ l ∈ T, (tau a l).trace.re ≤ invErr G a b := by
  rw [invErr_eq hG]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    fun l _ _ => trMin_tau_nonneg a b l)
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [← hT l hl]
  unfold trMin
  rw [sub_self, (tnorm_eq_zero_iff Matrix.isHermitian_zero).2 rfl]
  ring

end Blind

/-- **`prop:blind` (multiplicity-one form) for `Helstrom.Pe`, unconditionally.**  In the isotypic
coordinates `W` of the frame group, `P_e(k) ≥ ½ Σ_{l : dim M_l = 1} Tr τ_l(ψ^{⊗k})` (for every `ψ`,
unit or not, with `τ_l(v) = Σ_α |v_{lα}⟩⟨v_{lα}|`), the sector masses of `ψ^{⊗k}` and `(Θψ)^{⊗k}` agree in
every sector, and the exact block formula of `Pe_blockdecomp` holds.  Here `dim M_l` is the multiplicity in
the full `(ℂ^{2^n})^{⊗k}`, not in the symmetric subspace as in the paper, so sectors of multiplicity one only
inside `Sym^k` are not included; `RealCoordsFrame.Pe_ge_blind_all` covers every sector with real `τ_l`. -/
theorem Pe_blockdecomp_blind (n k : ℕ) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W (frameGroup n k)) ∧
      ∀ ψ : Ψ n,
        Pe k ψ = (1 / 2) * ∑ l, trMin (tau (Wᴴ *ᵥ copies k ψ) l) (tau (Wᴴ *ᵥ copies k (Θ ψ)) l) ∧
        (∀ l, 0 < b l →
          (tau (Wᴴ *ᵥ copies k (Θ ψ)) l).trace = (tau (Wᴴ *ᵥ copies k ψ) l).trace) ∧
        (1 / 2) * ∑ l ∈ Finset.univ.filter (fun l => b l = 1),
          (tau (Wᴴ *ᵥ copies k ψ) l).trace.re ≤ Pe k ψ := by
  obtain ⟨r, a, b, W, ha, hW1, hW2, hG⟩ :=
    exists_isotypic_invariants (frameGroup n k) (frameGroup_star_closed n k)
  haveI : ∀ l, Nonempty (Fin (a l)) := fun l => ⟨⟨0, ha l⟩⟩
  refine ⟨r, a, b, W, ha, hW1, hW2, hG, fun ψ => ⟨?_, ?_, ?_⟩⟩
  · rw [Pe_eq_invErr_coords hW1 hW2, invErr_eq hG]
  · exact fun l hb => sector_mass_theta ha hW1 hW2 hG ψ l hb
  · rw [Pe_eq_invErr_coords hW1 hW2]
    refine invErr_ge_of_eq hG _ _ _ fun l hl => ?_
    have hb1 : b l = 1 := (Finset.mem_filter.1 hl).2
    haveI : Subsingleton (Fin (b l)) := by rw [hb1]; infer_instance
    exact tau_eq_of_trace_eq _ _ l
      (sector_mass_theta ha hW1 hW2 hG ψ l (by omega)).symm

end FormalResearch.QIB
