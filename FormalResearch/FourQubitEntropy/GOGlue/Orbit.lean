module

public import FormalResearch.FourQubitEntropy.PaperEGoSliceFinal
public import FormalResearch.FourQubitEntropy.GOProbe.PolySound

/-!
# GO glue: closest-point frames are preserved by orthogonal lower conjugations

`orbit_coord`: every `χ ∈ 𝓜` has magic coordinates `e · P diag(η₀) Qᵀ` with `P, Q` real orthogonal
(either determinant).  Hence if `sX v' = R · sX v · Rᵀ` and `sY v' = R · sY v · Rᵀ` for `R = diag(1, O)`,
`O` real orthogonal, a closest-point frame at `v` gives one at `v'` (`frame_orth`): the overlaps of the
slice states with `χ` are those with another point of `𝓜` (`ip_orbit`).  Claim class: proved.
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset
open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-! ### Coordinates of the points of `𝓜` -/

/-- Reindex a pair-indexed real matrix to `Fin 4`. -/
def fromR (O : RMat4) : M4R := O.submatrix pairEquiv.symm pairEquiv.symm

theorem fromR_apply (O : RMat4) (p q : Fin 2 × Fin 2) : fromR O (pairIdx p) (pairIdx q) = O p q := by
  have h : ∀ p : Fin 2 × Fin 2, pairEquiv.symm (pairIdx p) = p := fun p => pairEquiv.symm_apply_apply p
  simp [fromR, Matrix.submatrix_apply, h]

theorem fromR_orth {O : RMat4} (hO : Oᵀ * O = 1) : (fromR O)ᵀ * fromR O = 1 := by
  ext a b
  have h := congrFun (congrFun hO (pairEquiv.symm a)) (pairEquiv.symm b)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h ⊢
  have e1 : ∑ i : Fin 4, fromR O i a * fromR O i b =
      ∑ p : Fin 2 × Fin 2, O p (pairEquiv.symm a) * O p (pairEquiv.symm b) := by
    rw [← Equiv.sum_comp pairEquiv.symm (fun p : Fin 2 × Fin 2 => O p (pairEquiv.symm a) * O p (pairEquiv.symm b))]
    rfl
  rw [e1, h]
  by_cases hab : a = b
  · subst hab; simp
  · have : pairEquiv.symm a ≠ pairEquiv.symm b := fun h' => hab (pairEquiv.symm.injective h')
    simp [hab, this]

theorem coord_diag_entry (O1 O2 : RMat4) (s : ℂ) (w : Fin 2 × Fin 2 → ℂ) (p q : Fin 2 × Fin 2) :
    (rc O1 * Matrix.diagonal (fun k => s * w k) * (rc O2)ᵀ) p q =
      s * ∑ r, (O1 p r : ℂ) * w r * (O2 q r : ℂ) := by
  have : Matrix.diagonal (fun k => s * w k) = s • Matrix.diagonal w := by
    ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  rw [this]
  exact coord_entry O1 O2 s w p q

/-- Every point of `𝓜` has coordinates `e P diag(η₀) Qᵀ` with `P, Q` orthogonal. -/
theorem orbit_coord {χ : Psi} (h : InOrbit χ) :
    ∃ (e : ℂ) (P Q : M4R), Complex.normSq e = 1 ∧ Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧
      ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
        e * ∑ k : Fin 4, (P (pairIdx p) k : ℂ) * etaC 0 k * (Q (pairIdx q) k : ℂ) := by
  have hDm : ∀ (A : M4R) i k, (A * Dm) i k = A i k * sgn4 k := by
    intro A i k
    unfold Dm
    rw [Matrix.mul_diagonal]
    fin_cases k <;> simp [sgn4]
  rcases exists_same_class h with ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ | ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
  · obtain ⟨s, O1, O2, hs, hO1, hO2, hX⟩ := coord_localApply ha hb hc hd (etaV 0)
    refine ⟨s, fromR O1, fromR O2, hs, fromR_orth hO1, fromR_orth hO2, fun p q => ?_⟩
    rw [hX, coord_diag_entry]
    congr 1
    rw [← sum_pairG (fun j => ((fromR O1 (pairIdx p) j : ℝ) : ℂ) * etaC 0 j * ((fromR O2 (pairIdx q) j : ℝ) : ℂ))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [fromR_apply, fromR_apply]; rfl
  · obtain ⟨s, O1, O2, hs, hO1, hO2, hX⟩ := coord_localApply ha hb hc hd (etaV 7)
    refine ⟨s, fromR O1, fromR O2 * Dm, hs, fromR_orth hO1, orth_mul_Dm (fromR_orth hO2), fun p q => ?_⟩
    rw [hX, coord_diag_entry]
    congr 1
    rw [← sum_pairG (fun j => ((fromR O1 (pairIdx p) j : ℝ) : ℂ) * etaC 0 j *
      (((fromR O2 * Dm) (pairIdx q) j : ℝ) : ℂ))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hDm, fromR_apply, fromR_apply]
    show _ = _
    simp only [etaV, etaC_seven]
    push_cast
    ring

/-! ### Frames and orthogonal conjugation -/

theorem fn4_conj {R A : M4R} (hR : Rᵀ * R = 1) : fn4 (R * A * Rᵀ) = fn4 A := by
  rw [← trace_tmul_self, ← trace_tmul_self]
  have e : (R * A * Rᵀ)ᵀ * (R * A * Rᵀ) = R * (Aᵀ * A) * Rᵀ := by
    calc (R * A * Rᵀ)ᵀ * (R * A * Rᵀ) = R * Aᵀ * (Rᵀ * R) * A * Rᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = R * (Aᵀ * A) * Rᵀ := by rw [hR, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hR, Matrix.one_mul]

theorem frame_orth {O : M3R} (hO : Oᵀ * O = 1) {v v' : SV} {h : ℝ}
    (hX : sX v' = lift4 O * sX v * (lift4 O)ᵀ) (hY : sY v' = lift4 O * sY v * (lift4 O)ᵀ)
    (hf : IsFrame (sState v) h) : IsFrame (sState v') h := by
  have hR : (lift4 O)ᵀ * lift4 O = 1 := lift4_orth hO
  have hRR : lift4 O * (lift4 O)ᵀ = 1 := mul_eq_one_comm.mp hR
  refine ⟨?_, hf.2.1, ?_, ?_⟩
  · rw [normSqPsi_sState]
    have := hf.1
    rw [normSqPsi_sState] at this
    unfold sN at this ⊢
    rw [hX, hY, fn4_conj hR, fn4_conj hR]
    exact this
  · rw [ip_Zs_of_coord (coordIs_sState v'), hX, hY, Dfun_rot hO, ← ip_Zs_of_coord (coordIs_sState v)]
    exact hf.2.2.1
  · intro χ hχ
    obtain ⟨e, P, Q, he, hP, hQ, hc⟩ := orbit_coord hχ
    have horth : ∀ A : M4R, Aᵀ * A = 1 → ((lift4 O)ᵀ * A)ᵀ * ((lift4 O)ᵀ * A) = 1 := by
      intro A hA
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      calc Aᵀ * lift4 O * ((lift4 O)ᵀ * A) = Aᵀ * (lift4 O * (lift4 O)ᵀ) * A := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hRR, Matrix.mul_one, hA]
    obtain ⟨χ2, hχ2, hc2⟩ := orbit_mem4 ((lift4 O)ᵀ * P) ((lift4 O)ᵀ * Q) (horth P hP) (horth Q hQ) e he
    have i1 := ip_orbit v' P Q e χ hc
    have i2 := ip_orbit v ((lift4 O)ᵀ * P) ((lift4 O)ᵀ * Q) e χ2 hc2
    have hmat : ∀ A B : M4R, A = lift4 O * B * (lift4 O)ᵀ →
        Pᵀ * A * Q = ((lift4 O)ᵀ * P)ᵀ * B * ((lift4 O)ᵀ * Q) := by
      intro A B hAB
      rw [hAB, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    have : ip χ (sState v') = ip χ2 (sState v) := by
      rw [i1, i2, hmat _ _ hX, hmat _ _ hY]
    rw [this]
    exact hf.2.2.2 χ2 hχ2

end

end FormalResearch.FourQubitEntropy.GO
