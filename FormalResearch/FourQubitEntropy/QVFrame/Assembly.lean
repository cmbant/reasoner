import FormalResearch.FourQubitEntropy.QVFrame.Gram
import FormalResearch.FourQubitEntropy.QVFrame.Defect

/-!
# T1 + T2 + T3 assembled: the certificate identity as a quadratic form in `z^{⊗6}`

For any finite family of blocks `B : κ → Block` (no data of `QVCert/Data.lean` is used), counts `cnt`, integer weights `w`
and constant `D`:

`2 D 𝔇(z) - Σ_{k,i} w_{ki} ‖Φ_{ki}(z)‖²_w = ⟨z^{⊗6}, K z^{⊗6}⟩` (Hermitian form `qf (conj ψ) K ψ`, `ψ = z^{⊗6}`),

`K = 2 D · K_RHS - Σ_{k,i} w_{ki} · tauGram a_k p_k v_{ki}`, where `tauGram a p v = Σ_σ Σ_{s,s'} x x' ⊗_q τ_a(E…)`
is `gramOp` with the J-twisted partial transpose `τ_a` applied to every per-qubit factor.
-/

open scoped ComplexConjugate
open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

theorem qf_lsum {ι α : Type*} [Fintype ι] (u : ι → ℂ) (L : List α) (A : α → Matrix ι ι ℂ) (v : ι → ℂ) :
    qf u (lsum L A) v = lsum L (fun s => qf u (A s) v) := by
  induction L with
  | nil => simp [lsum_nil, qf_zero]
  | cons a L ih => rw [lsum_cons, qf_add, ih, lsum_cons]

theorem kronPi_map_int {n : ℕ} (X : Fin 4 → Matrix (Wd n) (Wd n) ℤ) :
    (kronPi X).map (Int.castRingHom ℂ) = kronPi (fun q => (X q).map (Int.castRingHom ℂ)) := by
  ext α β
  simp [kronPi_apply]

/-- `gramOp` with `τ_a` applied to every per-qubit factor (the frame-6 operator). -/
def tauGram (a : ℕ) (p : Fin 4 → ℕ) (v : List (ℕ × ℤ)) : Matrix (Cfg 6) (Cfg 6) ℤ :=
  ∑ σ : Equiv.Perm (Fin 4), lsum v fun s => lsum v fun s' =>
    (s.2 * s'.2) • kronPi (fun q => tau a (Eop (p (σ.symm q)) (QVCert.muDigit p s.1 (σ.symm q))
      (QVCert.muDigit p s'.1 (σ.symm q))))

theorem qf_term (a : ℕ) (u v : Site → ℂ) (c : ℤ) (X : Fin 4 → Matrix (Wd 6) (Wd 6) ℤ) :
    qf (pw a u v) ((c • kronPi X).map (Int.castRingHom ℂ)) (pw a v u) =
      qf (copyPower u 6) ((c • kronPi (fun q => tau a (X q))).map (Int.castRingHom ℂ)) (copyPower v 6) := by
  have h : ∀ (Y : Matrix (Cfg 6) (Cfg 6) ℤ), (c • Y).map (Int.castRingHom ℂ) =
      (c : ℂ) • Y.map (Int.castRingHom ℂ) := by
    intro Y; ext α β
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, eq_intCast]
  rw [h, h, qf_smul, qf_smul, kronPi_map_int, kronPi_map_int]
  rw [twist_qf]
  have : (fun q => tau a ((X q).map (Int.castRingHom ℂ))) =
      fun q => (tau a (X q)).map (Int.castRingHom ℂ) := funext fun q => (tau_map _ a (X q)).symm
  rw [this]

theorem qf_gramOp_tau (a : ℕ) (u v : Site → ℂ) (p : Fin 4 → ℕ) (vec : List (ℕ × ℤ)) :
    qf (pw a u v) ((gramOp p vec).map (Int.castRingHom ℂ)) (pw a v u) =
      qf (copyPower u 6) ((tauGram a p vec).map (Int.castRingHom ℂ)) (copyPower v 6) := by
  have hm : ∀ M : Matrix (Cfg 6) (Cfg 6) ℤ, M.map (Int.castRingHom ℂ) = (Int.castRingHom ℂ).mapMatrix M :=
    fun _ => rfl
  unfold gramOp tauGram
  simp only [hm, map_sum, lsum_map_hom, qf_sum, qf_lsum]
  refine Finset.sum_congr rfl fun σ _ => lsum_congr _ fun s _ => lsum_congr _ fun s' _ => ?_
  simp only [← hm]
  exact qf_term a u v _ _

/-- **T1 + T2.** `‖Φ_{ki}(z)‖²_w = ⟨z^{⊗6}, A^{(6)}_{ki} z^{⊗6}⟩` for every block and covariant. -/
theorem normSqPhi_eq_qf_tau (b : QVCert.Block) (z : Psi) (i : ℕ) :
    ((b.normSqPhi z i : ℝ) : ℂ) =
      qf (copyPower (fun c => conj (zf z c)) 6)
        ((tauGram b.a b.spins (b.vecs.getD i [])).map (Int.castRingHom ℂ)) (copyPower (zf z) 6) := by
  rw [normSqPhi_eq_qf, ← qf_gramOp_tau]
  rfl

/-- `Σ_{k,i} w_{ki} A^{(6)}_{ki}`. -/
def certFam {κ : Type*} [Fintype κ] (B : κ → QVCert.Block) (cnt : κ → ℕ) (w : κ → ℕ → ℤ) :
    Matrix (Cfg 6) (Cfg 6) ℤ :=
  ∑ k, ∑ i ∈ range (cnt k), w k i • tauGram (B k).a (B k).spins ((B k).vecs.getD i [])

/-- `K = 2 D K_RHS - Σ_{k,i} w_{ki} A^{(6)}_{ki}`. -/
def Kfam {κ : Type*} [Fintype κ] (B : κ → QVCert.Block) (cnt : κ → ℕ) (w : κ → ℕ → ℤ) (D : ℤ) :
    Matrix (Cfg 6) (Cfg 6) ℤ :=
  (2 * D) • rhsOp - certFam B cnt w

/-- **T1 + T2 + T3.** `2 D 𝔇(z) - Σ_{k,i} w_{ki} ‖Φ_{ki}(z)‖²_w = ⟨z^{⊗6}, K z^{⊗6}⟩`. -/
theorem cert_diff_eq_qf {κ : Type*} [Fintype κ] (B : κ → QVCert.Block) (cnt : κ → ℕ) (w : κ → ℕ → ℤ)
    (D : ℤ) (z : Psi) :
    (2 * (D : ℂ) * (QVCert.defectD z : ℂ) -
        ∑ k, ∑ i ∈ range (cnt k), (w k i : ℂ) * ((B k).normSqPhi z i : ℂ)) =
      qf (copyPower (fun c => conj (zf z c)) 6) ((Kfam B cnt w D).map (Int.castRingHom ℂ))
        (copyPower (zf z) 6) := by
  have h1 : ∀ (M N : Matrix (Cfg 6) (Cfg 6) ℤ), (M - N).map (Int.castRingHom ℂ) =
      M.map (Int.castRingHom ℂ) - N.map (Int.castRingHom ℂ) := by
    intro M N; ext α β; simp
  have h2 : ∀ (c : ℤ) (Y : Matrix (Cfg 6) (Cfg 6) ℤ), (c • Y).map (Int.castRingHom ℂ) =
      (c : ℂ) • Y.map (Int.castRingHom ℂ) := by
    intro c Y; ext α β
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, eq_intCast]
  unfold Kfam certFam
  rw [h1, qf_sub, h2, qf_smul, ← defectD_eq_qf]
  have h4 : ∀ (s : Finset κ) (A : κ → Matrix (Cfg 6) (Cfg 6) ℤ),
      (∑ k ∈ s, A k).map (Int.castRingHom ℂ) = ∑ k ∈ s, (A k).map (Int.castRingHom ℂ) := by
    intro s A; ext α β; simp [Matrix.sum_apply]
  have h5 : ∀ (s : Finset ℕ) (A : ℕ → Matrix (Cfg 6) (Cfg 6) ℤ),
      (∑ k ∈ s, A k).map (Int.castRingHom ℂ) = ∑ k ∈ s, (A k).map (Int.castRingHom ℂ) := by
    intro s A; ext α β; simp [Matrix.sum_apply]
  rw [h4, qf_sum]
  have e : ((2 * D : ℤ) : ℂ) = 2 * (D : ℂ) := by push_cast; ring
  rw [e, sub_right_inj]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h5, qf_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2, qf_smul, normSqPhi_eq_qf_tau]

end FormalResearch.FourQubitEntropy.QVFrame
