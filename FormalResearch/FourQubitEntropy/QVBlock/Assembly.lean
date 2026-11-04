module

public import FormalResearch.FourQubitEntropy.QVBlock.Extension
public import FormalResearch.FourQubitEntropy.QVBlock.Invariants

/-!
# Assembly of the block calculus (QV block calculus, T4–T8)

* `kron_C_mul_copySym`: `C^{⊗Q} P = Blk_spin(R_p) C^{⊗Q}` with `R_p = repAvg (⊗_q ρ(·)(p q))`.
* `kron_C_mul_sum`: `C^{⊗Q} K = Blk_spin(Y_p) C^{⊗Q}` for `K = ∑_k ⊗_q X k q`.
* `copySym_mul_sum_mul_copySym_eq_zero`: `R_p Y_p R_p = 0 ∀ p ⇒ P K P = 0`.
* `quad_eq_zero_of_blockData`: the abstract top theorem (T4 + T6 + T7 + T8).
* `quad_eq_zero_of_certificate`: the same with all data given by generators, words and finite
  matrix identities.
-/

@[expose] public section


open scoped Matrix BigOperators

namespace FormalResearch.FourQubitEntropy.QVBlock

set_option linter.unusedSectionVars false

section
variable {𝕜 : Type*} [Field 𝕜]
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
variable {J : Type*} [Fintype J] [DecidableEq J] (dim : J → ℕ) {mult : J → ℕ}
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **T6 for the symmetriser.** -/
theorem kron_C_mul_copySym [CharZero 𝕜] (C : Matrix (Idx dim mult) (Fin n → σ) 𝕜)
    (ρ : Equiv.Perm (Fin n) →* (∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜))
    (hρ : ∀ g, C * slotPerm 𝕜 g = blk dim (ρ g) * C) :
    kronPi (fun _ : Q => C) * copySym 𝕜 Q σ n =
      blkSpin dim (fun p => repAvg (kronRep ρ p)) * kronPi (fun _ : Q => C) := by
  have hg : ∀ g, kronPi (fun _ : Q => C) * copyPerm 𝕜 Q σ g =
      blkSpin dim (fun p => kronRep ρ p g) * kronPi (fun _ : Q => C) := by
    intro g
    calc kronPi (fun _ : Q => C) * copyPerm 𝕜 Q σ g
        = kronPi (fun _ : Q => C * slotPerm 𝕜 g) := kronPi_mul _ _
      _ = kronPi (fun _ : Q => blk dim (ρ g) * C) :=
          congrArg (fun A => kronPi (fun _ : Q => A)) (hρ g)
      _ = kronPi (fun _ : Q => blk dim (ρ g)) * kronPi (fun _ : Q => C) := (kronPi_mul _ _).symm
      _ = blkSpin dim (fun p => kronRep ρ p g) * kronPi (fun _ : Q => C) := by
          rw [kronPi_blk dim (fun _ : Q => ρ g)]; rfl
  unfold copySym
  calc kronPi (fun _ : Q => C) *
        (((Fintype.card (Equiv.Perm (Fin n)) : 𝕜)⁻¹) • ∑ π : Equiv.Perm (Fin n), copyPerm 𝕜 Q σ π)
      = ((Fintype.card (Equiv.Perm (Fin n)) : 𝕜)⁻¹) •
          ∑ g : Equiv.Perm (Fin n), kronPi (fun _ : Q => C) * copyPerm 𝕜 Q σ g := by
        rw [Matrix.mul_smul, Matrix.mul_sum]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : 𝕜)⁻¹) •
          ∑ g : Equiv.Perm (Fin n), blkSpin dim (fun p => kronRep ρ p g) *
            kronPi (fun _ : Q => C) := by
        congr 1
        exact Finset.sum_congr rfl (fun g _ => hg g)
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : 𝕜)⁻¹) •
          ((∑ g : Equiv.Perm (Fin n), blkSpin dim (fun p => kronRep ρ p g)) *
            kronPi (fun _ : Q => C)) :=
        congrArg _ (Matrix.sum_mul _ _ _).symm
    _ = blkSpin dim (fun p => repAvg (kronRep ρ p)) * kronPi (fun _ : Q => C) := by
        rw [← blkSpin_sum]
        exact (Matrix.smul_mul _ _ _).symm.trans
          (congrArg (· * kronPi (fun _ : Q => C)) (blkSpin_smul dim _ _).symm)

/-- **T6 for a sum of Kronecker products.** -/
theorem kron_C_mul_sum {κ : Type*} [Fintype κ] (C : Matrix (Idx dim mult) (Fin n → σ) 𝕜)
    (X : κ → Q → Matrix (Fin n → σ) (Fin n → σ) 𝕜)
    (Xh : κ → Q → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)
    (hX : ∀ k q, C * X k q = blk dim (Xh k q) * C) :
    kronPi (fun _ : Q => C) * (∑ k, kronPi (X k)) =
      blkSpin dim (fun p => ∑ k, kronPi (fun q => Xh k q (p q))) * kronPi (fun _ : Q => C) := by
  have hk : ∀ k, kronPi (fun _ : Q => C) * kronPi (X k) =
      blkSpin dim (fun p => kronPi (fun q => Xh k q (p q))) * kronPi (fun _ : Q => C) := by
    intro k
    calc kronPi (fun _ : Q => C) * kronPi (X k) = kronPi (fun q => C * X k q) := kronPi_mul _ _
      _ = kronPi (fun q => blk dim (Xh k q) * C) :=
          congrArg kronPi (funext fun q => hX k q)
      _ = kronPi (fun q => blk dim (Xh k q)) * kronPi (fun _ : Q => C) := (kronPi_mul _ _).symm
      _ = _ := by rw [kronPi_blk dim (Xh k)]
  calc kronPi (fun _ : Q => C) * (∑ k, kronPi (X k))
      = ∑ k, kronPi (fun _ : Q => C) * kronPi (X k) := Matrix.mul_sum _ _ _
    _ = ∑ k, blkSpin dim (fun p => kronPi (fun q => Xh k q (p q))) * kronPi (fun _ : Q => C) :=
        Finset.sum_congr rfl (fun k _ => hk k)
    _ = (∑ k, blkSpin dim (fun p => kronPi (fun q => Xh k q (p q)))) *
          kronPi (fun _ : Q => C) := (Matrix.sum_mul _ _ _).symm
    _ = _ := by rw [← blkSpin_sum]

/-- **T8 assembly.** If `R_p Y_p R_p = 0` for every spin tuple `p`, then `P K P = 0`. -/
theorem copySym_mul_sum_mul_copySym_eq_zero [CharZero 𝕜]
    (C : Matrix (Idx dim mult) (Fin n → σ) 𝕜) (Cinv : Matrix (Fin n → σ) (Idx dim mult) 𝕜)
    (hCi : Cinv * C = 1)
    (ρ : Equiv.Perm (Fin n) →* (∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜))
    (hρ : ∀ g, C * slotPerm 𝕜 g = blk dim (ρ g) * C)
    {κ : Type*} [Fintype κ] (X : κ → Q → Matrix (Fin n → σ) (Fin n → σ) 𝕜)
    (Xh : κ → Q → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)
    (hX : ∀ k q, C * X k q = blk dim (Xh k q) * C)
    (hRYR : ∀ p : Q → J, repAvg (kronRep ρ p) * (∑ k, kronPi (fun q => Xh k q (p q))) *
      repAvg (kronRep ρ p) = 0) :
    copySym 𝕜 Q σ n * (∑ k, kronPi (X k)) * copySym 𝕜 Q σ n = 0 := by
  set C4 : Matrix (Q → Idx dim mult) (Q → Fin n → σ) 𝕜 := kronPi (fun _ : Q => C) with hC4
  set C4i : Matrix (Q → Fin n → σ) (Q → Idx dim mult) 𝕜 := kronPi (fun _ : Q => Cinv) with hC4i
  have hinv : C4i * C4 = 1 := by
    rw [hC4i, hC4, kronPi_mul]
    simp_rw [hCi]
    exact kronPi_one
  have hP := kron_C_mul_copySym dim C ρ hρ (Q := Q) (σ := σ)
  have hK := kron_C_mul_sum dim C X Xh hX (Q := Q)
  set P := copySym 𝕜 Q σ n
  set K := ∑ k, kronPi (X k)
  set BR := blkSpin dim (fun p : Q → J => repAvg (kronRep ρ p))
  set BY := blkSpin dim (fun p : Q → J => ∑ k, kronPi (fun q => Xh k q (p q)))
  have hP' : C4 * P = BR * C4 := hP
  have hK' : C4 * K = BY * C4 := hK
  have hzero : C4 * (P * K * P) = 0 := by
    calc C4 * (P * K * P) = ((C4 * P) * K) * P := by simp only [Matrix.mul_assoc]
      _ = ((BR * C4) * K) * P := by rw [hP']
      _ = (BR * (C4 * K)) * P := by simp only [Matrix.mul_assoc]
      _ = (BR * (BY * C4)) * P := by rw [hK']
      _ = BR * BY * (C4 * P) := by simp only [Matrix.mul_assoc]
      _ = BR * BY * (BR * C4) := by rw [hP']
      _ = (BR * BY * BR) * C4 := by simp only [Matrix.mul_assoc]
      _ = blkSpin dim (fun p : Q → J => repAvg (kronRep ρ p) *
            (∑ k, kronPi (fun q => Xh k q (p q))) * repAvg (kronRep ρ p)) * C4 := by
          rw [blkSpin_mul, blkSpin_mul]
      _ = 0 := by
          simp only [hRYR, blkSpin_zero, Matrix.zero_mul]
  calc P * K * P = (C4i * C4) * (P * K * P) := by rw [hinv, Matrix.one_mul]
    _ = C4i * (C4 * (P * K * P)) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hzero, Matrix.mul_zero]

/-- **Top theorem, abstract form (T4 + T6 + T7 + T8).**  `K = ∑_k ⊗_q X k q` with per-qubit block
form `C X k q = Blk(X̂ k q) C`, an invertible `C` intertwining the slot permutations with a
representation `ρ`, and for each spin tuple `p` invariant bases `V p`, `W p` of the right/left
invariants of `⊗_q ρ(·)(p q)` of the character-formula size with `Wᵀ Y_p V = 0`. -/
theorem quad_eq_zero_of_blockData [CharZero 𝕜]
    (C : Matrix (Idx dim mult) (Fin n → σ) 𝕜) (Cinv : Matrix (Fin n → σ) (Idx dim mult) 𝕜)
    (hCi : Cinv * C = 1)
    (ρ : Equiv.Perm (Fin n) →* (∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜))
    (hρ : ∀ g, C * slotPerm 𝕜 g = blk dim (ρ g) * C)
    {κ : Type*} [Fintype κ] (X : κ → Q → Matrix (Fin n → σ) (Fin n → σ) 𝕜)
    (Xh : κ → Q → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)
    (hX : ∀ k q, C * X k q = blk dim (Xh k q) * C)
    (nn : (Q → J) → ℕ)
    (V W : ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (Fin (nn p)) 𝕜)
    (hV : ∀ p g, kronRep ρ p g * V p = V p) (hW : ∀ p g, (kronRep ρ p g)ᵀ * W p = W p)
    (hVli : ∀ p, LinearIndependent 𝕜 (V p)ᵀ) (hWli : ∀ p, LinearIndependent 𝕜 (W p)ᵀ)
    (hn : ∀ p, (nn p : 𝕜) = (repAvg (kronRep ρ p)).trace)
    (hcheck : ∀ p, (W p)ᵀ * (∑ k, kronPi (fun q => Xh k q (p q))) * V p = 0)
    (z' z : (Q → σ) → 𝕜) :
    copyPower z' n ⬝ᵥ ((∑ k, kronPi (X k)) *ᵥ copyPower z n) = 0 := by
  apply copyPower_quad_eq_zero
  exact copySym_mul_sum_mul_copySym_eq_zero dim C Cinv hCi ρ hρ X Xh hX
    (fun p => repAvg_mul_mul_repAvg_eq_zero (kronRep ρ p) (V p) (W p) (hV p) (hW p) (hVli p)
      (hWli p) (hn p) _ (hcheck p))

/-- **Top theorem, certificate form.**  All finite data: generators `gens` of `S_n` with a word
function `w` (`hw`), their block matrices `ρ₀`, per-qubit block identities `hX`, invariant
vectors under the generators (`hV`, `hW`), pivot minors (`hdetV`, `hdetW`: linear independence),
the character-sum identity `|S_n| · n_p = ∑_g ∏_q tr ρ_{p_q}(g)` with `ρ(g)` computed from the
word of `g` (`hchar`), and the finite contraction check `Wᵀ Y_p V = 0` (`hcheck`). -/
theorem quad_eq_zero_of_certificate [CharZero 𝕜] (hdim : ∀ j, 0 < dim j)
    (C : Matrix (Idx dim mult) (Fin n → σ) 𝕜) (Cinv : Matrix (Fin n → σ) (Idx dim mult) 𝕜)
    (hCi : Cinv * C = 1) (hiC : C * Cinv = 1)
    {ι : Type*} (gens : ι → Equiv.Perm (Fin n)) (w : Equiv.Perm (Fin n) → List ι)
    (hw : ∀ g, ((w g).map gens).prod = g)
    (ρ0 : ι → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)
    (hρ0 : ∀ i, C * slotPerm 𝕜 (gens i) = blk dim (ρ0 i) * C)
    {κ : Type*} [Fintype κ] (X : κ → Q → Matrix (Fin n → σ) (Fin n → σ) 𝕜)
    (Xh : κ → Q → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)
    (hX : ∀ k q, C * X k q = blk dim (Xh k q) * C)
    (nn : (Q → J) → ℕ)
    (V W : ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (Fin (nn p)) 𝕜)
    (hV : ∀ p i, kronPi (fun q => ρ0 i (p q)) * V p = V p)
    (hW : ∀ p i, (kronPi (fun q => ρ0 i (p q)))ᵀ * W p = W p)
    (pivV pivW : ∀ p : Q → J, Fin (nn p) → (∀ q, Fin (mult (p q))))
    (hdetV : ∀ p, ((V p).submatrix (pivV p) id).det ≠ 0)
    (hdetW : ∀ p, ((W p).submatrix (pivW p) id).det ≠ 0)
    (hchar : ∀ p, (Fintype.card (Equiv.Perm (Fin n)) : 𝕜) * nn p =
      ∑ g : Equiv.Perm (Fin n), ∏ q, (((w g).map (fun i => ρ0 i (p q))).prod).trace)
    (hcheck : ∀ p, (W p)ᵀ * (∑ k, kronPi (fun q => Xh k q (p q))) * V p = 0)
    (z' z : (Q → σ) → 𝕜) :
    copyPower z' n ⬝ᵥ ((∑ k, kronPi (X k)) *ᵥ copyPower z n) = 0 := by
  have hgen : Submonoid.closure (Set.range gens) = ⊤ := by
    apply top_unique
    intro g _
    rw [← hw g]
    exact Submonoid.list_prod_mem _ (fun a ha => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact Submonoid.subset_closure ⟨i, rfl⟩)
  obtain ⟨ρ, hρgen, hρ⟩ := exists_blockRep dim hdim C Cinv hiC gens hgen ρ0 hρ0
  have hρw : ∀ g, ρ g = ((w g).map ρ0).prod := by
    intro g
    conv_lhs => rw [← hw g]
    rw [map_list_prod, List.map_map]
    congr 2
    funext i
    exact hρgen i
  refine quad_eq_zero_of_blockData dim C Cinv hCi ρ hρ X Xh hX nn V W ?_ ?_
    (fun p => linearIndependent_cols_of_det_ne_zero _ _ (hdetV p))
    (fun p => linearIndependent_cols_of_det_ne_zero _ _ (hdetW p)) ?_ hcheck z' z
  · intro p
    exact invariant_of_closure (kronRep ρ p) (Set.range gens) hgen (V p) (by
      rintro _ ⟨i, rfl⟩
      simpa [kronRep_apply, hρgen] using hV p i)
  · intro p
    exact left_invariant_of_closure (kronRep ρ p) (Set.range gens) hgen (W p) (by
      rintro _ ⟨i, rfl⟩
      simpa [kronRep_apply, hρgen] using hW p i)
  · intro p
    have hc := hchar p
    rw [trace_repAvg]
    have h0 : (Fintype.card (Equiv.Perm (Fin n)) : 𝕜) ≠ 0 := card_ne_zero'
    have : ∀ g, (kronRep ρ p g).trace =
        ∏ q, (((w g).map (fun i => ρ0 i (p q))).prod).trace := by
      intro g
      rw [kronRep_apply, trace_kronPi]
      refine Finset.prod_congr rfl (fun q _ => ?_)
      rw [hρw g, Pi.list_prod_apply, List.map_map]
      rfl
    simp only [this]
    rw [← hc]
    field_simp

end

end FormalResearch.FourQubitEntropy.QVBlock
