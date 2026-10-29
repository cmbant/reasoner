import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicSwap

/-!
# Squared reduced matrix on the cuts containing the special site

For the 15 three-qubit cuts `S ∋ 0` of the seven-qubit icosahedral family the Gram matrices `P`, `Q`, `R`
of `SevenQubitIcoPurity` satisfy `Q = 0` (`SevenQubitIcoCert`) and the integer matrix identities
`P² = -32 + 12 P + 21 R`, `PR = RP = R`, `R² = R` (checked here for all 128 masks, in chunks, in the
kernel: `gramCert`). Hence, for `ρ_S = α² P + β² R` the reduced matrix of `ψ = α U + β V`
(`U = alphaReal`, `V = betaReal`),
`ρ_S² = α⁴ (-32 + 12 P + 21 R) + (2 α² β² + β⁴) R`, and `(ρ_S² ⊗ I) ψ` is a combination of `ψ` and the
two trilinear forms `redApplyT c U ψ U`, `redApplyT c V ψ V` (`redApplySq_contain`).

This is the algebraic half of the identity `G_{2,1}` of `SevenQubitIcoContraction` (not a paper statement:
the paper's proof of `prop:entropy-seven-stationarity` no longer displays it); the evaluation of the
trilinear forms is in `SevenQubitIcoContraction`.
Status: exact certificate (kernel-checked integer identities) plus elementary algebra.
-/

open Matrix Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### The Gram identities, for every mask -/

/-- The integer matrix identities on a cut containing the special site. -/
def ContainGram (cut : Cut 3 4) : Prop :=
  matP cut * matP cut = (-32 : ℤ) • (1 : Matrix Triple Triple ℤ) + (12 : ℤ) • matP cut + (21 : ℤ) • matR cut ∧
    matP cut * matR cut = matR cut ∧ matR cut * matP cut = matR cut ∧ matR cut * matR cut = matR cut

instance (cut : Cut 3 4) : Decidable (ContainGram cut) := by unfold ContainGram; infer_instance

/-- The Gram identities of a mask: for the weight-3 masks containing site `0`. -/
def GramCert (m : Fin 7 → Bool) : Prop :=
  weight m = 3 → m 0 = true → ContainGram (maskCut 3 4 m)

instance (m : Fin 7 → Bool) : Decidable (GramCert m) := by unfold GramCert; infer_instance

theorem gramCert_chunk0 : ∀ k < 16, GramCert (maskOfNat (16 * 0 + k)) := by decide +kernel
theorem gramCert_chunk1 : ∀ k < 16, GramCert (maskOfNat (16 * 1 + k)) := by decide +kernel
theorem gramCert_chunk2 : ∀ k < 16, GramCert (maskOfNat (16 * 2 + k)) := by decide +kernel
theorem gramCert_chunk3 : ∀ k < 16, GramCert (maskOfNat (16 * 3 + k)) := by decide +kernel
theorem gramCert_chunk4 : ∀ k < 16, GramCert (maskOfNat (16 * 4 + k)) := by decide +kernel
theorem gramCert_chunk5 : ∀ k < 16, GramCert (maskOfNat (16 * 5 + k)) := by decide +kernel
theorem gramCert_chunk6 : ∀ k < 16, GramCert (maskOfNat (16 * 6 + k)) := by decide +kernel
theorem gramCert_chunk7 : ∀ k < 16, GramCert (maskOfNat (16 * 7 + k)) := by decide +kernel

theorem gramCert (m : Fin 7 → Bool) : GramCert m := by
  obtain ⟨n, hn, rfl⟩ := maskOfNat_surjective m
  obtain ⟨c, k, hk, hc, rfl⟩ : ∃ c k, k < 16 ∧ c < 8 ∧ n = 16 * c + k :=
    ⟨n / 16, n % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [gramCert_chunk0 k hk, gramCert_chunk1 k hk, gramCert_chunk2 k hk, gramCert_chunk3 k hk,
    gramCert_chunk4 k hk, gramCert_chunk5 k hk, gramCert_chunk6 k hk, gramCert_chunk7 k hk]

/-! ### Selection sums -/

/-- `∑_{a,r} [encode c a r = z] F(a,r)`: for a bijective cut, the value of `F` at the preimage of `z`. -/
def selSum {k l : ℕ} (c : Cut k l) (z : BitString)
    (F : (Fin k → Bool) → (Fin l → Bool) → ℝ) : ℝ :=
  ∑ a : Fin k → Bool, ∑ r : Fin l → Bool, if encode c a r = z then F a r else 0

theorem selSum_encode {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c)
    (F : (Fin k → Bool) → (Fin l → Bool) → ℝ) (a0 : Fin k → Bool) (r0 : Fin l → Bool) :
    selSum c (encode c a0 r0) F = F a0 r0 := by
  have hf := FormalResearch.FourQubitEntropy.SevenQubitConseq.encode_bijective c hc
  have hinj := hf.injective
  unfold selSum
  rw [← Fintype.sum_prod_type' (f := fun a r => if encode c a r = encode c a0 r0 then F a r else 0)]
  rw [Finset.sum_eq_single (a0, r0)]
  · simp
  · intro p _ hp
    have : encode c p.1 p.2 ≠ encode c a0 r0 := fun h => hp (hinj (by simpa using h))
    simp [this]
  · simp

theorem selSum_add {k l : ℕ} (c : Cut k l) (z : BitString)
    (F G : (Fin k → Bool) → (Fin l → Bool) → ℝ) :
    selSum c z (fun a r => F a r + G a r) = selSum c z F + selSum c z G := by
  unfold selSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

theorem selSum_smul {k l : ℕ} (c : Cut k l) (z : BitString) (t : ℝ)
    (F : (Fin k → Bool) → (Fin l → Bool) → ℝ) :
    selSum c z (fun a r => t * F a r) = t * selSum c z F := by
  unfold selSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

theorem selSum_congr {k l : ℕ} (c : Cut k l) (z : BitString)
    (F G : (Fin k → Bool) → (Fin l → Bool) → ℝ) (h : ∀ a r, F a r = G a r) :
    selSum c z F = selSum c z G := by
  have : F = G := funext fun a => funext fun r => h a r
  rw [this]

theorem selSum_vec {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (z : BitString)
    (ψ : BitString → ℝ) : selSum c z (fun a r => ψ (encode c a r)) = ψ z := by
  obtain ⟨⟨a0, r0⟩, rfl⟩ := (FormalResearch.FourQubitEntropy.SevenQubitConseq.encode_bijective c hc).surjective z
  exact selSum_encode c hc _ a0 r0

theorem redApplyT_eq_selSum {k l : ℕ} (c : Cut k l) (f g h : BitString → ℝ) (z : BitString) :
    redApplyT c f g h z = selSum c z (fun a r =>
      ∑ b, (∑ r' : Fin l → Bool, f (encode c a r') * h (encode c b r')) * g (encode c b r)) := rfl

/-- `redApplyT` is linear in the acted vector. -/
theorem redApplyT_lin_g {k l : ℕ} (c : Cut k l) (f g1 g2 h : BitString → ℝ) (s t : ℝ)
    (z : BitString) :
    redApplyT c f (fun w => s * g1 w + t * g2 w) h z =
      s * redApplyT c f g1 h z + t * redApplyT c f g2 h z := by
  rw [redApplyT_eq_selSum, redApplyT_eq_selSum, redApplyT_eq_selSum, ← selSum_smul, ← selSum_smul,
    ← selSum_add]
  refine selSum_congr c z _ _ fun a r => ?_
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ### The squared reduced matrix -/

/-- `(ρ² ⊗ I) ψ` at `z` for the reduced matrix `ρ = (entryG c ψ)` of `ψ` on the `k`-side of the cut `c`. -/
def redApplySq {k l : ℕ} (c : Cut k l) (ψ : BitString → ℝ) (z : BitString) : ℝ :=
  selSum c z fun a r => ∑ b, (∑ d, entryG c ψ a d * entryG c ψ d b) * ψ (encode c b r)

theorem gramP_eq_sum {k l : ℕ} (c : Cut k l) (a b : Fin k → Bool) :
    (gramP c a b : ℝ) = ∑ r : Fin l → Bool, alphaReal (encode c a r) * alphaReal (encode c b r) := by
  unfold gramP gram alphaReal
  push_cast
  rfl

theorem gramR_eq_sum {k l : ℕ} (c : Cut k l) (a b : Fin k → Bool) :
    (gramR c a b : ℝ) = ∑ r : Fin l → Bool, betaReal (encode c a r) * betaReal (encode c b r) := by
  unfold gramR gram betaReal
  push_cast
  rfl

/-- The real entries of `ρ_S²` on a cut containing the special site. -/
theorem entry_sq_contain (c : Cut 3 4) (hQ : matQ c = 0) (hG : ContainGram c) (α β : ℝ)
    (a b : Fin 3 → Bool) :
    ∑ d, entryG c (icosahedralState α β) a d * entryG c (icosahedralState α β) d b =
      α ^ 4 * (-32 * (if a = b then 1 else 0) + 12 * (gramP c a b : ℝ) + 21 * (gramR c a b : ℝ)) +
        (2 * α ^ 2 * β ^ 2 + β ^ 4) * (gramR c a b : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  have hq : ∀ a b, gramQ c a b = 0 := fun a b => congrFun (congrFun hQ a) b
  have e : ∀ a b, entryG c (icosahedralState α β) a b =
      α ^ 2 * (gramP c a b : ℝ) + β ^ 2 * (gramR c a b : ℝ) := by
    intro a b
    have h := entry_expand c α β a b
    rw [hq a b] at h
    simp only [Int.cast_zero, mul_zero, add_zero] at h
    exact h
  have i1 := congrFun (congrFun h1 a) b
  have i2 := congrFun (congrFun h2 a) b
  have i3 := congrFun (congrFun h3 a) b
  have i4 := congrFun (congrFun h4 a) b
  simp only [matP, matR, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul] at i1 i2 i3 i4
  have r1 : ∑ d, (gramP c a d : ℝ) * (gramP c d b : ℝ) =
      -32 * (if a = b then 1 else 0) + 12 * (gramP c a b : ℝ) + 21 * (gramR c a b : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) i1
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_add] at this
    rw [this]
    split_ifs <;> simp
  have r2 : ∑ d, (gramP c a d : ℝ) * (gramR c d b : ℝ) = (gramR c a b : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) i2
    simpa using this
  have r3 : ∑ d, (gramR c a d : ℝ) * (gramP c d b : ℝ) = (gramR c a b : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) i3
    simpa using this
  have r4 : ∑ d, (gramR c a d : ℝ) * (gramR c d b : ℝ) = (gramR c a b : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) i4
    simpa using this
  simp only [e]
  have : ∀ d, (α ^ 2 * (gramP c a d : ℝ) + β ^ 2 * (gramR c a d : ℝ)) *
      (α ^ 2 * (gramP c d b : ℝ) + β ^ 2 * (gramR c d b : ℝ)) =
      α ^ 4 * ((gramP c a d : ℝ) * (gramP c d b : ℝ)) +
        α ^ 2 * β ^ 2 * ((gramP c a d : ℝ) * (gramR c d b : ℝ)) +
        α ^ 2 * β ^ 2 * ((gramR c a d : ℝ) * (gramP c d b : ℝ)) +
        β ^ 4 * ((gramR c a d : ℝ) * (gramR c d b : ℝ)) := fun d => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, r1, r2, r3, r4]
  ring

/-- **`(ρ_S² ⊗ I) ψ` on a cut containing the special site**, `ψ = α U + β V`:
`α⁴ (-32 ψ + 12 (P ⊗ I) ψ + 21 (R ⊗ I) ψ) + (2α²β² + β⁴) (R ⊗ I) ψ`, with `(P ⊗ I) ψ = redApplyT c U ψ U`
and `(R ⊗ I) ψ = redApplyT c V ψ V`. -/
theorem redApplySq_contain (m : Fin 7 → Bool) (hw : weight m = 3) (h0 : m 0 = true) (α β : ℝ)
    (z : BitString) :
    redApplySq (maskCut 3 4 m) (icosahedralState α β) z =
      α ^ 4 * (-32 * icosahedralState α β z +
          12 * redApplyT (maskCut 3 4 m) alphaReal (icosahedralState α β) alphaReal z +
          21 * redApplyT (maskCut 3 4 m) betaReal (icosahedralState α β) betaReal z) +
        (2 * α ^ 2 * β ^ 2 + β ^ 4) *
          redApplyT (maskCut 3 4 m) betaReal (icosahedralState α β) betaReal z := by
  have hc := maskCut_bijective_three m hw
  have hQ := ((cuts_cert m hw).1 h0).1
  have hG := gramCert m hw h0
  set c := maskCut 3 4 m with hcdef
  have key : ∀ a r, (∑ b, (∑ d, entryG c (icosahedralState α β) a d * entryG c (icosahedralState α β) d b) * (icosahedralState α β) (encode c b r)) =
      α ^ 4 * (-32 * (icosahedralState α β) (encode c a r) +
          12 * ∑ b, (∑ r' : Fin 4 → Bool, alphaReal (encode c a r') * alphaReal (encode c b r')) *
            (icosahedralState α β) (encode c b r) +
          21 * ∑ b, (∑ r' : Fin 4 → Bool, betaReal (encode c a r') * betaReal (encode c b r')) *
            (icosahedralState α β) (encode c b r)) +
        (2 * α ^ 2 * β ^ 2 + β ^ 4) *
          ∑ b, (∑ r' : Fin 4 → Bool, betaReal (encode c a r') * betaReal (encode c b r')) *
            (icosahedralState α β) (encode c b r) := by
    intro a r
    simp only [entry_sq_contain c hQ hG α β, ← gramP_eq_sum, ← gramR_eq_sum]
    have hδ : ∑ b, (if a = b then (1 : ℝ) else 0) * (icosahedralState α β) (encode c b r) = (icosahedralState α β) (encode c a r) := by
      simp [ite_mul]
    calc _ = ∑ b, (α ^ 4 * (-32 * ((if a = b then (1 : ℝ) else 0) * (icosahedralState α β) (encode c b r)) +
          12 * ((gramP c a b : ℝ) * (icosahedralState α β) (encode c b r)) +
          21 * ((gramR c a b : ℝ) * (icosahedralState α β) (encode c b r))) +
        (2 * α ^ 2 * β ^ 2 + β ^ 4) * ((gramR c a b : ℝ) * (icosahedralState α β) (encode c b r))) :=
          Finset.sum_congr rfl fun b _ => by ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hδ]

  unfold redApplySq
  rw [selSum_congr c z _ (fun a r =>
    α ^ 4 * (-32 * (icosahedralState α β) (encode c a r) +
          12 * ∑ b, (∑ r' : Fin 4 → Bool, alphaReal (encode c a r') * alphaReal (encode c b r')) *
            (icosahedralState α β) (encode c b r) +
          21 * ∑ b, (∑ r' : Fin 4 → Bool, betaReal (encode c a r') * betaReal (encode c b r')) *
            (icosahedralState α β) (encode c b r)) +
        (2 * α ^ 2 * β ^ 2 + β ^ 4) *
          ∑ b, (∑ r' : Fin 4 → Bool, betaReal (encode c a r') * betaReal (encode c b r')) *
            (icosahedralState α β) (encode c b r)) key]
  simp only [selSum_add, selSum_smul, selSum_vec c hc]
  rfl

end FormalResearch.FourQubitEntropy.SevenQubitIco
