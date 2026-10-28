import FormalResearch.FourQubitEntropy.SevenQubitIcoCert

/-!
# Joint spin-flip relations for the triple marginals of the icosahedral family

Formalizes `lem:seven-adaptive-joint-spinflip` (exact AH-5) of
`ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_joint.tex`.
-/

open Matrix

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Algebra with abstract matrices -/

set_option linter.unusedSimpArgs false

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem avoid_algebra (S1 S2 : Matrix n n ℝ) (A B : ℝ)
    (h1 : (S1 - (8:ℝ) • 1) * (S1 - (6:ℝ) • 1) = 0)
    (h2 : (S1 - (8:ℝ) • 1) * (S2 - (2:ℝ) • 1) + S2 * (S1 - (6:ℝ) • 1) = 0)
    (h3 : S2 * (S2 - (2:ℝ) • 1) = 0) :
    ((1/2:ℝ) • (A • S1 + B • S2) - (4 * A) • 1) *
      ((1/2:ℝ) • (A • S1 + B • S2) - (3 * A + B) • 1) = 0 := by
  have : ((1/2:ℝ) • (A • S1 + B • S2) - (4 * A) • 1) *
      ((1/2:ℝ) • (A • S1 + B • S2) - (3 * A + B) • 1) =
      ((1/4:ℝ) * A ^ 2) • ((S1 - (8:ℝ) • 1) * (S1 - (6:ℝ) • 1)) +
      ((1/4:ℝ) * (A * B)) • ((S1 - (8:ℝ) • 1) * (S2 - (2:ℝ) • 1) + S2 * (S1 - (6:ℝ) • 1)) +
      ((1/4:ℝ) * B ^ 2) • (S2 * (S2 - (2:ℝ) • 1)) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_one, one_mul, smul_add, smul_sub]
    module
  rw [this, h1, h2, h3]; simp


theorem contain_algebra (S1 S2 D1 D2 : Matrix n n ℝ) (A B : ℝ)
    (hc1 : S1 * D1 - D1 * S1 = 0)
    (hc2 : (S1 * D2 - D2 * S1) + (S2 * D1 - D1 * S2) = 0)
    (hc3 : S2 * D2 - D2 * S2 = 0)
    (ho1 : D1 * (S1 - (12:ℝ) • 1) = 0)
    (ho2 : D1 * S2 + D2 * (S1 - (12:ℝ) • 1) = 0)
    (ho3 : D2 * S2 = 0)
    (hq1 : (2:ℝ) • ((S1 - (8:ℝ) • 1) * (S1 - (2:ℝ) • 1)) - (5:ℝ) • (D1 * D1) = 0)
    (hq2 : (2:ℝ) • ((S1 - (8:ℝ) • 1) * (S2 - (2:ℝ) • 1) + S2 * (S1 - (2:ℝ) • 1))
      - (5:ℝ) • (D1 * D2 + D2 * D1) + D1 * D1 = 0)
    (hq3 : (2:ℝ) • (S2 * (S2 - (2:ℝ) • 1)) - (5:ℝ) • (D2 * D2) + (D1 * D2 + D2 * D1) = 0)
    (hq4 : D2 * D2 = 0) :
    let E : Matrix n n ℝ := (1/2:ℝ) • (A • S1 + B • S2)
    let O : Matrix n n ℝ := (1/2:ℝ) • (A • D1 + B • D2)
    E * O = O * E ∧ O * (E - (6 * A) • 1) = 0 ∧
      (2 * A) • ((E - (4 * A) • 1) * (E - (A + B) • 1)) - (5 * A - B) • (O * O) = 0 := by
  intro E O
  refine ⟨?_, ?_, ?_⟩
  · have : E * O - O * E = ((1/4:ℝ) * A ^ 2) • (S1 * D1 - D1 * S1) +
        ((1/4:ℝ) * (A * B)) • ((S1 * D2 - D2 * S1) + (S2 * D1 - D1 * S2)) +
        ((1/4:ℝ) * B ^ 2) • (S2 * D2 - D2 * S2) := by
      simp only [E, O, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
        smul_smul, mul_one, one_mul, smul_add, smul_sub, one_smul]
      module
    have h0 : E * O - O * E = 0 := by rw [this, hc1, hc2, hc3]; simp
    exact sub_eq_zero.mp h0
  · have : O * (E - (6 * A) • 1) = ((1/4:ℝ) * A ^ 2) • (D1 * (S1 - (12:ℝ) • 1)) +
        ((1/4:ℝ) * (A * B)) • (D1 * S2 + D2 * (S1 - (12:ℝ) • 1)) +
        ((1/4:ℝ) * B ^ 2) • (D2 * S2) := by
      simp only [E, O, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
        smul_smul, mul_one, one_mul, smul_add, smul_sub, one_smul]
      module
    rw [this, ho1, ho2, ho3]; simp
  · have : (2 * A) • ((E - (4 * A) • 1) * (E - (A + B) • 1)) - (5 * A - B) • (O * O) =
        ((1/4:ℝ) * A ^ 3) • ((2:ℝ) • ((S1 - (8:ℝ) • 1) * (S1 - (2:ℝ) • 1)) - (5:ℝ) • (D1 * D1)) +
        ((1/4:ℝ) * (A ^ 2 * B)) • ((2:ℝ) • ((S1 - (8:ℝ) • 1) * (S2 - (2:ℝ) • 1) + S2 * (S1 - (2:ℝ) • 1))
          - (5:ℝ) • (D1 * D2 + D2 * D1) + D1 * D1) +
        ((1/4:ℝ) * (A * B ^ 2)) • ((2:ℝ) • (S2 * (S2 - (2:ℝ) • 1)) - (5:ℝ) • (D2 * D2) + (D1 * D2 + D2 * D1)) +
        ((1/4:ℝ) * B ^ 3) • (D2 * D2) := by
      simp only [E, O, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
        smul_smul, mul_one, one_mul, smul_add, smul_sub, one_smul]
      module
    rw [this, hq1, hq2, hq3, hq4]; simp

end Algebra

/-! ### The spin-flip `ε^{⊗3}` and the integer certificates -/

/-- The single-qubit `ε = [[0,1],[-1,0]]`, indexed by bits. -/
def epsBit (a b : Bool) : ℤ :=
  if a = false ∧ b = true then 1 else if a = true ∧ b = false then -1 else 0

/-- `ε ⊗ ε ⊗ ε` as an integer matrix on three qubits. -/
def eps3 : Matrix Triple Triple ℤ := Matrix.of fun a b => ∏ i, epsBit (a i) (b i)

/-- `M ↦ ε^{⊗3} Mᵀ (ε^{⊗3})ᵀ` on integer matrices. -/
def flipMat (M : Matrix Triple Triple ℤ) : Matrix Triple Triple ℤ := eps3 * Mᵀ * eps3ᵀ

/-- `c · I`. -/
def sc (c : ℤ) : Matrix Triple Triple ℤ := c • 1

/-- Doubled even parts and doubled odd parts of the `α²`- and `β²`-coefficient matrices. -/
def sP (cut : Cut 3 4) : Matrix Triple Triple ℤ := matP cut + flipMat (matP cut)
def sR (cut : Cut 3 4) : Matrix Triple Triple ℤ := matR cut + flipMat (matR cut)
def dP (cut : Cut 3 4) : Matrix Triple Triple ℤ := matP cut - flipMat (matP cut)
def dR (cut : Cut 3 4) : Matrix Triple Triple ℤ := matR cut - flipMat (matR cut)

/-- Integer coefficient identities for a cut avoiding the special site. -/
def AvoidFlip (cut : Cut 3 4) : Prop :=
  dP cut = 0 ∧ dR cut = 0 ∧
    (sP cut - sc 8) * (sP cut - sc 6) = 0 ∧
    (sP cut - sc 8) * (sR cut - sc 2) + sR cut * (sP cut - sc 6) = 0 ∧
    sR cut * (sR cut - sc 2) = 0

/-- Integer coefficient identities for a cut containing the special site. -/
def ContainFlipA (cut : Cut 3 4) : Prop :=
  sP cut * dP cut - dP cut * sP cut = 0 ∧
  (sP cut * dR cut - dR cut * sP cut) + (sR cut * dP cut - dP cut * sR cut) = 0 ∧
  sR cut * dR cut - dR cut * sR cut = 0 ∧
  dP cut * (sP cut - sc 12) = 0 ∧
  dP cut * sR cut + dR cut * (sP cut - sc 12) = 0 ∧
  dR cut * sR cut = 0

def ContainFlipB (cut : Cut 3 4) : Prop :=
  (2:ℤ) • ((sP cut - sc 8) * (sP cut - sc 2)) - (5:ℤ) • (dP cut * dP cut) = 0 ∧
  (2:ℤ) • ((sP cut - sc 8) * (sR cut - sc 2) + sR cut * (sP cut - sc 2))
    - (5:ℤ) • (dP cut * dR cut + dR cut * dP cut) + dP cut * dP cut = 0 ∧
  (2:ℤ) • (sR cut * (sR cut - sc 2)) - (5:ℤ) • (dR cut * dR cut)
    + (dP cut * dR cut + dR cut * dP cut) = 0 ∧
  dR cut * dR cut = 0

def ContainFlip (cut : Cut 3 4) : Prop := ContainFlipA cut ∧ ContainFlipB cut

instance (cut : Cut 3 4) : Decidable (AvoidFlip cut) := by unfold AvoidFlip; infer_instance
instance (cut : Cut 3 4) : Decidable (ContainFlipA cut) := by unfold ContainFlipA; infer_instance
instance (cut : Cut 3 4) : Decidable (ContainFlipB cut) := by unfold ContainFlipB; infer_instance
instance (cut : Cut 3 4) : Decidable (ContainFlip cut) := by unfold ContainFlip; infer_instance

def FlipCert (m : Fin 7 → Bool) : Prop :=
  weight m = 3 →
    (m 0 = true → ContainFlip (maskCut 3 4 m)) ∧ (¬ m 0 = true → AvoidFlip (maskCut 3 4 m))

instance (m : Fin 7 → Bool) : Decidable (FlipCert m) := by unfold FlipCert; infer_instance

theorem flipCert_chunk0 : ∀ k < 16, FlipCert (maskOfNat (16 * 0 + k)) := by decide +kernel
theorem flipCert_chunk1 : ∀ k < 16, FlipCert (maskOfNat (16 * 1 + k)) := by decide +kernel
theorem flipCert_chunk2 : ∀ k < 16, FlipCert (maskOfNat (16 * 2 + k)) := by decide +kernel
theorem flipCert_chunk3 : ∀ k < 16, FlipCert (maskOfNat (16 * 3 + k)) := by decide +kernel
theorem flipCert_chunk4 : ∀ k < 16, FlipCert (maskOfNat (16 * 4 + k)) := by decide +kernel
theorem flipCert_chunk5 : ∀ k < 16, FlipCert (maskOfNat (16 * 5 + k)) := by decide +kernel
theorem flipCert_chunk6 : ∀ k < 16, FlipCert (maskOfNat (16 * 6 + k)) := by decide +kernel
theorem flipCert_chunk7 : ∀ k < 16, FlipCert (maskOfNat (16 * 7 + k)) := by decide +kernel

theorem flip_cert (m : Fin 7 → Bool) : FlipCert m := by
  obtain ⟨n, hn, rfl⟩ := maskOfNat_surjective m
  obtain ⟨c, k, hk, hc, rfl⟩ : ∃ c k, k < 16 ∧ c < 8 ∧ n = 16 * c + k :=
    ⟨n / 16, n % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [flipCert_chunk0 k hk, flipCert_chunk1 k hk, flipCert_chunk2 k hk, flipCert_chunk3 k hk,
    flipCert_chunk4 k hk, flipCert_chunk5 k hk, flipCert_chunk6 k hk, flipCert_chunk7 k hk]

/-! ### The real matrices -/

abbrev RM := Matrix Triple Triple ℝ

/-- Integer matrices to real matrices. -/
abbrev castZ : Matrix Triple Triple ℤ →+* RM := (Int.castRingHom ℝ).mapMatrix

/-- The triple marginal `R` of `icosahedralState alpha beta` across a three-qubit cut. -/
noncomputable def realRed (cut : Cut 3 4) (alpha beta : ℝ) : RM :=
  Matrix.of fun a b => entry cut alpha beta a b

/-- `R̃ = ε^{⊗3} Rᵀ (ε^{⊗3})ᵀ`. -/
noncomputable def spinFlip (R : RM) : RM := castZ eps3 * Rᵀ * (castZ eps3)ᵀ

/-- `E = (R + R̃)/2`. -/
noncomputable def evenPart (R : RM) : RM := (1/2 : ℝ) • (R + spinFlip R)

/-- `O = (R - R̃)/2`. -/
noncomputable def oddPart (R : RM) : RM := (1/2 : ℝ) • (R - spinFlip R)

theorem castZ_smul (c : ℤ) (X : Matrix Triple Triple ℤ) : castZ (c • X) = (c : ℝ) • castZ X := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    eq_intCast]

theorem castZ_sc (c : ℤ) : castZ (sc c) = (c : ℝ) • (1 : RM) := by
  unfold sc
  rw [castZ_smul, map_one]

theorem spinFlip_comb (X Y : RM) (A B : ℝ) :
    spinFlip (A • X + B • Y) = A • spinFlip X + B • spinFlip Y := by
  simp only [spinFlip, transpose_add, transpose_smul, mul_add, add_mul, mul_smul_comm,
    smul_mul_assoc]

theorem spinFlip_castZ (M : Matrix Triple Triple ℤ) : spinFlip (castZ M) = castZ (flipMat M) := by
  simp only [spinFlip, flipMat, map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem realRed_eq (cut : Cut 3 4) (hQ : matQ cut = 0) (alpha beta : ℝ) :
    realRed cut alpha beta = (alpha ^ 2) • castZ (matP cut) + (beta ^ 2) • castZ (matR cut) := by
  ext a b
  have hq : gramQ cut a b = 0 := by
    have := congrFun (congrFun hQ a) b
    simpa [matQ] using this
  simp [realRed, entry_expand, hq, matP, matR, RingHom.mapMatrix_apply]

theorem evenPart_eq (cut : Cut 3 4) (hQ : matQ cut = 0) (alpha beta : ℝ) :
    evenPart (realRed cut alpha beta) =
      (1/2 : ℝ) • ((alpha ^ 2) • castZ (sP cut) + (beta ^ 2) • castZ (sR cut)) := by
  rw [evenPart, realRed_eq cut hQ, spinFlip_comb, spinFlip_castZ, spinFlip_castZ]
  simp only [sP, sR, map_add]
  module

theorem oddPart_eq (cut : Cut 3 4) (hQ : matQ cut = 0) (alpha beta : ℝ) :
    oddPart (realRed cut alpha beta) =
      (1/2 : ℝ) • ((alpha ^ 2) • castZ (dP cut) + (beta ^ 2) • castZ (dR cut)) := by
  rw [oddPart, realRed_eq cut hQ, spinFlip_comb, spinFlip_castZ, spinFlip_castZ]
  simp only [dP, dR, map_sub]
  module

/-- Cuts avoiding the special site. -/
theorem avoiding_spinflip (cut : Cut 3 4) (hQ : matQ cut = 0) (h : AvoidFlip cut)
    (alpha beta : ℝ) :
    oddPart (realRed cut alpha beta) = 0 ∧
      (evenPart (realRed cut alpha beta) - (4 * alpha ^ 2) • (1 : RM)) *
        (evenPart (realRed cut alpha beta) - (3 * alpha ^ 2 + beta ^ 2) • (1 : RM)) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  constructor
  · rw [oddPart_eq cut hQ]
    have e1 : castZ (dP cut) = 0 := by rw [h1, map_zero]
    have e2 : castZ (dR cut) = 0 := by rw [h2, map_zero]
    rw [e1, e2]; simp
  · rw [evenPart_eq cut hQ]
    have t3 := congrArg castZ h3
    have t4 := congrArg castZ h4
    have t5 := congrArg castZ h5
    simp only [map_mul, map_sub, map_add, castZ_sc, map_zero] at t3 t4 t5
    push_cast at t3 t4 t5
    exact avoid_algebra _ _ _ _ t3 t4 t5

/-- Cuts containing the special site. -/
theorem containing_spinflip (cut : Cut 3 4) (hQ : matQ cut = 0) (h : ContainFlip cut)
    (alpha beta : ℝ) :
    evenPart (realRed cut alpha beta) * oddPart (realRed cut alpha beta) =
        oddPart (realRed cut alpha beta) * evenPart (realRed cut alpha beta) ∧
      oddPart (realRed cut alpha beta) *
        (evenPart (realRed cut alpha beta) - (6 * alpha ^ 2) • (1 : RM)) = 0 ∧
      (2 * alpha ^ 2) • ((evenPart (realRed cut alpha beta) - (4 * alpha ^ 2) • (1 : RM)) *
          (evenPart (realRed cut alpha beta) - (alpha ^ 2 + beta ^ 2) • (1 : RM))) -
        (5 * alpha ^ 2 - beta ^ 2) • (oddPart (realRed cut alpha beta) *
          oddPart (realRed cut alpha beta)) = 0 := by
  obtain ⟨⟨c1, c2, c3, o1, o2, o3⟩, q1, q2, q3, q4⟩ := h
  rw [evenPart_eq cut hQ, oddPart_eq cut hQ]
  have t1 := congrArg castZ c1
  have t2 := congrArg castZ c2
  have t3 := congrArg castZ c3
  have u1 := congrArg castZ o1
  have u2 := congrArg castZ o2
  have u3 := congrArg castZ o3
  have v1 := congrArg castZ q1
  have v2 := congrArg castZ q2
  have v3 := congrArg castZ q3
  have v4 := congrArg castZ q4
  simp only [map_mul, map_sub, map_add, castZ_sc, castZ_smul, map_zero] at t1 t2 t3 u1 u2 u3 v1 v2 v3 v4
  push_cast at t1 t2 t3 u1 u2 u3 v1 v2 v3 v4
  exact contain_algebra _ _ _ _ _ _ t1 t2 t3 u1 u2 u3 v1 v2 v3 v4

/-! ### All 35 cuts -/

/-- **`lem:seven-adaptive-joint-spinflip`** (exact AH-5), for arbitrary real amplitudes
`(alpha, beta)` (so `u = alpha²`, `x = beta²`, homogeneous form): for every three-qubit cut `m`
(site `0` is the distinguished site), with `R` the triple marginal, `R̃ = ε^{⊗3} Rᵀ (ε^{⊗3})ᵀ`,
`E = (R+R̃)/2`, `O = (R-R̃)/2`. -/
theorem tripleCut_spinflip (m : Fin 7 → Bool) (hm : weight m = 3) (alpha beta : ℝ) :
    let R := realRed (maskCut 3 4 m) alpha beta
    (¬ m 0 = true →
      oddPart R = 0 ∧
        (evenPart R - (4 * alpha ^ 2) • (1 : RM)) *
          (evenPart R - (3 * alpha ^ 2 + beta ^ 2) • (1 : RM)) = 0) ∧
    (m 0 = true →
      evenPart R * oddPart R = oddPart R * evenPart R ∧
        oddPart R * (evenPart R - (6 * alpha ^ 2) • (1 : RM)) = 0 ∧
        (2 * alpha ^ 2) • ((evenPart R - (4 * alpha ^ 2) • (1 : RM)) *
            (evenPart R - (alpha ^ 2 + beta ^ 2) • (1 : RM))) -
          (5 * alpha ^ 2 - beta ^ 2) • (oddPart R * oddPart R) = 0) := by
  intro R
  obtain ⟨hc, ha⟩ := flip_cert m hm
  obtain ⟨hc0, ha0⟩ := cuts_cert m hm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact avoiding_spinflip _ (ha0 h).1 (ha h) alpha beta
  · exact containing_spinflip _ (hc0 h).1 (hc h) alpha beta

/-- The statement on the normalized family `α² = u x = (1-2x)/30`, `β² = x`. -/
theorem tripleCut_spinflip_family (m : Fin 7 → Bool) (hm : weight m = 3) (x alpha beta : ℝ)
    (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    let R := realRed (maskCut 3 4 m) alpha beta
    (¬ m 0 = true →
      oddPart R = 0 ∧
        (evenPart R - (4 * u x) • (1 : RM)) * (evenPart R - (3 * u x + x) • (1 : RM)) = 0) ∧
    (m 0 = true →
      evenPart R * oddPart R = oddPart R * evenPart R ∧
        oddPart R * (evenPart R - (6 * u x) • (1 : RM)) = 0 ∧
        (2 * u x) • ((evenPart R - (4 * u x) • (1 : RM)) * (evenPart R - (u x + x) • (1 : RM))) -
          (5 * u x - x) • (oddPart R * oddPart R) = 0) := by
  have h := tripleCut_spinflip m hm alpha beta
  rw [hα, hβ] at h
  exact h

end FormalResearch.FourQubitEntropy.SevenQubitIco
