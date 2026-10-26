import FormalResearch.FourQubitEntropy.SevenQubitIcoPurity

/-!
# Integer certificates for the spectra of the three-qubit cuts

For every three-qubit cut of the seven-qubit icosahedral family the Gram matrices `P`, `Q`, `R`
(of `αα`, `αβ+βα`, `ββ`, see `SevenQubitIcoPurity`) satisfy a few integer matrix identities, checked
in the kernel for all 35 cuts. `SevenQubitIcoSpectrum` derives the spectra from them.
-/

open Matrix

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Integer certificates for every three-qubit cut -/

abbrev Triple := Fin 3 → Bool

/-- The `αα`, `αβ+βα` and `ββ` Gram matrices of a three-qubit cut as integer matrices. -/
def matP (cut : Cut 3 4) : Matrix Triple Triple ℤ := Matrix.of (gramP cut)
def matQ (cut : Cut 3 4) : Matrix Triple Triple ℤ := Matrix.of (gramQ cut)
def matR (cut : Cut 3 4) : Matrix Triple Triple ℤ := Matrix.of (gramR cut)
/-- The integer matrix with eigenvalues `0, 4, 8` on a cut containing the special site. -/
def matT (cut : Cut 3 4) : Matrix Triple Triple ℤ := matP cut - 4 + (11 : ℤ) • matR cut

/-- Cuts avoiding the special site: `Q = 0`, `R` is an idempotent of trace `2` and `P = 4 - R`. -/
def AvoidCert (cut : Cut 3 4) : Prop :=
  matQ cut = 0 ∧ matR cut * matR cut = matR cut ∧ matP cut = 4 - matR cut ∧ trace (matR cut) = 2

/-- Cuts containing the special site: `Q = 0`, `T = P - 4 + 11 R` satisfies `T (T-4)(T-8) = 0`,
`32 R = T² - 4T`, `tr T = 20`, `tr T² = 144`. -/
def ContainCert (cut : Cut 3 4) : Prop :=
  matQ cut = 0 ∧ matT cut * (matT cut - 4) * (matT cut - 8) = 0 ∧
    32 * matR cut = matT cut * matT cut - 4 * matT cut ∧ trace (matT cut) = 20 ∧
      trace (matT cut * matT cut) = 144

instance (cut : Cut 3 4) : Decidable (AvoidCert cut) := by unfold AvoidCert; infer_instance
instance (cut : Cut 3 4) : Decidable (ContainCert cut) := by unfold ContainCert; infer_instance

/-- The mask with bit `i` equal to the `i`-th binary digit of `n`. -/
def maskOfNat (n : ℕ) : Fin 7 → Bool := fun i => n.testBit i.val

theorem maskOfNat_surjective : ∀ m : Fin 7 → Bool, ∃ n < 128, maskOfNat n = m := by
  decide +kernel

/-- The certificates of a mask: `AvoidCert` or `ContainCert` according to the special site. -/
def CutCert (m : Fin 7 → Bool) : Prop :=
  weight m = 3 →
    (m 0 = true → ContainCert (maskCut 3 4 m)) ∧ (¬ m 0 = true → AvoidCert (maskCut 3 4 m))

instance (m : Fin 7 → Bool) : Decidable (CutCert m) := by unfold CutCert; infer_instance

-- The kernel keeps its caches for the length of a proof, so the 128 masks are checked in eight chunks.
theorem cutCert_chunk0 : ∀ k < 16, CutCert (maskOfNat (16 * 0 + k)) := by decide +kernel
theorem cutCert_chunk1 : ∀ k < 16, CutCert (maskOfNat (16 * 1 + k)) := by decide +kernel
theorem cutCert_chunk2 : ∀ k < 16, CutCert (maskOfNat (16 * 2 + k)) := by decide +kernel
theorem cutCert_chunk3 : ∀ k < 16, CutCert (maskOfNat (16 * 3 + k)) := by decide +kernel
theorem cutCert_chunk4 : ∀ k < 16, CutCert (maskOfNat (16 * 4 + k)) := by decide +kernel
theorem cutCert_chunk5 : ∀ k < 16, CutCert (maskOfNat (16 * 5 + k)) := by decide +kernel
theorem cutCert_chunk6 : ∀ k < 16, CutCert (maskOfNat (16 * 6 + k)) := by decide +kernel
theorem cutCert_chunk7 : ∀ k < 16, CutCert (maskOfNat (16 * 7 + k)) := by decide +kernel

theorem cuts_cert (m : Fin 7 → Bool) : CutCert m := by
  obtain ⟨n, hn, rfl⟩ := maskOfNat_surjective m
  obtain ⟨c, k, hk, hc, rfl⟩ : ∃ c k, k < 16 ∧ c < 8 ∧ n = 16 * c + k :=
    ⟨n / 16, n % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [cutCert_chunk0 k hk, cutCert_chunk1 k hk, cutCert_chunk2 k hk, cutCert_chunk3 k hk,
    cutCert_chunk4 k hk, cutCert_chunk5 k hk, cutCert_chunk6 k hk, cutCert_chunk7 k hk]

end FormalResearch.FourQubitEntropy.SevenQubitIco
