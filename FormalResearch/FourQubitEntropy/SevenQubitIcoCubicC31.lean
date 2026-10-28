import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicSwap

/-!
# Kernel evaluation of the cubic forms of the icosahedral tensor, mask class `C31`

Class `C31`: masks `M < 128` with `cfPc M = 3 ∧ M &&& 1 = 1`. This file checks, in the kernel,
(i) the table `cfWP31` of the counts `cfCount` (`D ⊆ M`, `E ∩ M = ∅`) and (ii) the eight trilinear forms
`T(f,g,h)(z) = ∑ cfCount(z⊕v,z⊕u) f(u) g(v) h(z⊕u⊕v)` in the integer tables `cfA`, `cfB`, each of which turns
out to lie in `span{cfA, cfB}` with explicit integer coefficients, and concludes with
`cubicMaskSum_C31`: the cubic mask sum of `icosahedralState α β` over the class is
`s · cfA + t · cfB` (`s`, `t` cubic polynomials in `α`, `β`).
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- The class of masks. -/
def cfC31 (M : ℕ) : Prop := cfPc M = 3 ∧ M &&& 1 = 1

instance : DecidablePred cfC31 := fun M => inferInstanceAs (Decidable (cfPc M = 3 ∧ M &&& 1 = 1))

/-- The masks of the class. -/
def cfMasksC31 : List ℕ := [7, 11, 13, 19, 21, 25, 35, 37, 41, 49, 67, 69, 73, 81, 97]

theorem cfMasksC31_spec :
    cfMasksC31.Nodup ∧ (∀ x ∈ cfMasksC31, x < 128) ∧ ∀ M < 128, cfC31 M → M ∈ cfMasksC31 := by
  decide +kernel

/-- The weight table of the class (see `cfWt`). -/
def cfWP31 : ℕ := 34622310400568092400295273916629452707654673809533094495863947357676012803325861651181196566646131432408066720293611375489274115832806922568954264945725572062569514378845116543930938573104081549942700729879290885093487706784113820693343188243063127942843842671820915049758735
theorem cfWP31_valid_chunk0 : ∀ d < 32, ∀ E < 128, (32 * 0 + d) &&& E = 0 →
    (cfMasksC31.map fun M => if cfC31 M ∧ (32 * 0 + d) &&& M = (32 * 0 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP31 (32 * 0 + d) E := by
  decide +kernel
theorem cfWP31_valid_chunk1 : ∀ d < 32, ∀ E < 128, (32 * 1 + d) &&& E = 0 →
    (cfMasksC31.map fun M => if cfC31 M ∧ (32 * 1 + d) &&& M = (32 * 1 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP31 (32 * 1 + d) E := by
  decide +kernel
theorem cfWP31_valid_chunk2 : ∀ d < 32, ∀ E < 128, (32 * 2 + d) &&& E = 0 →
    (cfMasksC31.map fun M => if cfC31 M ∧ (32 * 2 + d) &&& M = (32 * 2 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP31 (32 * 2 + d) E := by
  decide +kernel
theorem cfWP31_valid_chunk3 : ∀ d < 32, ∀ E < 128, (32 * 3 + d) &&& E = 0 →
    (cfMasksC31.map fun M => if cfC31 M ∧ (32 * 3 + d) &&& M = (32 * 3 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP31 (32 * 3 + d) E := by
  decide +kernel
theorem cfWP31_valid : ∀ D < 128, ∀ E < 128, cfCount cfC31 D E = cfWt cfWP31 D E := by
  intro D hD E hE
  by_cases h : D &&& E = 0
  · rw [cfCount_eq_list cfC31 cfMasksC31 (cfMasksC31_spec).1 (cfMasksC31_spec).2.1 (cfMasksC31_spec).2.2]
    obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 32 ∧ c < 4 ∧ D = 32 * c + d :=
      ⟨D / 32, D % 32, by omega, by omega, by omega⟩
    interval_cases c
    exacts [cfWP31_valid_chunk0 d hd E hE h, cfWP31_valid_chunk1 d hd E hE h,
      cfWP31_valid_chunk2 d hd E hE h, cfWP31_valid_chunk3 d hd E hE h]
  · rw [cfCount_nondisj _ h]
    simp [cfWt, h]
theorem cfC31_AAA_chunk0 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 0 + d) = (73) * cfA (16 * 0 + d) + (0) * cfB (16 * 0 + d) := by
  decide +kernel
theorem cfC31_AAA_chunk1 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 1 + d) = (73) * cfA (16 * 1 + d) + (0) * cfB (16 * 1 + d) := by
  decide +kernel
theorem cfC31_AAA_chunk2 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 2 + d) = (73) * cfA (16 * 2 + d) + (0) * cfB (16 * 2 + d) := by
  decide +kernel
theorem cfC31_AAA_chunk3 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 3 + d) = (73) * cfA (16 * 3 + d) + (0) * cfB (16 * 3 + d) := by
  decide +kernel
theorem cfC31_AAA_chunk4 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 4 + d) = (73) * cfA (16 * 4 + d) + (0) * cfB (16 * 4 + d) := by
  decide +kernel
theorem cfC31_AAA_chunk5 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 5 + d) = (73) * cfA (16 * 5 + d) + (0) * cfB (16 * 5 + d) := by
  decide +kernel
theorem cfC31_AAA_chunk6 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 6 + d) = (73) * cfA (16 * 6 + d) + (0) * cfB (16 * 6 + d) := by
  decide +kernel
theorem cfC31_AAA_chunk7 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 7 + d) = (73) * cfA (16 * 7 + d) + (0) * cfB (16 * 7 + d) := by
  decide +kernel
theorem cfC31_AAA : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) z = (73) * cfA z + (0) * cfB z := by
  intro z hz
  obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 16 ∧ c < 8 ∧ z = 16 * c + d :=
    ⟨z / 16, z % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [cfC31_AAA_chunk0 d hd, cfC31_AAA_chunk1 d hd, cfC31_AAA_chunk2 d hd, cfC31_AAA_chunk3 d hd,
    cfC31_AAA_chunk4 d hd, cfC31_AAA_chunk5 d hd, cfC31_AAA_chunk6 d hd, cfC31_AAA_chunk7 d hd]
theorem cfC31_AAB_chunk0 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 0 + d) = (0) * cfA (16 * 0 + d) + (-15) * cfB (16 * 0 + d) := by
  decide +kernel
theorem cfC31_AAB_chunk1 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 1 + d) = (0) * cfA (16 * 1 + d) + (-15) * cfB (16 * 1 + d) := by
  decide +kernel
theorem cfC31_AAB_chunk2 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 2 + d) = (0) * cfA (16 * 2 + d) + (-15) * cfB (16 * 2 + d) := by
  decide +kernel
theorem cfC31_AAB_chunk3 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 3 + d) = (0) * cfA (16 * 3 + d) + (-15) * cfB (16 * 3 + d) := by
  decide +kernel
theorem cfC31_AAB_chunk4 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 4 + d) = (0) * cfA (16 * 4 + d) + (-15) * cfB (16 * 4 + d) := by
  decide +kernel
theorem cfC31_AAB_chunk5 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 5 + d) = (0) * cfA (16 * 5 + d) + (-15) * cfB (16 * 5 + d) := by
  decide +kernel
theorem cfC31_AAB_chunk6 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 6 + d) = (0) * cfA (16 * 6 + d) + (-15) * cfB (16 * 6 + d) := by
  decide +kernel
theorem cfC31_AAB_chunk7 : ∀ d < 16, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 7 + d) = (0) * cfA (16 * 7 + d) + (-15) * cfB (16 * 7 + d) := by
  decide +kernel
theorem cfC31_AAB : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) z = (0) * cfA z + (-15) * cfB z := by
  intro z hz
  obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 16 ∧ c < 8 ∧ z = 16 * c + d :=
    ⟨z / 16, z % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [cfC31_AAB_chunk0 d hd, cfC31_AAB_chunk1 d hd, cfC31_AAB_chunk2 d hd, cfC31_AAB_chunk3 d hd,
    cfC31_AAB_chunk4 d hd, cfC31_AAB_chunk5 d hd, cfC31_AAB_chunk6 d hd, cfC31_AAB_chunk7 d hd]
theorem cfC31_ABA : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp false) (cfSupp true) (cfTab false) (cfTab true) (cfTab false) z = (0) * cfA z + (15) * cfB z := by
  decide +kernel
theorem cfC31_ABB : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp false) (cfSupp true) (cfTab false) (cfTab true) (cfTab true) z = (1) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC31_BAA : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp true) (cfSupp false) (cfTab true) (cfTab false) (cfTab false) z = (0) * cfA z + (15) * cfB z := by
  decide +kernel
theorem cfC31_BAB : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp true) (cfSupp false) (cfTab true) (cfTab false) (cfTab true) z = (1) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC31_BBA : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp true) (cfSupp true) (cfTab true) (cfTab true) (cfTab false) z = (-1) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC31_BBB : ∀ z < 128, cubW (cfWt cfWP31) (cfSupp true) (cfSupp true) (cfTab true) (cfTab true) (cfTab true) z = (0) * cfA z + (15) * cfB z := by
  decide +kernel
theorem cfC31_hP : ∀ M < 128, (weight (maskOfNat M) = 3 ∧ maskOfNat M 0 = true) ↔ cfC31 M := by
  decide +kernel

theorem cfK_C31 (z : ℕ) (hz : z < 128) (x y w : Bool) (p q : ℤ)
    (h : cubW (cfWt cfWP31) (cfSupp x) (cfSupp y) (cfTab x) (cfTab y) (cfTab w) z = p * cfA z + q * cfB z) :
    cfK cfWP31 z x y w = (p : ℝ) * (cfA z : ℝ) + (q : ℝ) * (cfB z : ℝ) := by
  unfold cfK
  rw [h]
  push_cast
  ring

/-- **Cubic mask sum over the class `C31`** for the icosahedral state: `s · cfA + t · cfB`. -/
theorem cubicMaskSum_C31 (α β : ℝ) (z : ℕ) (hz : z < 128) :
    cubicMaskSum (icosahedralState α β) (maskOfNat z) (fun m => weight m = 3 ∧ m 0 = true) =
      ((73) * α ^ 3 + (1) * α * β ^ 2) * (cfA z : ℝ) + ((15) * α ^ 2 * β + (15) * β ^ 3) * (cfB z : ℝ) := by
  rw [cubicMaskSum_ico (fun m => weight m = 3 ∧ m 0 = true) cfC31 (fun M hM => cfC31_hP M hM) cfWP31 cfWP31_valid α β z hz]
  rw [cfK_C31 z hz false false false _ _ (cfC31_AAA z hz)]
  rw [cfK_C31 z hz false false true _ _ (cfC31_AAB z hz)]
  rw [cfK_C31 z hz false true false _ _ (cfC31_ABA z hz)]
  rw [cfK_C31 z hz false true true _ _ (cfC31_ABB z hz)]
  rw [cfK_C31 z hz true false false _ _ (cfC31_BAA z hz)]
  rw [cfK_C31 z hz true false true _ _ (cfC31_BAB z hz)]
  rw [cfK_C31 z hz true true false _ _ (cfC31_BBA z hz)]
  rw [cfK_C31 z hz true true true _ _ (cfC31_BBB z hz)]
  ring

end FormalResearch.FourQubitEntropy.SevenQubitIco
