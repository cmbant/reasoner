import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicSwap

/-!
# Kernel evaluation of the cubic forms of the icosahedral tensor, mask class `C30`

Class `C30`: masks `M < 128` with `cfPc M = 3 ∧ M &&& 1 = 0`. This file checks, in the kernel,
(i) the table `cfWP30` of the counts `cfCount` (`D ⊆ M`, `E ∩ M = ∅`) and (ii) the eight trilinear forms
`T(f,g,h)(z) = ∑ cfCount(z⊕v,z⊕u) f(u) g(v) h(z⊕u⊕v)` in the integer tables `cfA`, `cfB`, each of which turns
out to lie in `span{cfA, cfB}` with explicit integer coefficients, and concludes with
`cubicMaskSum_C30`: the cubic mask sum of `icosahedralState α β` over the class is
`s · cfA + t · cfB` (`s`, `t` cubic polynomials in `α`, `β`).
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- The class of masks. -/
def cfC30 (M : ℕ) : Prop := cfPc M = 3 ∧ M &&& 1 = 0

instance : DecidablePred cfC30 := fun M => inferInstanceAs (Decidable (cfPc M = 3 ∧ M &&& 1 = 0))

/-- The masks of the class. -/
def cfMasksC30 : List ℕ := [14, 22, 26, 28, 38, 42, 44, 50, 52, 56, 70, 74, 76, 82, 84, 88, 98, 100, 104, 112]

theorem cfMasksC30_spec :
    cfMasksC30.Nodup ∧ (∀ x ∈ cfMasksC30, x < 128) ∧ ∀ M < 128, cfC30 M → M ∈ cfMasksC30 := by
  decide +kernel

/-- The weight table of the class (see `cfWt`). -/
def cfWP30 : ℕ := 135243400002342114094405188849326790062200699757575456155467712659278232975871153436124419662280890433768867272778384799646638291419511478807848389860906518597157224118539172331651123438228449576908207191124346262048367808699740923847394313366673660612487408880044199641108
theorem cfWP30_valid_chunk0 : ∀ d < 32, ∀ E < 128, (32 * 0 + d) &&& E = 0 →
    (cfMasksC30.map fun M => if cfC30 M ∧ (32 * 0 + d) &&& M = (32 * 0 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP30 (32 * 0 + d) E := by
  decide +kernel
theorem cfWP30_valid_chunk1 : ∀ d < 32, ∀ E < 128, (32 * 1 + d) &&& E = 0 →
    (cfMasksC30.map fun M => if cfC30 M ∧ (32 * 1 + d) &&& M = (32 * 1 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP30 (32 * 1 + d) E := by
  decide +kernel
theorem cfWP30_valid_chunk2 : ∀ d < 32, ∀ E < 128, (32 * 2 + d) &&& E = 0 →
    (cfMasksC30.map fun M => if cfC30 M ∧ (32 * 2 + d) &&& M = (32 * 2 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP30 (32 * 2 + d) E := by
  decide +kernel
theorem cfWP30_valid_chunk3 : ∀ d < 32, ∀ E < 128, (32 * 3 + d) &&& E = 0 →
    (cfMasksC30.map fun M => if cfC30 M ∧ (32 * 3 + d) &&& M = (32 * 3 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP30 (32 * 3 + d) E := by
  decide +kernel
theorem cfWP30_valid : ∀ D < 128, ∀ E < 128, cfCount cfC30 D E = cfWt cfWP30 D E := by
  intro D hD E hE
  by_cases h : D &&& E = 0
  · rw [cfCount_eq_list cfC30 cfMasksC30 (cfMasksC30_spec).1 (cfMasksC30_spec).2.1 (cfMasksC30_spec).2.2]
    obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 32 ∧ c < 4 ∧ D = 32 * c + d :=
      ⟨D / 32, D % 32, by omega, by omega, by omega⟩
    interval_cases c
    exacts [cfWP30_valid_chunk0 d hd E hE h, cfWP30_valid_chunk1 d hd E hE h,
      cfWP30_valid_chunk2 d hd E hE h, cfWP30_valid_chunk3 d hd E hE h]
  · rw [cfCount_nondisj _ h]
    simp [cfWt, h]
theorem cfC30_AAA_chunk0 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 0 + d) = (76) * cfA (16 * 0 + d) + (0) * cfB (16 * 0 + d) := by
  decide +kernel
theorem cfC30_AAA_chunk1 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 1 + d) = (76) * cfA (16 * 1 + d) + (0) * cfB (16 * 1 + d) := by
  decide +kernel
theorem cfC30_AAA_chunk2 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 2 + d) = (76) * cfA (16 * 2 + d) + (0) * cfB (16 * 2 + d) := by
  decide +kernel
theorem cfC30_AAA_chunk3 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 3 + d) = (76) * cfA (16 * 3 + d) + (0) * cfB (16 * 3 + d) := by
  decide +kernel
theorem cfC30_AAA_chunk4 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 4 + d) = (76) * cfA (16 * 4 + d) + (0) * cfB (16 * 4 + d) := by
  decide +kernel
theorem cfC30_AAA_chunk5 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 5 + d) = (76) * cfA (16 * 5 + d) + (0) * cfB (16 * 5 + d) := by
  decide +kernel
theorem cfC30_AAA_chunk6 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 6 + d) = (76) * cfA (16 * 6 + d) + (0) * cfB (16 * 6 + d) := by
  decide +kernel
theorem cfC30_AAA_chunk7 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 7 + d) = (76) * cfA (16 * 7 + d) + (0) * cfB (16 * 7 + d) := by
  decide +kernel
theorem cfC30_AAA : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) z = (76) * cfA z + (0) * cfB z := by
  intro z hz
  obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 16 ∧ c < 8 ∧ z = 16 * c + d :=
    ⟨z / 16, z % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [cfC30_AAA_chunk0 d hd, cfC30_AAA_chunk1 d hd, cfC30_AAA_chunk2 d hd, cfC30_AAA_chunk3 d hd,
    cfC30_AAA_chunk4 d hd, cfC30_AAA_chunk5 d hd, cfC30_AAA_chunk6 d hd, cfC30_AAA_chunk7 d hd]
theorem cfC30_AAB_chunk0 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 0 + d) = (0) * cfA (16 * 0 + d) + (0) * cfB (16 * 0 + d) := by
  decide +kernel
theorem cfC30_AAB_chunk1 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 1 + d) = (0) * cfA (16 * 1 + d) + (0) * cfB (16 * 1 + d) := by
  decide +kernel
theorem cfC30_AAB_chunk2 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 2 + d) = (0) * cfA (16 * 2 + d) + (0) * cfB (16 * 2 + d) := by
  decide +kernel
theorem cfC30_AAB_chunk3 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 3 + d) = (0) * cfA (16 * 3 + d) + (0) * cfB (16 * 3 + d) := by
  decide +kernel
theorem cfC30_AAB_chunk4 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 4 + d) = (0) * cfA (16 * 4 + d) + (0) * cfB (16 * 4 + d) := by
  decide +kernel
theorem cfC30_AAB_chunk5 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 5 + d) = (0) * cfA (16 * 5 + d) + (0) * cfB (16 * 5 + d) := by
  decide +kernel
theorem cfC30_AAB_chunk6 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 6 + d) = (0) * cfA (16 * 6 + d) + (0) * cfB (16 * 6 + d) := by
  decide +kernel
theorem cfC30_AAB_chunk7 : ∀ d < 16, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 7 + d) = (0) * cfA (16 * 7 + d) + (0) * cfB (16 * 7 + d) := by
  decide +kernel
theorem cfC30_AAB : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) z = (0) * cfA z + (0) * cfB z := by
  intro z hz
  obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 16 ∧ c < 8 ∧ z = 16 * c + d :=
    ⟨z / 16, z % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [cfC30_AAB_chunk0 d hd, cfC30_AAB_chunk1 d hd, cfC30_AAB_chunk2 d hd, cfC30_AAB_chunk3 d hd,
    cfC30_AAB_chunk4 d hd, cfC30_AAB_chunk5 d hd, cfC30_AAB_chunk6 d hd, cfC30_AAB_chunk7 d hd]
theorem cfC30_ABA : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp false) (cfSupp true) (cfTab false) (cfTab true) (cfTab false) z = (0) * cfA z + (60) * cfB z := by
  decide +kernel
theorem cfC30_ABB : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp false) (cfSupp true) (cfTab false) (cfTab true) (cfTab true) z = (0) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC30_BAA : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp true) (cfSupp false) (cfTab true) (cfTab false) (cfTab false) z = (0) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC30_BAB : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp true) (cfSupp false) (cfTab true) (cfTab false) (cfTab true) z = (4) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC30_BBA : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp true) (cfSupp true) (cfTab true) (cfTab true) (cfTab false) z = (0) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC30_BBB : ∀ z < 128, cubW (cfWt cfWP30) (cfSupp true) (cfSupp true) (cfTab true) (cfTab true) (cfTab true) z = (0) * cfA z + (20) * cfB z := by
  decide +kernel
theorem cfC30_hP : ∀ M < 128, (weight (maskOfNat M) = 3 ∧ maskOfNat M 0 = false) ↔ cfC30 M := by
  decide +kernel

theorem cfK_C30 (z : ℕ) (hz : z < 128) (x y w : Bool) (p q : ℤ)
    (h : cubW (cfWt cfWP30) (cfSupp x) (cfSupp y) (cfTab x) (cfTab y) (cfTab w) z = p * cfA z + q * cfB z) :
    cfK cfWP30 z x y w = (p : ℝ) * (cfA z : ℝ) + (q : ℝ) * (cfB z : ℝ) := by
  unfold cfK
  rw [h]
  push_cast
  ring

/-- **Cubic mask sum over the class `C30`** for the icosahedral state: `s · cfA + t · cfB`. -/
theorem cubicMaskSum_C30 (α β : ℝ) (z : ℕ) (hz : z < 128) :
    cubicMaskSum (icosahedralState α β) (maskOfNat z) (fun m => weight m = 3 ∧ m 0 = false) =
      ((76) * α ^ 3 + (4) * α * β ^ 2) * (cfA z : ℝ) + ((60) * α ^ 2 * β + (20) * β ^ 3) * (cfB z : ℝ) := by
  rw [cubicMaskSum_ico (fun m => weight m = 3 ∧ m 0 = false) cfC30 (fun M hM => cfC30_hP M hM) cfWP30 cfWP30_valid α β z hz]
  rw [cfK_C30 z hz false false false _ _ (cfC30_AAA z hz)]
  rw [cfK_C30 z hz false false true _ _ (cfC30_AAB z hz)]
  rw [cfK_C30 z hz false true false _ _ (cfC30_ABA z hz)]
  rw [cfK_C30 z hz false true true _ _ (cfC30_ABB z hz)]
  rw [cfK_C30 z hz true false false _ _ (cfC30_BAA z hz)]
  rw [cfK_C30 z hz true false true _ _ (cfC30_BAB z hz)]
  rw [cfK_C30 z hz true true false _ _ (cfC30_BBA z hz)]
  rw [cfK_C30 z hz true true true _ _ (cfC30_BBB z hz)]
  ring

end FormalResearch.FourQubitEntropy.SevenQubitIco
