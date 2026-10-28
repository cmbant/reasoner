import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicSwap

/-!
# Kernel evaluation of the cubic forms of the icosahedral tensor, mask class `C2`

Class `C2`: masks `M < 128` with `cfPc M = 2`. This file checks, in the kernel,
(i) the table `cfWP2` of the counts `cfCount` (`D ⊆ M`, `E ∩ M = ∅`) and (ii) the eight trilinear forms
`T(f,g,h)(z) = ∑ cfCount(z⊕v,z⊕u) f(u) g(v) h(z⊕u⊕v)` in the integer tables `cfA`, `cfB`, each of which turns
out to lie in `span{cfA, cfB}` with explicit integer coefficients, and concludes with
`cubicMaskSum_C2`: the cubic mask sum of `icosahedralState α β` over the class is
`s · cfA + t · cfB` (`s`, `t` cubic polynomials in `α`, `β`).
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- The class of masks. -/
def cfC2 (M : ℕ) : Prop := cfPc M = 2

instance : DecidablePred cfC2 := fun M => inferInstanceAs (Decidable (cfPc M = 2))

/-- The masks of the class. -/
def cfMasksC2 : List ℕ := [3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96]

theorem cfMasksC2_spec :
    cfMasksC2.Nodup ∧ (∀ x ∈ cfMasksC2, x < 128) ∧ ∀ M < 128, cfC2 M → M ∈ cfMasksC2 := by
  decide +kernel

/-- The weight table of the class (see `cfWt`). -/
def cfWP2 : ℕ := 1289229323399248150071799308395185019452822843317105961783884590814981166563637402751407679939349448947084272833797989884564860755051712231295961737993517769925669263614452266255275271072151975163993394249749
theorem cfWP2_valid_chunk0 : ∀ d < 32, ∀ E < 128, (32 * 0 + d) &&& E = 0 →
    (cfMasksC2.map fun M => if cfC2 M ∧ (32 * 0 + d) &&& M = (32 * 0 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP2 (32 * 0 + d) E := by
  decide +kernel
theorem cfWP2_valid_chunk1 : ∀ d < 32, ∀ E < 128, (32 * 1 + d) &&& E = 0 →
    (cfMasksC2.map fun M => if cfC2 M ∧ (32 * 1 + d) &&& M = (32 * 1 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP2 (32 * 1 + d) E := by
  decide +kernel
theorem cfWP2_valid_chunk2 : ∀ d < 32, ∀ E < 128, (32 * 2 + d) &&& E = 0 →
    (cfMasksC2.map fun M => if cfC2 M ∧ (32 * 2 + d) &&& M = (32 * 2 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP2 (32 * 2 + d) E := by
  decide +kernel
theorem cfWP2_valid_chunk3 : ∀ d < 32, ∀ E < 128, (32 * 3 + d) &&& E = 0 →
    (cfMasksC2.map fun M => if cfC2 M ∧ (32 * 3 + d) &&& M = (32 * 3 + d) ∧ E &&& M = 0 then 1 else 0).sum =
      cfWt cfWP2 (32 * 3 + d) E := by
  decide +kernel
theorem cfWP2_valid : ∀ D < 128, ∀ E < 128, cfCount cfC2 D E = cfWt cfWP2 D E := by
  intro D hD E hE
  by_cases h : D &&& E = 0
  · rw [cfCount_eq_list cfC2 cfMasksC2 (cfMasksC2_spec).1 (cfMasksC2_spec).2.1 (cfMasksC2_spec).2.2]
    obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 32 ∧ c < 4 ∧ D = 32 * c + d :=
      ⟨D / 32, D % 32, by omega, by omega, by omega⟩
    interval_cases c
    exacts [cfWP2_valid_chunk0 d hd E hE h, cfWP2_valid_chunk1 d hd E hE h,
      cfWP2_valid_chunk2 d hd E hE h, cfWP2_valid_chunk3 d hd E hE h]
  · rw [cfCount_nondisj _ h]
    simp [cfWt, h]
theorem cfC2_AAA_chunk0 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 0 + d) = (163) * cfA (16 * 0 + d) + (0) * cfB (16 * 0 + d) := by
  decide +kernel
theorem cfC2_AAA_chunk1 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 1 + d) = (163) * cfA (16 * 1 + d) + (0) * cfB (16 * 1 + d) := by
  decide +kernel
theorem cfC2_AAA_chunk2 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 2 + d) = (163) * cfA (16 * 2 + d) + (0) * cfB (16 * 2 + d) := by
  decide +kernel
theorem cfC2_AAA_chunk3 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 3 + d) = (163) * cfA (16 * 3 + d) + (0) * cfB (16 * 3 + d) := by
  decide +kernel
theorem cfC2_AAA_chunk4 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 4 + d) = (163) * cfA (16 * 4 + d) + (0) * cfB (16 * 4 + d) := by
  decide +kernel
theorem cfC2_AAA_chunk5 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 5 + d) = (163) * cfA (16 * 5 + d) + (0) * cfB (16 * 5 + d) := by
  decide +kernel
theorem cfC2_AAA_chunk6 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 6 + d) = (163) * cfA (16 * 6 + d) + (0) * cfB (16 * 6 + d) := by
  decide +kernel
theorem cfC2_AAA_chunk7 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) (16 * 7 + d) = (163) * cfA (16 * 7 + d) + (0) * cfB (16 * 7 + d) := by
  decide +kernel
theorem cfC2_AAA : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab false) z = (163) * cfA z + (0) * cfB z := by
  intro z hz
  obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 16 ∧ c < 8 ∧ z = 16 * c + d :=
    ⟨z / 16, z % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [cfC2_AAA_chunk0 d hd, cfC2_AAA_chunk1 d hd, cfC2_AAA_chunk2 d hd, cfC2_AAA_chunk3 d hd,
    cfC2_AAA_chunk4 d hd, cfC2_AAA_chunk5 d hd, cfC2_AAA_chunk6 d hd, cfC2_AAA_chunk7 d hd]
theorem cfC2_AAB_chunk0 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 0 + d) = (0) * cfA (16 * 0 + d) + (0) * cfB (16 * 0 + d) := by
  decide +kernel
theorem cfC2_AAB_chunk1 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 1 + d) = (0) * cfA (16 * 1 + d) + (0) * cfB (16 * 1 + d) := by
  decide +kernel
theorem cfC2_AAB_chunk2 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 2 + d) = (0) * cfA (16 * 2 + d) + (0) * cfB (16 * 2 + d) := by
  decide +kernel
theorem cfC2_AAB_chunk3 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 3 + d) = (0) * cfA (16 * 3 + d) + (0) * cfB (16 * 3 + d) := by
  decide +kernel
theorem cfC2_AAB_chunk4 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 4 + d) = (0) * cfA (16 * 4 + d) + (0) * cfB (16 * 4 + d) := by
  decide +kernel
theorem cfC2_AAB_chunk5 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 5 + d) = (0) * cfA (16 * 5 + d) + (0) * cfB (16 * 5 + d) := by
  decide +kernel
theorem cfC2_AAB_chunk6 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 6 + d) = (0) * cfA (16 * 6 + d) + (0) * cfB (16 * 6 + d) := by
  decide +kernel
theorem cfC2_AAB_chunk7 : ∀ d < 16, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) (16 * 7 + d) = (0) * cfA (16 * 7 + d) + (0) * cfB (16 * 7 + d) := by
  decide +kernel
theorem cfC2_AAB : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp false) (cfSupp false) (cfTab false) (cfTab false) (cfTab true) z = (0) * cfA z + (0) * cfB z := by
  intro z hz
  obtain ⟨c, d, hd, hc, rfl⟩ : ∃ c d, d < 16 ∧ c < 8 ∧ z = 16 * c + d :=
    ⟨z / 16, z % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [cfC2_AAB_chunk0 d hd, cfC2_AAB_chunk1 d hd, cfC2_AAB_chunk2 d hd, cfC2_AAB_chunk3 d hd,
    cfC2_AAB_chunk4 d hd, cfC2_AAB_chunk5 d hd, cfC2_AAB_chunk6 d hd, cfC2_AAB_chunk7 d hd]
theorem cfC2_ABA : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp false) (cfSupp true) (cfTab false) (cfTab true) (cfTab false) z = (0) * cfA z + (135) * cfB z := by
  decide +kernel
theorem cfC2_ABB : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp false) (cfSupp true) (cfTab false) (cfTab true) (cfTab true) z = (0) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC2_BAA : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp true) (cfSupp false) (cfTab true) (cfTab false) (cfTab false) z = (0) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC2_BAB : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp true) (cfSupp false) (cfTab true) (cfTab false) (cfTab true) z = (9) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC2_BBA : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp true) (cfSupp true) (cfTab true) (cfTab true) (cfTab false) z = (0) * cfA z + (0) * cfB z := by
  decide +kernel
theorem cfC2_BBB : ∀ z < 128, cubW (cfWt cfWP2) (cfSupp true) (cfSupp true) (cfTab true) (cfTab true) (cfTab true) z = (0) * cfA z + (21) * cfB z := by
  decide +kernel
theorem cfC2_hP : ∀ M < 128, (weight (maskOfNat M) = 2) ↔ cfC2 M := by
  decide +kernel

theorem cfK_C2 (z : ℕ) (hz : z < 128) (x y w : Bool) (p q : ℤ)
    (h : cubW (cfWt cfWP2) (cfSupp x) (cfSupp y) (cfTab x) (cfTab y) (cfTab w) z = p * cfA z + q * cfB z) :
    cfK cfWP2 z x y w = (p : ℝ) * (cfA z : ℝ) + (q : ℝ) * (cfB z : ℝ) := by
  unfold cfK
  rw [h]
  push_cast
  ring

/-- **Cubic mask sum over the class `C2`** for the icosahedral state: `s · cfA + t · cfB`. -/
theorem cubicMaskSum_C2 (α β : ℝ) (z : ℕ) (hz : z < 128) :
    cubicMaskSum (icosahedralState α β) (maskOfNat z) (fun m => weight m = 2) =
      ((163) * α ^ 3 + (9) * α * β ^ 2) * (cfA z : ℝ) + ((135) * α ^ 2 * β + (21) * β ^ 3) * (cfB z : ℝ) := by
  rw [cubicMaskSum_ico (fun m => weight m = 2) cfC2 (fun M hM => cfC2_hP M hM) cfWP2 cfWP2_valid α β z hz]
  rw [cfK_C2 z hz false false false _ _ (cfC2_AAA z hz)]
  rw [cfK_C2 z hz false false true _ _ (cfC2_AAB z hz)]
  rw [cfK_C2 z hz false true false _ _ (cfC2_ABA z hz)]
  rw [cfK_C2 z hz false true true _ _ (cfC2_ABB z hz)]
  rw [cfK_C2 z hz true false false _ _ (cfC2_BAA z hz)]
  rw [cfK_C2 z hz true false true _ _ (cfC2_BAB z hz)]
  rw [cfK_C2 z hz true true false _ _ (cfC2_BBA z hz)]
  rw [cfK_C2 z hz true true true _ _ (cfC2_BBB z hz)]
  ring

end FormalResearch.FourQubitEntropy.SevenQubitIco
