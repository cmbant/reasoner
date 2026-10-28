import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicC2
import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicC30
import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicC31

/-!
# The plane hypothesis of `prop:zero-focus` is a theorem for `r = 2, 3`

`SevenQubitIcoZeroFocus` proves the second (Wronskian) relation of `eq:zero-focus-family`
(`sextic_covariant_generalizations.tex`, `prop:zero-focus`) under the `Prop` hypotheses
`PlaneHyp 2 α β` and `PlaneHyp 3 α β`: that `V_r(ψ_x) = ∑_{|S|=r} (R_S ⊗ I) ψ_x` lies in the real plane
spanned by the two integer tables `alphaReal`, `betaReal`.

The paper obtains this from the `A₅` switching symmetry. Here it is proved directly, without the
symmetry: `SevenQubitIcoCubicForm` writes `V_r` as a cut-free cubic sum over the masks,
`SevenQubitIcoCubicSwap` turns the sums over the masks into weighted sums over `z ⊕ v`, `z ⊕ u`, and the class
files `SevenQubitIcoCubicC2/C30/C31` evaluate them in the kernel (`decide +kernel`) for every `z < 128`.
This file only assembles: `PlaneHyp 2` from the class `|S| = 2`, `PlaneHyp 3` from the two classes `|S| = 3`
(`0 ∉ S`, `0 ∈ S`), and then restates the Wronskian relation and `zeroFocus_three_ico` unconditionally.

Status: proved (exact certificate: kernel-checked integer identities for all 128 points `z`, in the three
class files; no numerical input).
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Splitting a mask class -/

theorem cubicMaskSumT_split (f g h : BitString → ℝ) (z : BitString) (P Q : (Fin 7 → Bool) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    cubicMaskSumT f g h z P =
      cubicMaskSumT f g h z (fun m => P m ∧ Q m) + cubicMaskSumT f g h z (fun m => P m ∧ ¬ Q m) := by
  unfold cubicMaskSumT
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hP : P m <;> by_cases hQ : Q m <;> simp [hP, hQ]

theorem cubicMaskSumT_congr (f g h : BitString → ℝ) (z : BitString) (P P' : (Fin 7 → Bool) → Prop)
    [DecidablePred P] [DecidablePred P'] (hPP : ∀ m, P m ↔ P' m) :
    cubicMaskSumT f g h z P = cubicMaskSumT f g h z P' := by
  unfold cubicMaskSumT
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hPP m]

theorem cubicMaskSum_three_split (ψ : BitString → ℝ) (z : BitString) :
    cubicMaskSum ψ z (fun m => weight m = 3) =
      cubicMaskSum ψ z (fun m => weight m = 3 ∧ m 0 = false) +
        cubicMaskSum ψ z (fun m => weight m = 3 ∧ m 0 = true) := by
  unfold cubicMaskSum
  rw [cubicMaskSumT_split ψ ψ ψ z (fun m => weight m = 3) (fun m => m 0 = true), add_comm]
  congr 1

/-! ### Every point is a mask number -/

theorem exists_nat_of_bitString (z : BitString) : ∃ n < 128, maskOfNat n = z :=
  maskOfNat_surjective z

theorem alphaReal_maskOfNat (n : ℕ) (hn : n < 128) : alphaReal (maskOfNat n) = (cfA n : ℝ) := by
  unfold alphaReal
  rw [alphaCoefficient_maskOfNat n hn]

theorem betaReal_maskOfNat (n : ℕ) (hn : n < 128) : betaReal (maskOfNat n) = (cfB n : ℝ) := by
  unfold betaReal
  rw [betaCoefficient_maskOfNat n hn]

/-! ### `V_2` and `V_3` of the icosahedral state -/

/-- **`V_2(ψ) = α(163α²+9β²) alphaReal + β(135α²+21β²) betaReal`**, unconditionally: the real vector
`V_2(ψ_x) = ∑_{|S|=2} (R_S ⊗ I) ψ_x` of `prop:zero-focus`. Proved by the kernel-checked class evaluation
`cubicMaskSum_C2`. -/
theorem zfV_two_ico (α β : ℝ) (z : BitString) :
    zfV 2 (icosahedralState α β) z =
      α * (163 * α ^ 2 + 9 * β ^ 2) * alphaReal z + β * (135 * α ^ 2 + 21 * β ^ 2) * betaReal z := by
  obtain ⟨n, hn, rfl⟩ := exists_nat_of_bitString z
  rw [zfV_eq_cubicMaskSum 2 (Or.inr (Or.inl rfl)), cubicMaskSum_C2 α β n hn, alphaReal_maskOfNat n hn,
    betaReal_maskOfNat n hn]
  ring

/-- **`V_3(ψ) = α(149α²+5β²) alphaReal + β(75α²+35β²) betaReal`**, unconditionally: the sum of the classes
`0 ∉ S` (`cubicMaskSum_C30`) and `0 ∈ S` (`cubicMaskSum_C31`). -/
theorem zfV_three_ico (α β : ℝ) (z : BitString) :
    zfV 3 (icosahedralState α β) z =
      α * (149 * α ^ 2 + 5 * β ^ 2) * alphaReal z + β * (75 * α ^ 2 + 35 * β ^ 2) * betaReal z := by
  obtain ⟨n, hn, rfl⟩ := exists_nat_of_bitString z
  rw [zfV_eq_cubicMaskSum 3 (Or.inr (Or.inr rfl)), cubicMaskSum_three_split, cubicMaskSum_C30 α β n hn,
    cubicMaskSum_C31 α β n hn, alphaReal_maskOfNat n hn, betaReal_maskOfNat n hn]
  ring

/-- **The plane hypothesis `PlaneHyp 2 α β` holds** (`prop:zero-focus`, proof; there from `A₅`). -/
theorem planeHyp_two (α β : ℝ) : PlaneHyp 2 α β :=
  ⟨α * (163 * α ^ 2 + 9 * β ^ 2), β * (135 * α ^ 2 + 21 * β ^ 2), zfV_two_ico α β⟩

/-- **The plane hypothesis `PlaneHyp 3 α β` holds** (`prop:zero-focus`, proof; there from `A₅`). -/
theorem planeHyp_three (α β : ℝ) : PlaneHyp 3 α β :=
  ⟨α * (149 * α ^ 2 + 5 * β ^ 2), β * (75 * α ^ 2 + 35 * β ^ 2), zfV_three_ico α β⟩

/-- **`prop:zero-focus`, second relation of `eq:zero-focus-family`, unconditionally.**
`4(104x-7) Φ_{∅,3} - 2(524x-37) Φ_{∅,2} + (96x²+3628x-263) Φ_{∅,0} = 0` along `ψ_x`
(stated for `V_r = (-1)^n Φ_{∅,r}`; the relation is homogeneous). Proved; the `PlaneHyp` arguments of
`zeroFocus_wronskian` are discharged by `planeHyp_two`, `planeHyp_three`. -/
theorem zeroFocus_wronskian_unconditional (x α β : ℝ) (hα : α ^ 2 = u x) (hβ : β ^ 2 = x)
    (z : BitString) :
    4 * (104 * x - 7) * zfV 3 (icosahedralState α β) z -
        2 * (524 * x - 37) * zfV 2 (icosahedralState α β) z +
        (96 * x ^ 2 + 3628 * x - 263) * zfV 0 (icosahedralState α β) z = 0 :=
  zeroFocus_wronskian x α β hα hβ (planeHyp_two α β) (planeHyp_three α β) z

/-- At `x = 37/524`: `Φ_{∅,3}(Ψ_ico) = (605/131) Φ_{∅,0}(Ψ_ico)`, unconditionally. -/
theorem zeroFocus_three_ico_unconditional (α β : ℝ) (hα : α ^ 2 = u (37 / 524))
    (hβ : β ^ 2 = 37 / 524) (z : BitString) :
    zfV 3 (icosahedralState α β) z = 605 / 131 * zfV 0 (icosahedralState α β) z :=
  zeroFocus_three_ico α β hα hβ (planeHyp_three α β) z

end FormalResearch.FourQubitEntropy.SevenQubitIco
