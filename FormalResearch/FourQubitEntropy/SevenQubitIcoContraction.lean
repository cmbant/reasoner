import FormalResearch.FourQubitEntropy.SevenQubitIcoContractGram
import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicC30
import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicC31
import FormalResearch.FourQubitEntropy.SevenQubitIcoZeroFocusPlane

/-!
# The integer contraction identities `G_{1,0}`, `G_{1,1}`, `G_{2,1}` (ES-1)

`seven_qubit_entropy_local.tex`, `prop:entropy-seven-stationarity`: for `ψ = a U + b V`
(`U = alphaReal`, `V = betaReal`, here `ψ = icosahedralState a b`) and `ε ∈ {0, 1}`,
```
G_{r,ε}(ψ) = ∑_{|S| = 3, [0 ∈ S] = ε} (ρ_S^r ⊗ I) ψ ,      ρ_S = Gram matrix of ψ on S,
G_{1,0} = (76a³ + 4ab²) U + (60a²b + 20b³) V,
G_{1,1} = (73a³ + ab²) U + (15a²b + 15b³) V,
G_{2,1} = (417a⁵ + 2a³b² + ab⁴) U + (15a⁴b + 30a²b³ + 15b⁵) V.
```
Here these are theorems (`esG1_avoid`, `esG1_contain`, `esG2_contain`), proved without symmetry:
`G_{1,ε}` is the cubic mask sum over the class (`SevenQubitIcoCubicC30/C31`, kernel-checked for all 128 points);
`G_{2,1}` follows from the integer Gram identities `P² = -32 + 12 P + 21 R`, `PR = RP = R`, `R² = R` on the
15 cuts containing the special site (`SevenQubitIcoContractGram`) and the four trilinear forms
`T(U,U,U) = 73 U`, `T(U,V,U) = 15 V`, `T(V,U,V) = U`, `T(V,V,V) = 15 V` of the class `0 ∈ S`.

Status: exact certificate (kernel-checked integer identities) plus elementary algebra. The consequence
`esPolyGrad_in_span` records that any gradient of the form `∑_S p_S(ρ_S) ψ` with `p_S` of degree `≤ 1`
(avoiding cuts) resp. `≤ 2` (containing cuts) lies in `span{U, V}`. That the gradient of the mean cut entropy
has this form (the logarithm of `ρ_S` on its support is a polynomial of that degree, since `ρ_S` has two
resp. three distinct nonzero eigenvalues, `SevenQubitIcoSpectrum`) is NOT formalised here.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- `G_{1,ε}(ψ)(z) = ∑_{|S|=3, [0∈S]=ε} (ρ_S ⊗ I) ψ (z)`. -/
noncomputable def esG1 (ε : Bool) (ψ : BitString → ℝ) (z : BitString) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = ε),
    redApply (maskCut 3 4 m) ψ z

/-- `G_{2,ε}(ψ)(z) = ∑_{|S|=3, [0∈S]=ε} (ρ_S² ⊗ I) ψ (z)`. -/
noncomputable def esG2 (ε : Bool) (ψ : BitString → ℝ) (z : BitString) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = ε),
    redApplySq (maskCut 3 4 m) ψ z

theorem card_avoid : (Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = false)).card = 20 := by
  decide +kernel

theorem card_contain : (Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = true)).card = 15 := by
  decide +kernel

/-! ### `G_{1,ε}` -/

/-- **`G_{1,0}`**: the triples avoiding the special site. -/
theorem esG1_avoid (α β : ℝ) (z : BitString) :
    esG1 false (icosahedralState α β) z =
      (76 * α ^ 3 + 4 * α * β ^ 2) * alphaReal z + (60 * α ^ 2 * β + 20 * β ^ 3) * betaReal z := by
  obtain ⟨n, hn, rfl⟩ := exists_nat_of_bitString z
  unfold esG1
  rw [sum_masks_cubic 3 maskCut_bijective_three (fun m => m 0 = false), cubicMaskSum_C30 α β n hn,
    alphaReal_maskOfNat n hn, betaReal_maskOfNat n hn]

/-- **`G_{1,1}`**: the triples containing the special site. -/
theorem esG1_contain (α β : ℝ) (z : BitString) :
    esG1 true (icosahedralState α β) z =
      (73 * α ^ 3 + α * β ^ 2) * alphaReal z + (15 * α ^ 2 * β + 15 * β ^ 3) * betaReal z := by
  obtain ⟨n, hn, rfl⟩ := exists_nat_of_bitString z
  unfold esG1
  rw [sum_masks_cubic 3 maskCut_bijective_three (fun m => m 0 = true), cubicMaskSum_C31 α β n hn,
    alphaReal_maskOfNat n hn, betaReal_maskOfNat n hn]
  ring

/-! ### The four trilinear forms of the class `0 ∈ S` -/

theorem sumT_contain (x y w : Bool) (n : ℕ) (hn : n < 128) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = true),
      redApplyT (maskCut 3 4 m) (tabReal x) (tabReal y) (tabReal w) (maskOfNat n) =
        cfK cfWP31 n x y w := by
  rw [sum_masks_cubicT 3 maskCut_bijective_three (fun m => m 0 = true)]
  exact cubicMaskSumT_tab (fun m => weight m = 3 ∧ m 0 = true) cfC31 (fun M hM => cfC31_hP M hM)
    cfWP31 cfWP31_valid x y w n hn

theorem sum_UψU (α β : ℝ) (n : ℕ) (hn : n < 128) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = true),
      redApplyT (maskCut 3 4 m) alphaReal (icosahedralState α β) alphaReal (maskOfNat n) =
        α * 73 * (cfA n : ℝ) + β * 15 * (cfB n : ℝ) := by
  have hψ : icosahedralState α β = fun w => α * alphaReal w + β * betaReal w :=
    funext fun w => icosahedralState_eq α β w
  have e1 := sumT_contain false false false n hn
  have e2 := sumT_contain false true false n hn
  simp only [tabReal] at e1 e2
  simp only [hψ, redApplyT_lin_g, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2]
  rw [cfK_C31 n hn false false false 73 0 (cfC31_AAA n hn),
    cfK_C31 n hn false true false 0 15 (cfC31_ABA n hn)]
  push_cast
  ring

theorem sum_VψV (α β : ℝ) (n : ℕ) (hn : n < 128) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = true),
      redApplyT (maskCut 3 4 m) betaReal (icosahedralState α β) betaReal (maskOfNat n) =
        α * (cfA n : ℝ) + β * 15 * (cfB n : ℝ) := by
  have hψ : icosahedralState α β = fun w => α * alphaReal w + β * betaReal w :=
    funext fun w => icosahedralState_eq α β w
  have e1 := sumT_contain true false true n hn
  have e2 := sumT_contain true true true n hn
  simp only [tabReal] at e1 e2
  simp only [hψ, redApplyT_lin_g, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2]
  rw [cfK_C31 n hn true false true 1 0 (cfC31_BAB n hn),
    cfK_C31 n hn true true true 0 15 (cfC31_BBB n hn)]
  push_cast
  ring

/-! ### `G_{2,1}` -/

/-- **`G_{2,1}`**: `∑_{|S|=3, 0∈S} (ρ_S² ⊗ I) ψ = (417α⁵ + 2α³β² + αβ⁴) U + (15α⁴β + 30α²β³ + 15β⁵) V`. -/
theorem esG2_contain (α β : ℝ) (z : BitString) :
    esG2 true (icosahedralState α β) z =
      (417 * α ^ 5 + 2 * α ^ 3 * β ^ 2 + α * β ^ 4) * alphaReal z +
        (15 * α ^ 4 * β + 30 * α ^ 2 * β ^ 3 + 15 * β ^ 5) * betaReal z := by
  obtain ⟨n, hn, rfl⟩ := exists_nat_of_bitString z
  unfold esG2
  rw [Finset.sum_congr rfl (fun m hm => by
    obtain ⟨hw, h0⟩ := (Finset.mem_filter.1 hm).2
    exact redApplySq_contain m hw h0 α β (maskOfNat n))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_contain]
  rw [sum_UψU α β n hn, sum_VψV α β n hn, icosahedralState_eq, alphaReal_maskOfNat n hn,
    betaReal_maskOfNat n hn]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-! ### Consequence: gradients of polynomial type lie in `span{U, V}` -/

/-- A vector of the form `∑_S p_S(ρ_S) ψ`, with `p_S = c₀ + c₁ t` on the 20 avoiding triples and
`p_S = d₀ + d₁ t + d₂ t²` on the 15 containing triples. -/
noncomputable def esPolyGrad (c0 c1 d0 d1 d2 : ℝ) (ψ : BitString → ℝ) (z : BitString) : ℝ :=
  (∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = false),
      (c0 * ψ z + c1 * redApply (maskCut 3 4 m) ψ z)) +
    ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = 3 ∧ m 0 = true),
      (d0 * ψ z + d1 * redApply (maskCut 3 4 m) ψ z + d2 * redApplySq (maskCut 3 4 m) ψ z)

/-- **Polynomial gradients lie in the plane `span{U, V}`** (explicit coefficients). -/
theorem esPolyGrad_in_span (c0 c1 d0 d1 d2 α β : ℝ) (z : BitString) :
    esPolyGrad c0 c1 d0 d1 d2 (icosahedralState α β) z =
      (20 * c0 * α + 15 * d0 * α + c1 * (76 * α ^ 3 + 4 * α * β ^ 2) +
          d1 * (73 * α ^ 3 + α * β ^ 2) +
          d2 * (417 * α ^ 5 + 2 * α ^ 3 * β ^ 2 + α * β ^ 4)) * alphaReal z +
        (20 * c0 * β + 15 * d0 * β + c1 * (60 * α ^ 2 * β + 20 * β ^ 3) +
          d1 * (15 * α ^ 2 * β + 15 * β ^ 3) +
          d2 * (15 * α ^ 4 * β + 30 * α ^ 2 * β ^ 3 + 15 * β ^ 5)) * betaReal z := by
  have h1 := esG1_avoid α β z
  have h2 := esG1_contain α β z
  have h3 := esG2_contain α β z
  unfold esG1 at h1 h2
  unfold esG2 at h3
  unfold esPolyGrad
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_avoid, card_contain, h1, h2,
    h3, nsmul_eq_mul, icosahedralState_eq]
  push_cast
  ring

end FormalResearch.FourQubitEntropy.SevenQubitIco
