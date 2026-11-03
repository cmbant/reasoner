module

public import FormalResearch.PPTThreeQubit.MomentConeGME
public import MathLab.ChainTheory.PPTCriterion

/-!
# `PPTSeparable23` from the vendored math-lab proof

The Horodecki–Horodecki–Horodecki (1996) / Woronowicz (1976) theorem that every PPT operator on
`ℂ² ⊗ ℂ³` is separable is not in Mathlib.  It is proved in the vendored third-party development
`ThirdParty/math-lab` (see `ThirdParty/math-lab/NOTICE.md`) as `ChainPPT.pptSeparable23`.  This file
transports that theorem to the conventions of this repository (`ptFirst`, Mathlib `PosSemidef`,
`GurvitsBarnum.IsSeparable`) and proves `pptSeparable23 : PPTSeparable23` outright, and
states hypothesis-free versions (primed names) of the results that take `PPTSeparable23` as an argument.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.GurvitsBarnum
open scoped Kronecker ComplexOrder

noncomputable section

/-- Mathlib's `PosSemidef` gives math-lab's quadratic-form predicate `IsPSD`. -/
theorem isPSD_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (h : P.PosSemidef) : ChainDuality.IsPSD P := fun v => by
  have h0 : (0 : ℂ) ≤ star v ⬝ᵥ (P *ᵥ v) := (Matrix.posSemidef_iff_dotProduct_mulVec.1 h).2 v
  exact ⟨(Complex.nonneg_iff.1 h0).1, (Complex.nonneg_iff.1 h0).2.symm⟩

/-- Our `ptFirst` is the full transpose of math-lab's partial transpose on the second factor. -/
theorem ptFirst_eq_transpose_pt (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    ptFirst ρ = (ChainDuality.pt ρ)ᵀ := by
  ext ⟨i, k⟩ ⟨j, l⟩; rfl

/-- `prodRankOne a b` is math-lab's rank-one projector on the product vector `a ⊗ b`. -/
theorem prodRankOne_eq_vecMulVec_prodVec (a : Fin 2 → ℂ) (b : Fin 3 → ℂ) :
    GurvitsBarnum.prodRankOne a b =
      vecMulVec (ChainDuality.prodVec a b) (star (ChainDuality.prodVec a b)) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [prodRankOne_apply, ChainDuality.prodVec, vecMulVec_apply, Pi.star_apply, star_mul']
  ring

/-- **Horodecki–Horodecki–Horodecki 2⊗3 criterion**: every PPT operator on `ℂ² ⊗ ℂ³` is separable.
Proved via the vendored `ChainPPT.pptSeparable23`. -/
theorem pptSeparable23 : PPTSeparable23 := by
  intro ρ hρ hT
  have hpt : ChainDuality.IsPSD (ChainDuality.pt ρ) := by
    apply ChainWoronowicz.isPSD_of_transpose
    rw [← ptFirst_eq_transpose_pt]
    exact isPSD_of_posSemidef hT
  obtain ⟨r, x, y, hxy⟩ := ChainPPT.pptSeparable23 ρ ⟨isPSD_of_posSemidef hρ, hpt⟩
  exact ⟨r, x, y, by rw [hxy]; exact Finset.sum_congr rfl fun s _ =>
    (prodRankOne_eq_vecMulVec_prodVec _ _).symm⟩

/-! ## Hypothesis-free versions

The unprimed theorems keep `PPTSeparable23` as an explicit argument (it is the only external input
of their proofs); the primed ones discharge it by `pptSeparable23`, with otherwise identical
statements. -/

/-- `ppt_product_kernel` without the hypothesis (`lem:ppt3-product-kernel`, first sentence). -/
theorem ppt_product_kernel' (ρ : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptFirst ρ).PosSemidef) (a : Fin 2 → ℂ) (b : Fin 4 → ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hk : ρ *ᵥ kroneckerVec a b = 0) : IsSeparable ρ :=
  ppt_product_kernel pptSeparable23 ρ hρ hT a b ha hb hk

/-- `biseparable_of_prodA_kernel` without the hypothesis. -/
theorem biseparable_of_prodA_kernel' (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptA ρ).PosSemidef) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hp : IsProdA x)
    (hk : ρ *ᵥ x = 0) : IsBiseparable ρ :=
  biseparable_of_prodA_kernel pptSeparable23 ρ hρ hT x hx hp hk

/-- `biseparable_of_prodB_kernel` without the hypothesis. -/
theorem biseparable_of_prodB_kernel' (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptB ρ).PosSemidef) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hp : IsProdB x)
    (hk : ρ *ᵥ x = 0) : IsBiseparable ρ :=
  biseparable_of_prodB_kernel pptSeparable23 ρ hρ hT x hx hp hk

/-- `biseparable_of_prodC_kernel` without the hypothesis. -/
theorem biseparable_of_prodC_kernel' (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptC ρ).PosSemidef) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hp : IsProdC x)
    (hk : ρ *ᵥ x = 0) : IsBiseparable ρ :=
  biseparable_of_prodC_kernel pptSeparable23 ρ hρ hT x hx hp hk

/-- `kernel_free_of_gme` without the hypothesis (`lem:ppt3-product-kernel`, second sentence). -/
theorem kernel_free_of_gme' (ρ : Matrix (Fin 8) (Fin 8) ℂ) (hρ : ρ.PosSemidef)
    (hA : (ptA ρ).PosSemidef) (hB : (ptB ρ).PosSemidef) (hC : (ptC ρ).PosSemidef)
    (hg : IsGME ρ) (x : Fin 8 → ℂ) (hx : x ≠ 0) (hk : ρ *ᵥ x = 0) : ¬ IsCutProduct x :=
  kernel_free_of_gme pptSeparable23 ρ hρ hA hB hC hg x hx hk

/-- `ppt3_universal_moments_of_gme` without the hypothesis (`thm:ppt3-universal-moments` for the
support of a fully-PPT GME state). -/
theorem ppt3_universal_moments_of_gme' (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hA : (ptA ρ).PosSemidef) (hB' : (ptB ρ).PosSemidef)
    (hC : (ptC ρ).PosSemidef) (hg : IsGME ρ)
    (B : Matrix (Fin 8) (Fin 5) ℂ) (K : Matrix (Fin 8) (Fin 3) ℂ)
    (hB : Function.Injective B.mulVec) (hK : Function.Injective K.mulVec) (hKB : Kᴴ * B = 0)
    (hKρ : ρ * K = 0) :
    ∃ T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ, (∀ c, IsUnit (T c).det) ∧ CutCurve B T ∧
      (∀ X : Matrix (Fin 5) (Fin 5) ℂ, IsBiseparable (B * X * Bᴴ) ↔ InMomentCone T X) ∧
      (∀ H : Matrix (Fin 5) (Fin 5) ℂ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ, IsBiseparable (B * X * Bᴴ) → 0 ≤ (trace (H * X)).re) ↔
          ∀ (c : Fin 3) (a : Fin 2 → ℂ),
            0 ≤ (star (nuVec a) ⬝ᵥ ((T c)ᴴ * H * T c) *ᵥ nuVec a).re) :=
  ppt3_universal_moments_of_gme pptSeparable23 ρ hρ hA hB' hC hg B K hB hK hKB hKρ

end

end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.pptSeparable23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.pptSeparable23

/-- info: 'FormalResearch.PPTThreeQubit.ppt_product_kernel'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.ppt_product_kernel'

/-- info: 'FormalResearch.PPTThreeQubit.biseparable_of_prodA_kernel'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.biseparable_of_prodA_kernel'

/-- info: 'FormalResearch.PPTThreeQubit.biseparable_of_prodB_kernel'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.biseparable_of_prodB_kernel'

/-- info: 'FormalResearch.PPTThreeQubit.biseparable_of_prodC_kernel'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.biseparable_of_prodC_kernel'

/-- info: 'FormalResearch.PPTThreeQubit.kernel_free_of_gme'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.kernel_free_of_gme'

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_universal_moments_of_gme'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.ppt3_universal_moments_of_gme'
