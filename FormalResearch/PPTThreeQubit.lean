module

public import FormalResearch.PPTThreeQubit.Basic
public import FormalResearch.PPTThreeQubit.Witness
public import FormalResearch.PPTThreeQubit.Criterion
public import FormalResearch.PPTThreeQubit.FamilyGME
public import FormalResearch.PPTThreeQubit.PartialTranspose
public import FormalResearch.PPTThreeQubit.FamilyPPT
public import FormalResearch.PPTThreeQubit.Coexistence
public import FormalResearch.PPTThreeQubit.FlatPauli
public import FormalResearch.PPTThreeQubit.Flat
public import FormalResearch.PPTThreeQubit.SurfaceWitness
public import FormalResearch.PPTThreeQubit.Surface
public import FormalResearch.PPTThreeQubit.SurfaceExtreme
public import FormalResearch.PPTThreeQubit.SurfacePPT
public import FormalResearch.PPTThreeQubit.CoexistencePPT
public import FormalResearch.PPTThreeQubit.ProductKernel
public import FormalResearch.PPTThreeQubit.CutEquiv
public import FormalResearch.PPTThreeQubit.ProductKernelThree
public import FormalResearch.PPTThreeQubit.PencilKernel
public import FormalResearch.PPTThreeQubit.MomentCone
public import FormalResearch.PPTThreeQubit.CurveParam
public import FormalResearch.PPTThreeQubit.MomentConeGME
public import FormalResearch.PPTThreeQubit.ConeCaratheodory
public import FormalResearch.PPTThreeQubit.MomentConeCaratheodory
public import FormalResearch.PPTThreeQubit.KernelPenalty
public import FormalResearch.PPTThreeQubit.SwapSymmetric
public import FormalResearch.PPTThreeQubit.PPTSeparable23
public import FormalResearch.PPTThreeQubit.ExtremeCriterion
public import FormalResearch.PPTThreeQubit.ChiralityBasics
public import FormalResearch.PPTThreeQubit.ChiralityRays
public import FormalResearch.PPTThreeQubit.Chirality
public import FormalResearch.PPTThreeQubit.ChiralityStabiliser
public import FormalResearch.PPTThreeQubit.ChiralityUnitary
public import FormalResearch.PPTThreeQubit.RankProfile
public import FormalResearch.PPTThreeQubit.WClass
public import FormalResearch.PPTThreeQubit.WClassStates
public import FormalResearch.PPTThreeQubit.WClassTilde

/-!
# Fully-PPT three-qubit GME: the rank-five family

Lean companion of `QI/hidden_entanglement/ppt_three_qubit/family.tex`
(`prop:ppt3-witness`, `thm:ppt3-family` GME part).  Headlines:
`prodA_classification` / `prodA_of_qs` (`prop:ppt3-witness`(a)), `formH_qs`
(`eq:ppt3-sos`), `formH_nonneg_of_cutProduct` (`prop:ppt3-witness`(b), all cuts),
`trace_Hs_nonneg_of_biseparable` (support criterion), `trace_H5_Xt` (`eq:ppt3-h5-value`),
`ppt3_family_gme` (`thm:ppt3-family`, GME part).

Moment-cone part (`relaxations_and_scope.tex`, `thm:ppt3-universal-moments`; `appendix_moment_cone.tex`,
`lem:ppt3-product-kernel`): `pptSeparable23` (the Horodecki 2⊗3 theorem, transported in
`PPTSeparable23.lean` from the vendored math-lab proof), `ppt_product_kernel`, `kernel_free_of_gme`, `biseparable_iff_mem_cone`, `dual_iff`, `cofCoeff_indep`, `curve_cut`,
`ppt3_universal_moments` (unconditional), `ppt3_universal_moments_of_gme`; all unconditional.

Extremality (`ExtremeCriterion.lean`; `appendix_family.tex`, `appendix_surface.tex`, the supported-face
criterion of Garberg--Irgens--Myrheim used for `cor:ppt3-extreme6` and `cor:ppt3-extreme5`):
`ExtremeCriterion.mem_extremePoints_iff_faceDirection` (generic: a state of the unit-trace set cut out by
finitely many real-linear cut maps is extreme iff every face direction is a multiple of it),
`ExtremeCriterion.mem_extremePoints_of_sandwich` (`σ = B X B†` form), and the three-qubit forms
`ExtremeCriterion.ppt3_extreme_iff`, `ExtremeCriterion.ppt3_extreme_of_sandwich`.

Moment cone, Carathéodory and closedness (`ConeCaratheodory.lean`, `MomentConeCaratheodory.lean`;
`thm:ppt3-universal-moments`): `ConeCar.exists_coneRep_card_le` (conic Carathéodory), `ConeCar.isClosed_cone_of_isCompact`,
`biseparable_card_le_25`, `isClosed_inMomentCone`, and for all three-qubit operators `isClosed_isBiseparable`,
`isBiseparable_card_le_64`.

Swap symmetry (`SwapSymmetric.lean`; `family.tex`, `cor:ppt3-symmetrisation`): `isSeparable_of_swap` (PPT and
swap-invariant on `ℂ² ⊗ ℂ⁴` implies separable), `isBiseparable_of_swapBC/AC/AB`, `no_gme_of_swap_invariant` (no
fully-PPT GME state is invariant under the exchange of two qubits), `isBiseparable_swap_average` (pinching),
`isBiseparable_permAvg` (permutation average of a fully-PPT state).

Kernel-penalty lift (`KernelPenalty.lean`; `kernel_penalty_lemma.tex`, `lem:ppt3-kernel-penalty`):
`exists_kernel_penalty` (any compact free set), `exists_kernel_penalty_cutProduct`, `kernel_penalty_witness`
(the nonstrict form with `W₀ + εI + λK†K` and the trace identity on states supported on `ker K`).

Chirality (`ChiralityBasics.lean`, `ChiralityRays.lean`, `Chirality.lean`, `ChiralityStabiliser.lean`;
`family.tex` `cor:ppt3-chirality` (b), proof in `appendix_family.tex`): `det_phiS`, `fullProd_mem_Rs_iff`
(`R_s` contains exactly three fully product rays), `eq_smul_one_of_eigen` (Möbius maps are determined by
three points), `no_local_filter_conj`, `no_local_filter_conj_onto`, `no_local_filter_state`,
`stabiliser_iff`, `exists_filter_perm`, `eq_smul_of_perm`.

Local-unitary chirality, ranks and the mixed `W` class: `ChiralityUnitary.lean` (`ppt3_chirality_conj`,
`ppt3_chirality_timeReverse`: no local unitary relates `ρ_t` to `ρ̄_t` or to its spin time reversal;
`cor:ppt3-chirality` (a)), `RankProfile.lean` (`rankProfile_rhoT_interior` `(5,8,8,8)`,
`rankProfile_rhoT_tMinus`/`tPlus` `(5,7,7,7)`, `rankProfile_rhoSurface` `(5,5,5,5)`, `rankProfile_sigma6`
`(5,6,6,6)`), `WClass.lean`, `WClassStates.lean`, `WClassTilde.lean` (`IsWClass`, `ppt3_w_class`,
`isWClass_rhoTilde`; `thm:ppt3-w-class`).
-/

@[expose] public section

