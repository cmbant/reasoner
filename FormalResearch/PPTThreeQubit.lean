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

/-!
# Fully-PPT three-qubit GME: the rank-five family

Lean companion of `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/family.tex`
(`prop:ppt3-witness`, `thm:ppt3-family` GME part).  Headlines:
`prodA_classification` / `prodA_of_qs` (`prop:ppt3-witness`(a)), `formH_qs`
(`eq:ppt3-sos`), `formH_nonneg_of_cutProduct` (`prop:ppt3-witness`(b), all cuts),
`trace_Hs_nonneg_of_biseparable` (support criterion), `trace_H5_Xt` (`eq:ppt3-h5-value`),
`ppt3_family_gme` (`thm:ppt3-family`, GME part).

Moment-cone part (`relaxations_and_scope.tex`, `thm:ppt3-universal-moments`; `appendix_moment_cone.tex`,
`lem:ppt3-product-kernel`): `ppt_product_kernel`, `kernel_free_of_gme` (hypothesis `PPTSeparable23`, the
Horodecki 2⊗3 theorem), `biseparable_iff_mem_cone`, `dual_iff`, `cofCoeff_indep`, `curve_cut`,
`ppt3_universal_moments` (unconditional), `ppt3_universal_moments_of_gme`.
-/

@[expose] public section

