import FormalResearch.PPTThreeQubit.Basic
import FormalResearch.PPTThreeQubit.Witness
import FormalResearch.PPTThreeQubit.Criterion
import FormalResearch.PPTThreeQubit.FamilyGME
import FormalResearch.PPTThreeQubit.PartialTranspose
import FormalResearch.PPTThreeQubit.FamilyPPT
import FormalResearch.PPTThreeQubit.Coexistence
import FormalResearch.PPTThreeQubit.FlatPauli
import FormalResearch.PPTThreeQubit.Flat
import FormalResearch.PPTThreeQubit.SurfaceWitness
import FormalResearch.PPTThreeQubit.Surface
import FormalResearch.PPTThreeQubit.SurfaceExtreme

/-!
# Fully-PPT three-qubit GME: the rank-five family

Lean companion of `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/family.tex`
(`prop:ppt3-witness`, `thm:ppt3-family` GME part).  Headlines:
`prodA_classification` / `prodA_of_qs` (`prop:ppt3-witness`(a)), `formH_qs`
(`eq:ppt3-sos`), `formH_nonneg_of_cutProduct` (`prop:ppt3-witness`(b), all cuts),
`trace_Hs_nonneg_of_biseparable` (support criterion), `trace_H5_Xt` (`eq:ppt3-h5-value`),
`ppt3_family_gme` (`thm:ppt3-family`, GME part).
-/
