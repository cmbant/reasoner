module

public import FormalResearch.Special.BulkKappaDef
public import FormalResearch.Special.BulkKappaWin
public import FormalResearch.Special.BulkKappaWinH
public import FormalResearch.Special.BulkKappaAbs
public import FormalResearch.Special.BulkKappaSharp
public import FormalResearch.Special.BulkKappaHahn
public import FormalResearch.Special.BulkKappaHahnH
public import FormalResearch.Special.BulkKappaAmp
public import FormalResearch.Special.BulkKappaExplicit
public import FormalResearch.Special.BulkKappaHahnInst
public import FormalResearch.Special.BulkKappaZeros
public import FormalResearch.Special.BulkKappaHahnZeros
public import FormalResearch.Special.BulkKappaRacah
public import FormalResearch.Special.BulkKappaRacahInst

/-!
# Umbrella: sharp `κ` composed with the bulk Liouville-Green form for the physical chains

Window-first restructuring of the amplitude programme: the radius cap, the Airy window and the sharp `κ`
are produced once (`bk_win`, `bk_sharp_abs`), so that for every window of the exported constants the bulk
form, the band mass and `|κ²δ - 2| ≤ τ'` hold simultaneously (`BkOut`).  Composition gives, for the Hahn `3j`
chains (integer and half-integer, `τ = ±1`) and the Wigner `6j` chains (same four cases), an explicit bulk
amplitude-phase theorem `Y_k = ± A(q_k) cos(Φ(q_k)/h - π/4) (1 + o(1))` and bulk zero localisation to
`O(h)` in phase.  See `BulkKappaHahnInst` and `BulkKappaRacahInst` for the public statements.
-/
