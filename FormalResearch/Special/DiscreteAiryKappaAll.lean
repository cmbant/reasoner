module

public import FormalResearch.Special.DiscreteAiryKappaAiSum
public import FormalResearch.Special.DiscreteAiryKappaBand3j
public import FormalResearch.Special.DiscreteAiryKappaBandHahn
public import FormalResearch.Special.DiscreteAiryKappaBandMass
public import FormalResearch.Special.DiscreteAiryKappaChart
public import FormalResearch.Special.DiscreteAiryKappaChart2
public import FormalResearch.Special.DiscreteAiryKappaEdge
public import FormalResearch.Special.DiscreteAiryKappaErmakov
public import FormalResearch.Special.DiscreteAiryKappaInvariant
public import FormalResearch.Special.DiscreteAiryKappaLeft
public import FormalResearch.Special.DiscreteAiryKappaLeftBand
public import FormalResearch.Special.DiscreteAiryKappaMain
public import FormalResearch.Special.DiscreteAiryKappaMass
public import FormalResearch.Special.DiscreteAiryKappaMassId
public import FormalResearch.Special.DiscreteAiryKappaOrder
public import FormalResearch.Special.DiscreteAiryKappaOrderData
public import FormalResearch.Special.DiscreteAiryKappaOrderLow
public import FormalResearch.Special.DiscreteAiryKappaOrderSetup
public import FormalResearch.Special.DiscreteAiryKappaOrderUp
public import FormalResearch.Special.DiscreteAiryKappaProfile
public import FormalResearch.Special.DiscreteAiryKappaRiemann
public import FormalResearch.Special.DiscreteAiryKappaRight
public import FormalResearch.Special.DiscreteAiryKappaSharpAlg
public import FormalResearch.Special.DiscreteAiryKappaSharpAssemble
public import FormalResearch.Special.DiscreteAiryKappaSharpBand
public import FormalResearch.Special.DiscreteAiryKappaSharpChart
public import FormalResearch.Special.DiscreteAiryKappaSharpFinal
public import FormalResearch.Special.DiscreteAiryKappaSharpFinalNode
public import FormalResearch.Special.DiscreteAiryKappaSharpGeom
public import FormalResearch.Special.DiscreteAiryKappaSharpLeft
public import FormalResearch.Special.DiscreteAiryKappaSharpMatch
public import FormalResearch.Special.DiscreteAiryKappaSharpNode1
public import FormalResearch.Special.DiscreteAiryKappaSharpNode2
public import FormalResearch.Special.DiscreteAiryKappaSharpNode3
public import FormalResearch.Special.DiscreteAiryKappaSharpParam
public import FormalResearch.Special.DiscreteAiryKappaSharpParam2
public import FormalResearch.Special.DiscreteAiryKappaSharpRho
public import FormalResearch.Special.DiscreteAiryKappaSharpZone
public import FormalResearch.Special.DiscreteAiryKappaTransport

/-!
# `κ` for the actual `3j` chain: umbrella for the `DiscreteAiryKappa*` modules (39 modules)

For integers `M, σ` and a rational `x ∈ (0,1)` (`τ = +1`), `hahn_chain_airy_full` writes the natural-gauge chain `Ŷ_k = √(2k+1) Φ_k` at a lattice node as `κ g Ai + μ g Bi` on the
macroscopic window but leaves `κ` unidentified.  This umbrella collects the modules that determine it (`δ³ = 1/N`; constants depending on `(M, σ, x)`):

* **`κ ≠ 0`** (`DiscreteAiryKappaMain`, with `Chart`, `Right`, `Edge`, `Left`, `LeftBand`, `Invariant`): `hahn_chain_kappa`, `|κ| ≥ κ_min > 0`, by the mass identity `ΣŶ² = N` and an a priori
  bound on the whole chain (first-order adiabatic invariant `ki_invariant`, left bound to the hard edge `kl_hahn_left`, monotone decay `kr_chain_mono`).
* **Order** (`AiSum`, `Chart2`, `Mass`, `OrderUp`, `OrderLow`, `OrderSetup`, `OrderData`, `Order`): `hahn_chain_kappa_order`, `c_lo ≤ κ² δ ≤ c_up`, from lattice sums of `Ai²`
  (`kai_sum_lower`, `kai_sum_upper_bound`) against the Gauss weight (`kk_mass_eq`, `kk_sum_le`, `kk_le_sum`).
* **Second-order interior** (`Ermakov`, `MassId`, `Profile`, `Transport`, `BandMass`, `BandHahn`, `Riemann`, `Band3j`): the Ermakov-Milne form of a three-term recurrence and its exact step
  identity (`kerm_invariant`, relative error `Σ|E|B`), the mass identity (`kerm_mass_id`), the WKB profile `P = 2/α` with `O(h²)` defect (`kp_defect`), amplitude transport (`kp_transport`),
  band masses (`kp_band_mass`, `kp_hahn_band_mass`, `hahn3j_band_mass`) and the Riemann sums of `1/α` (`kr_sum_bounds`).
* **Sharp constant** (the 16 modules `DiscreteAiryKappaSharp*`: `Alg`, `Rho`, `Chart`, `Match`, `Band`, `Zone`, `Assemble`, `Geom`, `Left`, `Node1`, `Node2`, `Node3`, `Param`, `Param2`, `FinalNode`,
  `Final`): `hahn_chain_kappa_sharp`, for every `τ > 0` and `1/N ≤ ε₁(τ)`, `|κ² δ - 2| ≤ τ`, i.e. `κ² = 2 N^{1/3}(1 + o(1))`, `|κ| = √2 N^{1/6}(1 + o(1))`.

**Claim class: proved** (no extra hypotheses; each headline has a pinned axiom guard `[propext, Classical.choice, Quot.sound]`).  Constants are existential in `(M, σ, x)`.

**Not formalised:** an explicit rate for `κ² δ → 2` (the proof gives `|κ² δ - 2| ≤ C₁ A + C₂(A) δ` for every small `A`, `C₂(A) ~ A⁻⁹`, no uniform power rate; numerically the error is about
`δ⁴`, not a Lean claim) and uniformity in `x`, including the hard edges `x → 0, 1`; the Darboux phase and the sign of `κ` (only `κ²` is determined); `τ = -1` and half-integer parameters for the `3j` chain.  (The Racah `6j` chain, integer and half-integer data, both `τ`, is the separate umbrella `RacahKappaAll`:
`racah_chain_kappa_sharp` and its variants.)
-/

@[expose] public section
