module

public import FormalResearch.Special.RacahKappaBand
public import FormalResearch.Special.RacahKappaBandD
public import FormalResearch.Special.RacahKappaBandMass
public import FormalResearch.Special.RacahKappaBulk
public import FormalResearch.Special.RacahKappaChain
public import FormalResearch.Special.RacahKappaChoose
public import FormalResearch.Special.RacahKappaCompose
public import FormalResearch.Special.RacahKappaConst
public import FormalResearch.Special.RacahKappaFam
public import FormalResearch.Special.RacahKappaFinalAlg
public import FormalResearch.Special.RacahKappaHBandD
public import FormalResearch.Special.RacahKappaHBandMass
public import FormalResearch.Special.RacahKappaHBulk
public import FormalResearch.Special.RacahKappaHChain
public import FormalResearch.Special.RacahKappaHCompose
public import FormalResearch.Special.RacahKappaHFam
public import FormalResearch.Special.RacahKappaHHardEdge
public import FormalResearch.Special.RacahKappaHLeft
public import FormalResearch.Special.RacahKappaHLeftBand
public import FormalResearch.Special.RacahKappaHLeftBandT
public import FormalResearch.Special.RacahKappaHLeftCoef
public import FormalResearch.Special.RacahKappaHLeftEdge
public import FormalResearch.Special.RacahKappaHLgHahn
public import FormalResearch.Special.RacahKappaHLgMatch
public import FormalResearch.Special.RacahKappaHRacah
public import FormalResearch.Special.RacahKappaHRiem
public import FormalResearch.Special.RacahKappaHSharp
public import FormalResearch.Special.RacahKappaHSharpInst
public import FormalResearch.Special.RacahKappaHZoneAbs
public import FormalResearch.Special.RacahKappaHZoneWin
public import FormalResearch.Special.RacahKappaLeft
public import FormalResearch.Special.RacahKappaLeftBand
public import FormalResearch.Special.RacahKappaLeftCoef
public import FormalResearch.Special.RacahKappaLeftEdge
public import FormalResearch.Special.RacahKappaLeftMass
public import FormalResearch.Special.RacahKappaMu
public import FormalResearch.Special.RacahKappaOsc
public import FormalResearch.Special.RacahKappaRacah
public import FormalResearch.Special.RacahKappaSharp
public import FormalResearch.Special.RacahKappaSharpInst
public import FormalResearch.Special.RacahKappaZone
public import FormalResearch.Special.RacahKappaZoneAbs
public import FormalResearch.Special.RacahKappaZoneWin

/-!
# `κ² δ → 2` for the actual Wigner `6j` chain: umbrella for the `RacahKappa*` modules (43 modules)

The Racah counterpart of `hahn_chain_kappa_sharp` (`DiscreteAiryKappaAll`).  `racah_chain_airy_full_pos/_neg` write the actual `6j` chain at a macroscopic window as `κ g Ai + μ g Bi` but leave `κ`
unidentified.  The 43 modules here (23 for integer data, 20 with `H` in the name for half-integer data) determine `|κ|`:

* **Headlines.**  `racah_chain_kappa_sharp` (`τ = +1`, natural gauge `racah6jY`) and `racah_chain_kappa_sharp_neg` (`τ = -1`, twisted chain `(-1)^k Y_k`), integer data (`RacahKappaSharpInst`);
  `racah_chain_kappa_sharp_half` and `racah_chain_kappa_sharp_half_neg` for `racah6jYH` (labels `m + 1/2`, `n + 1/2`, rank `k + 1/2`, shifted lattice `q_k = (k+1) h`; `RacahKappaHSharpInst`).
  Generic twisted chains `u_k Y_k`, `u_k² = 1`: `rk_racah_sharp_gen`, `rk_racah_sharp_genH`.
* **Statement.**  For fixed `(α, β, x, m, n)` the window constants are chosen first (depending on `(α, β, x, m, n)` only), and then for every `τ' > 0` there is `ε₁ > 0`, depending on `τ'` and
  `(α, β, x, m, n)` but not on the system or on `h`, such that for every finite Racah system with `A h = α`, `B h = β`, `cos A = x` (exact equalities) and every `0 < h ≤ ε₁`, the Airy-window amplitude `κ` of the Langer
  matching (`RkWinAt`, resp. `RkWinAtH`) satisfies `|κ² δ - 2| ≤ τ'`, `δ³ = h`; i.e. `κ² = 2 h^{-1/3} (1 + o(1))`, the same constant 2 as for Hahn, independent of `τ`, `x`, `m`, `n`.
* **Abstract theorem** `rk_kappa_sharp_abs` (`RacahKappaSharp`), half-lattice `rk_kappa_sharp_absH`: for a family of closed-form Jacobi chains with rows, Gauss mass `M h √s = 1`, `Y² ≤ M`, support, total-mass identity,
  monotone forbidden tail and a left a priori bound; the `6j` chain is an instance (`rkFam`, `rkFamH`; facts `rd_*`, `rdH_*`).
* **Ingredients** (generic in `(P, Q, τ, x, a, b)`): Liouville-Green bulk form with the same `κ, μ` as the Airy window (`rk_bulk`, `rk_bulkH`; Airy window with chart data `rk_compose`), LG band mass (`rkb_band`),
  Abel summation (`rko_abel`), zone and tail bounds (`rk_zone_abs`), the real algebra `|κ² δ - 2| ≤ 40 u` (`rk_final_alg`), the Racah turn identity `1 - x² = s q*²` (`rk_turn_id`, `rk_racah_s`),
  and the left a priori bound `rl_left`, `rl_leftH` (margin `2 a_k - |c_k| ≥ m₀`, valid for either `τ`).

**Claim class: proved** (no extra hypotheses; the headlines carry pinned axiom guards `[propext, Classical.choice, Quot.sound]`).  Numerical evidence (not part of the proof, not committed): `κ² δ → 2` to
`3·10⁻³` at `1/h = 150` and `10⁻⁴` at `1/h = 2400`.

**Not formalised:** the sign of `κ` and the `O(1)` Airy phase; uniformity of `ε₁` and the constants in `(α, β, x, m, n)`; `x` or `A h` only approximately fitted (the equalities `A h = α`, `B h = β`, `cos A = x` are
exact hypotheses); mixed-parity labels; `q`-Racah; an explicit rate; the Hahn half-integer `κ` (an instance of `rk_kappa_sharp_absH`, not done).
-/

@[expose] public section
