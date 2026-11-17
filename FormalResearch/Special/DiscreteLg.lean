module

public import FormalResearch.Special.DiscreteLgTaylor
public import FormalResearch.Special.DiscreteLgSite
public import FormalResearch.Special.DiscreteLgDefect
public import FormalResearch.Special.DiscreteLgMarch
public import FormalResearch.Special.DiscreteLgBulk
public import FormalResearch.Special.DiscreteLgZeros
public import FormalResearch.Special.DiscreteLgMatch
public import FormalResearch.Special.DiscreteLgSmooth
public import FormalResearch.Special.DiscreteLgHahn
public import FormalResearch.Special.DiscreteLgHahnMatch

/-!
# Discrete Liouville-Green (Darboux) layer for Jacobi chains (umbrella module)

The oscillatory *bulk* of a three-term recurrence `a_{k+1} Y_{k+1} + a_k Y_{k-1} = c_k Y_k` with smooth symmetric Jacobi coefficients
(`a_k ≈ A(q_k - h/2)`, `c_k ≈ 2A(q_k) u(q_k)`, `|u| < 1`, `q_k = q₀ + k h`), as an amplitude-phase statement `Y_k = R w(q_k) [cos(Θ(q_k)/h - φ₀) + O(h)]`,
and its matching to the Airy turning-point layer (`DiscreteAiry*`).  Method: the exact Liouville-Green pair `φ = w cos(Θ/h)`, `ψ = w sin(Θ/h)` with the transport
relation `A w² sin θ = 1` (`θ = arccos u`, `Θ' = θ`) has row defect `O(h²)` and Casoratian `1 + O(h)` from first-order jets; the Airy-free variation-of-constants
Grönwall march (`voc_march_up/down`, `DiscreteAiryOsc*`) then transports every solution.

* `DiscreteLgTaylor`: Lipschitz and Taylor estimates of orders 2 and 3 with explicit constants on convex sets, product jets.
* `DiscreteLgSite`: trigonometric site identities; the `O(h²)` remainders `dlg_X1`, `dlg_X2` and the Casoratian estimate `dlg_cas_real`.
* `DiscreteLgDefect`: the bulk datum `DlgData`, its lattice pair `dlgPhi`, `dlgPsi`, `dlg_row_defect`, `dlg_cas_bound`.
* `DiscreteLgMarch`: constant-weight drift of the Cramer coefficients (`dlg_march_const`).
* `DiscreteLgBulk`: `dlg_bulk_cart`, `dlg_bulk` (the discrete Darboux / Liouville-Green theorem), `dlg_amp_phase`, `dlg_polar`.
* `DiscreteLgZeros`: zero localisation in phase (`dlg_zero_localisation`, `dlg_bulk_zero_bond`, `dlg_phase_mono`).
* `DiscreteLgMatch`: the one-site Airy/LG matching `dlgm_site`, the Maslov offset `π/4` and amplitude `h^{1/6}|κ|/√π` (`dlg_airy_match`, `DlgAiryAt`), with the Langer
  chart relations as hypotheses.
* `DiscreteLgSmooth`: smooth `(A, u)` give a datum (`dlg_smooth_data`); `dlg_bulk_smooth`, `dlg_airy_match_smooth`.
* `DiscreteLgHahn`: the closed-form Hahn/Racah chains on an arbitrary window (`dlgh_close`, `dlg_bulk_hahn`, `dlg_airy_match_hahn`).
* `DiscreteLgHahnMatch`: the chart relations at the Hahn turn from the Langer coordinate (`dlgh_chart`, `dlgh_airyat`) and the end-to-end statement `dlg_hahn_airy`.

**Honest limits.**  Everything is first order (relative error `C h`, `C` depending on the datum bounds only).  The Hahn/Racah instance assumes the oscillatory hypothesis
`|hrU| < 1` on `[c₀, q_*)` and `q_* > 0`, `c₀ > 0` (assumed, not derived from the parameters); the other turning point / left edge, Bohr-Sommerfeld quantisation and node
counting over the whole oscillatory interval are not treated.  The value of `κ` is not identified in this layer itself, so `R` is
`h^{1/6}|κ|/√π` only up to `O(h)` here; the sharp value `κ² δ → 2` is composed with this layer in `BulkKappa*` (umbrella `BulkKappaAll`, imported by `FormalResearch.Special`): the explicit amplitude and zero localisation for the physical chains, integer and half-integer, both `τ`, are `hahn_chain_bulk_explicit*`, `racah_chain_bulk_explicit*`, `hahn_chain_bulk_zeros*`, `racah_chain_bulk_zeros*` (`BulkKappa*`).  Second-order Liouville-Green, the continuum Wigner-`d` ODE form and explicit constants in `(P, Q, a, b, x, c)` are not formalised.
-/

@[expose] public section
