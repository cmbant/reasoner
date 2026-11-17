module

public import FormalResearch.Special.HermiteKappaSup
public import FormalResearch.Special.HermiteKappaLower

/-!
# The Airy amplitude `κ` of the Hermite chain and the sup bound of the Hermite functions

Umbrella for the `HermiteKappa*` modules (r31):

* `HermiteKappaWeber`, `HermiteKappaOde`, `HermiteKappaInvariant`, `HermiteKappaBulk`, `HermiteKappaEnvelope`, `HermiteKappaSup`:
  the Weber equation for `φ_n`, the adiabatic invariant and the **uniform envelope** `φ_n(x)² √(|2n+1-x²| + (2n+1)^{1/3}) ≤ C`
  (`hermite_envelope`), and the product form of W1 `lem:PR(b)` (`hermite_PR_b`);
* `HermiteKappaEdge`: the Airy edge `hermite_airy_edge` with the chart data exported (`hermite_kappa_edge`);
* `HermiteKappaUpper`, `HermiteKappaLowerX`, `HermiteKappaSites`, `HermiteKappaLower`: the order of the amplitude,
  `κ² x^{1/3} ≍ 1` (`hermite_kappa_order`).

**Claim class: proved** (explicit but crude constants: `12·10⁶` in the envelope; `δ₀, c_κ, C_κ` existential).

**Not formalised:** the sharp envelope constant (numerically `√2/√π ≈ 0.798`, at `n = 0`, `x = 0`, tending to `≈ 0.75`); the exact amplitude
(`κ = S^{-1/12}(1 + o(1))`, i.e. `κ² x^{1/3} → 2^{1/6}`, `S = x²/2`; numerics only); uniqueness of `κ` in the Airy decomposition
(`κ` is the coefficient produced by `hermite_airy_edge`/`hermite_kappa_edge`, constrained only through `HkEdge`); the derivative
asymptotics (the oscillatory form of `lem:PR(a)` is `hermite_bulk_PR`, `HermiteBulk`; the derivative bound is `hpr_deriv_bound`); negative `x` and `x = 0`
(in `hermite_kappa_order`; `hermite_envelope` covers all real `x`); the region `δ > δ₀` in `hermite_kappa_order`.
-/

@[expose] public section
