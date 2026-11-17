module

public import FormalResearch.Special.HermiteKappaSup
public import FormalResearch.Special.HermiteKappaLower

/-!
# The Airy amplitude `κ` of the Hermite chain and the sup bound of the Hermite functions

Umbrella for the `HermiteKappa*` modules (r31):

* `HermiteKappaWeber`, `HermiteKappaOde`, `HermiteKappaInvariant`, `HermiteKappaBulk`, `HermiteKappaEnvelope`, `HermiteKappaSup`:
  the Weber equation for `φ_n`, the adiabatic invariant and the **uniform envelope** `φ_n(x)² √(|2n+1-x²| + (2n+1)^{1/3}) ≤ C`
  (`hermite_envelope`), and the product form of W1 `lem:PR(b)` (`hermite_PR_b`);
* `HermiteKappaChart`, `HermiteKappaEdge`: the Airy edge `hermite_airy_edge` with the chart data exported (`hermite_kappa_edge`);
* `HermiteKappaUpper`, `HermiteKappaLowerX`, `HermiteKappaSites`, `HermiteKappaLower`: the order of the amplitude,
  `κ² x^{1/3} ≍ 1` (`hermite_kappa_order`).

**Claim class: proved.**  Not formalised: the exact value of `κ` (`κ² ≈ (2/π)·(…) √δ`), i.e. the constant in the Plancherel-Rotach amplitude.
-/

@[expose] public section
