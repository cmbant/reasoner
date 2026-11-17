module

public import FormalResearch.EuclTet.Gram
public import FormalResearch.EuclTet.Cofactor
public import FormalResearch.EuclTet.AreaVec
public import FormalResearch.EuclTet.Schlafli
public import FormalResearch.EuclTet.SchlafliApp
public import FormalResearch.EuclTet.Dichotomy
public import FormalResearch.EuclTet.Radon
public import FormalResearch.EuclTet.RacahBridge
public import FormalResearch.EuclTet.P5Alg

/-!
# Euclidean tetrahedron geometry (namespace `FormalResearch.EuclTet`)

Cayley--Menger, dihedral angles, Schläfli and Radon for a tetrahedron of `ℝ³` (Weyl/P3
`lem:racah-cayley-menger` geometric half; Weyl/P5 `cayley_menger_trichotomy`):

* `EuclTet.Gram` : `det CM = 8 det Gram` as a polynomial identity, `det CM = 288 V²` in `ℝ³`
  (`V = |det|/6`), `det CM ≥ 0`, and the Gram realisation direction;
* `EuclTet.Cofactor` : the Cayley--Menger cofactors (`= adjugate`), row sums, Heron diagonals, the
  Jacobi identity, `∂D/∂x_ij = 2 C_ij` (six `HasDerivAt`);
* `EuclTet.AreaVec` : area vectors, dihedral angles from cofactors (`cos θ = C_ij/√(C_ii C_jj)`),
  the sine formula `sin θ_ij A_i A_j = (3/2) ℓ_kl V`;
* `EuclTet.Schlafli`, `EuclTet.SchlafliApp` : the Euclidean Schläfli identity `∑ ℓ_e dθ_e = 0`
  (squared-edge and length paths), the Regge function `dS = ∑ θ dℓ`, the volume derivative
  `dV/dℓ_kl = ℓ_kl ℓ_ij cot θ_ij / 6`, and the Van Vleck formula `∂θ_A/∂D = AD/(6V)`;
* `EuclTet.Dichotomy` : the Lorentzian dichotomy (`|cos θ| < 1 / = 1 / > 1` iff `D > 0 / = 0 / < 0`),
  wall angles in `{0, π}`, and Blumenthal's criterion (`blumenthal_iff`);
* `EuclTet.Radon` : planar tetrahedra (`C_ij = -16 λ_i λ_j`), the Radon sign pattern and partition,
  the flat-edge table and `n₊`;
* `EuclTet.RacahBridge` : a principal Racah tetrahedron exists in `ℝ³` iff `D₆ ≥ 0`, with
  `288 V² = 8 N⁶ ρ² α² β² D₆`.

* `EuclTet.P5AlgInertia` : the bordered-distance inertia `(1, d+1, m-d-1)` (`prop:inertia`) as an
  orthogonal decomposition (`p5a_bordered_distance_inertia`, for `0 < m`);
* `EuclTet.P5AlgDiscriminant` : the finite-`h` frozen-symbol discriminant as a polynomial identity in six
  reals and `h` (`p5a_cm_constant`, `p5a_discriminant_expansion`, `p5a_discriminant_even`);
* `EuclTet.P5AlgEgorov` : the entrywise Racah Egorov relations `J^(a) R = R D_d`, `D_a R = R J^(d)`
  (`p5a_racah_egorov_first`, `p5a_racah_egorov_second`; `a > 0`, resp. `d > 0`).

Not formalised: the corank-one adjugate structure and the sign of `c` in `adj M = c v vᵀ` derived
from the inertia (only the explicit planar value is proved, in `EuclTet.Radon`); the `n`-simplex statements and Blumenthal for general `n`; Regge integrability for all
pairs of edges (only the opposite pair, `regge_mixed`); `V` and `|N_i|` as measure and area (they
are the absolute-determinant and area-vector formulas).
-/
