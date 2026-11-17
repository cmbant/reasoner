module

public import FormalResearch.Special.ComplexStirlingLaplace
public import FormalResearch.Special.ComplexStirlingKernel
public import FormalResearch.Special.ComplexStirlingRemainder
public import FormalResearch.Special.ComplexStirlingBinet
public import FormalResearch.Special.ComplexStirlingLine
public import FormalResearch.Special.ComplexStirlingStrip

/-!
# Complex Stirling formula with explicit remainders (Binet's formulas)

Umbrella module (namespace `FormalResearch.Special.ComplexStirling`).

* `ComplexStirlingLaplace` : Laplace transforms of bounded kernels on `Re z > 0` (bound, differentiation).
* `ComplexStirlingKernel` : the Binet kernel `1/2 - 1/t + 1/(e^t-1)`, `binetI`, `binetB`, the Frullani
  transform `∫ (1-e^{-t})/t e^{-tz} = log(1+1/z)` and the difference equation of `binetI`.
* `ComplexStirlingRemainder` : `‖binetI'‖ ≤ (2/3)/|z|³`, `‖binetI‖ ≤ 1/|z|²`, `‖binetB‖ ≤ 2/|z|` on
  `Re z > 0` (telescoping of the difference equation; no contour rotation).
* `ComplexStirlingBinet` : Binet's formula for `ψ` (DLMF 5.9.16) and for `log Γ`
  (`binetLogGamma`, `exp = Γ`), real form, branch uniqueness, remainders for `ψ`, `ψ'`, `log Γ`.
* `ComplexStirlingLine` : `|Γ(1/2+is)|² = π/cosh(πs)`, `Re ψ`, `Im log Γ` on `Re z = 1/2`.
* `ComplexStirlingStrip` : `|Γ(x+iy)|` in vertical strips with explicit remainder.
-/

@[expose] public section

