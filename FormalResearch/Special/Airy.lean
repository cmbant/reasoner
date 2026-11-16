module

public import FormalResearch.Special.AiryKernel
public import FormalResearch.Special.AiryDef
public import FormalResearch.Special.AiryReal
public import FormalResearch.Special.AiryBound
public import FormalResearch.Special.AiryEquation
public import FormalResearch.Special.AiryIdentities
public import FormalResearch.Special.AiryPositive
public import FormalResearch.Special.AiryZeros
public import FormalResearch.Special.AiryRotation
public import FormalResearch.Special.AiryKernelOpOperator

/-!
# The Airy function: aggregate and design note

Mathlib has no Airy function.  Here `Ai(z) = (1/2π) ∫_ℝ exp((1+is)³/3 - z(1+is)) ds` is defined on `ℂ`
(`airyAiC`; absolutely convergent, Gaussian decay in `s`), with `airyAi : ℝ → ℝ` its real restriction.
Modules: `AiryKernel` (kernel, majorants, integration by parts in `s`), `AiryDef` (entire, `Ai'' = z Ai`,
independence of the abscissa `c > 0` by differentiating in `c`, derivatives are the moments),
`AiryReal` (real on `ℝ`, smooth), `AiryBound` (explicit decay on `(0,∞)`), `AiryEquation` (identities for any
solution of `y'' = x y`, ODE uniqueness; independent of the definition), `AiryIdentities` (`∫_x^∞ Ai²`, kernel
limits), `AiryPositive` (two-sided bounds, `Ai > 0`, `Ai' < 0` on `[0,∞)`), `AiryZeros` (zeros are real and
negative), `AiryRotation` (`Ai(z) + ω Ai(ωz) + ω² Ai(ω²z) = 0`, `Bi`, Wronskian constant), `AiryKernelOp{Formula,Bounds,Operator}`
(the Airy kernel as a Gram integral `∫_0^∞ Ai(x+t)Ai(y+t)dt` for real `x,y`, diagonal bounds, `∫_u^∞ K(s,s)ds`,
Hilbert–Schmidt/trace finiteness and positivity of the quadratic form).

**Not formalised:** `Ai(0) = 3^{-2/3}/Γ(2/3)`, `Ai'(0)`, the value `W(Ai, Bi) = 1/π` (only `-2√3 Ai(0)Ai'(0) > 0`
is proved), `Bi` asymptotics, `Ai` for `x < 0` (oscillation, `|x|^{-1/4}` envelope, zero asymptotics), sector
bounds `|Ai(z)| ≲ |z|^{-1/4} e^{-(2/3) Re z^{3/2}}` and Olver-type uniform expansions, `∫_0^∞ Ai = 1/3`.

Design note: what the Airy connection of `Weyl/P3` (`thm:general-rank-airy`) and the free-fermion edge
(`Weyl/free_fermion`, `thm:edge`) need next, and what is now reachable.
* *Forbidden-side/recessive input*: `Ai > 0`, monotone, `|Ai|, |Ai'|` explicit decay, `Ai'/Ai < 0`:
  done (`AiryPositive`, `AiryBound`).  Intrinsic boundedness of the discrete solution beyond the turn
  compares with this recessive solution: reachable now (Sturm-type comparison for the recurrence).
* *Canonical `Ai/Bi` basis and variation of constants* (Green function of the Airy-form branch): `Bi`, `Bi'' = zBi`
  and a constant Wronskian are in place; the normalisation `W = 1/π` needs `Ai(0)Ai'(0) = -1/(2√3 π)`, i.e. a
  contour rotation to the rays `arg t = ±π/3` (the differentiate-in-the-ray-angle trick of `airyMom_indep`
  should work, with the arc decay `Re t³ < 0` on `π/3 < arg t < π/2`): next step.
* *Olver modulus/weight `M, E` and the uniform bracket `Ai + N^{-4/3}ϖ Ai' + O(N^{-2})`*: needs `Ai`, `Bi` for
  `x < 0` and the envelope `M² = 2(Ai² + Bi²)`, hence Bi asymptotics and steepest descent on tilted contours
  (complex abscissa `c`, sectors `|arg z| ≤ π - δ`).  Not yet reachable; first extend `airyMom_indep` to
  complex `c` in a sector.
* *Discrete recurrence → Airy ODE limit*: Gronwall/uniqueness (`airy_unique_real`) and the wronskian/energy
  identities exist; the remaining analytic input is a stable comparison (Taylor of the Jacobi coefficients at the
  turn, `h^{4/3}`-scaling), independent of the Airy definition.
* *Free-fermion edge*: the Airy kernel `K(x,y)`, `K(x,x) = Ai'² - x Ai²`, `(∂_x + ∂_y)K = -Ai(x)Ai(y)` and
  `∫_x^∞ Ai² = K(x,x)` are in place, and `K(x,y) = ∫_0^∞ Ai(x+s)Ai(y+s) ds` (real `x,y`; hence positivity of `K`) is
  `airyKer_eq_integral` (`AiryKernelOp*`).  Complex `x,y` needs decay of `Ai(z)` along real shifts of complex `z`: not done.
-/
