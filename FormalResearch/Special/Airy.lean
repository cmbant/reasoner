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
public import FormalResearch.Special.AiryValues
public import FormalResearch.Special.AiryTaylor
public import FormalResearch.Special.AiryFourier
public import FormalResearch.Special.AiryKernelOpOperator
public import FormalResearch.Special.AiryKernelOpComplex
public import FormalResearch.Special.AiryKernelOpSharp
public import FormalResearch.Special.AiryBridge
public import FormalResearch.Special.AiryNodes
public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryEnvelopeReal

/-!
# The Airy function: aggregate and design note

Mathlib has no Airy function.  Here `Ai(z) = (1/2π) ∫_ℝ exp((1+is)³/3 - z(1+is)) ds` is defined on `ℂ`
(`airyAiC`; absolutely convergent, Gaussian decay in `s`), with `airyAi : ℝ → ℝ` its real restriction.
Modules: `AiryKernel` (kernel, majorants, integration by parts in `s`), `AiryDef` (entire, `Ai'' = z Ai`,
independence of the abscissa `c > 0` by differentiating in `c`, derivatives are the moments),
`AiryReal` (real on `ℝ`, smooth), `AiryBound` (explicit decay on `(0,∞)`), `AiryEquation` (identities for any
solution of `y'' = x y`, ODE uniqueness; independent of the definition), `AiryIdentities` (`∫_x^∞ Ai²`, kernel
limits), `AiryPositive` (two-sided bounds, `Ai > 0`, `Ai' < 0` on `[0,∞)`), `AiryZeros` (zeros are real and
negative), `AiryRotation` (`Ai(z) + ω Ai(ωz) + ω² Ai(ω²z) = 0`, `Bi`, Wronskian constant), `AiryValues`
(`Ai(0)`, `Ai'(0)`, `Bi(0)`, `Bi'(0)` in terms of `Γ(1/3), Γ(2/3)`; `W(Ai, Bi) = 1/π`; contour rotation to
the rays `arg t = ±π/3`), `AiryTaylor` (`Ai = Ai(0) F + Ai'(0) G` with the explicit entire series `F, G`),
`AiryFourier` (`∫_ℝ Ai(x) e^{ax} dx = e^{a³/3}` for `Re a > 0`; Abel-regularised Fourier transform),
`AiryKernelOp{Formula,Bounds,Operator,Complex}` (the Airy kernel as a Gram integral `∫_0^∞ Ai(x+t)Ai(y+t)dt` for real and
complex `x,y`, diagonal bounds, `∫_u^∞ K(s,s)ds`, Hilbert–Schmidt/trace finiteness and positivity of the quadratic form),
`AiryEnvelope*` (free-parameter bound for every `c > 0`; the complex envelope `|Ai(z)| ≲ (1+|z|)^{-1/4} e^{-(2/3) Re z^{3/2}}`
on all of `ℂ`, the same for `Ai'`, order `3/2`; `Ai > 0` on `[-1, ∞)` and the two-sided real-axis envelope there).

**Not formalised:** `Bi` asymptotics, `Ai` for `x < 0` (oscillation, lower envelope `|x|^{-1/4}`, zero asymptotics; only the
upper envelope on `ℂ` and positivity on `[-1, ∞)` are proved), lower bounds for `|Ai(z)|` off the real axis, Olver-type
uniform expansions, the conditionally convergent improper integrals `∫_{-∞}^∞ Ai = 1` and `∫_0^∞ Ai = 1/3` (only their
Abel-regularised forms `∫ Ai(x) e^{εx} dx = e^{ε³/3}` are proved).

Design note: what the Airy connection of `Weyl/P3` (`thm:general-rank-airy`) and the free-fermion edge
(`Weyl/free_fermion`, `thm:edge`) need next, and what is now reachable.
* *Forbidden-side/recessive input*: `Ai > 0`, monotone, `|Ai|, |Ai'|` explicit decay, `Ai'/Ai < 0`:
  done (`AiryPositive`, `AiryBound`).  Intrinsic boundedness of the discrete solution beyond the turn
  compares with this recessive solution: reachable now (Sturm-type comparison for the recurrence).
* *Canonical `Ai/Bi` basis and variation of constants* (Green function of the Airy-form branch): `Bi`, `Bi'' = zBi`
  and the Wronskian `W(Ai, Bi) = 1/π` are in place (`AiryValues`: `Ai(0)Ai'(0) = -1/(2√3 π)` by a contour
  rotation to the rays `arg t = ±π/3`, proved by a derivative-in-the-ray-direction argument as for `airyMom_indep`).
* *Olver modulus/weight `M, E` and the uniform bracket `Ai + N^{-4/3}ϖ Ai' + O(N^{-2})`*: needs `Ai`, `Bi` for
  `x < 0` and the envelope `M² = 2(Ai² + Bi²)`, hence Bi asymptotics and steepest descent on tilted contours
  (complex abscissa `c`, sectors `|arg z| ≤ π - δ`).  Not yet reachable; first extend `airyMom_indep` to
  complex `c` in a sector.
* *Discrete recurrence → Airy ODE limit*: Gronwall/uniqueness (`airy_unique_real`) and the wronskian/energy
  identities exist; the remaining analytic input is a stable comparison (Taylor of the Jacobi coefficients at the
  turn, `h^{4/3}`-scaling), independent of the Airy definition.
* *Free-fermion edge*: the Airy kernel `K(x,y)`, `K(x,x) = Ai'² - x Ai²`, `(∂_x + ∂_y)K = -Ai(x)Ai(y)` and
  `∫_x^∞ Ai² = K(x,x)` are in place, and `K(x,y) = ∫_0^∞ Ai(x+s)Ai(y+s) ds` (hence positivity of `K`) is
  `airyKer_eq_integral` (real `x,y`) and `airyKerC_eq_integral` (complex `x,y`) in `AiryKernelOp*`.
-/

