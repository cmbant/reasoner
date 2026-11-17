module

public import FormalResearch.Special.AiryTransformMul
public import FormalResearch.Special.AiryTransformDef
public import FormalResearch.Special.AiryTransformKernel
public import FormalResearch.Special.AiryTransformWeak
public import FormalResearch.Special.AiryTransformProj
public import FormalResearch.Special.AiryTransformEnv
public import FormalResearch.Special.AiryTransformEval
public import FormalResearch.Special.AiryTransformBasis
public import FormalResearch.Special.AiryTransformParseval
public import FormalResearch.Special.AiryTransformLiouville
public import FormalResearch.Special.AiryTransformHilbert
public import FormalResearch.Special.AiryTransformRKHS

/-!
# The Airy transform on `L²(ℝ)`, the Airy projector and the Paley–Wiener space (aggregate)

Survey row T5.  Modules:

* `AiryTransformMul`: multiplication operators by unimodular functions and indicator projections on `L²(ℝ; ℂ)`,
  reflection `R f(t) = f(-t)`;
* `AiryTransformDef`: `𝒜 = 𝓕⁻¹ M_{e^{iω³/3}} 𝓕` unitary; `𝓕𝓕 = R`; `𝒜⁻¹ = 𝒜* = R 𝒜 R`; `A = 𝒜 R` a self-adjoint
  unitary involution;
* `AiryTransformKernel`: `(𝒜 f)(u) = ∫ f(t) Ai(u-t) dt`, `(A f)(u) = ∫ f(t) Ai(u+t) dt` for Schwartz `f`
  (Abel regularisation);
* `AiryTransformWeak`: `A(Pφ)(u) = ∫_{t>0} φ(t) Ai(u+t) dt` a.e., for every `φ ∈ L²(ℝ)` (weak form + Fubini);
* `AiryTransformProj`: `K_Ai = A P A` orthogonal projection onto `PW = A L²(0,∞)`, integral kernel `K(u,v)`,
  `K_u = A_u A_u^*` (positive);
* `AiryTransformEnv`: `∫_0^∞ |Ai(z+t)|² dt ≤ 9 e(z)(2|z|+5/2)`;
* `AiryTransformEval`: `Ψφ(z) = ∫_{t>0} φ(t) Ai(z+t) dt` is entire with `|Ψφ(z)|² ≲ ‖φ‖² (1+|z|) e(z)`;
* `AiryTransformBasis`: the Airy zeros `a_n`, `K(·,a_n) ∈ PW`, orthonormality of `e_n = K(·,a_n)/|Ai'(a_n)|`
  (Christoffel–Darboux), `⟨e_n, Aφ⟩ = Ψφ(a_n)/|Ai'(a_n)|`;
* `AiryTransformLiouville`: completeness of `{e_n}` in `PW` by good circles and a Liouville argument (`Ψφ(a_n) = 0` for
  all `n` forces `Ψφ = c Ai`, then `c = 0` since `Ai ∉ L²(-∞,0)`); no Hardy-space input;
* `AiryTransformHilbert`: `{K(·,a_n)/|Ai'(a_n)|}` is a Hilbert basis of `PW` (`airyPW_hilbertBasis`) and Parseval
  `⟨G,F⟩ = Σ ⟨e_n,F⟩ \overline{⟨e_n,G⟩}` (`airyPW_parseval_of_basis`);
* `AiryTransformParseval`: independent cross-check: Parseval at the Airy zeros from Theorem Q (`airyQ_hasSum_unc`,
  which uses Hardy/Fejér–Riesz), hence completeness again (`airyPW_parseval`, `airyPW_eq_zero_of_inner`);
* `AiryTransformRKHS`: `PW` is a reproducing-kernel space of entire functions with kernel `airyKerC`; the bridge
  between the operator `K_u = A_u A_u^*` and `airyKerOp`.

**Correction to the survey wording.**  `𝒜 = 𝓕⁻¹ M_{e^{iω³/3}} 𝓕` is unitary and equals convolution with `Ai`,
`(𝒜 f)(u) = ∫ f(t) Ai(u-t) dt`, but it is **not** an involution (`𝒜⁻¹ = 𝒜* = R 𝒜 R`).  The self-adjoint unitary
involution with kernel `Ai(u+t)` is `A = 𝒜 R` (`airyA`); all statements about `PW`, `K_Ai` and `K_u` are about `A`.  (`FormalResearch.Special.airyA` is this involution; the unrelated `FormalResearch.Hadamard.airyA n` of `Complex/HadamardAiry.lean` is the `n`-th zero of `Ai`; the namespaces differ, so there is no clash.)

**Not formalised:** the converse Paley–Wiener-type characterisation (every entire `F` with `F|_ℝ ∈ L²` and growth
`|F(z)|² ≲ (1+|z|)^ν e(z)` lies in `PW`); the sharp exponent `(1+|z|)^{1/2}` in the growth bounds for `κ` and `Ψφ`
(proved: `(1+|z|)`, which suffices for completeness and Parseval); trace-class / Fredholm-determinant statements for
`K_Ai` and `K_u` and the Tracy–Widom identification; `A` on tempered distributions (for `φ ∈ L²(ℝ)` the kernel formula
`Ai(u+t)` is proved for `Pφ`, since `Ai(u+·)` is not square integrable on `(-∞,0)`).
-/
