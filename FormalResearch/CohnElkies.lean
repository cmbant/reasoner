module

public import FormalResearch.CohnElkies.ResolventAverage
public import FormalResearch.CohnElkies.FourierL1Interp
public import FormalResearch.CohnElkies.CardinalTruncation
public import FormalResearch.CohnElkies.ClosedResolvent
public import FormalResearch.CohnElkies.StieltjesMixture
public import FormalResearch.CohnElkies.CardinalAsymptotics
public import FormalResearch.CohnElkies.MellinAiryToolkit
public import FormalResearch.CohnElkies.MellinPhaseBounds
public import FormalResearch.CohnElkies.AiryNicholsonIntegral
public import FormalResearch.CohnElkies.AirySymbolWKB

/-!
# Cohn–Elkies / CFT Paper I elementary and toolkit lemmas (umbrella)

Formalised lemmas for CFT Paper I (`CFT/sign_uncertainty/paper/sign_uncertainty_core.tex` and components) in Mathlib
and the Airy library:

* `FormalResearch.CohnElkies.ResolventAverage`: scalar resolvent-product average identity `(CR.18)`.
* `FormalResearch.CohnElkies.FourierL1Interp`: `∫|f̂| ≤ 2π (‖f‖₂‖f'‖₂)^{1/2}` for Schwartz and `H¹(ℝ)` functions
  (Lemma T.5 / `(FG.3c)`), exact Fourier-multiplier representation `(FG.3b)`, and uniform `‖T_c f‖_∞` bound (Lemma FG.3).
* `FormalResearch.CohnElkies.CardinalTruncation`: `‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂)‖H_N − H‖₂` and uniform `H^∞`
  convergence `(GT.0)` for Airy-class functions.
* `FormalResearch.CohnElkies.ClosedResolvent`: Theorem CR.1 (closed diagonal Airy resolvent `(CR.2)`, Riccati equation,
  `(CR.4)` diagonal derivative step, `(CR.3)`, and removable case `z = a`).
* `FormalResearch.CohnElkies.StieltjesMixture`: Stieltjes mixture identities `(CR.19a)`, `(CR.8)`, `(CR.6b)`, `(CR.20)`,
  `(CR.7)`, and `(CR.9)`.
* `FormalResearch.CohnElkies.CardinalAsymptotics`: Proposition CR.3 asymptotics `(CR.11)–(CR.13)` and Theorem CR.4 Step 1
  `(CR.14a)–(CR.15)`.
* `FormalResearch.CohnElkies.MellinAiryToolkit`: Mellin–Airy toolkit Lemmas T.4(a)–(f) and T.3(1), T.3(3).
* `FormalResearch.CohnElkies.MellinPhaseBounds`: Mellin–Airy toolkit exact imaginary identity `T.3(3)`,
  Gaussian vertical-line bounds `T.3(4)–(5)`, and phase facts `T.4(e)` `(P1)–(P4)`.
* `FormalResearch.CohnElkies.AiryNicholsonIntegral`: unconditional Nicholson integral error `E(x)` and
  phase correction `ϖ(x)` symbol/asymptotic bounds (Lemmas `W.3(a)` and `W.4(a)`).
* `FormalResearch.CohnElkies.AirySymbolWKB`: negative-axis Airy WKB representation, oscillation
  extraction, and `(CR.14)` all-order symbol decomposition (Lemmas `W.2(b)–(c)`, `W.3(b)`, `W.4(b)`,
  Props `W.5`, `W.6`).

This umbrella is deliberately not imported by `FormalResearch.lean`.
-/
