module

public import FormalResearch.Special.AiryPwsDeriv
public import FormalResearch.Special.AiryPwsSum
public import FormalResearch.Special.AiryPwsClass
public import FormalResearch.Special.AiryPwsContour
public import FormalResearch.Special.AiryPwsGrowth
public import FormalResearch.Special.AiryPwsMain
public import FormalResearch.Special.AiryPwsPW
public import FormalResearch.Special.AiryPwsConverse
public import FormalResearch.Special.AiryPwsIdent
public import FormalResearch.Special.AiryPwsIdent2
public import FormalResearch.Special.AiryPwsIdent3
public import FormalResearch.Special.AiryPwsConverseMain
public import FormalResearch.Special.AiryPwsPlaneWave
public import FormalResearch.Special.AiryPwsLaplace

/-!
# Airy Paley–Wiener–Schwartz theorem: umbrella

Theorem 3.1 of `CFT/notes/general_theorems.tex` (`(a) ⇔ (b)`, complex `f`; `(c)` only for absolutely continuous `μ`),
the Airy-kernel identities of the CFT PR 240 branch note `CE_O1_ROUTE.md` (not yet on `main`) O.11 (Step 0) and the uniform `H^∞` bound for `H²`:

* `AiryPwsDeriv`, `AiryPwsSum`: `Σ_n |L_n^{(j)}(-x)|² = ∫_{-x}^∞ Ai^{(j)}(t)² dt`, and `H = ∫₀^∞ Ai(u+t) v(t) dt`
  has `‖H‖ = ‖v‖`, `H = Σ b_n L_n`;
* `AiryPwsClass`, `AiryPwsContour`, `AiryPwsGrowth`, `AiryPwsMain`: the class `G`, `F̃`, and `(a) ⇒ (b)` with the
  sharp bound `|F̃| ≤ k‖f‖₁` (`airyFtilde_norm_le`);
* `AiryPwsPW`: decay transfer, `PW·PW ⊂ G`, `|F̃_{H²}| ≤ k‖F‖²`;
* `AiryPwsConverse`, `AiryPwsIdent`, `AiryPwsIdent2`, `AiryPwsIdent3`, `AiryPwsConverseMain`: `(b) ⇒ (a)`
  (`airyPws_converse`);
* `AiryPwsPlaneWave`, `AiryPwsLaplace`: `F̃_{Φ_τ} = e^{iζτ}` and `F̃_f = ∫ e^{iζτ} m(τ) dτ` for `f = ∫ Φ_τ m dτ`.
-/
