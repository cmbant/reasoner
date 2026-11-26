# FIVE-S design note (strip structure of the Virasoro outer function `Gout`)

Work package FIVE-S of Paper II (`CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`): the shared input of
`cts:smooth-env` (2)-(3) (FIVE-U) and of `cts:cauchy-dual` Step 2 (FIVE-L).  All new files are `FiveTerm/Outer*.lean`
plus the phase-free core `Complex/StripBdryFunctional.lean`; no existing file is edited.  The four target statements
are `Prop`s in `OuterStripStatements.lean` (`OuterS1`, `OuterS2`, `OuterS3`, `OuterS4 = OuterS4a ∧ OuterS4b`).

This note is rewritten (not appended to) as slices land; the status table is current.

## 1. Status

| statement (paper) | Lean `Prop` | proved by | module | status |
|---|---|---|---|---|
| S1 `cts:main` Piece 3 / `cts:cauchy-dual` Step 2: bridge `G_outer(iy) = W_slit(y) e^{iθ_out(y)}`, `θ_out` odd, continuous, `θ_out(0)=0`; `H₃` holomorphic, zero-free, `H₃(0)=1`, positive on `(0,1)`, `|H₃(iy)| = (x(y)/ξ_*)²`, holomorphic fourth root `R4`; `G̃ = (1+z²)G_outer/R4` holomorphic, zero-free, slit `log|G̃|` formula | `OuterS1` | `outerS1` | `OuterBridge` (`gout_polar`, `thetaOut_soft`), `OuterH3` (`differentiableOn_H3`, `H3_ne_zero`, `H3_zero`, `H3_real_pos`, `norm_H3_slit`, `R4c`), `OuterS1` (`gtilde_diff`, `gtilde_ne_zero`, `log_gtilde_slit`, `outerS1`) | proved |
| S2 `cts:cauchy-dual` Step 2, `cts:theta-deriv`; `cts:smooth-env` (3) first bullet: `θ_out(y(x))` bounds `j = 0,1,2` and exponential limit | `OuterS2` (corrected form, see 3) | `outerS2` | `OuterTheta` (`thetaOutT_data`, the `τ`-level core), `OuterX` (chain rule, `outerS2`) | proved |
| S3 `cts:smooth-env` (2): extension `E_e` of `ℰ_δ`, branch-point factorisation, uniform bounds, global strip bound, boundary identities | `OuterS3` | prefix only: `fDelta_slit_dphi`, `fDelta_factor` | `OuterS3a` | open (prefix proved; see 4) |
| S4a `cts:smooth-env` (3): `δφ_δ'`, `δφ_δ''` bounds | `OuterS4a` (corrected form, see 3) | `outerS4a` | `OuterDphi` | proved |
| S4b `cts:smooth-env` (3): `ΔΦ_δ` holomorphic on the band, `Re ΔΦ_δ = 0` on `E_+`, `C²` bounds | `OuterS4b` | `outerS4b` | `OuterS4bPhi` (`φ_y = log(-T_y)`, uniform band bounds), `OuterS4b` (differentiation under the integral) | proved |

Each proved headline has a docstring with its paper label and a `#print axioms` guard
`[propext, Classical.choice, Quot.sound]`.  Class of every proved line: proved (no numerical input anywhere).

## 2. Architecture of the S1 + S2 proof

* **Strip variable.** `z = tan(πs/4)`, `s = iτ` on the slit, `y = tanh(πτ/4)`; `thetaOutT τ = Im h̄_a(iτ) - (5/2) arctan(tanh(πτ/4))
  + (1/4) arctan(2 v_T(τ))`, `thetaOut y = thetaOutT((4/π) artanh y)`, `thetaOutX x = thetaOutT(τ(x))` with
  `τ(x) = (2/π) arcosh(cosh(πx)/√2)` (`cosh πτ = sinh² πx`, `x_T(τ(x)) = x`, `y(x) = tanh(πτ(x)/4)`).
* **Splitting of the amplitude** (`OuterRest`). `a = aAmp = aXb + aRest` with `exp(4 aXb) = x_T b_T/ξ_*²` explicit and
  `aRest = 2 log λ + (5/2) log cosh(πt/4) + (3/4) log cosh(πt/2) - (1/2) log cosh(πt)`, a smooth even amplitude with
  `|aRest'| ≤ B` and `|aRest''|, |aRest'''| ≤ A e^{-π|t|/2}` (`aRest_deriv_data`, `OuterRestDeriv`).
* **The explicit part of the Schwarz integral** (`OuterKfun`, `OuterPL`, `OuterPhase`). `K(s) = (1+sin πs) g_S(s) g_S(1-s)/(π² ξ_*²)`
  (`g_S(s) = S(cos πs)`) is holomorphic and zero-free on the strip, `K(1-s) = K(s)`, extends continuously to the closed strip
  (`Kb`), and `|Kb| = x_T b_T/ξ_*²` on both edges.  Phragmén-Lindelöf (`PhragmenLindelof.vertical_strip`) on
  `e^{-4 Hxb} Kb` and `e^{4 Hxb}/Kb` (`Hxb = h̄_{aAmp} - h̄_{aRest}`) gives `|e^{4 Hxb}| = |Kb|` on the strip, maximum modulus
  makes the quotient constant, and `s = 1/2` gives `1`: `exp(4 Hxb) = Kb` (`exp_four_Hxb`).  Phase on the edge:
  `Im Hxb(it) = thetaXb t / 4`, `thetaXb t = arctan(sinh πt) - arctan(2 v_T t)` (`im_Hxb_left_edge`, via a polar form of
  `Kb(it)` and an integer-valued continuous function argument).
* **Master formula** (`OuterTheta`): `thetaOutT τ = (1/4) arctan(sinh πτ) - (5/2) arctan(tanh(πτ/4)) + bdryF aRest τ`
  (`thetaOutT_eq`), where `bdryF` is the boundary value of the Schwarz integral of a smooth amplitude
  (`Complex/StripBdryFunctional`: `hasDerivAt_bdryF_lin`, `abs_bdryF_decay_half`).  Hence
  `thetaOutT_data`: `Θ' , Θ''` exist everywhere, are `O(e^{-πτ/2})` on `τ ≥ 0`, `Θ(0) = 0`, `Θ` odd, `Θ → L` with
  `|Θ - L| ≤ C e^{-πτ/2}`.
* **Chain rule to `x`** (`OuterX`). `τ' = 2 sinh πx/D`, `τ'' = -2π cosh πx/D³`, `D = √(sinh² πx - 1)`; `D² ≥ 2√2 π r`,
  `D² ≤ C r` (`r ≤ 1`), `D ≥ k sinh πx` (`r ≥ 1`), `τ ≤ √2 D/π`, `e^{-πτ/2} ≤ 3 e^{-πx}`.
  `chain_bounds` (`OuterDphi`) is the generic form: `F = Φ∘τ` with `|Φ'|,|Φ''| ≤ D e^{-πτ/2}` gives
  `|F'| ≤ C r̃^{-1/2} e^{-πx}`, `|F''| ≤ C r̃^{-3/2} e^{-πx}`, `r̃ = min(r,1)`.
* **Bridge** (`OuterBridge`). Each factor of `Gout` at `z = iy` is put in polar form (`polar_re_pos`, `cpow_polar`): phases
  `Im h̄_a(iτ)`, `-(1/2) arctan y`, `-2 arctan y`, `+(1/4) arctan(2 v_x)`; modulus `W_slit` is `gout_modulus`.
* **`H₃`, `R4`, `G̃`** (`OuterH3`, `OuterS1`). `R4c = (1 + sin πs)^{1/4} S(u)^{1/2}/√(π ξ_*)` (principal powers; `Re(1+sin πs) > 0`
  on the strip and `Re S(u) > 0` off `(-∞,-1]`), `R4c⁴ = H₃`, `‖R4c(iy)‖ = √(x/ξ_*)`, and
  `‖G̃(iy)‖ = ((1-e^{-4πx})/(1-e^{-4πξ_*}))² / √(1+6y²+y⁴)`, which is the stated `log` formula
  (`1 + ρ = 2/(1+y)`, `1 + ρ⁴ = 2(1+6y²+y⁴)/(1+y)⁴`).
* **`δφ_δ`** (`OuterDphi`). `δφ_δ = Φ_δ∘τ`, `Φ_δ = -Θ + g_{1-δ}`, `g_a(τ) = ½(arctan(a tanh(πτ/4)) - arctan(tanh(πτ/4)))`;
  `|g_a'|, |g_a''| ≤ 3π² e^{-πτ/2}` uniformly in `0 ≤ a ≤ 1` (`g_bounds`).

## 3. Paper findings

1. **`cts:theta-deriv` / `cts:smooth-env` (3), bound `|∂_x^j θ_out(y(x))| ≤ C min(r^{1/2-j}, (1+x) e^{-πx})`.**
   Read literally it is false at the tip: `θ_out(y(x)) = g₁ y(x) + ...` with `y(x) ≍ r^{1/2}`, so `∂_x θ_out ≍ r^{-1/2}` while
   `(1+x) e^{-πx}` is bounded.  The correct combined statement, proved here, is
   `|θ_out(y(x))| ≤ C r^{1/2}` (`r ≤ 1`), `|∂_x θ_out| ≤ C r̃^{-1/2} e^{-πx}`, `|∂_x² θ_out| ≤ C r̃^{-3/2} e^{-πx}`,
   `r̃ = min(r,1)`, plus: `θ_out(y(x)) → L` exponentially, `|θ_out(y(x)) - L| ≤ C e^{-πx}` (numerically `L ≈ -π/4`).
   The variant `C r^{1/2-j} e^{-πx}` (all `x`) is also false: `r^{-1/2} → 0` at infinity while `θ_out' ≍ e^{-πx}`.
2. **`cts:smooth-env` (3), `|δφ_δ'| ≤ C r^{-1/2} e^{-πx}`, `|δφ_δ''| ≤ C r^{-3/2} e^{-πx}`** (all `x > ξ_*`) cannot hold for large `x`
   for the same reason, now also because of the arctan part: `δφ_δ'(x) ~ ½ y'(x) ((1-δ)/(1+(1-δ)²) - 1/2) ≍ e^{-πx}` with a
   `δ`-dependent nonzero constant.  Proved (`outerS4a`): the bounds with `r̃ = min(r,1)` in place of `r`, uniformly in `δ ∈ (0,1/4)`.
3. **Explicit structure behind the phase.** `θ_out` splits as an explicit piece plus the Schwarz-integral boundary phase of the
   smooth, exponentially flat amplitude `a_rest`; this is why `θ_out', θ_out''` are `O(e^{-πτ/2})` in the strip variable, and why the
   tip singularity is exactly the chain-rule factor `τ'(x) ≍ r^{-1/2}` (the strip-variable functions are smooth at `τ = 0`).
4. **`H₃`.** `H₃ · Ŝ(u) = K` (the comparison function), so `K = H₃ q̂` explains why `|H₃(iy)| = (x/ξ_*)²` is the modulus on the slit
   and `|Kb| = x_T b_T/ξ_*²` on the strip edges.

## 4. S4b and the S3 prefix (proved), and what remains of S3

* **S4b.** `φ_y = log(-T_y)` on `0 < Im b < 1` (`-T_y` is in the slit plane because both `tanh` factors have positive imaginary part;
  `phiY_eq`, using `-T_y(i/2) = 1`); on the band `‖φ_y‖ ≤ 15 + π`, `‖φ_y'‖ ≤ 4π`, `‖φ_y''‖ ≤ 8π²` uniformly in `y ∈ ℝ`, `Re b`
  (`norm_phiY_le`, `norm_phiYDeriv_le`, `norm_phiYDeriv2_le`); `Re φ_y = 0` on `Im b = 1/2` (`re_phiY_half`).
  `δφ_δ' ∈ L¹(ξ_*, ∞)` and continuous (from `outerS4a`), so `hasDerivAt_param` (dominated differentiation under the integral, applied
  twice) gives `ΔΦ_δ'`, `ΔΦ_δ''`; the constant is `C = C₀ J ((15+π)/π + 4 + 8π) + 1` with `J = ∫ min(r,1)^{-1/2} e^{-πy}` and `C₀` from
  `outerS4a`, uniform in `δ ∈ (0, 1/40)` (`δ₀ = 1/40`, `etaDelta (1/40) < 1/16`).
* **S3 prefix** (`OuterS3a`). `fDelta_slit_dphi`: `F_δ(i y(x)) = ρ e^{i δφ_δ(x)}` with `ρ > 0`, i.e. `dphi` is the boundary argument of `F_δ`
  on the slit (so the definition of `dphi` in `OuterStripStatements` is the right one).  `fDelta_factor`: `F_δ(z) = (1-(1-δ)z)^{-1/2}(1+z²)²/(R4(z)Ĝ(z))`,
  `Ĝ = (1-z)^{-1/2} G̃`, on `Ω` (the factorisation used in the paper's proof of (2)-(3)).
* **Remaining for S3** (`OuterS3`), in dependency order (none of these exists in the library yet):
  1. `ΔΦ_δ` holomorphic on the whole open strip `0 < Im b < 1` (S4b's argument with the band replaced by `ε ≤ Im b ≤ 1-ε`; the constants become
     `1/sin(πε)`-type), plus its boundary values at `Im b → 0+`: `Im ΔΦ_δ(x) = -δφ_δ(x)` for `x ≥ ξ_*` (`Im φ_y(x+i0) = -π·1_{x>y}`,
     `Im φ_y(x+i0) = π·1_{x<-y}`), `Im ΔΦ_δ = 0` for `|x| < ξ_*`; this needs the L¹-with-log-singularity continuity of `∫ δφ' φ_y`.
     Note `ζ_D(x + i0) = -i y(x)` for `x > ξ_*` (lower half-plane), so `F_δ(ζ_D(x+i0)) e^{-ΔΦ}` is real positive (phase `-δφ + δφ`): this is the identity
     `‖Ee(x)‖ e^{Re ΔΦ_δ(x)} = ‖F_δ(i y(x))‖`; the modulus half is `fDelta_slit_dphi`.
  2. A Schwarz reflection principle (continuous on a closed half-disc, holomorphic inside, real on the diameter, extends holomorphically): not in
     Mathlib; provable via Morera/`integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn_off_countable`.  With evenness and the removable singularity at
     `±ξ_*` (`ζ_D` has a square-root branch point there while `ℰ_δ` does not) this gives `Ee` on `|Im b| < 1/2`.
  3. Extension across `E_+` (`Im b = 1/2`) up to `1/2 + η_δ`: needs the holomorphic extension of `Ĝ∘ζ_D` across the arc, i.e. `cts:involution(1)` and the Schwarz
     reflection `g(w) = 2u_E(w) - conj g(conj w)` of the paper (inputs: the explicit `u_E`, bounded on `|Im v| ≤ 1/8`; Hölder regularity of `Ũ` at `0`).
  4. The branch-point factorisation `Ee = (1 - (1-δ)ζ_D)^{-1/2} Esm` with `Esm` zero-free and the two-sided `(1+|v|)^{-1/2} e^{-2π|v|}` bound
     (from `fDelta_factor`, `norm_H3_slit`-type moduli of `R4c`, `norm_gtilde_slit`, `ΔΦ` bounded on the band), and the global strip bound.

## 5. Hygiene

* All declarations live in `FormalResearch.ModularBootstrap.FiveTerm.OuterStrip` (or `FormalResearch.StripBdry`); short generic helper names
  (`tt`, `t1`, `t2`, `dd`, `ee`, `g1`, `g2`, `gfun`, `kap`, `H3`, `dphi`, ...) coincide with names in other namespaces of the library, so importers
  should refer to them qualified rather than `open` the namespace together with the others.
* No proof placeholders and no custom axioms; every headline is axiom-guarded.
