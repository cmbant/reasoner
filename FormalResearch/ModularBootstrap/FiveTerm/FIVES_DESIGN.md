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
| S3 `cts:smooth-env` (2): extension `E_e` of `ℰ_δ`, branch-point factorisation, uniform bounds, global strip bound, boundary identities | `OuterS3` | none | none | open (see 4) |
| S4a `cts:smooth-env` (3): `δφ_δ'`, `δφ_δ''` bounds | `OuterS4a` (corrected form, see 3) | `outerS4a` | `OuterDphi` | proved |
| S4b `cts:smooth-env` (3): `ΔΦ_δ` holomorphic on the band, `Re ΔΦ_δ = 0` on `E_+`, `C²` bounds | `OuterS4b` | none | none | open (see 4) |

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

## 4. Open items and exact next steps

* **S4b** (`OuterS4b`).  Inputs now available: `outerS4a` gives `|δφ_δ'(y)| ≤ C r̃^{-1/2} e^{-πy}`, integrable on `(ξ_*, ∞)`.  Next steps:
  (i) `φ_y' = π(1/sinh π(b-y) + 1/sinh π(b+y))` is holomorphic on `{0 < Im b < 1}`; on the band `1/4 < Im b < 3/4`,
  `|sinh π(u + iv)|² = sinh² πu + sin² πv ≥ 1/2` gives `|φ_y'|, |φ_y''| ≤ C e^{-π|Re b ∓ y|}`-type bounds uniform in `y ≥ ξ_*`;
  (ii) `|φ_y(b)| ≤ C` on the band (integrate `φ_y'` along the straight segment from `i/2`, which stays in the band, using `∫ sech = 1/π·π`),
  (iii) differentiate `ΔΦ_δ(b) = (1/π) ∫ δφ_δ'(y) φ_y(b) dy` under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominated by
  `C r̃^{-1/2} e^{-πy}`) twice; `Re ΔΦ_δ = 0` on `Im b = 1/2` from `|T_y(v + i/2)| = 1`.
* **S3** (`OuterS3`).  Needs `S4b` plus: the identification of `ℰ_δ = F_δ(ζ_D(b)) e^{-ΔΦ_δ}` with an even zero-free holomorphic `Ee` across
  `E_+` (the stripped envelope has no jump because `δφ_δ` is the phase of `F_δ` there), the branch-point factorisation at `b = ±i/2`
  from `m_δ(z) = (1 - (1-δ) ζ_D)^{-1/2}`-type factor, the uniform bounds from `S1` (`|G̃|` formula: the modulus of `Esm` is explicit) and `S2`, and the
  boundary identities.  First concrete step: write `F_δ(iy(x))` through `gout_polar` and `norm_gtilde_slit` to get `|Ee(x)| e^{Re ΔΦ} = |F_δ(iy(x))|`
  on the slit (the last two bullets of `OuterS3`), which needs only S1.

## 5. Hygiene

* All declarations live in `FormalResearch.ModularBootstrap.FiveTerm.OuterStrip` (or `FormalResearch.StripBdry`); short generic helper names
  (`tt`, `t1`, `t2`, `dd`, `ee`, `g1`, `g2`, `gfun`, `kap`, `H3`, `dphi`, ...) coincide with names in other namespaces of the library, so importers
  should refer to them qualified rather than `open` the namespace together with the others.
* No proof placeholders and no custom axioms; every headline is axiom-guarded.
