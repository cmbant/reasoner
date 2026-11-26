# PM-2 design note (fixed-design transfer for mixtures, `pmix:vac`)

Label: `pmix:vac` (Proposition PM.9) of `CFT/modular_bootstrap/paper/positive_mixtures.tex`, with `pmix:fixed-transfer`.
Namespace `FormalResearch.ModularBootstrap.Mixtures`; new files `Mixtures/Vac*.lean` only; no existing file is edited.

## What the paper states, and what Lean states

Paper: common source convention at parameter `n'`; fixed `(f, r)`, `γ = 2f - 1/2 - r ≥ 3/2`; the bumped comb `h_r^{(p)}`
(independent of `V_mix`), `g_w = ½(h_r^{(p)} - 𝓗_w h_r^{(p)})`, `Ψ^{mix}(u) = g_w V_mix J`, `q_mix(ξ_*) = (2ξ_*)^{w-1} A(ξ_*)/(1-e^{-4πξ_*})²`,
`F^{mix}_{f,r} = q_mix(ξ_*) F^{Vir}_{f,r}(n')`.  Conclusions: (1) `g_w ∈ Ā_{w,mix}`, decay, `g_w > 0` for `t ≥ t_f + 1`;
(2) `(F^{mix})^{-1} Ψ^{mix} → C W` locally uniformly and `(F^{mix})^{-1} ∫ Ψ^{mix} du → C ∫ W`.

Lean keeps the form of the design side (W-P5, W-T2w): `FK^{mix}_c := FKc (qMix src) 1 c'` (`qMix src` is exactly `q_mix(ξ_*)`,
and `FKc q f c' = q · FKc 1 f c'`), `∫ Ψ du = -g_vac/(2π) = ∫_0^∞ g V_mix dt` and

* (P1) `TestClass src (c/12) g`, decay `|g| ≤ C e^{-4π√(a t) - π x}`;  (P2) `g > 0` on `t ≥ t_f + 1`;
* (P3) window: `|FK^{-1}·(2/C_*) Ψ^{mix}(u) - W(u)| ≤ ε` on `[-R, R]` (two-sided, locally uniform);
* (P4) vacuum: `limsup (2/(C_* FK^{mix})) ∫ Ψ^{mix} du ≤ V_D`, and `V_D < 0 ⟹ g_vac ≥ π C_* |V_D| FK^{mix}/4 > 0`.

**Difference from the paper (stated, not hidden).** The second limit is one-sided in Lean: `limsup ≤`, the form W-P5
(`proposition_V_i_bumped`, `bump_psi_limsup`) and W-T2w (`limsup_le`) prove at the single weight `(w, Q ≡ 1)`, and the form
that `sr:P` (P4) and `TwoZeroTransferData.limsup_le` state (it is all that the rigidity argument uses).  At `f = 1` the deep lobe
`x < ξ_* - Sλ` is controlled only by the sign of `h V`, which gives an upper bound only.  At `(2, 1)` the lobe, band and far band
are bounded in absolute value, so the matching lower bound is within reach (it needs `∫_{|u|>R} |W_2| → 0` and the window limit);
it is not formalised at any weight, and `SrcTwoZeroTransferData` has `limsup_le` like `TwoZeroTransferData`.

## Reduction to W-P5 / W-T2w (the trivial product `triv = Q ≡ 1`, `V = K_{c'/12}^{(w)}`)

The comb and the test depend on the problem only through `w` (`bumpG`, `twoZeroBumpG`): take them at
`triv = trivialProductProblem w hw` (as PM-1 does for `rampedBumpG`).  Item (1) is `bumpSig_k7W` / `bumpG_pos` at `triv`
(unchanged) plus `k7_src` (membership `Ā_{w,src}`, vacuum identity `pmix:comb-vac`, comb term `≤ ‖λ‖_TV = C_vac`).
Window and vacuum use two facts about `V_src = src.cardyV (c'/12)` against `V_t := K_{c'/12}^{(w)}`:

* **Comparison on compact `σ`-windows** (`VacCompare.cmp_window`): for `S ≥ 0`, `δ > 0`, `c'` large, all `|σ| ≤ S`,
  `x = ξ_* + λσ`, `t = c'x²/3`:  `|V_src(t) - A(ξ_*) V_t(t)| ≤ δ V_t(t)` with `V_t(t) > 0`.
  From `pmix:weight`(b) (`ShiftSource.real_asymp`, error `C/c'`), the same asymptote for `triv` (`cardyV_asymptotic_real`,
  amplitude `1`), the Lipschitz bound of `A` (`abs_ampl_sub_le`) and `|x - ξ_*| ≤ λ S = O(c'^{-2/3})`: this is the paper's
  `V_mix/V_Vir = q_mix(ξ_*)(1 + O(n^{-2/3}))`.
* **Global domination** `0 ≤ V_src ≤ ‖λ‖_TV V_t` (`FloorData.At.nonneg_V`, `.upper`): transfers every *absolute* tail estimate of
  `triv` (`lemma_T_sig1_prob_mul` band and far, `twoZeroBump_lobe_bound`/`_band_bound`/`_far_bound`) with the constant
  `‖λ‖_TV/A(ξ_*)` (because `FKc (qProb triv) = FKc (qMix)/A(ξ_*)`).

Proofs: (P3) is `bump_psi_uniform triv` (black box) times the ratio `V_src/(A V_t)`, `|ratio - 1| ≤ δ/A`.  (P4) is the
vacuum core re-run for `V_src`: the pieces are lobe (`h V_src ≤ 0`: `h ≤ 0` from `sig_lobe_nonpos triv` and `V_t > 0`,
`V_src ≥ 0`), window (`bump_part1 triv` times the ratio), band and far (Lemma T at `triv` times `‖λ‖_TV`), then the
splitting lemmas of `VacuumCore`/`VacuumMain` (`split_integral_le`, `window_part_le`, `final_arith`).  The vacuum identity
(`k7_src`) turns the core into `g_vac,src ≥ -‖λ‖_TV - π ∫ h V_src` and Prop V (i), (ii).

## Which `(f, r)` are covered, and why

* `(f, r) = (1, 0)`: **covered**, every `FixedWeightProblem`-free common source (`CommonSource`), all `N ≥ 1`, `η_*`, offsets
  `σs` (so the families `D(N, η_*, d)`, displaced and far-first-site designs, i.e. `𝓕_1` with any terminal site `q < 0`).
  This gives Property (P) of `sr:P` for `V_mix` in the form of the eventual comb data `SrcEventualCombData` (the analogue
  of `EventualCombData`), and the transfer of `𝓕_1` used by `pmix:rigidity`(a).
* `(f, r) = (2, 1)`: **covered** (two-zero designs, `ut:T2`, `𝓕_2`, `γ = 5/2`), every weight `w`, every compact family `𝒦` of admissible
  `TwoZeroDesign`s, every `CommonSource`: `twoSimpleZeroTransfer_src` produces `SrcTwoZeroTransferData C 𝒦`, the `TwoZeroTransferData`
  of W-T2w with `V_src`, `psiAirySrc` and `F^{mix}_{2,c} = twoZeroFSrc = A(ξ_*) F_{2,c}^{(w,1)}`.  At `f = 2` the deep lobe is already
  bounded in absolute value at `triv` (`twoZeroBump_lobe_bound`), so lobe, band and far band transfer by `cmp_global` with the
  constant `‖λ‖_TV/A(ξ_*)` (`int_abs_src_le`), and the window by `cmp_window` (`twoZeroBump_window_comb_src`,
  `twoZeroBump_window_limit_src`, using the uniform bound `twoZero_Wr_bound` of `C_* κ² W_2` on `𝒦 × [-R, R]`).  The vacuum identity is
  `k7_src` (`twoZeroBump_gVac_bounds_src`: `|g_vac + π ∫ h V_s| ≤ ‖λ‖_TV`).  The second limit is one-sided, as at `triv`.
* general `(f, r)`, in particular `(m, m-1)`, `m ≥ 3`, and the Hermite-Biehler taper `(m_0, m_0 - 1)` of `pmix:rigidity`(c):
  **not in Lean**: the design side at `(w, Q ≡ 1)` itself is open (W-T2w, general `m`).  The comparison/transfer
  step proved here is design-independent, so each new design-side result at `triv` of the same shape (lobe, window, band, far)
  transfers verbatim.

## Modules (all build; headline declarations carry `#print axioms` guards, all `[propext, Classical.choice, Quot.sound]`)

| module | content |
|---|---|
| `VacCompare` | `triv`, `qMix`, `FKc_qMix`, `cmp_global`, `cmp_window`, `psiAirySrc`, `integral_psiAirySrc`, `integrable_psiAirySrc` |
| `VacWindow` | `ratio_aux`, `bump_part1_src` (comb window), `bump_psi_uniform_src` (first limit, `(1,0)`) |
| `VacCore` | `vacuum_core_bumped_src` (second limit core, `(1,0)`) |
| `VacProp` | `bumpSigGVac_ge_src`, `proposition_V_i/ii_bumped_src`, `bumpG_good_src`, `bump_psi_limsup_src`, `SrcEventualCombData`, `bumpEventualSrc`, `pmix_vac_f1` |
| `VacTwoZeroWindow` | `twoZeroFSrc`, `twoZero_Wr_bound`, `twoZeroBump_window_comb_src`, `twoZeroBump_window_limit_src` |
| `VacTwoZeroCore` | `int_abs_src_le`, `twoZeroBump_vacuum_core_src`, `twoZeroBump_gVac_bounds_src` |
| `VacTwoZero` | `twoZeroBump_{fields_eventually,integrable,window_field,limsup_field,vac_eventually}_src`, `SrcTwoZeroTransferData`, `twoSimpleZeroTransfer_src` |
