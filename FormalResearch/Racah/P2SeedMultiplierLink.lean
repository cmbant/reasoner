module

public import FormalResearch.Racah.P2SeedGridUnique
public import FormalResearch.Racah.P2AnalyticAllOrder3j

/-!
# The local-calculus multiplier at the seed row equals the seed coefficient (Weyl P2, `app:3j-allorder`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `app:3j-allorder`: `prop:localcalculus` (b),
`eq:3jpsi2r`, `eq:3jseedlogallorder`, `thm:3jallorderlocal`.

Notation.  `M, σ ∈ ℚ` with `α = M-σ`, `β = M+σ` natural numbers (the extremal chamber `M ≥ |σ|`, so
`L₀ = max(|M|,|σ|) = M`; `M = 0` is allowed, then `σ = 0`), `d_M = d^M_{Mσ}(arccos x)` the rank-`0` Wigner
vector `dv M σ 0`, `f_{2r}^{(0)} = f3even M σ 0 r` the `t^r`-Taylor coefficient of the exact germ of
`Φ_M^{Mσ}` (`P2AnalyticAllOrder3jSeries`), and `κ_r = expCoeff (seedEll α β) r` the coefficient of
`N^{-2r}` in `Φ_M^{Mσ}/d^M_{Mσ}` (`P2SeedLogAllOrderPhys`, `κ_r = [t^r] exp(∑ ℓ_s t^s)`).

## Results

* `f3even_zero_eq_expCoeff_mul` (**the link**): for every `r` and `x ∈ (-1,1)`,
  `f_{2r}^{(0)}(x) = κ_r(x) · d^M_{Mσ}(x)`, i.e. the Taylor coefficients of the exact germ at the seed row
  are `κ_r d`.  Proof: both sides are coefficients of an expansion of the *same* function `Φ_M^{Mσ}(x;1/N)`
  on the physical grid (`Phi3j_hasUniformExpansionOn` and `Phi3j_ratio_hasUniformExpansionOn`), the
  coefficients are continuous on `(-1,1)`, and the physical lattice is dense in `x` and unbounded in `N`
  (`grid_coeff_unique`, `exists_grid_point`).
* `kap_apply_eq_expCoeff`: the multiplier `κ_r = f_{2r}^{(0)}/d₀` of `allorder_operators` (`kap`) acts as
  multiplication by `expCoeff (seedEll α β) r`.
* `allorder_operators_seed_multiplier`: **the all-order operators `𝒢_r` of `allorder_operators` satisfy
  `(𝒢_r d_M)(x) = κ_r(x) d_M(x)`**, and `(𝒢_r d_n)(x) = f_{2r}^{(n)}(x)` for every rank `n`.
* `allorder_operators_seed_psi` (**`eq:3jpsi2r` at the seed row**, `L₀ > 0`): the operators of
  `thm:3jallorderlocal` can be taken with the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}`,
  `ψ_{r+1} ∈ C` a multiplier by a smooth `φ_{r+1}`, `φ_{r+1} = κ_{r+1} - 𝒥(𝖡_{r+1})d_M/d_M` on `(-1,1)`
  with `κ_{r+1} = expCoeff (seedEll α β) (r+1)` (the paper's `ψ_{2r} = κ_r - 𝒥(𝖡_{2r}) d/d`), and
  `𝒢_r d_n = f_{2r}^{(n)}` for every rank.
* `seed_G1_formula`: the first operator: `(𝒢_1 d_M)/d_M = κ_1 = ℓ_1 =
  (1/4)[S_2(2M+1) - S_2(β)/u₊² - S_2(α)/u₋²]`, `S_2(p) = p(p²-1)/12`.

Conventions (all reconciled by the statements): `x = 2μ/N`, `t = N⁻²`; `Phi3j M M σ N μ` with
`L = L₀ = M`; the grid `phys3jGrid M σ` (`SpecAdm`, `Lat4`) is the one on which both expansions are
stated, so no re-indexing is needed.  `hα : M - σ = α` (rational equation, `P2SeedLogAllOrderPhys`) and
`hα' : |M - σ| = α` (`P2AnalyticAllOrder3j`) are interchanged by `abs_of_nonneg`.

Not covered here: rationality of `ψ_{2r}` with poles at `±1` only (the multipliers here are smooth on `(-1,1)`
and given by the formula above), proved in `P2SeedRational` (`allorder_operators_seed_psi_rat`, every chamber);
the `6j` analogues (canonical sector: `P2AnalyticAllOrder6j`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Asymptotics FormalResearch.Wigner Finset Filter Topology Set

section Continuity

theorem continuousOn_coeff_pow {S : Set ℝ} {a : ℕ → ℝ → ℝ} (ha : ∀ s, ContinuousOn (a s) S)
    (n r : ℕ) : ContinuousOn (fun z => PowerSeries.coeff r (coeffSeries a z ^ n)) S := by
  induction n generalizing r with
  | zero =>
    simp only [pow_zero]
    exact continuousOn_const
  | succ n ih =>
    simp only [pow_succ, PowerSeries.coeff_mul]
    refine continuousOn_finsetSum _ fun p _ => (ih p.1).mul ?_
    simpa [coeffSeries] using ha p.2

/-- The exponential coefficients of continuous coefficient functions are continuous. -/
theorem continuousOn_expCoeff {S : Set ℝ} {a : ℕ → ℝ → ℝ} (ha : ∀ s, ContinuousOn (a s) S)
    (r : ℕ) : ContinuousOn (expCoeff a r) S := by
  have : expCoeff a r = fun z => ∑ n ∈ range (r + 1),
      ((n.factorial : ℝ))⁻¹ * PowerSeries.coeff r (coeffSeries a z ^ n) := by
    funext z; simp [expCoeff, expSeries]
  rw [this]
  exact continuousOn_finsetSum _ fun n _ => continuousOn_const.mul (continuousOn_coeff_pow ha n r)

theorem continuousOn_seedEll (α β r : ℕ) : ContinuousOn (seedEll α β r) (Ioo (-1 : ℝ) 1) := by
  unfold seedEll
  have h1 : ∀ x ∈ Ioo (-1 : ℝ) 1, ((1 - x) / 2) ^ (2 * r) ≠ 0 := fun x hx =>
    pow_ne_zero _ (by linarith [hx.2])
  have h2 : ∀ x ∈ Ioo (-1 : ℝ) 1, ((1 + x) / 2) ^ (2 * r) ≠ 0 := fun x hx =>
    pow_ne_zero _ (by linarith [hx.1])
  refine continuousOn_const.mul ((continuousOn_const.sub (continuousOn_const.div (by fun_prop) h1)).sub
    (continuousOn_const.div (by fun_prop) h2))

end Continuity

section Link

variable {M σ : ℚ} {α β : ℕ}

theorem continuousOn_wignerSmallDx_extremal (hα : M - σ = α) (hβ : M + σ = β) :
    ContinuousOn (wignerSmallDx M M σ) (Ioo (-1 : ℝ) 1) := by
  have hc : Continuous fun x : ℝ => (-1 : ℝ) ^ α * Real.sqrt (((α + β).factorial : ℝ) /
      ((α.factorial : ℝ) * β.factorial)) * Real.sqrt (((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β) := by
    fun_prop
  refine hc.continuousOn.congr fun x hx => ?_
  exact wignerSmallDx_extremal M σ α β hα hβ ⟨hx.1.le, hx.2.le⟩

/-- **The link: the Taylor coefficients of the exact germ at the seed row are `κ_r d`.**
For `α = M-σ`, `β = M+σ` natural (the extremal chamber `M ≥ |σ|`, `L₀ = M`; `M = 0` allowed),
every `r` and every `x ∈ (-1,1)`: `f_{2r}^{(0)}(x) = κ_r(x) · d^M_{Mσ}(x)`, where
`κ_r = expCoeff (seedEll α β) r = [t^r] exp(∑_s ℓ_s t^s)`.
Proved (no hypothesis beyond `α, β ∈ ℕ`): both sides are continuous coefficients of an expansion of
`Φ_M^{Mσ}(x; 1/N)` on the physical grid, and `grid_coeff_unique` identifies them. -/
theorem f3even_zero_eq_expCoeff_mul (hα : M - σ = α) (hβ : M + σ = β) (r : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    f3even M σ 0 r x = expCoeff (seedEll α β) r x * wignerSmallDx M M σ x := by
  have hmax := max_abs_eq_of_chamber hα hβ
  have hdc := continuousOn_wignerSmallDx_extremal hα hβ
  refine grid_coeff_unique hα hβ (fun q => Phi3j M M σ q.1 q.2) (f3even M σ 0)
    (fun r y => expCoeff (seedEll α β) r y * wignerSmallDx M M σ y)
    (fun r => (analyticOnNhd_f3even M σ 0 r).continuousOn)
    (fun r => (continuousOn_expCoeff (fun s => continuousOn_seedEll α β s) r).mul hdc)
    ?_ ?_ r x hx
  · intro K hK hKI R
    have h := Phi3j_hasUniformExpansionOn M σ 0 hK hKI
    simp only [Nat.cast_zero, add_zero, hmax] at h
    obtain ⟨C, hC⟩ := (hasUniformExpansionOn_iff.1 h) R
    refine ⟨C, hC.mono fun i hi z hz hzS => ?_⟩
    simpa [Real.norm_eq_abs, smul_eq_mul] using hi z hz hzS
  · intro K hK hKI R
    have h := Phi3j_ratio_hasUniformExpansionOn M σ α β hα hβ hK hKI
    obtain ⟨C0, hC0⟩ := (hasUniformExpansionOn_iff.1 h) R
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hdc.mono hKI)
    refine ⟨D * C0, hC0.mono fun i hi z hz hzS => ?_⟩
    have hne : wignerSmallDx M M σ z ≠ 0 := wignerSmallDx_extremal_ne_zero M σ α β hα hβ (hKI hz)
    have hb := hi z hz hzS
    simp only [Real.norm_eq_abs, smul_eq_mul] at hb
    have e : Phi3j M M σ i.1 i.2 - ∑ r ∈ range R, eps3j i ^ r * (expCoeff (seedEll α β) r z *
        wignerSmallDx M M σ z) = wignerSmallDx M M σ z * (Phi3j M M σ i.1 i.2 /
          wignerSmallDx M M σ z - ∑ r ∈ range R, eps3j i ^ r * expCoeff (seedEll α β) r z) := by
      rw [mul_sub, mul_div_cancel₀ _ hne, Finset.mul_sum]
      congr 1
      exact sum_congr rfl fun r _ => by ring
    show |_ - _| ≤ _
    rw [e, abs_mul]
    have hDz : |wignerSmallDx M M σ z| ≤ D := by simpa [Real.norm_eq_abs] using hD z hz
    calc _ ≤ D * (C0 * |eps3j i| ^ R) :=
          mul_le_mul hDz hb (abs_nonneg _) ((abs_nonneg _).trans hDz)
      _ = _ := by ring

theorem dv_zero_eq_wignerSmallDx (hα : M - σ = α) (hβ : M + σ = β) {y : ℝ}
    (hy : y ∈ LocalCalculus.Fun.Sx) :
    (LocalCalculus.Fun.dv M σ 0).1 y = wignerSmallDx M M σ y := by
  unfold LocalCalculus.Fun.dv
  rw [LocalCalculus.Fun.wigF_apply _ M σ hy, Nat.cast_zero, add_zero, max_abs_eq_of_chamber hα hβ]

end Link

namespace LocalCalculus.Fun

open Module
open scoped ContDiff

variable {M σ : ℚ} {α β : ℕ}

lemma abs_chamber {a : ℚ} {n : ℕ} (h : a = n) : |a| = n := by rw [h, Nat.abs_cast]

/-- The multiplier `κ_r = f_{2r}^{(0)}/d₀` of `allorder_operators` (`kap`) is multiplication by
`expCoeff (seedEll α β) r` on `(-1,1)`. -/
theorem kap_apply_eq_expCoeff (hα : M - σ = α) (hβ : M + σ = β) (r : ℕ) (f : Fn) {y : ℝ}
    (hy : y ∈ Sx) :
    (kap (abs_chamber hα) (abs_chamber hβ) r f).1 y = expCoeff (seedEll α β) r y * f.1 y := by
  show f3even M σ 0 r y / (dv M σ 0).1 y * f.1 y = _
  rw [f3even_zero_eq_expCoeff_mul hα hβ r hy, ← dv_zero_eq_wignerSmallDx hα hβ hy,
    mul_div_assoc, div_self (dv_zero_ne_zero (abs_chamber hα) (abs_chamber hβ) hy), mul_one]

/-- **The all-order operators act on the seed vector as multiplication by the seed coefficients.**
Any family `𝒢_r` with `(𝒢_r d_M)(x) = f_{2r}^{(0)}(x)` on `(-1,1)` (in particular the operators of
`allorder_operators`) satisfies `(𝒢_r d_M)(x) = κ_r(x) d_M(x)`, `κ_r = expCoeff (seedEll α β) r`
(`α = M-σ`, `β = M+σ` natural). -/
theorem seed_multiplier_link (hα : M - σ = α) (hβ : M + σ = β) {G : ℕ → End ℝ Fn}
    (hid : ∀ r, ∀ y ∈ Sx, (G r (dv M σ 0)).1 y = f3even M σ 0 r y) (r : ℕ) {y : ℝ} (hy : y ∈ Sx) :
    (G r (dv M σ 0)).1 y = expCoeff (seedEll α β) r y * (dv M σ 0).1 y := by
  rw [hid r y hy, f3even_zero_eq_expCoeff_mul hα hβ r hy, dv_zero_eq_wignerSmallDx hα hβ hy]

/-- **`thm:3jallorderlocal` at the seed row with the explicit multipliers.**  The operators `𝒢_r` of
`allorder_operators` (`α = M-σ`, `β = M+σ` natural) satisfy `(𝒢_r d_M)(x) = κ_r(x) d_M(x)` for all
`x ∈ (-1,1)`, `κ_r = expCoeff (seedEll α β) r` (`eq:3jseedlogallorder`). -/
theorem allorder_operators_seed_multiplier (hα : M - σ = α) (hβ : M + σ = β) :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) G r) ∧
      (∀ n r, ∀ y ∈ Sx, (G r (dv M σ n)).1 y = f3even M σ n r y) ∧
      ∀ r, ∀ y ∈ Sx, (G r (dv M σ 0)).1 y = expCoeff (seedEll α β) r y * (dv M σ 0).1 y := by
  obtain ⟨G, hG0, hGm, hGB, hGid⟩ := allorder_operators (abs_chamber hα) (abs_chamber hβ)
  exact ⟨G, hG0, hGm, hGB, hGid, fun r y hy =>
    seed_multiplier_link hα hβ (fun r y hy => hGid 0 r y hy) r hy⟩

/-- **The first operator at the seed row**: `(𝒢_1 d_M)(x)/d_M(x) = κ_1(x) = ℓ_1(x)
= (1/4)[S_2(2M+1) - S_2(β)/u₊² - S_2(α)/u₋²]`, `S_2(p) = p(p²-1)/12`, `u_∓ = (1∓x)/2`
(`2M+1 = α+β+1`). -/
theorem seed_G1_formula (hα : M - σ = α) (hβ : M + σ = β) {G : ℕ → End ℝ Fn}
    (hid : ∀ r, ∀ y ∈ Sx, (G r (dv M σ 0)).1 y = f3even M σ 0 r y) {y : ℝ} (hy : y ∈ Sx) :
    (G 1 (dv M σ 0)).1 y / (dv M σ 0).1 y =
      1 / 4 * (((α + β + 1 : ℕ) : ℝ) * (((α + β + 1 : ℕ) : ℝ) ^ 2 - 1) / 12 -
        (α : ℝ) * ((α : ℝ) ^ 2 - 1) / 12 / ((1 - y) / 2) ^ 2 -
        (β : ℝ) * ((β : ℝ) ^ 2 - 1) / 12 / ((1 + y) / 2) ^ 2) := by
  rw [seed_multiplier_link hα hβ hid 1 hy, mul_div_assoc,
    div_self (dv_zero_ne_zero (abs_chamber hα) (abs_chamber hβ) hy), mul_one,
    expCoeff_one _ (fun z => seedEll_zero α β z), seedEll_one]

/-- **`eq:3jpsi2r` at the seed row** (`L₀ = M > 0`).  There are operators `𝒢_r` as in
`allorder_operators` (rank-independent, left-normal, `[x, 𝒢_{r+1}] = 𝖡_{r+1}`, and
`𝒢_r d_n = f_{2r}^{(n)}` at every rank `n`) with the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}`
(`𝒥 = Jsol`), where `ψ_{r+1}` is multiplication by a function `φ` smooth on `(-1,1)` and
`φ = κ_{r+1} - 𝒥(𝖡_{r+1}) d_M / d_M` there, `κ_{r+1} = expCoeff (seedEll α β) (r+1)`: the paper's
`ψ_{2r} = κ_r - 𝒥(𝖡_{2r}) d/d`, with the seed coefficient `κ_r` of `eq:3jseedlogallorder`.
(For `M = σ = 0` the two-start argument of `allorder_operators_zero` is needed instead; there
`seed_multiplier_link` still gives `𝒢_r d_0 = κ_r d_0`.)  Rationality of `φ` is
`allorder_operators_seed_psi_rat` (`P2SeedRational`); the case `M = σ = 0` is `allorder_operators_zero_psi`
(`P2SeedZeroPsi`). -/
theorem allorder_operators_seed_psi (hα : M - σ = α) (hβ : M + σ = β) (hL : 0 < max |M| |σ|) :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) G r) ∧
      (∀ n r, ∀ y ∈ Sx, (G r (dv M σ n)).1 y = f3even M σ n r y) ∧
      ∀ r, ∃ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ Sx ∧
        (∀ (f : Fn) (y : ℝ), ((G (r + 1) - Jsol xOp DOp Csm (Bop xOp (Hop (SigM M σ) (TauM M σ))
          (0 : Polynomial ℝ) c3 (TauM M σ) G r)) f).1 y = φ y * f.1 y) ∧
        ∀ y ∈ Sx, φ y = expCoeff (seedEll α β) (r + 1) y -
          (Jsol xOp DOp Csm (Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) G r)
            (dv M σ 0)).1 y / (dv M σ 0).1 y := by
  have hα' := abs_chamber hα
  have hβ' := abs_chamber hβ
  have hk : 0 < kz M σ := by unfold kz; exact_mod_cast hL
  have hfwd : ∀ n : ℕ, (kz M σ + n) * Rn M σ (n + 1) ≠ 0 := by
    intro n
    have hR : 0 < Rn M σ (n + 1) := by
      unfold Rn
      refine Rk_pos M σ _ ?_
      have : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
      linarith
    have : 0 < kz M σ + n := by positivity
    exact (mul_pos this hR).ne'
  obtain ⟨G, hG0, hGm, hGB, hGκ, hGψ⟩ := LocalCalculus.local_calculus_start (D := DOp) (C := Csm)
    (x := xOp) DOp_xOp (fun c hc => comm_x_Csm hc) (fun c hc => comm_Csm hc) xOp_mem_Csm
    (Hop_mem_LN_sm (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) (d0 := dv M σ 0)
    (mulOp_mem_Csm _ (contDiffOn_div_dv0 hα' hβ' (dv M σ 0).contDiffOn_deriv))
    (DOp_dv_zero hα' hβ') (kap hα' hβ') (fun r => mulOp_mem_Csm _ _) (kap_zero hα' hβ')
  have hranks := LocalCalculus.local_calculus_ranks xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ)
    c3 c3_zero G hG0 (TauM M σ) (kz M σ) (Rn M σ) (dv M σ) (Hop_dv M σ) (dv_rec M σ) hGB
  have hu := LocalCalculus.rank_unique_of_start xOp (0 : Polynomial ℝ) c3 c3_zero (TauM M σ) (kz M σ)
    (Rn M σ) (Rn_zero M σ) hfwd (physFn_rankDefect hα' hβ') hranks (by
      rw [physFn_zero_eq_kap hα' hβ']
      funext r
      exact (hGκ r).symm)
  have hid : ∀ n r, ∀ y ∈ Sx, (G r (dv M σ n)).1 y = f3even M σ n r y := by
    intro n r y hy
    have := congrFun (congrFun hu n) r
    rw [← physFn_apply (M := M) (σ := σ) n r hy, this]
    rfl
  refine ⟨G, hG0, hGm, hGB, hid, fun r => ?_⟩
  obtain ⟨ψ, ⟨φ, hφ, hψφ⟩, hGs, hψd⟩ := hGψ r
  refine ⟨φ, hφ, fun f y => ?_, fun y hy => ?_⟩
  · have e : G (r + 1) - Jsol xOp DOp Csm (Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3
        (TauM M σ) G r) = ψ := by rw [hGs]; abel
    rw [e]
    exact hψφ f y
  · have h1 := hψφ (dv M σ 0) y
    rw [hψd] at h1
    have hd := dv_zero_ne_zero hα' hβ' hy
    have h3 := kap_apply_eq_expCoeff hα hβ (r + 1) (dv M σ 0) hy
    have h1' : (kap hα' hβ' (r + 1) (dv M σ 0)).1 y -
        (Jsol xOp DOp Csm (Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) G r)
          (dv M σ 0)).1 y = φ y * (dv M σ 0).1 y := h1
    rw [h3] at h1'
    field_simp
    linarith

end LocalCalculus.Fun

/-- info: 'FormalResearch.Racah.f3even_zero_eq_expCoeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.f3even_zero_eq_expCoeff_mul

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.kap_apply_eq_expCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.kap_apply_eq_expCoeff

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.seed_multiplier_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.seed_multiplier_link

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_seed_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_seed_multiplier

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.seed_G1_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.seed_G1_formula

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_seed_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_seed_psi

end FormalResearch.Racah
