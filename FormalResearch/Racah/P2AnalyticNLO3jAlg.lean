module

public import FormalResearch.Wigner.WignerDLadder
public import FormalResearch.Wigner.WignerDODE

/-!
# Next-to-leading squeezed `3j` formula: the Wigner-`d` algebra (Weyl P2, `thm:3jNLO`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jNLO` (`eq:3jf2`,
`eq:3jf2seednorm`); ladders `eq:dranklower`, `eq:drankupper`, ODE `eq:dODE`.

This file is the pure Wigner-`d` half of the induction in `P2AnalyticNLO3j`: it knows nothing
about the `3j` carrier.  With `d_L = wignerSmallDx L M σ`, `J = L(L+1)`,

* `nloA2`, `nloB2`: the paper's `A_2`, `B_2`; `nloF2 L M σ x = (A_2 d_L' + B_2 d_L)/(12(x²-1))`;
* `nloH`: `F_2 - (2L+1)L(L+1)/12 · d_L` (the `t`-derivative of the carrier, with the factor
  `√(Ct(2L+1,1,t))` removed, minus the `L`-independent part `μ d_L`);
* `nloH_rec`: **the inhomogeneous rank recurrence**, for `x ∈ (-1,1)`,
  `(2L+1)(L(L+1)x - Mσ) H_L = (L+1) R_L (H_{L-1} - L² d_{L-1}) + L R_{L+1} H_{L+1}`, proved from the
  rank ladders `wignerSmallDx_rank_lower/upper` differentiated once in `x`, and the ODE
  `wignerSmallDx_ode` to eliminate `d''` (a single rational identity, `nlo_alg_rec`);
* `nlo_seed_alg`: the extremal-rank identity `H_{L₀} + μ d_{L₀} = 0`
  (`eq:3jf2seednorm` in every chamber, in terms of `α = |M-σ|`, `β = |M+σ|`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Set

/-! ### The paper's `A_2`, `B_2`, `f_2` -/

/-- `A_2(x) = 2J(x³-x) - 4x(M²+σ²) + 2Mσ(x²+3) + 4x`, `J = L(L+1)` (`thm:3jNLO`). -/
noncomputable def nloA2 (L M σ : ℚ) (x : ℝ) : ℝ :=
  2 * ((L : ℝ) * ((L : ℝ) + 1)) * (x ^ 3 - x) - 4 * x * ((M : ℝ) ^ 2 + (σ : ℝ) ^ 2) +
    2 * ((M : ℝ) * σ) * (x ^ 2 + 3) + 4 * x

/-- `B_2(x) = J(x²-3) + 2Mσ x`, `J = L(L+1)` (`thm:3jNLO`). -/
noncomputable def nloB2 (L M σ : ℚ) (x : ℝ) : ℝ :=
  (L : ℝ) * ((L : ℝ) + 1) * (x ^ 2 - 3) + 2 * ((M : ℝ) * σ) * x

/-- `f_2 = (A_2 f' + B_2 f) / (12 (x²-1))` with `f = d^L_{Mσ}(arccos x)` (`eq:3jf2`). -/
noncomputable def nloF2 (L M σ : ℚ) (x : ℝ) : ℝ :=
  (nloA2 L M σ x * deriv (wignerSmallDx L M σ) x + nloB2 L M σ x * wignerSmallDx L M σ x) /
    (12 * (x ^ 2 - 1))

/-- `H_L = f_2 - (2L+1)L(L+1)/12 · f`. -/
noncomputable def nloH (L M σ : ℚ) (x : ℝ) : ℝ :=
  nloF2 L M σ x - (2 * (L : ℝ) + 1) * ((L : ℝ) * ((L : ℝ) + 1)) / 12 * wignerSmallDx L M σ x

/-! ### Real-variable versions (for the algebra) -/

/-- `A_2` in the variables `J = L(L+1)`, `S = M²+σ²`, `m = Mσ`. -/
noncomputable def nloAr (J S m x : ℝ) : ℝ :=
  2 * J * (x ^ 3 - x) - 4 * x * S + 2 * m * (x ^ 2 + 3) + 4 * x

/-- `B_2` in the variables `J`, `m`. -/
noncomputable def nloBr (J m x : ℝ) : ℝ := J * (x ^ 2 - 3) + 2 * m * x

/-- `H` in real variables: `(A d' + B d)/(12(x²-1)) - (2L+1)L(L+1)/12 d`. -/
noncomputable def nloHr (L S m x d dp : ℝ) : ℝ :=
  (nloAr (L * (L + 1)) S m x * dp + nloBr (L * (L + 1)) m x * d) / (12 * (x ^ 2 - 1)) -
    (2 * L + 1) * (L * (L + 1)) / 12 * d

lemma nloH_eq (L M σ : ℚ) (x : ℝ) :
    nloH L M σ x = nloHr (L : ℝ) ((M : ℝ) ^ 2 + (σ : ℝ) ^ 2) ((M : ℝ) * σ) x
      (wignerSmallDx L M σ x) (deriv (wignerSmallDx L M σ) x) := rfl

/-- **The rational identity** behind the inhomogeneous rank recurrence.  The four hypotheses
`h1..h4` are the rank ladders `R_L d_{L-1}`, `R_{L+1} d_{L+1}` and their `x`-derivatives (with `d''`
left in `w`), `hode` the Wigner ODE. -/
lemma nlo_alg_rec (x L m S u v w Rm dm dmp Rp dq dqp : ℝ) (hx : 1 - x ^ 2 ≠ 0)
    (hode : (1 - x ^ 2) * w - 2 * x * v + (L * (L + 1) - (S - 2 * m * x) / (1 - x ^ 2)) * u = 0)
    (h1 : Rm * dm = L * (1 - x ^ 2) * v + (L ^ 2 * x - m) * u)
    (h2 : Rm * dmp = L * (1 - x ^ 2) * w + L * (-2 * x) * v + L ^ 2 * u + (L ^ 2 * x - m) * v)
    (h3 : Rp * dq = ((L + 1) ^ 2 * x - m) * u - (L + 1) * (1 - x ^ 2) * v)
    (h4 : Rp * dqp = (L + 1) ^ 2 * u + ((L + 1) ^ 2 * x - m) * v -
      (L + 1) * ((-2 * x) * v + (1 - x ^ 2) * w)) :
    (2 * L + 1) * (L * (L + 1) * x - m) * nloHr L S m x u v =
      (L + 1) * (Rm * nloHr (L - 1) S m x dm dmp - L ^ 2 * (Rm * dm)) +
        L * (Rp * nloHr (L + 1) S m x dq dqp) := by
  have e1 : Rm * nloHr (L - 1) S m x dm dmp =
      (nloAr ((L - 1) * (L - 1 + 1)) S m x * (Rm * dmp) +
          nloBr ((L - 1) * (L - 1 + 1)) m x * (Rm * dm)) / (12 * (x ^ 2 - 1)) -
        (2 * (L - 1) + 1) * ((L - 1) * (L - 1 + 1)) / 12 * (Rm * dm) := by
    unfold nloHr; ring
  have e2 : Rp * nloHr (L + 1) S m x dq dqp =
      (nloAr ((L + 1) * (L + 1 + 1)) S m x * (Rp * dqp) +
          nloBr ((L + 1) * (L + 1 + 1)) m x * (Rp * dq)) / (12 * (x ^ 2 - 1)) -
        (2 * (L + 1) + 1) * ((L + 1) * (L + 1 + 1)) / 12 * (Rp * dq) := by
    unfold nloHr; ring
  rw [e1, e2, h1, h2, h3, h4]
  have hw : w = (2 * x * v - (L * (L + 1) - (S - 2 * m * x) / (1 - x ^ 2)) * u) / (1 - x ^ 2) := by
    rw [eq_div_iff hx]
    linear_combination hode
  have hx' : x ^ 2 - 1 ≠ 0 := by intro h; apply hx; linarith
  subst hw
  unfold nloHr nloAr nloBr
  field_simp
  ring

/-- **The seed identity** (`eq:3jf2seednorm`, every chamber): with `L = (a+b)/2 > 0`,
`S = (a²+b²)/2`, `m = (b²-a²)/4` (`a = |M-σ|`, `b = |M+σ|`) and the extremal ladder
`L(1-x²) d' + (L²x - m) d = 0`, one has `H + μ d = 0` with
`μ = (c_a/τ² + c_b/τ'²)/2`, `c_r = r(r²-1)/24`, `τ = (1-x)/2`, `τ' = (1+x)/2`. -/
lemma nlo_seed_alg (x a b d dp : ℝ) (hx1 : -1 < x) (hx2 : x < 1) (hL : 0 < a + b)
    (hlad : (a + b) / 2 * (1 - x ^ 2) * dp +
      (((a + b) / 2) ^ 2 * x - (b ^ 2 - a ^ 2) / 4) * d = 0) :
    nloHr ((a + b) / 2) ((a ^ 2 + b ^ 2) / 2) ((b ^ 2 - a ^ 2) / 4) x d dp +
      (a * (a ^ 2 - 1) / 24 / ((1 - x) / 2) ^ 2 + b * (b ^ 2 - 1) / 24 / ((1 + x) / 2) ^ 2) / 2 *
        d = 0 := by
  have h1 : 1 - x ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - x ≠ 0 := by linarith
  have h3 : 1 + x ≠ 0 := by linarith
  have h4 : x ^ 2 - 1 ≠ 0 := by intro h; apply h1; linarith
  have h5 : a + b ≠ 0 := hL.ne'
  have hdp : dp = -((((a + b) / 2) ^ 2 * x - (b ^ 2 - a ^ 2) / 4) * d) /
      ((a + b) / 2 * (1 - x ^ 2)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) h1)]
    linear_combination hlad
  subst hdp
  unfold nloHr nloAr nloBr
  field_simp
  ring

/-! ### Differentiating the ladders -/

lemma wdx_differentiableAt (j M σ : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (wignerSmallDx j M σ) x :=
  (hasDerivAt_wignerSmallDx j M σ hx).differentiableAt

lemma wdx_differentiableAt_deriv (j M σ : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (deriv (wignerSmallDx j M σ)) x := by
  have h : ContDiffOn ℝ 2 (wignerSmallDx j M σ) (Ioo (-1 : ℝ) 1) := by
    intro y hy
    have h1 : ContDiffAt ℝ 2 Real.arccos y :=
      Real.contDiffAt_arccos (by linarith [hy.1]) (by linarith [hy.2])
    exact ((wignerSmallD_contDiff j M σ (n := 2)).contDiffAt.comp y h1).contDiffWithinAt
  have h2 : ContDiffOn ℝ 1 (deriv (wignerSmallDx j M σ)) (Ioo (-1 : ℝ) 1) :=
    h.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (h2.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hx)

/-- `x`-derivative of the lower ladder `eq:dranklower`, with `d''` left in place. -/
lemma wdx_lower_deriv (j M σ : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wigR j M σ * deriv (wignerSmallDx (j - 1) M σ) x =
      (j : ℝ) * (1 - x ^ 2) * deriv (deriv (wignerSmallDx j M σ)) x +
        (j : ℝ) * (-2 * x) * deriv (wignerSmallDx j M σ) x + (j : ℝ) ^ 2 * wignerSmallDx j M σ x +
        ((j : ℝ) ^ 2 * x - (σ : ℝ) * M) * deriv (wignerSmallDx j M σ) x := by
  have heq : (fun y => wigR j M σ * wignerSmallDx (j - 1) M σ y) =ᶠ[nhds x]
      fun y => (j : ℝ) * (1 - y ^ 2) * deriv (wignerSmallDx j M σ) y +
        ((j : ℝ) ^ 2 * y - (σ : ℝ) * M) * wignerSmallDx j M σ y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact wignerSmallDx_rank_lower j M σ hy
  rw [← deriv_const_mul _ (wdx_differentiableAt (j - 1) M σ hx), heq.deriv_eq]
  have h1 : HasDerivAt (fun y : ℝ => (j : ℝ) * (1 - y ^ 2)) ((j : ℝ) * (-2 * x)) x := by
    have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).const_mul (j : ℝ)
    convert this using 1; simp
  have h2 : HasDerivAt (fun y : ℝ => (j : ℝ) ^ 2 * y - (σ : ℝ) * M) ((j : ℝ) ^ 2) x := by
    have := ((hasDerivAt_id x).const_mul ((j : ℝ) ^ 2)).sub_const ((σ : ℝ) * M)
    simpa using this
  have h3 := (h1.mul (wdx_differentiableAt_deriv j M σ hx).hasDerivAt).add
    (h2.mul (wdx_differentiableAt j M σ hx).hasDerivAt)
  exact h3.deriv.trans (by ring)

/-- `x`-derivative of the upper ladder `eq:drankupper`, with `d''` left in place. -/
lemma wdx_upper_deriv (j M σ : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wigR (j + 1) M σ * deriv (wignerSmallDx (j + 1) M σ) x =
      ((j : ℝ) + 1) ^ 2 * wignerSmallDx j M σ x +
        (((j : ℝ) + 1) ^ 2 * x - (σ : ℝ) * M) * deriv (wignerSmallDx j M σ) x -
        ((j : ℝ) + 1) * ((-2 * x) * deriv (wignerSmallDx j M σ) x +
          (1 - x ^ 2) * deriv (deriv (wignerSmallDx j M σ)) x) := by
  have heq : (fun y => wigR (j + 1) M σ * wignerSmallDx (j + 1) M σ y) =ᶠ[nhds x]
      fun y => (((j : ℝ) + 1) ^ 2 * y - (σ : ℝ) * M) * wignerSmallDx j M σ y -
        ((j : ℝ) + 1) * (1 - y ^ 2) * deriv (wignerSmallDx j M σ) y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact wignerSmallDx_rank_upper j M σ hy
  rw [← deriv_const_mul _ (wdx_differentiableAt (j + 1) M σ hx), heq.deriv_eq]
  have h1 : HasDerivAt (fun y : ℝ => ((j : ℝ) + 1) * (1 - y ^ 2)) (((j : ℝ) + 1) * (-2 * x)) x := by
    have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).const_mul ((j : ℝ) + 1)
    convert this using 1; simp
  have h2 : HasDerivAt (fun y : ℝ => ((j : ℝ) + 1) ^ 2 * y - (σ : ℝ) * M) (((j : ℝ) + 1) ^ 2) x := by
    have := ((hasDerivAt_id x).const_mul (((j : ℝ) + 1) ^ 2)).sub_const ((σ : ℝ) * M)
    simpa using this
  have h3 := (h2.mul (wdx_differentiableAt j M σ hx).hasDerivAt).sub
    (h1.mul (wdx_differentiableAt_deriv j M σ hx).hasDerivAt)
  exact h3.deriv.trans (by ring)

/-! ### The inhomogeneous rank recurrence -/

/-- **Inhomogeneous rank recurrence of `H_L`** (`thm:3jNLO`, induction step), for `x ∈ (-1,1)`:
`(2L+1)(L(L+1)x - Mσ) H_L = (L+1) R_L (H_{L-1} - L² d_{L-1}) + L R_{L+1} H_{L+1}`
with `H_L = f_2 - (2L+1)L(L+1)/12 · d_L`, `R_k = wigR k M σ`.  Pure ladder-and-ODE algebra, valid
for all rational `L, M, σ` (the terms with `R_L = 0` vanish). -/
theorem nloH_rec (L M σ : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (2 * (L : ℝ) + 1) * ((L : ℝ) * ((L : ℝ) + 1) * x - (M : ℝ) * σ) * nloH L M σ x =
      ((L : ℝ) + 1) * (wigR L M σ * nloH (L - 1) M σ x -
          (L : ℝ) ^ 2 * (wigR L M σ * wignerSmallDx (L - 1) M σ x)) +
        (L : ℝ) * (wigR (L + 1) M σ * nloH (L + 1) M σ x) := by
  have hx1 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hode := wignerSmallDx_ode L M σ hx
  have hl := wignerSmallDx_rank_lower L M σ hx
  have hu := wignerSmallDx_rank_upper L M σ hx
  have hld := wdx_lower_deriv L M σ hx
  have hud := wdx_upper_deriv L M σ hx
  have key := nlo_alg_rec x (L : ℝ) ((M : ℝ) * σ) ((M : ℝ) ^ 2 + (σ : ℝ) ^ 2)
    (wignerSmallDx L M σ x) (deriv (wignerSmallDx L M σ) x)
    (deriv (deriv (wignerSmallDx L M σ)) x) (wigR L M σ) (wignerSmallDx (L - 1) M σ x)
    (deriv (wignerSmallDx (L - 1) M σ) x) (wigR (L + 1) M σ) (wignerSmallDx (L + 1) M σ x)
    (deriv (wignerSmallDx (L + 1) M σ) x) hx1
    (by linear_combination hode)
    (by linear_combination hl) (by linear_combination hld) (by linear_combination hu)
    (by linear_combination hud)
  simp only [nloH_eq]
  push_cast
  linear_combination key

/-- info: 'FormalResearch.Racah.nlo_alg_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nlo_alg_rec

/-- info: 'FormalResearch.Racah.nlo_seed_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nlo_seed_alg

/-- info: 'FormalResearch.Racah.nloH_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nloH_rec

end FormalResearch.Racah
