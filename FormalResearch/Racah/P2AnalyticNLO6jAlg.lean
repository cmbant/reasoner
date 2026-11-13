module

public import FormalResearch.Wigner.WignerDLadder
public import FormalResearch.Wigner.WignerDODE

/-!
# First `6j` correction: the Wigner-`d` algebra (Weyl P2, `thm:6jclosedcorrection`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:6jclosedcorrection` (`eq:6jclosedg`,
`eq:6jPf`, `eq:6jQf`, `eq:6jforcingconstants`), the rank ladders `eq:dranklower`, `eq:drankupper` and
the Wigner equation.

This file is the pure Wigner-`d` half of the induction in `P2AnalyticNLO6j`: it knows nothing about
the `6j` carrier.  In the *shape-homogeneous* variables `ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)` (for a
physical triple `ρ_{AB} = (A⁻²+B⁻²)/8`, `1/(AB)`; the formulas are linear in `(ρ, w)`), with
`J = f(f+1)`, `S = m²+n²`, `τ = mn`, `u = 1-x²`:

* `nlo6P`, `nlo6Q` (paper `P_f`, `Q_f`): `c_0 = (1-S)w/8 + ρτ`, `c_1 = w/4 - ρx`,
  `P = -c_0 + c_1 (2-2S+4τx-Ju)/(3u)`, `Q = ρJ/2 + c_1(τ-Jx)/(3u)`;
* `nlo6G J S τ ρ w x d d' = P d' + Q d` (`eq:6jclosedg`, `G_{f,2}`);
* `nlo6Hr`: `G_{f,2}` minus the diagonal part `ρ(2f+1)f(f+1)/6 · d_f` of the `t`-derivative of the
  normalisation `Π_f^{-1/2}`;
* `nlo6H_rec`: **the inhomogeneous rank recurrence** (for `x ∈ (-1,1)`, all rational `f,m,n`),
  `(2f+1)(f(f+1)x-mn) H_f = (f+1)R_f (H_{f-1} - 2ρf² d_{f-1}) + f R_{f+1} H_{f+1} + (2f+1)f(f+1)(2f(f+1)+1-S)(w/8) d_f`,
  proved from the ladders differentiated once in `x` and the ODE (one rational identity,
  `nlo6_alg_rec`);
* `nlo6_seed_alg`: the extremal-rank identity (`eq:kappaClosedMatch`, `eq:extremaldlog`,
  `eq:trianglePairIdentities`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Set

/-! ### The paper's `P_f`, `Q_f`, `G_{f,2}` -/

/-- `P_f = -c_0 + c_1 (2-2S+4τx-Ju)/(3u)` (`eq:6jPf`), `c_0 = (1-S)w/8 + ρτ`, `c_1 = w/4 - ρx`,
`u = 1-x²`, in the variables `J = f(f+1)`, `S = m²+n²`, `τ = mn`, `ρ = ϱ_{AB}`, `w = 1/(AB)`. -/
noncomputable def nlo6P (J S τ ρ w x : ℝ) : ℝ :=
  -((1 - S) * w / 8 + ρ * τ) +
    (w / 4 - ρ * x) * (2 - 2 * S + 4 * τ * x - J * (1 - x ^ 2)) / (3 * (1 - x ^ 2))

/-- `Q_f = ρJ/2 + c_1 (τ-Jx)/(3u)` (`eq:6jQf`). -/
noncomputable def nlo6Q (J _S τ ρ w x : ℝ) : ℝ :=
  ρ * J / 2 + (w / 4 - ρ * x) * (τ - J * x) / (3 * (1 - x ^ 2))

/-- `G_{f,2} = P_f d' + Q_f d` (`eq:6jclosedg`). -/
noncomputable def nlo6G (J S τ ρ w x d dp : ℝ) : ℝ :=
  nlo6P J S τ ρ w x * dp + nlo6Q J S τ ρ w x * d

/-- `H_f = G_{f,2} - ρ(2f+1)f(f+1)/6 · d_f`. -/
noncomputable def nlo6Hr (L S τ ρ w x d dp : ℝ) : ℝ :=
  nlo6G (L * (L + 1)) S τ ρ w x d dp - ρ * (2 * L + 1) * (L * (L + 1)) / 6 * d

lemma nlo6G_smul (J S τ ρ w x d dp s : ℝ) :
    nlo6G J S τ (s * ρ) (s * w) x d dp = s * nlo6G J S τ ρ w x d dp := by
  unfold nlo6G nlo6P nlo6Q; ring

/-- **The rational identity** behind the inhomogeneous rank recurrence.  `h1..h4` are the rank
ladders `R_f d_{f-1}`, `R_{f+1} d_{f+1}` and their `x`-derivatives (`d''` left in `wd`), `hode` the
Wigner equation. -/
lemma nlo6_alg_rec (x L S τ ρ w u v wd Rm dm dmp Rp dq dqp : ℝ) (hx : 1 - x ^ 2 ≠ 0)
    (hode : (1 - x ^ 2) * wd - 2 * x * v + (L * (L + 1) - (S - 2 * τ * x) / (1 - x ^ 2)) * u = 0)
    (h1 : Rm * dm = L * (1 - x ^ 2) * v + (L ^ 2 * x - τ) * u)
    (h2 : Rm * dmp = L * (1 - x ^ 2) * wd + L * (-2 * x) * v + L ^ 2 * u + (L ^ 2 * x - τ) * v)
    (h3 : Rp * dq = ((L + 1) ^ 2 * x - τ) * u - (L + 1) * (1 - x ^ 2) * v)
    (h4 : Rp * dqp = (L + 1) ^ 2 * u + ((L + 1) ^ 2 * x - τ) * v -
      (L + 1) * ((-2 * x) * v + (1 - x ^ 2) * wd)) :
    (2 * L + 1) * (L * (L + 1) * x - τ) * nlo6Hr L S τ ρ w x u v =
      (L + 1) * (Rm * nlo6Hr (L - 1) S τ ρ w x dm dmp - 2 * ρ * L ^ 2 * (Rm * dm)) +
        L * (Rp * nlo6Hr (L + 1) S τ ρ w x dq dqp) +
        (2 * L + 1) * (L * (L + 1)) * (2 * (L * (L + 1)) + 1 - S) * w / 8 * u := by
  have e1 : Rm * nlo6Hr (L - 1) S τ ρ w x dm dmp =
      nlo6P ((L - 1) * (L - 1 + 1)) S τ ρ w x * (Rm * dmp) +
        nlo6Q ((L - 1) * (L - 1 + 1)) S τ ρ w x * (Rm * dm) -
          ρ * (2 * (L - 1) + 1) * ((L - 1) * (L - 1 + 1)) / 6 * (Rm * dm) := by
    unfold nlo6Hr nlo6G; ring
  have e2 : Rp * nlo6Hr (L + 1) S τ ρ w x dq dqp =
      nlo6P ((L + 1) * (L + 1 + 1)) S τ ρ w x * (Rp * dqp) +
        nlo6Q ((L + 1) * (L + 1 + 1)) S τ ρ w x * (Rp * dq) -
          ρ * (2 * (L + 1) + 1) * ((L + 1) * (L + 1 + 1)) / 6 * (Rp * dq) := by
    unfold nlo6Hr nlo6G; ring
  rw [e1, e2, h1, h2, h3, h4]
  have hw : wd = (2 * x * v - (L * (L + 1) - (S - 2 * τ * x) / (1 - x ^ 2)) * u) / (1 - x ^ 2) := by
    rw [eq_div_iff hx]
    linear_combination hode
  subst hw
  unfold nlo6Hr nlo6G nlo6P nlo6Q
  field_simp
  ring


/-! ### Differentiating the ladders -/

lemma nlo6_differentiableAt (j m' m : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (wignerSmallDx j m' m) x :=
  (hasDerivAt_wignerSmallDx j m' m hx).differentiableAt

lemma nlo6_differentiableAt_deriv (j m' m : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (deriv (wignerSmallDx j m' m)) x := by
  have h : ContDiffOn ℝ 2 (wignerSmallDx j m' m) (Ioo (-1 : ℝ) 1) := by
    intro y hy
    have h1 : ContDiffAt ℝ 2 Real.arccos y :=
      Real.contDiffAt_arccos (by linarith [hy.1]) (by linarith [hy.2])
    exact ((wignerSmallD_contDiff j m' m (n := 2)).contDiffAt.comp y h1).contDiffWithinAt
  have h2 : ContDiffOn ℝ 1 (deriv (wignerSmallDx j m' m)) (Ioo (-1 : ℝ) 1) :=
    h.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (h2.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hx)

/-- `x`-derivative of the lower ladder `eq:dranklower`, with `d''` left in place. -/
lemma nlo6_lower_deriv (j m' m : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wigR j m' m * deriv (wignerSmallDx (j - 1) m' m) x =
      (j : ℝ) * (1 - x ^ 2) * deriv (deriv (wignerSmallDx j m' m)) x +
        (j : ℝ) * (-2 * x) * deriv (wignerSmallDx j m' m) x + (j : ℝ) ^ 2 * wignerSmallDx j m' m x +
        ((j : ℝ) ^ 2 * x - (m : ℝ) * m') * deriv (wignerSmallDx j m' m) x := by
  have heq : (fun y => wigR j m' m * wignerSmallDx (j - 1) m' m y) =ᶠ[nhds x]
      fun y => (j : ℝ) * (1 - y ^ 2) * deriv (wignerSmallDx j m' m) y +
        ((j : ℝ) ^ 2 * y - (m : ℝ) * m') * wignerSmallDx j m' m y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact wignerSmallDx_rank_lower j m' m hy
  rw [← deriv_const_mul _ (nlo6_differentiableAt (j - 1) m' m hx), heq.deriv_eq]
  have h1 : HasDerivAt (fun y : ℝ => (j : ℝ) * (1 - y ^ 2)) ((j : ℝ) * (-2 * x)) x := by
    have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).const_mul (j : ℝ)
    convert this using 1; simp
  have h2 : HasDerivAt (fun y : ℝ => (j : ℝ) ^ 2 * y - (m : ℝ) * m') ((j : ℝ) ^ 2) x := by
    have := ((hasDerivAt_id x).const_mul ((j : ℝ) ^ 2)).sub_const ((m : ℝ) * m')
    simpa using this
  have h3 := (h1.mul (nlo6_differentiableAt_deriv j m' m hx).hasDerivAt).add
    (h2.mul (nlo6_differentiableAt j m' m hx).hasDerivAt)
  exact h3.deriv.trans (by ring)

/-- `x`-derivative of the upper ladder `eq:drankupper`, with `d''` left in place. -/
lemma nlo6_upper_deriv (j m' m : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wigR (j + 1) m' m * deriv (wignerSmallDx (j + 1) m' m) x =
      ((j : ℝ) + 1) ^ 2 * wignerSmallDx j m' m x +
        (((j : ℝ) + 1) ^ 2 * x - (m : ℝ) * m') * deriv (wignerSmallDx j m' m) x -
        ((j : ℝ) + 1) * ((-2 * x) * deriv (wignerSmallDx j m' m) x +
          (1 - x ^ 2) * deriv (deriv (wignerSmallDx j m' m)) x) := by
  have heq : (fun y => wigR (j + 1) m' m * wignerSmallDx (j + 1) m' m y) =ᶠ[nhds x]
      fun y => (((j : ℝ) + 1) ^ 2 * y - (m : ℝ) * m') * wignerSmallDx j m' m y -
        ((j : ℝ) + 1) * (1 - y ^ 2) * deriv (wignerSmallDx j m' m) y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact wignerSmallDx_rank_upper j m' m hy
  rw [← deriv_const_mul _ (nlo6_differentiableAt (j + 1) m' m hx), heq.deriv_eq]
  have h1 : HasDerivAt (fun y : ℝ => ((j : ℝ) + 1) * (1 - y ^ 2)) (((j : ℝ) + 1) * (-2 * x)) x := by
    have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).const_mul ((j : ℝ) + 1)
    convert this using 1; simp
  have h2 : HasDerivAt (fun y : ℝ => ((j : ℝ) + 1) ^ 2 * y - (m : ℝ) * m') (((j : ℝ) + 1) ^ 2) x := by
    have := ((hasDerivAt_id x).const_mul (((j : ℝ) + 1) ^ 2)).sub_const ((m : ℝ) * m')
    simpa using this
  have h3 := (h2.mul (nlo6_differentiableAt j m' m hx).hasDerivAt).sub
    (h1.mul (nlo6_differentiableAt_deriv j m' m hx).hasDerivAt)
  exact h3.deriv.trans (by ring)

/-! ### The inhomogeneous rank recurrence -/

/-- **Inhomogeneous rank recurrence of `H_f = G_{f,2} - ρ(2f+1)f(f+1)/6 · d_f`** (`thm:6jclosedcorrection`,
induction step), for `x ∈ (-1,1)` and `d_f = wignerSmallDx f n m` (`R_k = wigR k n m`):
`(2f+1)(f(f+1)x-mn) H_f = (f+1)R_f (H_{f-1} - 2ρ f² d_{f-1}) + f R_{f+1} H_{f+1}
  + (2f+1) f(f+1)(2f(f+1)+1-m²-n²)(w/8) d_f`.
Pure ladder-and-ODE algebra, valid for all rational `f,m,n`. -/
theorem nlo6H_rec (L m n : ℚ) (ρ w : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (2 * (L : ℝ) + 1) * ((L : ℝ) * ((L : ℝ) + 1) * x - (m : ℝ) * n) *
        nlo6Hr (L : ℝ) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n) ρ w x
          (wignerSmallDx L n m x) (deriv (wignerSmallDx L n m) x) =
      ((L : ℝ) + 1) * (wigR L n m * nlo6Hr ((L - 1 : ℚ) : ℝ) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n)
          ρ w x (wignerSmallDx (L - 1) n m x) (deriv (wignerSmallDx (L - 1) n m) x) -
          2 * ρ * (L : ℝ) ^ 2 * (wigR L n m * wignerSmallDx (L - 1) n m x)) +
        (L : ℝ) * (wigR (L + 1) n m * nlo6Hr ((L + 1 : ℚ) : ℝ) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)
          ((m : ℝ) * n) ρ w x (wignerSmallDx (L + 1) n m x) (deriv (wignerSmallDx (L + 1) n m) x)) +
        (2 * (L : ℝ) + 1) * ((L : ℝ) * ((L : ℝ) + 1)) *
          (2 * ((L : ℝ) * ((L : ℝ) + 1)) + 1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) * w / 8 *
          wignerSmallDx L n m x := by
  have hx1 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hode := wignerSmallDx_ode L n m hx
  have hl := wignerSmallDx_rank_lower L n m hx
  have hu := wignerSmallDx_rank_upper L n m hx
  have hld := nlo6_lower_deriv L n m hx
  have hud := nlo6_upper_deriv L n m hx
  have key := nlo6_alg_rec x (L : ℝ) ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ((m : ℝ) * n) ρ w
    (wignerSmallDx L n m x) (deriv (wignerSmallDx L n m) x)
    (deriv (deriv (wignerSmallDx L n m)) x) (wigR L n m) (wignerSmallDx (L - 1) n m x)
    (deriv (wignerSmallDx (L - 1) n m) x) (wigR (L + 1) n m) (wignerSmallDx (L + 1) n m x)
    (deriv (wignerSmallDx (L + 1) n m) x) hx1
    (by linear_combination hode)
    (by linear_combination hl) (by linear_combination hld) (by linear_combination hu)
    (by linear_combination hud)
  push_cast
  linear_combination key

/-! ### The seed identity -/

/-- `c_r = r(r²-1)/24`. -/
noncomputable def nlo6cc (r : ℝ) : ℝ := r * (r ^ 2 - 1) / 24

/-- The `f`-independent part of the `t`-derivative of the edge factor,
`μ = ½[c_p(Δ₁⁻²+Δ₂⁻²) + c_q(Δ₃⁻²+Δ₄⁻²)]`, with the triangle-pair identities
(`eq:trianglePairIdentities`) applied: `Δ₁⁻²+Δ₂⁻² = (8ρ-(1+x)w)/(1-x)²`,
`Δ₃⁻²+Δ₄⁻² = (8ρ+(1-x)w)/(1+x)²`. -/
noncomputable def nlo6Mu (p q ρ w x : ℝ) : ℝ :=
  (nlo6cc p * ((8 * ρ - (1 + x) * w) / (1 - x) ^ 2) +
    nlo6cc q * ((8 * ρ + (1 - x) * w) / (1 + x) ^ 2)) / 2

/-- **The seed identity** (`eq:kappaClosedMatch`): at the extremal rank `f = m > 0` with
`m(1-x²)d' + (m²x - mn)d = 0` (`eq:extremaldlog`), `H_m + μ d = 0`, `p = m-n`, `q = m+n`. -/
lemma nlo6_seed_alg (x m n ρ w d dp : ℝ) (hx1 : -1 < x) (hx2 : x < 1) (hm : 0 < m)
    (hlad : m * (1 - x ^ 2) * dp + (m ^ 2 * x - m * n) * d = 0) :
    nlo6Hr m (m ^ 2 + n ^ 2) (m * n) ρ w x d dp + nlo6Mu (m - n) (m + n) ρ w x * d = 0 := by
  have h1 : 1 - x ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - x ≠ 0 := by linarith
  have h3 : 1 + x ≠ 0 := by linarith
  have hdp : dp = -((m ^ 2 * x - m * n) * d) / (m * (1 - x ^ 2)) := by
    rw [eq_div_iff (mul_ne_zero hm.ne' h1)]
    linear_combination hlad
  subst hdp
  unfold nlo6Hr nlo6G nlo6P nlo6Q nlo6Mu nlo6cc
  field_simp
  ring

/-- info: 'FormalResearch.Racah.nlo6H_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nlo6H_rec

/-- info: 'FormalResearch.Racah.nlo6_seed_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nlo6_seed_alg

end FormalResearch.Racah
