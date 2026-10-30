import FormalResearch.FourQubitEntropy.AH6Assembly

/-!
# The double factor `(e - e₀)²` of the discriminant polynomial

`joint_entropy_analytic_proof.tex`, paragraph "The one polynomial sign": the cubic `F(e₀,·)` has a double root at
`v₀` and `F_e(e₀,v₀) = 0`; hence the discriminant of `F(e,·)`, equal to `-e¹⁰L(e)² R(e)`, vanishes to second order at
`e₀`, i.e. `R(e₀) = 0` and `R'(e₀) = 0` (`R_flat`).  Here the argument is algebraic: a cubic with a double root `r` has
`disc = 0` and `dF·δp(r)` is a multiple of `δp(r)` (`disc3_double`, `disc3_deriv_zero`), combined with the chain rule
for the explicit polynomial `disc3`.
-/

namespace FormalResearch.FourQubitEntropy.AH6

theorem disc3_double (a b c d r : ℝ) (h0 : d + c * r + b * r ^ 2 + a * r ^ 3 = 0)
    (h1 : c + 2 * b * r + 3 * a * r ^ 2 = 0) : disc3 a b c d = 0 := by
  have hc : c = -2 * b * r - 3 * a * r ^ 2 := by linarith
  have hd : d = -(c * r + b * r ^ 2 + a * r ^ 3) := by linarith
  rw [hd, hc]; unfold disc3; ring

theorem disc3_deriv_zero (a b c d a' b' c' d' r : ℝ) (h0 : d + c * r + b * r ^ 2 + a * r ^ 3 = 0)
    (h1 : c + 2 * b * r + 3 * a * r ^ 2 = 0) (h2 : d' + c' * r + b' * r ^ 2 + a' * r ^ 3 = 0) :
    (-4 * c ^ 3 - 54 * a * d ^ 2 + 18 * b * c * d) * a' + (2 * b * c ^ 2 - 12 * b ^ 2 * d + 18 * a * c * d) * b' +
      (2 * b ^ 2 * c - 12 * a * c ^ 2 + 18 * a * b * d) * c' + (-4 * b ^ 3 - 54 * a ^ 2 * d + 18 * a * b * c) * d' = 0 := by
  have hc : c = -2 * b * r - 3 * a * r ^ 2 := by linarith
  have hd : d = -(c * r + b * r ^ 2 + a * r ^ 3) := by linarith
  have hd' : d' = -(c' * r + b' * r ^ 2 + a' * r ^ 3) := by linarith
  rw [hd', hd, hc]; ring

theorem disc3_hasDerivAt {a b c d : ℝ → ℝ} {a' b' c' d' x : ℝ} (ha : HasDerivAt a a' x)
    (hb : HasDerivAt b b' x) (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun e => disc3 (a e) (b e) (c e) (d e))
      ((-4 * c x ^ 3 - 54 * a x * d x ^ 2 + 18 * b x * c x * d x) * a' +
        (2 * b x * c x ^ 2 - 12 * b x ^ 2 * d x + 18 * a x * c x * d x) * b' +
        (2 * b x ^ 2 * c x - 12 * a x * c x ^ 2 + 18 * a x * b x * d x) * c' +
        (-4 * b x ^ 3 - 54 * a x ^ 2 * d x + 18 * a x * b x * c x) * d') x := by
  have hf : (fun e => disc3 (a e) (b e) (c e) (d e)) =
      fun e => b e ^ 2 * c e ^ 2 - 4 * (a e * c e ^ 3) - 4 * (b e ^ 3 * d e) - 27 * (a e ^ 2 * d e ^ 2) +
        18 * (a e * b e * c e * d e) := by
    funext e; unfold disc3; ring
  rw [hf]
  have h := ((((hb.pow 2).mul (hc.pow 2)).sub ((ha.mul (hc.pow 3)).const_mul 4)).sub
    ((((hb.pow 3).mul hd)).const_mul 4)).sub (((ha.pow 2).mul (hd.pow 2)).const_mul 27)
    |>.add ((((ha.mul hb).mul hc).mul hd).const_mul 18)
  refine HasDerivAt.congr_deriv h ?_
  simp only [Nat.cast_ofNat, Pi.pow_apply, Pi.mul_apply]
  ring

section Derivs

variable (D : MajData)

theorem MajData.L_hd (x : ℝ) : HasDerivAt D.L D.gam x := by
  have h := (((hasDerivAt_id x).sub_const D.e0).const_mul D.gam).const_add 1
  unfold MajData.L
  exact HasDerivAt.congr_deriv h (by ring)

theorem MajData.U_hd {q1 x : ℝ} (hq : HasDerivAt D.q q1 x) :
    HasDerivAt D.U (8 * D.k0 * (2 * D.q x * q1)) x := by
  have h := (hq.pow 2).const_mul (8 * D.k0)
  unfold MajData.U
  exact HasDerivAt.congr_deriv h (by simp)

theorem MajData.V_hd {A1 x : ℝ} (hA : HasDerivAt D.A A1 x) :
    HasDerivAt D.V (8 * (D.A x + x * A1)) x := by
  have h := ((((hasDerivAt_id x).const_mul 8).mul hA).const_add (1 / 2))
  unfold MajData.V
  have e : (fun e => 1 / 2 + 8 * e * D.A e) = fun y => 1 / 2 + (8 * id y) * D.A y := by
    funext y; simp
  rw [e]
  exact HasDerivAt.congr_deriv h (by simp; ring)

theorem MajData.W_hd {B1 x : ℝ} (hB : HasDerivAt D.B B1 x) :
    HasDerivAt D.W (8 * (3 * x ^ 2 * D.B x + x ^ 3 * B1)) x := by
  have h := ((((hasDerivAt_id x).pow 3).const_mul 8).mul hB).const_add eta2R
  unfold MajData.W
  have e : (fun e => eta2R + 8 * e ^ 3 * D.B e) = fun y => eta2R + (8 * (id ^ 3) y) * D.B y := by
    funext y; simp
  rw [e]
  exact HasDerivAt.congr_deriv h (by simp; ring)

end Derivs

open Filter Topology in
/-- **The double factor.** If the cubic `F(e₀,·)` has a double root `v₀` and `F_e(e₀,v₀) = 0` (the three
contact conditions, written out for the explicit coefficient functions), then `R(e₀) = 0` and `R'(e₀) = 0`. -/
theorem R_flat (D : MajData) {A1 B1 q1 v0 : ℝ} (he0 : 0 < D.e0) (hA : HasDerivAt D.A A1 D.e0)
    (hB : HasDerivAt D.B B1 D.e0) (hq : HasDerivAt D.q q1 D.e0)
    (hC0 : D.F D.e0 v0 = 0)
    (hCv : D.e0 ^ 4 * D.V D.e0 + 2 * D.e0 ^ 2 * D.W D.e0 * v0 + 3 * eta3R * v0 ^ 2 = 0)
    (hCe : 5 * D.e0 ^ 4 * D.U D.e0 + D.e0 ^ 5 * (8 * D.k0 * (2 * D.q D.e0 * q1)) +
      (4 * D.e0 ^ 3 * D.V D.e0 + D.gam * D.e0 ^ 4 * D.V D.e0 + D.e0 ^ 4 * (8 * (D.A D.e0 + D.e0 * A1))) * v0 +
      (2 * D.e0 * D.W D.e0 + D.gam * D.e0 ^ 2 * D.W D.e0 +
        D.e0 ^ 2 * (8 * (3 * D.e0 ^ 2 * D.B D.e0 + D.e0 ^ 3 * B1))) * v0 ^ 2 + eta3R * D.gam * v0 ^ 3 = 0) :
    D.R D.e0 = 0 ∧ HasDerivAt D.R 0 D.e0 := by
  have hL0 : D.L D.e0 = 1 := by unfold MajData.L; ring
  have hLd := D.L_hd D.e0
  have hUd := D.U_hd hq
  have hVd := D.V_hd hA
  have hWd := D.W_hd hB
  -- derivatives of the cubic coefficients
  have hd3 : HasDerivAt (fun e => eta3R * D.L e) (eta3R * D.gam) D.e0 := hLd.const_mul eta3R
  have hd2 : HasDerivAt (fun e => e ^ 2 * D.L e * D.W e)
      (2 * D.e0 * D.L D.e0 * D.W D.e0 + D.e0 ^ 2 * D.gam * D.W D.e0 +
        D.e0 ^ 2 * D.L D.e0 * (8 * (3 * D.e0 ^ 2 * D.B D.e0 + D.e0 ^ 3 * B1))) D.e0 := by
    have h := (((hasDerivAt_id D.e0).pow 2).mul hLd).mul hWd
    exact HasDerivAt.congr_deriv h (by simp; ring)
  have hd1 : HasDerivAt (fun e => e ^ 4 * D.L e * D.V e)
      (4 * D.e0 ^ 3 * D.L D.e0 * D.V D.e0 + D.e0 ^ 4 * D.gam * D.V D.e0 +
        D.e0 ^ 4 * D.L D.e0 * (8 * (D.A D.e0 + D.e0 * A1))) D.e0 := by
    have h := (((hasDerivAt_id D.e0).pow 4).mul hLd).mul hVd
    exact HasDerivAt.congr_deriv h (by simp; ring)
  have hd0 : HasDerivAt (fun e => e ^ 5 * D.U e)
      (5 * D.e0 ^ 4 * D.U D.e0 + D.e0 ^ 5 * (8 * D.k0 * (2 * D.q D.e0 * q1))) D.e0 := by
    have h := ((hasDerivAt_id D.e0).pow 5).mul hUd
    exact HasDerivAt.congr_deriv h (by simp)
  have hG := disc3_hasDerivAt hd3 hd2 hd1 hd0
  -- the contact conditions for the cubic
  have h0 : D.e0 ^ 5 * D.U D.e0 + D.e0 ^ 4 * D.L D.e0 * D.V D.e0 * v0 +
      D.e0 ^ 2 * D.L D.e0 * D.W D.e0 * v0 ^ 2 + eta3R * D.L D.e0 * v0 ^ 3 = 0 := hC0
  have h1 : D.e0 ^ 4 * D.L D.e0 * D.V D.e0 + 2 * (D.e0 ^ 2 * D.L D.e0 * D.W D.e0) * v0 +
      3 * (eta3R * D.L D.e0) * v0 ^ 2 = 0 := by rw [hL0]; linarith
  have h2 : (5 * D.e0 ^ 4 * D.U D.e0 + D.e0 ^ 5 * (8 * D.k0 * (2 * D.q D.e0 * q1))) +
      (4 * D.e0 ^ 3 * D.L D.e0 * D.V D.e0 + D.e0 ^ 4 * D.gam * D.V D.e0 +
        D.e0 ^ 4 * D.L D.e0 * (8 * (D.A D.e0 + D.e0 * A1))) * v0 +
      (2 * D.e0 * D.L D.e0 * D.W D.e0 + D.e0 ^ 2 * D.gam * D.W D.e0 +
        D.e0 ^ 2 * D.L D.e0 * (8 * (3 * D.e0 ^ 2 * D.B D.e0 + D.e0 ^ 3 * B1))) * v0 ^ 2 +
      eta3R * D.gam * v0 ^ 3 = 0 := by rw [hL0]; linarith
  have key := disc3_deriv_zero (eta3R * D.L D.e0) (D.e0 ^ 2 * D.L D.e0 * D.W D.e0)
    (D.e0 ^ 4 * D.L D.e0 * D.V D.e0) (D.e0 ^ 5 * D.U D.e0) (eta3R * D.gam)
    (2 * D.e0 * D.L D.e0 * D.W D.e0 + D.e0 ^ 2 * D.gam * D.W D.e0 +
        D.e0 ^ 2 * D.L D.e0 * (8 * (3 * D.e0 ^ 2 * D.B D.e0 + D.e0 ^ 3 * B1)))
    (4 * D.e0 ^ 3 * D.L D.e0 * D.V D.e0 + D.e0 ^ 4 * D.gam * D.V D.e0 +
        D.e0 ^ 4 * D.L D.e0 * (8 * (D.A D.e0 + D.e0 * A1)))
    (5 * D.e0 ^ 4 * D.U D.e0 + D.e0 ^ 5 * (8 * D.k0 * (2 * D.q D.e0 * q1))) v0 h0 h1 h2
  have hG0 : HasDerivAt (fun e => disc3 (eta3R * D.L e) (e ^ 2 * D.L e * D.W e) (e ^ 4 * D.L e * D.V e)
      (e ^ 5 * D.U e)) 0 D.e0 := HasDerivAt.congr_deriv hG key
  have hGv : disc3 (eta3R * D.L D.e0) (D.e0 ^ 2 * D.L D.e0 * D.W D.e0) (D.e0 ^ 4 * D.L D.e0 * D.V D.e0)
      (D.e0 ^ 5 * D.U D.e0) = 0 := disc3_double _ _ _ _ v0 h0 h1
  have hdisc : ∀ e : ℝ, disc3 (eta3R * D.L e) (e ^ 2 * D.L e * D.W e) (e ^ 4 * D.L e * D.V e)
      (e ^ 5 * D.U e) = -(e ^ 10 * D.L e ^ 2 * D.R e) := by
    intro e; unfold disc3 MajData.R; ring
  have hR0 : D.R D.e0 = 0 := by
    have := hdisc D.e0
    rw [hGv, hL0] at this
    have hpos : 0 < D.e0 ^ 10 := by positivity
    nlinarith
  refine ⟨hR0, ?_⟩
  -- R = -G/(e¹⁰ L²) near e₀
  have hden : HasDerivAt (fun e => e ^ 10 * D.L e ^ 2)
      (10 * D.e0 ^ 9 * D.L D.e0 ^ 2 + D.e0 ^ 10 * (2 * D.L D.e0 * D.gam)) D.e0 := by
    have h := ((hasDerivAt_id D.e0).pow 10).mul (hLd.pow 2)
    exact HasDerivAt.congr_deriv h (by simp)
  have hdenne : D.e0 ^ 10 * D.L D.e0 ^ 2 ≠ 0 := by rw [hL0]; positivity
  have hq' := (hG0.neg).div hden hdenne
  have hq'0 : HasDerivAt (fun e => (-disc3 (eta3R * D.L e) (e ^ 2 * D.L e * D.W e) (e ^ 4 * D.L e * D.V e)
      (e ^ 5 * D.U e)) / (e ^ 10 * D.L e ^ 2)) 0 D.e0 := by
    refine HasDerivAt.congr_deriv hq' ?_
    simp [hGv]
  have hev : D.R =ᶠ[nhds D.e0] fun e => (-disc3 (eta3R * D.L e) (e ^ 2 * D.L e * D.W e)
      (e ^ 4 * D.L e * D.V e) (e ^ 5 * D.U e)) / (e ^ 10 * D.L e ^ 2) := by
    have h1 : ∀ᶠ e in nhds D.e0, 0 < e := Ioi_mem_nhds he0
    have h2 : ∀ᶠ e in nhds D.e0, D.L e ≠ 0 :=
      (D.L_hd D.e0).continuousAt.eventually_ne (by rw [hL0]; norm_num)
    filter_upwards [h1, h2] with e he hLe
    rw [hdisc e]
    have : e ^ 10 * D.L e ^ 2 ≠ 0 := by positivity
    field_simp
  exact HasDerivAt.congr_of_eventuallyEq hq'0 hev

end FormalResearch.FourQubitEntropy.AH6
