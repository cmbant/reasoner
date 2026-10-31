import FormalResearch.FourQubitEntropy.AH6Final

/-!
# `lem:seven-joint-scalar-majorant` (AH-6): the equality set

`seven_qubit_entropy_joint.tex`, `lem:seven-joint-scalar-majorant`: for the explicit degree-five `H`,
`H(λ,μ) ≥ (f(λ)+f(μ))/2` on `[0,∞)²` with equality **exactly** at `(c,c),(a,a),(d,d),(b,c),(c,b)`, first-order
contact at each.  `AH6Final.joint_scalar_majorant` proves the inequality; this file proves the equality set,
reusing (importing) the AH6 pipeline without modifying it.

* `joint_majorant_eq_iff`, `joint_scalar_majorant_eq_iff` (for `polyH degFive (jointCoef x)`, `x` in the bracket of
  `x_*`, `u = (1-2x)/30`, `c = 4u`, `a = 3u+x`, `d = u+x`, `b = 8u`): for `λ, μ ≥ 0`,
  `H(λ,μ) = (f(λ)+f(μ))/2 ↔ (λ,μ) ∈ {(c,c),(a,a),(d,d),(b,c),(c,b)}`.
  `joint_scalar_majorant_full` bundles the inequality for every `cap` with this iff.
* `joint_majorant_contact`: at each equality point with `λ, μ > 0` both partial derivatives of the gap vanish.

Proof of `⇒` (the analytic proof's own structure): on the open quadrant `F(e,v) ≤ 8e⁵L·(gap)` and `F ≥ 0`
(`AH6Assembly`), so a zero gap forces `F(e,v) = 0`.  For `e ≠ e₀` the discriminant of `F(e,·)` is negative, so the
cubic has no positive root (`no_pos_root`): `v = 0`, i.e. `λ = μ`, and `F(e,0) = e⁵U(e) = 0` gives `q(e) = 0`, i.e.
`e ∈ {8c, 8a, 8d}`.  For `e = e₀` the cubic is nonnegative with the zero `v₀ = 256u²` (the contact pair), hence a
double root (`deriv_zero_of_min`), and with `d = e₀⁵U(e₀) > 0` it has no other nonnegative root
(`root_unique_of_double`): `λ+μ = 12u`, `|λ-μ| = 4u`.  On the boundary of the quadrant strictness comes from the
infinite slope of `f` at `0` (`pos_at_zero`, `H_boundary_strict`).  `⇐`: the diagonal nodes are Hermite
interpolation nodes (`H_nodes`, via `hermite_stieltjes`), and `H(b,c)` is the contact value fixed by the definitions of
`β₀, α₀` (`H_contact`, the value part of `contact_algebra`).

Nothing here is conditional: no `sorry`, no hypothesis beyond `InBracket x`.
-/

open Filter Topology
open FormalResearch.FourQubitEntropy.SevenQubitConseq.JointMajorant

namespace FormalResearch.FourQubitEntropy.AH6

/-- A cubic with positive leading coefficient, nonnegative constant term and negative discriminant has
no positive root. -/
theorem no_pos_root {a b c d v1 : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hdisc : disc3 a b c d < 0)
    (hv : 0 < v1) (hr : a * v1 ^ 3 + b * v1 ^ 2 + c * v1 + d = 0) : False := by
  have hdd : d = -(v1 * (c + b * v1 + a * v1 ^ 2)) := by linear_combination hr
  have hid : disc3 a b c d =
      ((b + a * v1) ^ 2 - 4 * a * (c + b * v1 + a * v1 ^ 2)) * (3 * a * v1 ^ 2 + 2 * b * v1 + c) ^ 2 := by
    unfold disc3; rw [hdd]; ring
  have h1 : (b + a * v1) ^ 2 - 4 * a * (c + b * v1 + a * v1 ^ 2) < 0 := by
    by_contra h
    push Not at h
    have := mul_nonneg h (sq_nonneg (3 * a * v1 ^ 2 + 2 * b * v1 + c))
    linarith
  have hC : 0 < c + b * v1 + a * v1 ^ 2 := by nlinarith [sq_nonneg (b + a * v1)]
  have : d < 0 := by rw [hdd]; nlinarith [mul_pos hv hC]
  linarith

/-- A cubic with `a > 0`, `d > 0` and a positive double root `v0` has no other nonnegative root. -/
theorem root_unique_of_double {a b c d v0 v : ℝ} (ha : 0 < a) (hd : 0 < d)
    (h0 : a * v0 ^ 3 + b * v0 ^ 2 + c * v0 + d = 0) (h1 : 3 * a * v0 ^ 2 + 2 * b * v0 + c = 0)
    (hv : 0 ≤ v) (hr : a * v ^ 3 + b * v ^ 2 + c * v + d = 0) : v = v0 := by
  have hc : c = -2 * b * v0 - 3 * a * v0 ^ 2 := by linarith
  have hdd : d = v0 ^ 2 * (b + 2 * a * v0) := by rw [hc] at h0; linarith
  have hs : 0 < b + 2 * a * v0 := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg v0, mul_nonneg (sq_nonneg v0) (neg_nonneg.2 h)]
  have hfac : a * v ^ 3 + b * v ^ 2 + c * v + d = (v - v0) ^ 2 * (a * v + (b + 2 * a * v0)) := by
    rw [hc, hdd]; ring
  rw [hfac] at hr
  have hpos : 0 < a * v + (b + 2 * a * v0) := by positivity
  rcases mul_eq_zero.mp hr with h | h
  · have := pow_eq_zero_iff (two_ne_zero) |>.mp h
    linarith
  · linarith

/-- Fermat: a cubic nonnegative on `[0,∞)` with a positive root `v0` has a double root there. -/
theorem deriv_zero_of_min {a b c d v0 : ℝ} (hv0 : 0 < v0)
    (hge : ∀ v : ℝ, 0 ≤ v → 0 ≤ a * v ^ 3 + b * v ^ 2 + c * v + d)
    (h0 : a * v0 ^ 3 + b * v0 ^ 2 + c * v0 + d = 0) : 3 * a * v0 ^ 2 + 2 * b * v0 + c = 0 := by
  have hmin : IsLocalMin (fun v : ℝ => a * v ^ 3 + b * v ^ 2 + c * v + d) v0 := by
    filter_upwards [Ioi_mem_nhds hv0] with v hv
    simp only [h0]
    exact hge v (le_of_lt hv)
  have hd : HasDerivAt (fun v : ℝ => a * v ^ 3 + b * v ^ 2 + c * v + d)
      (a * (3 * v0 ^ 2) + b * (2 * v0) + c) v0 := by
    have := (((hasDerivAt_pow 3 v0).const_mul a).add ((hasDerivAt_pow 2 v0).const_mul b)).add
      ((hasDerivAt_id v0).const_mul c) |>.add_const d
    simpa using this
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- If `Hm' (m) ≥ f(m)/2` for all `m > 0` (with `f = negMulLog`) and `Hm` is differentiable at `0`, then
`Hm 0 > 0`: the infinite slope of `f` at `0` forbids a vanishing minimum there. -/
theorem pos_at_zero {Hm : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt Hm d 0)
    (hge : ∀ m : ℝ, 0 < m → Real.negMulLog m / 2 ≤ Hm m) : 0 < Hm 0 := by
  by_contra h
  push Not at h
  have h1 := hd.tendsto_slope_zero_right
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (Hm (0 + t) - Hm 0) < d + 1 :=
    h1.eventually (gt_mem_nhds (by linarith))
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.log t < -2 * (d + 1) - 1 :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  have h4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht2, ht3, ht4⟩ := (h2.and (h3.and h4)).exists
  simp only [zero_add, smul_eq_mul] at ht2
  have hge' := hge t ht4
  have hslope : Hm t - Hm 0 < t * (d + 1) := (inv_mul_lt_iff₀ ht4).mp ht2
  unfold Real.negMulLog at hge'
  nlinarith

/-! ### The majorant `H` of the real computation -/

section Concrete

variable {x : ℝ}

theorem H_differentiable (x l : ℝ) : Differentiable ℝ (fun m => (majD (parR x)).H l m) := by
  have hP : Differentiable ℝ (majD (parR x)).P := fun e => (hasDerivAt_evalL _ e).differentiableAt
  have hA : Differentiable ℝ (majD (parR x)).A := fun e => (hasDerivAt_evalL _ e).differentiableAt
  have hB : Differentiable ℝ (majD (parR x)).B := fun e => (hasDerivAt_evalL _ e).differentiableAt
  unfold MajData.H
  fun_prop

theorem H_symm (x l m : ℝ) : (majD (parR x)).H l m = (majD (parR x)).H m l := by
  unfold MajData.H
  have e1 : 4 * (l + m) = 4 * (m + l) := by ring
  have e2 : (l - m) ^ 2 = (m - l) ^ 2 := by ring
  rw [e1, e2]

/-- On the boundary of the quadrant the majorant is **strict**: `H(l,0) > f(l)/2`. -/
theorem H_boundary_strict (hb : InBracket x) {l : ℝ} (hl : 0 ≤ l) :
    Real.negMulLog l / 2 < (majD (parR x)).H l 0 := by
  have hdiff := (H_differentiable x l 0).hasDerivAt
  have hd : HasDerivAt (fun m => (majD (parR x)).H l m - Real.negMulLog l / 2) _ 0 := hdiff.sub_const _
  have := pos_at_zero hd (fun m hm => by
    have := joint_majorant hb hl hm.le
    linarith)
  linarith

theorem H_boundary_strict' (hb : InBracket x) {m : ℝ} (hm : 0 ≤ m) :
    Real.negMulLog m / 2 < (majD (parR x)).H 0 m := by
  rw [H_symm]; exact H_boundary_strict hb hm


/-- **Equality at the contact pair `(b,c)`**: `H(8u, 4u) = (f(8u) + f(4u))/2` (value part of the
contact conditions; the coefficients `β₀, α₀` are defined to make this hold). -/
theorem H_contact (hb : InBracket x) :
    (majD (parR x)).H (8 * uOf x) (4 * uOf x) =
      (Real.negMulLog (8 * uOf x) + Real.negMulLog (4 * uOf x)) / 2 := by
  have F := cert_sound (parR x) (parR_enc hb)
  have hu := uOf_pos hb
  set p := parR x with hp
  set s := rA p with hs
  set c1 := rC1 p with hc1
  set c2 := rC2 p with hc2
  have hsu : s.u = uOf x := rfl
  have he0 : c1.e0 = 48 * uOf x := by
    show ic 48 * s.u = _
    simp only [ic_real, Int.cast_ofNat]; rw [hsu]
  have hv0 : c1.v0 = c1.e0 * c1.e0 / 9 := by
    show (c1.e0 * c1.e0) * rat 1 9 = _
    simp only [rat_real]; push_cast; ring
  have hhh : c1.hh = (-(8 * uOf x * (p.lc + p.l2)) + -(4 * uOf x * p.lc)) / 2 := by
    show (-(ic 8 * s.u * (p.lc + p.l2)) + -(s.c * p.lc)) * rat 1 2 = _
    have : s.c = ic 4 * s.u := rfl
    rw [this, hsu]; simp only [ic_real, rat_real]; push_cast; ring
  have hb0 : c2.b0 = (c1.v0 * c1.hv + -c1.hh + c1.Pe0) / (c1.v0 * c1.v0) + -(c1.b1 * c1.e0) := by
    show (c1.v0 * c1.hv + -c1.hh + c1.Pe0) * (c1.v0 * c1.v0)⁻¹ + -(c1.b1 * c1.e0) = _
    rw [div_eq_mul_inv]
  have ha0 : c2.a0 = c1.hv + -(2 * (c1.v0 * (c2.b0 + c1.b1 * c1.e0))) + -(c2.a1 * c1.e0) +
      -(c1.a2 * (c1.e0 * c1.e0)) + -(c1.a3 * (c1.e0 * (c1.e0 * c1.e0))) := by
    show c1.hv + -(ic 2 * (c1.v0 * (c2.b0 + c1.b1 * c1.e0))) + -(c2.a1 * c1.e0) +
      -(c1.a2 * (c1.e0 * c1.e0)) + -(c1.a3 * (c1.e0 * (c1.e0 * c1.e0))) = _
    simp only [ic_real]; push_cast; ring
  have hDA : (majD p).A c1.e0 = c2.a0 + c2.a1 * c1.e0 + c1.a2 * c1.e0 ^ 2 + c1.a3 * c1.e0 ^ 3 := by
    simp only [majD, evalL, ic_real]; push_cast; ring
  have hDB : (majD p).B c1.e0 = c2.b0 + c1.b1 * c1.e0 := by
    simp only [majD, evalL, ic_real]; push_cast; ring
  have hDP : (majD p).P c1.e0 = c1.Pe0 := rfl
  have hv0pos : c1.v0 ≠ 0 := by rw [hv0, he0]; positivity
  have e1 : 4 * (8 * uOf x + 4 * uOf x) = c1.e0 := by rw [he0]; ring
  have e2 : 16 * (8 * uOf x - 4 * uOf x) ^ 2 = c1.v0 := by rw [hv0, he0]; ring
  have hB0 : c1.v0 * c1.v0 * (c2.b0 + c1.b1 * c1.e0) = c1.v0 * c1.hv - c1.hh + c1.Pe0 := by
    rw [hb0]; field_simp; ring
  have hH : (majD p).H (8 * uOf x) (4 * uOf x) = c1.hh := by
    unfold MajData.H
    rw [e1, e2, hDA, hDB, hDP]
    have : c2.a0 + c2.a1 * c1.e0 + c1.a2 * c1.e0 ^ 2 + c1.a3 * c1.e0 ^ 3 =
        c1.hv - 2 * c1.v0 * (c2.b0 + c1.b1 * c1.e0) := by rw [ha0]; ring
    rw [this]
    linear_combination (-1 : ℝ) * hB0
  have hlog : Real.log (8 * uOf x) = Real.log (4 * uOf x) + Real.log 2 := by
    rw [show 8 * uOf x = (4 * uOf x) * 2 by ring, Real.log_mul (by positivity) (by norm_num)]
  have hlc : p.lc = Real.log (4 * uOf x) := by
    show Real.log (ic 4 * uOf x) = _
    simp only [ic_real, Int.cast_ofNat]
  have hl2 : p.l2 = Real.log 2 := rfl
  rw [hH, hhh, hlc, hl2]
  unfold Real.negMulLog
  rw [hlog]; ring


/-- The hypotheses of `AH6Assembly` for the real computation. -/
structure MajFacts (D : MajData) : Prop where
  heta : 0 < eta3R
  hk0 : 0 < D.k0
  hL : ∀ e : ℝ, 0 ≤ e → 0 < D.L e
  hK : ∀ e : ℝ, 0 < e → D.k0 * D.q e ^ 2 ≤ (D.P e - Real.negMulLog (e / 8)) * D.L e
  hR : ∀ e, D.R e = (e - D.e0) ^ 2 * D.Pi e
  hPi : ∀ e : ℝ, 0 ≤ e → 0 < D.Pi e
  hq : Continuous D.q
  hA : Continuous D.A
  hB : Continuous D.B

theorem majFacts (hb : InBracket x) : MajFacts (majD (parR x)) := by
  have F := cert_sound (parR x) (parR_enc hb)
  have hη3 := eta3_eq x
  refine ⟨by rw [← hη3]; exact F.eta3_pos, F.k0_pos, ?_, kmin_model hb, R_factor hb,
    fun e he => F.Pi_pos e he, continuous_evalL _, continuous_evalL _, continuous_evalL _⟩
  intro e he
  have h1 := F.gam_pos
  have h2 := F.gam_e0
  show 0 < 1 + (rC2 (parR x)).gam * (e - (rC1 (parR x)).e0)
  nlinarith

theorem majD_e0 (x : ℝ) : (majD (parR x)).e0 = 48 * uOf x := by
  show ic 48 * uOf x = _
  simp only [ic_real, Int.cast_ofNat]

theorem majD_q (x e : ℝ) : (majD (parR x)).q e =
    (e - 8 * (4 * uOf x)) * (e - 8 * (3 * uOf x + x)) * (e - 8 * (uOf x + x)) := by
  show evalL (rB (parR x)).q e = _
  rw [rB, evalL_stageB_q]
  show (e - ic 8 * (ic 4 * uOf x)) * (e - ic 8 * (ic 3 * uOf x + x)) * (e - ic 8 * (uOf x + x)) = _
  simp only [ic_real, Int.cast_ofNat]

/-- **Equality at the diagonal nodes**: `H(t,t) = f(t)` for `t ∈ {c, a, d}`. -/
theorem H_nodes (hb : InBracket x) :
    (majD (parR x)).H (4 * uOf x) (4 * uOf x) = Real.negMulLog (4 * uOf x) ∧
    (majD (parR x)).H (3 * uOf x + x) (3 * uOf x + x) = Real.negMulLog (3 * uOf x + x) ∧
    (majD (parR x)).H (uOf x + x) (uOf x + x) = Real.negMulLog (uOf x + x) := by
  have F := cert_sound (parR x) (parR_enc hb)
  obtain ⟨hG1, hG2, hG3, hW1, hW2, hW3⟩ := G_eq hb
  set p := parR x with hp
  set s := rA p with hs
  have hn1 : 0 < s.n1 := mul_pos (by simp only [ic_real]; norm_num) F.c_pos
  have hn2 : 0 < s.n2 := mul_pos (by simp only [ic_real]; norm_num) F.a_pos
  have hn3 : 0 < s.n3 := mul_pos (by simp only [ic_real]; norm_num) F.d_pos
  have h21 : (s.n2 - s.n1) * s.i21 = 1 := by
    have hi21 : s.i21 = (s.n2 + -s.n1)⁻¹ := rfl
    rw [hi21, ← sub_eq_add_neg]; exact mul_inv_cancel₀ (by rw [sub_eq_add_neg]; exact F.n21)
  have h31 : (s.n3 - s.n1) * s.i31 = 1 := by
    have hi31 : s.i31 = (s.n3 + -s.n1)⁻¹ := rfl
    rw [hi31, ← sub_eq_add_neg]; exact mul_inv_cancel₀ (by rw [sub_eq_add_neg]; exact F.n31)
  have h32 : (s.n3 - s.n2) * s.i32 = 1 := by
    have hi32 : s.i32 = (s.n3 + -s.n2)⁻¹ := rfl
    rw [hi32, ← sub_eq_add_neg]; exact mul_inv_cancel₀ (by rw [sub_eq_add_neg]; exact F.n32)
  have hPfun : ∀ e, evalL (rB p).P e = Pfun s.n1 s.n2 s.n3 s.i21 s.i31 s.i32 e := by
    intro e
    rw [rB, evalL_stageB_P, Pfun, hG1, hG2, hG3, hW1, hW2, hW3]
  have hnode : ∀ e : ℝ, 0 < e → (e - s.n1) * (e - s.n2) * (e - s.n3) = 0 →
      (majD p).P e = Real.negMulLog (e / 8) := by
    intro e he hq
    show evalL (rB p).P e = _
    rw [hPfun, Pfun, hermite_stieltjes hn1 hn2 hn3 h21 h31 h32 he, hq]
    simp
  have hdiag : ∀ t e : ℝ, e = 4 * (t + t) → (majD p).H t t = (majD p).P e := by
    intro t e he; subst he; simp [MajData.H]
  have hu := uOf_pos hb
  have hxpos : 0 < x := by linarith [hb.bounds.1]
  have hn1v : s.n1 = 8 * (4 * uOf x) := by
    show ic 8 * (ic 4 * uOf x) = _
    simp only [ic_real, Int.cast_ofNat]
  have hn2v : s.n2 = 8 * (3 * uOf x + x) := by
    show ic 8 * (ic 3 * uOf x + x) = _
    simp only [ic_real, Int.cast_ofNat]
  have hn3v : s.n3 = 8 * (uOf x + x) := by
    show ic 8 * (uOf x + x) = _
    simp only [ic_real, Int.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiag _ (8 * (4 * uOf x)) (by ring), hnode _ (by positivity)
      (by rw [hn1v]; ring)]
    congr 1; ring
  · rw [hdiag _ (8 * (3 * uOf x + x)) (by ring), hnode _ (by positivity)
      (by rw [hn2v]; ring)]
    congr 1; ring
  · rw [hdiag _ (8 * (uOf x + x)) (by ring), hnode _ (by positivity)
      (by rw [hn3v]; ring)]
    congr 1; ring


/-- The cubic `F(e, ·)` as `a v³ + b v² + c v + d`. -/
theorem F_eq_cubic (D : MajData) (e v : ℝ) :
    D.F e v = eta3R * D.L e * v ^ 3 + e ^ 2 * D.L e * D.W e * v ^ 2 + e ^ 4 * D.L e * D.V e * v +
      e ^ 5 * D.U e := by
  unfold MajData.F; ring

/-- At `e = e₀` the cubic `F(e₀, ·)` vanishes on `[0,∞)` only at `v₀ = 256u²`. -/
theorem F_zero_at_e0 (hb : InBracket x) {v : ℝ} (hv : 0 ≤ v)
    (h : (majD (parR x)).F (majD (parR x)).e0 v = 0) : v = 256 * uOf x ^ 2 := by
  have M := majFacts hb
  set D := majD (parR x) with hD
  have hu := uOf_pos hb
  have he0 : D.e0 = 48 * uOf x := majD_e0 x
  have he0pos : 0 < D.e0 := by rw [he0]; positivity
  -- the contact pair `(8u, 4u)` gives a zero of the cubic at `v₀ = 256 u²`
  have hc := H_contact hb
  have hF0 : D.F D.e0 (256 * uOf x ^ 2) = 0 := by
    have hnn := F_nonneg D M.heta M.hk0 M.hL M.hR M.hPi M.hq M.hA M.hB (e := 4 * (8 * uOf x + 4 * uOf x))
      (by positivity) (v := 16 * (8 * uOf x - 4 * uOf x) ^ 2) (by positivity)
    have hg := gap_lb D M.hL M.hK (l := 8 * uOf x) (m := 4 * uOf x) (by positivity) (by positivity)
    rw [hc, sub_self, mul_zero] at hg
    have e1 : 4 * (8 * uOf x + 4 * uOf x) = D.e0 := by rw [he0]; ring
    have e2 : 16 * (8 * uOf x - 4 * uOf x) ^ 2 = 256 * uOf x ^ 2 := by ring
    rw [e1, e2] at hnn hg
    exact le_antisymm hg hnn
  have hgep : ∀ w : ℝ, 0 ≤ w → 0 ≤ eta3R * D.L D.e0 * w ^ 3 + D.e0 ^ 2 * D.L D.e0 * D.W D.e0 * w ^ 2 +
      D.e0 ^ 4 * D.L D.e0 * D.V D.e0 * w + D.e0 ^ 5 * D.U D.e0 := by
    intro w hw
    rw [← F_eq_cubic]
    exact F_nonneg D M.heta M.hk0 M.hL M.hR M.hPi M.hq M.hA M.hB he0pos hw
  have hv0pos : (0 : ℝ) < 256 * uOf x ^ 2 := by positivity
  have h0 := hF0
  rw [F_eq_cubic] at h0 h
  have hder := deriv_zero_of_min hv0pos hgep h0
  have hapos : 0 < eta3R * D.L D.e0 := mul_pos M.heta (M.hL _ he0pos.le)
  have hdpos : 0 < D.e0 ^ 5 * D.U D.e0 := by
    have hq0 : D.q D.e0 ≠ 0 := (cert_sound (parR x) (parR_enc hb)).q0_ne
    have : 0 < D.U D.e0 := by
      unfold MajData.U; have := M.hk0; positivity
    positivity
  exact root_unique_of_double hapos hdpos h0 hder hv h


/-- **Equality set of the joint scalar majorant** (`lem:seven-joint-scalar-majorant`), for `H = ` the
real computation at `x` in the bracket of `x_*` (`u = (1-2x)/30`, `c = 4u`, `a = 3u+x`, `d = u+x`, `b = 8u`):
for `λ, μ ≥ 0`, `H(λ,μ) = (f(λ)+f(μ))/2` iff `(λ,μ) ∈ {(c,c),(a,a),(d,d),(b,c),(c,b)}`. -/
theorem joint_majorant_eq_iff (hb : InBracket x) {l m : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) :
    (majD (parR x)).H l m = (Real.negMulLog l + Real.negMulLog m) / 2 ↔
      ((l = 4 * uOf x ∧ m = 4 * uOf x) ∨ (l = 3 * uOf x + x ∧ m = 3 * uOf x + x) ∨
        (l = uOf x + x ∧ m = uOf x + x) ∨ (l = 8 * uOf x ∧ m = 4 * uOf x) ∨
        (l = 4 * uOf x ∧ m = 8 * uOf x)) := by
  have hu := uOf_pos hb
  have hxpos : 0 < x := by linarith [hb.bounds.1]
  constructor
  swap
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [(H_nodes hb).1]; ring
    · rw [(H_nodes hb).2.1]; ring
    · rw [(H_nodes hb).2.2]; ring
    · exact H_contact hb
    · rw [H_symm, H_contact hb]; ring
  intro hG
  have M := majFacts hb
  set D := majD (parR x) with hD
  have he0 : D.e0 = 48 * uOf x := majD_e0 x
  -- boundary points are strict
  have hl0 : 0 < l := by
    rcases hl.eq_or_lt with h | h
    · exfalso
      have := H_boundary_strict' hb hm
      rw [← h] at hG
      simp [Real.negMulLog_zero] at hG
      rw [hD] at hG
      linarith
    · exact h
  have hm0 : 0 < m := by
    rcases hm.eq_or_lt with h | h
    · exfalso
      have := H_boundary_strict hb hl
      rw [← h] at hG
      simp [Real.negMulLog_zero] at hG
      rw [hD] at hG
      linarith
    · exact h
  have he : 0 < 4 * (l + m) := by positivity
  have hgap := gap_lb D M.hL M.hK hl0 hm0
  have hnn := F_nonneg D M.heta M.hk0 M.hL M.hR M.hPi M.hq M.hA M.hB he
    (v := 16 * (l - m) ^ 2) (by positivity)
  rw [hG, sub_self, mul_zero] at hgap
  have hFz : D.F (4 * (l + m)) (16 * (l - m) ^ 2) = 0 := le_antisymm hgap hnn
  by_cases hne : 4 * (l + m) = D.e0
  · -- the contact pair
    rw [hne] at hFz
    have hv := F_zero_at_e0 hb (by positivity) hFz
    have h1 : l + m = 12 * uOf x := by rw [he0] at hne; linarith
    have h2 : (l - m) ^ 2 = (4 * uOf x) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · right; right; right; left; constructor <;> linarith
    · right; right; right; right; constructor <;> linarith
  · -- e ≠ e₀: the cubic has negative discriminant
    have hLe := M.hL _ he.le
    have hdisc : disc3 (eta3R * D.L (4 * (l + m))) ((4 * (l + m)) ^ 2 * D.L (4 * (l + m)) * D.W (4 * (l + m)))
        ((4 * (l + m)) ^ 4 * D.L (4 * (l + m)) * D.V (4 * (l + m)))
        ((4 * (l + m)) ^ 5 * D.U (4 * (l + m))) < 0 := by
      have hd : disc3 (eta3R * D.L (4 * (l + m))) ((4 * (l + m)) ^ 2 * D.L (4 * (l + m)) * D.W (4 * (l + m)))
          ((4 * (l + m)) ^ 4 * D.L (4 * (l + m)) * D.V (4 * (l + m)))
          ((4 * (l + m)) ^ 5 * D.U (4 * (l + m))) =
          -((4 * (l + m)) ^ 10 * D.L (4 * (l + m)) ^ 2 * D.R (4 * (l + m))) := by
        unfold disc3 MajData.R; ring
      have hRpos : 0 < D.R (4 * (l + m)) := by
        rw [M.hR]
        have : 0 < (4 * (l + m) - D.e0) ^ 2 := by
          have : 4 * (l + m) - D.e0 ≠ 0 := sub_ne_zero.2 hne
          positivity
        exact mul_pos this (M.hPi _ he.le)
      rw [hd]
      have : 0 < (4 * (l + m)) ^ 10 * D.L (4 * (l + m)) ^ 2 * D.R (4 * (l + m)) := by positivity
      linarith
    have hUnn : 0 ≤ (4 * (l + m)) ^ 5 * D.U (4 * (l + m)) := by
      unfold MajData.U; have := M.hk0; positivity
    have hv : 16 * (l - m) ^ 2 = 0 := by
      by_contra hv
      have hvpos : 0 < 16 * (l - m) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hv)
      rw [F_eq_cubic] at hFz
      exact no_pos_root (mul_pos M.heta hLe) hUnn hdisc hvpos hFz
    have hlm : l = m := by
      have : (l - m) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (two_ne_zero) |>.mp this
      linarith
    subst hlm
    rw [hv, F_eq_cubic] at hFz
    have hU : D.U (4 * (l + l)) = 0 := by
      have : (4 * (l + l)) ^ 5 * D.U (4 * (l + l)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exfalso; have : 0 < (4 * (l + l)) ^ 5 := by positivity
        linarith
      · exact h
    have hq : D.q (4 * (l + l)) = 0 := by
      unfold MajData.U at hU
      have := M.hk0
      have h8 : 8 * D.k0 ≠ 0 := by positivity
      rcases mul_eq_zero.mp hU with h | h
      · exact absurd h h8
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    rw [majD_q] at hq
    rcases mul_eq_zero.mp hq with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; constructor <;> linarith
      · right; left; constructor <;> linarith
    · right; right; left; constructor <;> linarith


/-- `u = (1 - 2x)/30`. -/
theorem uOf_eq (x : ℝ) : uOf x = (1 - 2 * x) / 30 := by
  unfold uOf; simp only [ic_real, Int.cast_one, Int.cast_ofNat]; ring

/-- **First-order contact** at every equality point (they are interior minima of
`H - (f(λ)+f(μ))/2 ≥ 0`): both partial derivatives vanish. -/
theorem joint_majorant_contact (hb : InBracket x) {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hG : (majD (parR x)).H l m = (Real.negMulLog l + Real.negMulLog m) / 2) :
    HasDerivAt (fun t => (majD (parR x)).H t m - (Real.negMulLog t + Real.negMulLog m) / 2) 0 l ∧
    HasDerivAt (fun t => (majD (parR x)).H l t - (Real.negMulLog l + Real.negMulLog t) / 2) 0 m := by
  have key : ∀ {l m : ℝ}, 0 < l → 0 < m →
      (majD (parR x)).H l m = (Real.negMulLog l + Real.negMulLog m) / 2 →
      HasDerivAt (fun t => (majD (parR x)).H t m - (Real.negMulLog t + Real.negMulLog m) / 2) 0 l := by
    intro l m hl hm hG
    set φ : ℝ → ℝ := fun t => (majD (parR x)).H t m - (Real.negMulLog t + Real.negMulLog m) / 2 with hφ
    have hHd : Differentiable ℝ (fun t => (majD (parR x)).H t m) := by
      have : (fun t => (majD (parR x)).H t m) = fun t => (majD (parR x)).H m t :=
        funext fun t => H_symm x t m
      rw [this]; exact H_differentiable x m
    have hfd : HasDerivAt Real.negMulLog (-Real.log l - 1) l := Real.hasDerivAt_negMulLog hl.ne'
    have hφd : HasDerivAt φ (deriv (fun t => (majD (parR x)).H t m) l - (-Real.log l - 1) / 2) l := by
      have h1 := (hHd l).hasDerivAt
      have h2 := (hfd.add_const (Real.negMulLog m)).div_const 2
      exact h1.sub h2
    have hmin : IsLocalMin φ l := by
      filter_upwards [Ioi_mem_nhds hl] with t ht
      have h1 := joint_majorant hb (le_of_lt ht) hm.le
      have h0 : φ l = 0 := by simp only [hφ]; rw [hG]; ring
      rw [h0]; simp only [hφ]; linarith
    have := hmin.hasDerivAt_eq_zero hφd
    rw [this] at hφd
    exact hφd
  refine ⟨key hl hm hG, ?_⟩
  have hG' : (majD (parR x)).H m l = (Real.negMulLog m + Real.negMulLog l) / 2 := by
    rw [H_symm, hG]; ring
  have := key hm hl hG'
  have e : (fun t => (majD (parR x)).H l t - (Real.negMulLog l + Real.negMulLog t) / 2) =
      fun t => (majD (parR x)).H t l - (Real.negMulLog t + Real.negMulLog l) / 2 := by
    funext t; rw [H_symm]; ring
  rw [e]; exact this

end Concrete

/-- **`lem:seven-joint-scalar-majorant`, equality set** (`seven_qubit_entropy_joint.tex`): for the explicit
degree-five `H = polyH degFive (jointCoef x)` with `x` in the bracket of `x_*`, and `u = (1-2x)/30`,
`c = 4u`, `a = 3u + x`, `d = u + x`, `b = 8u`: for all `λ, μ ≥ 0`,
`H(λ,μ) = (f(λ)+f(μ))/2` **iff** `(λ,μ) ∈ {(c,c), (a,a), (d,d), (b,c), (c,b)}`. -/
theorem joint_scalar_majorant_eq_iff {x : ℝ} (hb : InBracket x) {l m : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) :
    polyH degFive (jointCoef x) l m = (Real.negMulLog l + Real.negMulLog m) / 2 ↔
      ((l = 4 * ((1 - 2 * x) / 30) ∧ m = 4 * ((1 - 2 * x) / 30)) ∨
        (l = 3 * ((1 - 2 * x) / 30) + x ∧ m = 3 * ((1 - 2 * x) / 30) + x) ∨
        (l = (1 - 2 * x) / 30 + x ∧ m = (1 - 2 * x) / 30 + x) ∨
        (l = 8 * ((1 - 2 * x) / 30) ∧ m = 4 * ((1 - 2 * x) / 30)) ∨
        (l = 4 * ((1 - 2 * x) / 30) ∧ m = 8 * ((1 - 2 * x) / 30))) := by
  rw [polyH_jointCoef, joint_majorant_eq_iff hb hl hm, uOf_eq]

/-- The full statement of `lem:seven-joint-scalar-majorant`: the majorant inequality on all of `[0,∞)²`
(every `cap`) together with its exact equality set. -/
theorem joint_scalar_majorant_full {x : ℝ} (hb : InBracket x) :
    (∀ cap : ℝ, SevenQubitConseq.JointMajorant.ScalarMajorant (SevenQubitConseq.JointMajorant.polyH
      SevenQubitConseq.JointMajorant.degFive (jointCoef x)) cap) ∧
    ∀ l m : ℝ, 0 ≤ l → 0 ≤ m →
      (polyH degFive (jointCoef x) l m = (Real.negMulLog l + Real.negMulLog m) / 2 ↔
      ((l = 4 * ((1 - 2 * x) / 30) ∧ m = 4 * ((1 - 2 * x) / 30)) ∨
        (l = 3 * ((1 - 2 * x) / 30) + x ∧ m = 3 * ((1 - 2 * x) / 30) + x) ∨
        (l = (1 - 2 * x) / 30 + x ∧ m = (1 - 2 * x) / 30 + x) ∨
        (l = 8 * ((1 - 2 * x) / 30) ∧ m = 4 * ((1 - 2 * x) / 30)) ∨
        (l = 4 * ((1 - 2 * x) / 30) ∧ m = 8 * ((1 - 2 * x) / 30)))) :=
  ⟨fun cap => joint_scalar_majorant hb cap, fun _ _ hl hm => joint_scalar_majorant_eq_iff hb hl hm⟩


/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.AH6.no_pos_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_pos_root

/-- info: 'FormalResearch.FourQubitEntropy.AH6.root_unique_of_double' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms root_unique_of_double

/-- info: 'FormalResearch.FourQubitEntropy.AH6.deriv_zero_of_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deriv_zero_of_min

/-- info: 'FormalResearch.FourQubitEntropy.AH6.pos_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pos_at_zero

/-- info: 'FormalResearch.FourQubitEntropy.AH6.H_boundary_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms H_boundary_strict

/-- info: 'FormalResearch.FourQubitEntropy.AH6.H_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms H_nodes

/-- info: 'FormalResearch.FourQubitEntropy.AH6.H_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms H_contact

/-- info: 'FormalResearch.FourQubitEntropy.AH6.joint_majorant_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_majorant_eq_iff

/-- info: 'FormalResearch.FourQubitEntropy.AH6.joint_majorant_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_majorant_contact

/-- info: 'FormalResearch.FourQubitEntropy.AH6.joint_scalar_majorant_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_scalar_majorant_eq_iff

/-- info: 'FormalResearch.FourQubitEntropy.AH6.joint_scalar_majorant_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_scalar_majorant_full

end FormalResearch.FourQubitEntropy.AH6
