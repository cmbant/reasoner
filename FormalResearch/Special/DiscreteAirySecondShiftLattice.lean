module

public import FormalResearch.Special.DiscreteAirySecondShift
public import FormalResearch.Special.DiscreteAiryLimitDefect

/-!
# Second-order Airy parametrix, part 12: the shifted form on the lattice (Q4)

With `p := a2p = ζ q₁²/(2g)` (so that `g · y(X + δ⁴ q₁/g) = a2Psi + O(δ⁹ w)`, see `DiscreteAirySecondShift`) the paper-form row
defect (Q3, `airy2_defect_lattice`) transfers to the **shifted** parametrix
`ψ̂_j = g(q_j) · y(a2Xh)`, `a2Xh = ζ(q_j)/δ² + δ⁴ q₁(q_j)/g(q_j)`:

`airy2_shifted_defect`: for `q_k ∈ J` and `δ ≤ δ₀`,
`|jac a c ψ̂ (k)| ≤ K δ⁹ w(a2Xh(q_k))`, `a_j = (A + δ⁶ A₂)(q_j - δ³/2)`, `c_j = 2 A Ch(ζ ζ'²) + δ⁶ c₂` at `q_j`
(`w = airyWt` for `y = Ai`, `w = airyBiWt` for `Bi`: `airy2_shifted_defect_Ai`, `airy2_shifted_defect_Bi`).

This is exactly the shape of the hypotheses `hdA`, `hdB` of `dao_pair_rate` / `dai_full_rate` at `n = 1` (`δ^(6+3·1) = δ⁹`) for the
lattice sequences `X_j = a2Xh(q_j)`, `g_j = g(q_j)`.  `p` is *determined* (`p = g ζ B²/2`, `B = q₁/g`); it does not enter the
`q₁`-residual equation.  **Claim class: proved**; constants existential.
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry

namespace FormalResearch.Special

open SturmAiry

/-- The `h²` amplitude correction `p = g ζ B²/2 = ζ q₁²/(2g)` fixed by the shifted form. -/
noncomputable def a2p (ζ g q1 : ℝ → ℝ) (q : ℝ) : ℝ := ζ q * q1 q ^ 2 / (2 * g q)
/-- The shifted Airy argument `X + δ⁴ B`, `X = ζ/δ²`, `B = q₁/g`. -/
noncomputable def a2Xh (ζ g q1 : ℝ → ℝ) (δ q : ℝ) : ℝ := ζ q / δ ^ 2 + δ ^ 4 * (q1 q / g q)

/-- `g ≠ 0` from the amplitude relation. -/
lemma a2_g_ne {U : Set ℝ} {ζ A g : ℝ → ℝ}
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∀ q ∈ U, g q ≠ 0 := fun q hq h0 => by
  have := hrel q hq
  rw [h0] at this; simp at this

/-- Regularity data for `p = a2p`. -/
lemma Airy2Data.of_smooth {U : Set ℝ} {ζ A A2 g q1 : ℝ → ℝ} (hU : IsOpen U) (hζ : ContDiffOn ℝ 4 ζ U)
    (hA : ContDiffOn ℝ 3 A U) (hA2 : ContDiffOn ℝ 1 A2 U) (hg : ContDiffOn ℝ 3 g U)
    (hq1 : ContDiffOn ℝ 3 q1 U) (hg0 : ∀ q ∈ U, g q ≠ 0) :
    Airy2Data U ζ A A2 g (a2p ζ g q1) q1 := by
  refine ⟨hU, hζ, hA, hA2, hg, ?_, hq1⟩
  have h1 : ContDiffOn ℝ 1 ζ U := hζ.of_le (by norm_num)
  have h2 : ContDiffOn ℝ 1 q1 U := hq1.of_le (by norm_num)
  have h3 : ContDiffOn ℝ 1 g U := hg.of_le (by norm_num)
  exact (h1.mul (h2.pow 2)).div (contDiffOn_const.mul h3) (fun q hq => mul_ne_zero two_ne_zero (hg0 q hq))

/-- Bounds of a continuous function on a compact set. -/
lemma a2_bd {s : Set ℝ} (hs : IsCompact s) {f : ℝ → ℝ} (hf : ContinuousOn f s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hf
  exact ⟨max M 0, le_max_right _ _, fun x hx => by
    have := hM x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

/-- The algebra of the shifted form. -/
lemma a2_shift_alg {g ζ q1 y yp δ : ℝ} (hg : g ≠ 0) :
    g * (y + yp * (δ ^ 4 * (q1 / g)) + ζ / δ ^ 2 * y * (δ ^ 4 * (q1 / g)) ^ 2 / 2) =
      (g + (δ ^ 3) ^ 2 * (ζ * q1 ^ 2 / (2 * g))) * y + δ * (δ ^ 3 * q1) * yp := by
  field_simp
  ring


/-- **Pointwise remainder of the shifted form** (scalar form of the `ρ`-bound). -/
lemma a2_rho_pt {y y' w : ℝ → ℝ} (hy : IsAirySol y y') {Cy Cy' Cw : ℝ} (hCy : 0 ≤ Cy) (hCy' : 0 ≤ Cy')
    (hCw : 0 ≤ Cw) (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x)
    (hnb : ∀ {X ξ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ 1 → w ξ ≤ Cw * w X)
    {gx zx qx Mz Bm Gm δ K1 : ℝ} (hgx : gx ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : |zx| ≤ Mz)
    (hb : |qx / gx| ≤ Bm) (hG : |gx| ≤ Gm) (hsm : δ * (Bm * √(1 + Mz)) ≤ 1) (hBm1 : δ * Bm ≤ 1)
    (hK1 : Cw * (Cy + (Mz + 1) * √(3 + Mz) * Cy') * Bm ^ 3 ≤ K1) :
    |gx * y (zx / δ ^ 2 + δ ^ 4 * (qx / gx)) -
        ((gx + (δ ^ 3) ^ 2 * (zx * qx ^ 2 / (2 * gx))) * y (zx / δ ^ 2) +
          δ * (δ ^ 3 * qx) * y' (zx / δ ^ 2))| ≤ Gm * (K1 * δ ^ 9 * w (zx / δ ^ 2)) := by
  have hrem := a2_rem_lat hy hCy hCy' hCw hw0 hyb hyb' hnb hδ hδ1 hz hb hsm hBm1
  have e := a2_shift_alg (g := gx) (ζ := zx) (q1 := qx) (y := y (zx / δ ^ 2)) (yp := y' (zx / δ ^ 2)) (δ := δ) hgx
  have e2 : gx * y (zx / δ ^ 2 + δ ^ 4 * (qx / gx)) -
        ((gx + (δ ^ 3) ^ 2 * (zx * qx ^ 2 / (2 * gx))) * y (zx / δ ^ 2) + δ * (δ ^ 3 * qx) * y' (zx / δ ^ 2)) =
      gx * (y (zx / δ ^ 2 + δ ^ 4 * (qx / gx)) - (y (zx / δ ^ 2) +
          y' (zx / δ ^ 2) * (δ ^ 4 * (qx / gx)) +
          zx / δ ^ 2 * y (zx / δ ^ 2) * (δ ^ 4 * (qx / gx)) ^ 2 / 2)) := by
    rw [mul_sub, e]
  rw [e2, abs_mul]
  have hw := hw0 (zx / δ ^ 2)
  refine mul_le_mul hG ?_ (abs_nonneg _) ((abs_nonneg _).trans hG)
  refine hrem.trans ?_
  have : 0 ≤ δ ^ 9 * w (zx / δ ^ 2) := by positivity
  nlinarith

/-- Neighbour weights at lattice scale from a Lipschitz bound of `ζ`. -/
lemma a2_nbr_pt {w : ℝ → ℝ}
    (hnb : ∀ {X ξ Λ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ Λ → w ξ ≤ 6 / 5 * Real.exp Λ * w X)
    {z0 z1 Mz Lj δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hLj : 0 ≤ Lj) (hLj1 : Lj * δ ≤ 1) (hz : |z0| ≤ Mz)
    (hMz : 0 ≤ Mz) (hd : |z1 - z0| ≤ Lj * δ ^ 3) :
    w (z1 / δ ^ 2) ≤ 6 / 5 * Real.exp (Lj * √(1 + Mz)) * w (z0 / δ ^ 2) := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hX : |z0 / δ ^ 2| ≤ Mz / δ ^ 2 := by
    rw [abs_div, abs_of_pos hδ2]; exact div_le_div_of_nonneg_right hz hδ2.le
  refine a2_nbr hnb hδ hδ1 hLj hLj1 hX hMz ?_
  rw [← sub_div, abs_div, abs_of_pos hδ2, div_le_iff₀ hδ2]
  calc |z1 - z0| ≤ Lj * δ ^ 3 := hd
    _ = Lj * δ * δ ^ 2 := by ring

/-- The arithmetic of the row decomposition. -/
lemma a2_row_assembly {R rp rm r0 ap am c0 K0 Q P1 P2 T : ℝ} (hR : |R| ≤ K0 * T)
    (hp : |rp| ≤ Q * T) (hm : |rm| ≤ Q * T) (h0 : |r0| ≤ Q * T) (hap : |ap| ≤ P1) (ham : |am| ≤ P1)
    (hc : |c0| ≤ P2) :
    |R + (ap * rp + am * rm - c0 * r0)| ≤ (K0 + (2 * P1 + P2) * Q) * T := by
  have hP1 : 0 ≤ P1 := (abs_nonneg _).trans hap
  have hP2 : 0 ≤ P2 := (abs_nonneg _).trans hc
  have t1 : |ap * rp| ≤ P1 * (Q * T) := by rw [abs_mul]; exact mul_le_mul hap hp (abs_nonneg _) hP1
  have t2 : |am * rm| ≤ P1 * (Q * T) := by rw [abs_mul]; exact mul_le_mul ham hm (abs_nonneg _) hP1
  have t3 : |c0 * r0| ≤ P2 * (Q * T) := by rw [abs_mul]; exact mul_le_mul hc h0 (abs_nonneg _) hP2
  have u1 := abs_add_le R (ap * rp + am * rm - c0 * r0)
  have u2 := abs_sub (ap * rp + am * rm) (c0 * r0)
  have u3 := abs_add_le (ap * rp) (am * rm)
  nlinarith

/-- The row operator is linear: perturbing `ψ` by a small `ρ` (rows `k-1, k, k+1`). -/
lemma a2_row_of_rho {a c Ψ ψ : ℤ → ℝ} {k : ℤ} {K0 Q P1 P2 T : ℝ} (hΨ : |jac a c Ψ k| ≤ K0 * T)
    (hp : |ψ (k + 1) - Ψ (k + 1)| ≤ Q * T) (hm : |ψ (k - 1) - Ψ (k - 1)| ≤ Q * T)
    (h0 : |ψ k - Ψ k| ≤ Q * T) (hap : |a (k + 1)| ≤ P1) (ham : |a k| ≤ P1) (hc : |c k| ≤ P2) :
    |jac a c ψ k| ≤ (K0 + (2 * P1 + P2) * Q) * T := by
  have e : jac a c ψ k = jac a c Ψ k + (a (k + 1) * (ψ (k + 1) - Ψ (k + 1)) +
      a k * (ψ (k - 1) - Ψ (k - 1)) - c k * (ψ k - Ψ k)) := by
    unfold jac; ring
  rw [e]
  exact a2_row_assembly hΨ hp hm h0 hap ham hc

/-- The constants of the shifted-form estimate: bounds on the thickened set `J_η`. -/
structure A2Bnd (J : Set ℝ) (ζ A A2 g q1 c2 : ℝ → ℝ) (η Mz Bm Gm Am A2m Cm Em Lj δL : ℝ) : Prop where
  hMz0 : 0 ≤ Mz
  hBm0 : 0 ≤ Bm
  hGm0 : 0 ≤ Gm
  hAm0 : 0 ≤ Am
  hA2m0 : 0 ≤ A2m
  hCm0 : 0 ≤ Cm
  hEm0 : 0 ≤ Em
  hLj0 : 0 ≤ Lj
  hMz : ∀ x ∈ Metric.cthickening η J, |ζ x| ≤ Mz
  hBm : ∀ x ∈ Metric.cthickening η J, |q1 x / g x| ≤ Bm
  hGm : ∀ x ∈ Metric.cthickening η J, |g x| ≤ Gm
  hAm : ∀ x ∈ Metric.cthickening η J, |A x| ≤ Am
  hA2m : ∀ x ∈ Metric.cthickening η J, |A2 x| ≤ A2m
  hCm : ∀ x ∈ Metric.cthickening η J, |c2 x| ≤ Cm
  hEm : ∀ x ∈ Metric.cthickening η J, |langerCosh (ζ x * deriv ζ x ^ 2)| ≤ Em
  hg0 : ∀ x ∈ Metric.cthickening η J, g x ≠ 0
  hjet : ∀ q ∈ J, ∀ s : ℝ, |s| ≤ δL → |ζ (q + s) - ζ q| ≤ Lj * |s|

/-- Existence of the constants. -/
lemma a2_bnd_exist {U J : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} (hU : IsOpen U) (hζ : ContDiffOn ℝ 4 ζ U)
    (hA : ContDiffOn ℝ 3 A U) (hA2 : ContDiffOn ℝ 1 A2 U) (hg : ContDiffOn ℝ 3 g U)
    (hq1c : ContDiffOn ℝ 3 q1 U) (hc2 : ContinuousOn c2 U) (hg0 : ∀ q ∈ U, g q ≠ 0)
    (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ η Mz Bm Gm Am A2m Cm Em Lj δL : ℝ, 0 < η ∧ 0 < δL ∧ A2Bnd J ζ A A2 g q1 c2 η Mz Bm Gm Am A2m Cm Em Lj δL := by
  obtain ⟨η, hη, hcth⟩ := hJ.exists_cthickening_subset_open hU hJU
  have hJ' : IsCompact (Metric.cthickening η J) := hJ.cthickening
  have hζc : ContinuousOn ζ U := hζ.continuousOn
  have hζd : ContinuousOn (deriv ζ) U := hζ.continuousOn_deriv_of_isOpen hU (by norm_num)
  obtain ⟨Mz, hMz0, hMz⟩ := a2_bd hJ' (hζc.mono hcth)
  obtain ⟨Bm, hBm0, hBm⟩ := a2_bd hJ' ((hq1c.continuousOn.mono hcth).div (hg.continuousOn.mono hcth)
    (fun q hq => hg0 q (hcth hq)))
  obtain ⟨Gm, hGm0, hGm⟩ := a2_bd hJ' (hg.continuousOn.mono hcth)
  obtain ⟨Am, hAm0, hAm⟩ := a2_bd hJ' (hA.continuousOn.mono hcth)
  obtain ⟨A2m, hA2m0, hA2m⟩ := a2_bd hJ' (hA2.continuousOn.mono hcth)
  obtain ⟨Cm, hCm0, hCm⟩ := a2_bd hJ' (hc2.mono hcth)
  obtain ⟨Em, hEm0, hEm⟩ := a2_bd hJ' (((apuc_continuous 0).comp_continuousOn
    (hζc.mul ((hζd.pow 2)))).mono hcth)
  obtain ⟨Mj0, Lj, δL, hMj0, hLj, hδL, hjet⟩ := sj_jet1 hU (hζ.of_le (by norm_num)) hJ hJU
  exact ⟨η, Mz, Bm, Gm, Am, A2m, Cm, Em, Lj, δL, hη, hδL, ⟨hMz0, hBm0, hGm0, hAm0, hA2m0, hCm0, hEm0, hLj,
    hMz, hBm, hGm, hAm, hA2m, hCm, hEm, fun x hx => hg0 x (hcth hx), fun q hq s hs => (hjet q hq).2 s hs⟩⟩

/-- The `ρ`-bound at the lattice point `q + s`, `q ∈ J`, `|s| ≤ δ³`: `|ψ̂ - Ψ| ≤ (G K₁ C_n) δ⁹ w(X_q)`. -/
lemma a2_rho_bnd {y y' w : ℝ → ℝ} (hy : IsAirySol y y') {Cy Cy' : ℝ} (hCy : 0 ≤ Cy) (hCy' : 0 ≤ Cy')
    (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x) (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x)
    (hnb : ∀ {X ξ Λ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ Λ → w ξ ≤ 6 / 5 * Real.exp Λ * w X)
    {J : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} {η Mz Bm Gm Am A2m Cm Em Lj δL K1 Cn δ q s : ℝ}
    (B : A2Bnd J ζ A A2 g q1 c2 η Mz Bm Gm Am A2m Cm Em Lj δL) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsm : δ * (Bm * √(1 + Mz)) ≤ 1) (hBm1 : δ * Bm ≤ 1) (hLj1 : Lj * δ ≤ 1) (hδ3η : δ ^ 3 ≤ η)
    (hδ3L : δ ^ 3 ≤ δL)
    (hK1 : 6 / 5 * Real.exp 1 * (Cy + (Mz + 1) * √(3 + Mz) * Cy') * Bm ^ 3 ≤ K1)
    (hCn : 6 / 5 * Real.exp (Lj * √(1 + Mz)) ≤ Cn) (hq : q ∈ J) (hs : |s| ≤ δ ^ 3) :
    |g (q + s) * y (a2Xh ζ g q1 δ (q + s)) - a2Psi ζ g (a2p ζ g q1) q1 y y' δ (q + s)| ≤
      (Gm * K1 * Cn) * (δ ^ 9 * w (ζ q / δ ^ 2)) := by
  have hJJ' : J ⊆ Metric.cthickening η J := Metric.self_subset_cthickening J
  have hx : q + s ∈ Metric.cthickening η J :=
    Metric.mem_cthickening_of_dist_le (q + s) q η J hq (by
      rw [Real.dist_eq]; simp only [add_sub_cancel_left]; exact hs.trans hδ3η)
  have hCw0 : 0 ≤ 6 / 5 * Real.exp 1 := by positivity
  have hnb1 : ∀ {X ξ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ 1 → w ξ ≤ 6 / 5 * Real.exp 1 * w X :=
    fun h1 h2 => hnb h1 h2
  have hρ := a2_rho_pt hy hCy hCy' hCw0 hw0 hyb hyb' hnb1 (gx := g (q + s)) (zx := ζ (q + s))
    (qx := q1 (q + s)) (Mz := Mz) (Bm := Bm) (Gm := Gm) (K1 := K1) (δ := δ) (B.hg0 _ hx) hδ hδ1
    (B.hMz _ hx) (B.hBm _ hx) (B.hGm _ hx) hsm hBm1 hK1
  have hnbk : w (ζ (q + s) / δ ^ 2) ≤ Cn * w (ζ q / δ ^ 2) := by
    have h1 := a2_nbr_pt hnb hδ hδ1 B.hLj0 hLj1 (B.hMz q (hJJ' hq)) B.hMz0 (z1 := ζ (q + s)) (by
      have := B.hjet q hq s (hs.trans hδ3L)
      calc |ζ (q + s) - ζ q| ≤ Lj * |s| := this
        _ ≤ Lj * δ ^ 3 := mul_le_mul_of_nonneg_left hs B.hLj0)
    exact h1.trans (mul_le_mul_of_nonneg_right hCn (hw0 _))
  have hK10 : 0 ≤ K1 := by
    refine le_trans ?_ hK1
    have := B.hBm0
    have := B.hMz0
    positivity
  have hpos : 0 ≤ Gm * (K1 * δ ^ 9) := by have := B.hGm0; positivity
  refine (le_of_eq (by unfold a2Psi a2p a2Xh; rfl)).trans (hρ.trans ?_)
  calc Gm * (K1 * δ ^ 9 * w (ζ (q + s) / δ ^ 2)) = (Gm * (K1 * δ ^ 9)) * w (ζ (q + s) / δ ^ 2) := by ring
    _ ≤ (Gm * (K1 * δ ^ 9)) * (Cn * w (ζ q / δ ^ 2)) := mul_le_mul_of_nonneg_left hnbk hpos
    _ = _ := by ring

/-- Coefficient bounds near `q ∈ J`. -/
lemma a2_coef_bnd {J : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} {η Mz Bm Gm Am A2m Cm Em Lj δL δ q x : ℝ}
    (B : A2Bnd J ζ A A2 g q1 c2 η Mz Bm Gm Am A2m Cm Em Lj δL) (hδ1 : δ ≤ 1) (hδ : 0 < δ)
    (hq : q ∈ J) (hx : |x - q| ≤ η) :
    |A x + (δ ^ 3) ^ 2 * A2 x| ≤ Am + A2m ∧ |a2c ζ A c2 q (δ ^ 3)| ≤ 2 * Am * Em + Cm := by
  have h1 : (δ ^ 3) ^ 2 ≤ 1 := by
    have : δ ^ 3 ≤ 1 := (pow_le_one₀ hδ.le hδ1)
    nlinarith [pow_pos hδ 3]
  have hxJ : x ∈ Metric.cthickening η J :=
    Metric.mem_cthickening_of_dist_le x q η J hq (by rwa [Real.dist_eq])
  have hqJ' : q ∈ Metric.cthickening η J := Metric.self_subset_cthickening J hq
  refine ⟨?_, ?_⟩
  · calc |A x + (δ ^ 3) ^ 2 * A2 x| ≤ |A x| + |(δ ^ 3) ^ 2 * A2 x| := abs_add_le _ _
      _ ≤ Am + A2m := by
        refine add_le_add (B.hAm x hxJ) ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc (δ ^ 3) ^ 2 * |A2 x| ≤ 1 * A2m := mul_le_mul h1 (B.hA2m x hxJ) (abs_nonneg _) zero_le_one
          _ = A2m := one_mul _
  · unfold a2c
    calc |2 * A q * langerCosh (ζ q * deriv ζ q ^ 2) + (δ ^ 3) ^ 2 * c2 q| ≤
          |2 * A q * langerCosh (ζ q * deriv ζ q ^ 2)| + |(δ ^ 3) ^ 2 * c2 q| := abs_add_le _ _
      _ ≤ 2 * Am * Em + Cm := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_mul, abs_two]
          have := mul_le_mul (B.hAm q hqJ') (B.hEm q hqJ') (abs_nonneg _) B.hAm0
          linarith
        · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          calc (δ ^ 3) ^ 2 * |c2 q| ≤ 1 * Cm := mul_le_mul h1 (B.hCm q hqJ') (abs_nonneg _) zero_le_one
            _ = Cm := one_mul _

/-- The shifted argument is comparable to the unshifted one. -/
lemma a2_Xh_bound {z b Mz Bm δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : |z| ≤ Mz) (hb : |b| ≤ Bm)
    (hBm1 : δ * Bm ≤ 1) :
    |z / δ ^ 2 + δ ^ 4 * b| ≤ (Mz + 1) / δ ^ 2 ∧ |z / δ ^ 2 - (z / δ ^ 2 + δ ^ 4 * b)| ≤ Bm * δ := by
  have hBm0 : 0 ≤ Bm := (abs_nonneg _).trans hb
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h4 : δ ^ 4 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3, pow_pos hδ 4]
  have hs : |δ ^ 4 * b| ≤ δ ^ 4 * Bm := by
    rw [abs_mul, abs_of_pos (by positivity)]; exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hs1 : |δ ^ 4 * b| ≤ 1 := hs.trans (by nlinarith [mul_le_mul_of_nonneg_right h4 hBm0])
  have hX : |z / δ ^ 2| ≤ Mz / δ ^ 2 := by
    rw [abs_div, abs_of_pos hδ2]; exact div_le_div_of_nonneg_right hz hδ2.le
  refine ⟨?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ 1 / δ ^ 2 := by
      rw [le_div_iff₀ hδ2]; nlinarith [pow_le_one₀ hδ.le hδ1 (n := 2)]
    calc |z / δ ^ 2 + δ ^ 4 * b| ≤ |z / δ ^ 2| + |δ ^ 4 * b| := abs_add_le _ _
      _ ≤ Mz / δ ^ 2 + 1 / δ ^ 2 := add_le_add hX (hs1.trans h1)
      _ = _ := by ring
  · have : z / δ ^ 2 - (z / δ ^ 2 + δ ^ 4 * b) = -(δ ^ 4 * b) := by ring
    rw [this, abs_neg]
    exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right h4 hBm0])

/-- **The shifted-form row bound at one lattice point** (all constants and the small-`δ` conditions as hypotheses). -/
lemma a2_shifted_point {y y' w : ℝ → ℝ} (hy : IsAirySol y y') {Cy Cy' : ℝ} (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x)
    (hnb : ∀ {X ξ Λ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ Λ → w ξ ≤ 6 / 5 * Real.exp Λ * w X)
    {J : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} {η Mz Bm Gm Am A2m Cm Em Lj δL K0 K1 Cn Cn2 Kf δ q₀ : ℝ} {k : ℤ}
    (B : A2Bnd J ζ A A2 g q1 c2 η Mz Bm Gm Am A2m Cm Em Lj δL)
    (hK10 : 0 ≤ K1) (hK1 : K1 = 6 / 5 * Real.exp 1 * (Cy + (Mz + 1) * √(3 + Mz) * Cy') * Bm ^ 3)
    (hCn : Cn = 6 / 5 * Real.exp (Lj * √(1 + Mz))) (hCn0 : 0 ≤ Cn)
    (hCn2 : Cn2 = 6 / 5 * Real.exp (Bm * √(1 + (Mz + 1)))) (hK0 : 0 ≤ K0)
    (hKf : Kf = (K0 + (2 * (Am + A2m) + (2 * Am * Em + Cm)) * (Gm * K1 * Cn)) * Cn2 + 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδη : δ ^ 3 ≤ η) (hδL' : δ ^ 3 ≤ δL) (hδBm : δ * Bm ≤ 1)
    (hδsm : δ * (Bm * √(1 + Mz)) ≤ 1) (hδLj1 : Lj * δ ≤ 1) (hk : dalQ q₀ δ k ∈ J)
    (hΨ : |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
          (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
          (fun j => a2Psi ζ g (a2p ζ g q1) q1 y y' δ (dalQ q₀ δ j)) k| ≤
        K0 * |δ ^ 3| ^ 3 * w (ζ (dalQ q₀ δ k) / δ ^ 2)) :
    |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
        (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
        (fun j => g (dalQ q₀ δ j) * y (a2Xh ζ g q1 δ (dalQ q₀ δ j))) k| ≤
      Kf * δ ^ 9 * w (a2Xh ζ g q1 δ (dalQ q₀ δ k)) := by
  have hMz0 := B.hMz0
  have hBm0 := B.hBm0
  have hGm0 := B.hGm0
  have hAm0 := B.hAm0
  have hA2m0 := B.hA2m0
  have hCm0 := B.hCm0
  have hEm0 := B.hEm0
  have hLj0 := B.hLj0
  have hq1' : dalQ q₀ δ (k + 1) = dalQ q₀ δ k + δ ^ 3 := by unfold dalQ; push_cast; ring
  have hq2' : dalQ q₀ δ (k - 1) = dalQ q₀ δ k + -(δ ^ 3) := by unfold dalQ; push_cast; ring
  have hρ : ∀ s : ℝ, |s| ≤ δ ^ 3 →
      |g (dalQ q₀ δ k + s) * y (a2Xh ζ g q1 δ (dalQ q₀ δ k + s)) -
        a2Psi ζ g (a2p ζ g q1) q1 y y' δ (dalQ q₀ δ k + s)| ≤
        (Gm * K1 * Cn) * (δ ^ 9 * w (ζ (dalQ q₀ δ k) / δ ^ 2)) := fun s hs =>
    a2_rho_bnd hy hCy hCy' hw0 hyb hyb' hnb B hδ hδ1 hδsm hδBm hδLj1 hδη hδL' hK1.ge hCn.ge hk hs
  have hpd : 0 < δ ^ 3 := pow_pos hδ 3
  have e9 : |δ ^ 3| ^ 3 = δ ^ 9 := by rw [abs_of_pos hpd]; ring
  rw [e9, mul_assoc] at hΨ
  have hxa : |dalQ q₀ δ (k + 1) - δ ^ 3 / 2 - dalQ q₀ δ k| ≤ η := by
    rw [hq1', abs_le]; constructor <;> linarith
  have hxb : |dalQ q₀ δ k - δ ^ 3 / 2 - dalQ q₀ δ k| ≤ η := by
    rw [abs_le]; constructor <;> linarith
  have key := a2_row_of_rho (K0 := K0) (Q := Gm * K1 * Cn) (P1 := Am + A2m) (P2 := 2 * Am * Em + Cm)
    (T := δ ^ 9 * w (ζ (dalQ q₀ δ k) / δ ^ 2))
    (ψ := fun j => g (dalQ q₀ δ j) * y (a2Xh ζ g q1 δ (dalQ q₀ δ j))) hΨ
    (by have := hρ (δ ^ 3) (by rw [abs_of_pos hpd]); simp only [hq1']; exact this)
    (by have := hρ (-(δ ^ 3)) (by rw [abs_neg, abs_of_pos hpd]); simp only [hq2']; exact this)
    (by have := hρ 0 (by rw [abs_zero]; exact hpd.le); simpa using this)
    (a2_coef_bnd B hδ1 hδ hk hxa).1 (a2_coef_bnd B hδ1 hδ hk hxb).1 (a2_coef_bnd B hδ1 hδ hk hxb).2
  obtain ⟨hX1, hX2⟩ := a2_Xh_bound (z := ζ (dalQ q₀ δ k)) (b := q1 (dalQ q₀ δ k) / g (dalQ q₀ δ k))
    hδ hδ1 (B.hMz _ (Metric.self_subset_cthickening J hk)) (B.hBm _ (Metric.self_subset_cthickening J hk)) hδBm
  have hW : w (ζ (dalQ q₀ δ k) / δ ^ 2) ≤ Cn2 * w (a2Xh ζ g q1 δ (dalQ q₀ δ k)) := by
    rw [hCn2]
    exact a2_nbr hnb hδ hδ1 hBm0 (by linarith) hX1 (by linarith) hX2
  refine key.trans ?_
  have hw1 := hw0 (a2Xh ζ g q1 δ (dalQ q₀ δ k))
  have hP : 0 ≤ K0 + (2 * (Am + A2m) + (2 * Am * Em + Cm)) * (Gm * K1 * Cn) := by positivity
  have h9 : 0 < δ ^ 9 := by positivity
  calc (K0 + (2 * (Am + A2m) + (2 * Am * Em + Cm)) * (Gm * K1 * Cn)) * (δ ^ 9 * w (ζ (dalQ q₀ δ k) / δ ^ 2))
      ≤ (K0 + (2 * (Am + A2m) + (2 * Am * Em + Cm)) * (Gm * K1 * Cn)) *
          (δ ^ 9 * (Cn2 * w (a2Xh ζ g q1 δ (dalQ q₀ δ k)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW h9.le) hP
    _ = ((K0 + (2 * (Am + A2m) + (2 * Am * Em + Cm)) * (Gm * K1 * Cn)) * Cn2) *
          (δ ^ 9 * w (a2Xh ζ g q1 δ (dalQ q₀ δ k))) := by ring
    _ ≤ Kf * δ ^ 9 * w (a2Xh ζ g q1 δ (dalQ q₀ δ k)) := by
        rw [hKf]
        have : 0 ≤ δ ^ 9 * w (a2Xh ζ g q1 δ (dalQ q₀ δ k)) := by positivity
        nlinarith


/-- **Q4: the row defect of the shifted parametrix `g · y(X + δ⁴ q₁/g)` on the lattice.** -/
theorem airy2_shifted_defect {y y' w : ℝ → ℝ} (hy : IsAirySol y y') {Cy Cy' : ℝ} (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x)
    (hnb : ∀ {X ξ Λ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ Λ → w ξ ≤ 6 / 5 * Real.exp Λ * w X)
    {U J : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} (hU : IsOpen U) (hζ : ContDiffOn ℝ 4 ζ U)
    (hA : ContDiffOn ℝ 3 A U) (hA2 : ContDiffOn ℝ 1 A2 U) (hg : ContDiffOn ℝ 3 g U)
    (hq1c : ContDiffOn ℝ 3 q1 U) (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K δ0 : ℝ, 0 < K ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∀ k : ℤ, dalQ q₀ δ k ∈ J →
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
          (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
          (fun j => g (dalQ q₀ δ j) * y (a2Xh ζ g q1 δ (dalQ q₀ δ j))) k| ≤
        K * δ ^ 9 * w (a2Xh ζ g q1 δ (dalQ q₀ δ k)) := by
  have hg0 : ∀ q ∈ U, g q ≠ 0 := a2_g_ne hrel
  have hD : Airy2Data U ζ A A2 g (a2p ζ g q1) q1 := Airy2Data.of_smooth hU hζ hA hA2 hg hq1c hg0
  obtain ⟨K0, δ0, hK0, hδ0, hδ01, H0⟩ :=
    airy2_defect_lattice hy Cy Cy' hCy hCy' hw0 hyb hyb' hD hc2 hrel hq1 hJ hJU
  obtain ⟨η, Mz, Bm, Gm, Am, A2m, Cm, Em, Lj, δL, hη, hδL, B⟩ :=
    a2_bnd_exist hU hζ hA hA2 hg hq1c hc2 hg0 hJ hJU
  have hMz0 := B.hMz0
  have hBm0 := B.hBm0
  have hGm0 := B.hGm0
  have hAm0 := B.hAm0
  have hA2m0 := B.hA2m0
  have hCm0 := B.hCm0
  have hEm0 := B.hEm0
  have hLj0 := B.hLj0
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = 6 / 5 * Real.exp 1 * (Cy + (Mz + 1) * √(3 + Mz) * Cy') * Bm ^ 3 :=
    ⟨_, rfl⟩
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℝ, Cn = 6 / 5 * Real.exp (Lj * √(1 + Mz)) := ⟨_, rfl⟩
  have hCn0 : 0 ≤ Cn := by rw [hCn]; positivity
  obtain ⟨Cn2, hCn2⟩ : ∃ Cn2 : ℝ, Cn2 = 6 / 5 * Real.exp (Bm * √(1 + (Mz + 1))) := ⟨_, rfl⟩
  have hCn20 : 0 ≤ Cn2 := by rw [hCn2]; positivity
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ℝ,
      Kf = (K0 + (2 * (Am + A2m) + (2 * Am * Em + Cm)) * (Gm * K1 * Cn)) * Cn2 + 1 := ⟨_, rfl⟩
  have hKf0 : 0 < Kf := by
    rw [hKf]
    have : 0 ≤ (K0 + (2 * (Am + A2m) + (2 * Am * Em + Cm)) * (Gm * K1 * Cn)) * Cn2 := by positivity
    linarith
  refine ⟨Kf, min δ0 (min (min 1 η) (min δL (min (1 / (Bm + 1))
    (min (1 / (Bm * √(1 + Mz) + 1)) (1 / (Lj + 1)))))), hKf0, ?_, ?_, ?_⟩
  · exact lt_min hδ0 (lt_min (lt_min one_pos hη) (lt_min hδL (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))))
  · exact (min_le_left _ _).trans hδ01
  intro δ q₀ hδ hδδ k hk
  have hδ0' : δ ≤ δ0 := hδδ.trans (min_le_left _ _)
  have hr1 := hδδ.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hr1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδη : δ ≤ η := hr1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr2 := hr1.trans (min_le_right _ _)
  have hδL' : δ ≤ δL := hr2.trans (min_le_left _ _)
  have hr3 := hr2.trans (min_le_right _ _)
  have hδB : δ ≤ 1 / (Bm + 1) := hr3.trans (min_le_left _ _)
  have hr4 := hr3.trans (min_le_right _ _)
  have hδB2 : δ ≤ 1 / (Bm * √(1 + Mz) + 1) := hr4.trans (min_le_left _ _)
  have hδLj : δ ≤ 1 / (Lj + 1) := hr4.trans (min_le_right _ _)
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
  have hδBm : δ * Bm ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδB; linarith
  have hδsm : δ * (Bm * √(1 + Mz)) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδB2; linarith
  have hδLj1 : Lj * δ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδLj; linarith
  have hδ3η : δ ^ 3 ≤ η := hδ3.trans hδη
  have hδ3L : δ ^ 3 ≤ δL := hδ3.trans hδL'
  have hδ3η : δ ^ 3 ≤ η := hδ3.trans hδη
  have hδ3L : δ ^ 3 ≤ δL := hδ3.trans hδL'
  exact a2_shifted_point hy hCy hCy' hw0 hyb hyb' hnb B hK10 hK1 hCn hCn0 hCn2 hK0.le hKf hδ hδ1 hδ3η hδ3L
    hδBm hδsm hδLj1 hk (by have := H0 δ q₀ hδ hδ0' k hk; exact this)


/-- **The shifted `Ai` row defect**: `|row| ≤ K δ⁹ airyWt(X̂_k)`, `X̂ = ζ/δ² + δ⁴ q₁/g`, `ψ̂ = g Ai(X̂)`. -/
theorem airy2_shifted_defect_Ai {U J : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} (hU : IsOpen U)
    (hζ : ContDiffOn ℝ 4 ζ U) (hA : ContDiffOn ℝ 3 A U) (hA2 : ContDiffOn ℝ 1 A2 U)
    (hg : ContDiffOn ℝ 3 g U) (hq1c : ContDiffOn ℝ 3 q1 U) (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K δ0 : ℝ, 0 < K ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∀ k : ℤ, dalQ q₀ δ k ∈ J →
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
          (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
          (fun j => g (dalQ q₀ δ j) * airyAi (a2Xh ζ g q1 δ (dalQ q₀ δ j))) k| ≤
        K * δ ^ 9 * airyWt (a2Xh ζ g q1 δ (dalQ q₀ δ k)) :=
  airy2_shifted_defect isAirySol_airyAi (Cy := 25) (Cy' := 132500) (by norm_num) (by norm_num)
    (fun x => (airyWt_pos x).le) (fun x => (apx_airy_global x).1) (fun x => (apx_airy_global x).2)
    (fun h1 h2 => airyWt_le_of_close h1 h2) hU hζ hA hA2 hg hq1c hc2 hrel hq1 hJ hJU

/-- **The shifted `Bi` row defect**: `|row| ≤ K δ⁹ airyBiWt(X̂_k)`, `ψ̂ = g Bi(X̂)`. -/
theorem airy2_shifted_defect_Bi {U J : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} (hU : IsOpen U)
    (hζ : ContDiffOn ℝ 4 ζ U) (hA : ContDiffOn ℝ 3 A U) (hA2 : ContDiffOn ℝ 1 A2 U)
    (hg : ContDiffOn ℝ 3 g U) (hq1c : ContDiffOn ℝ 3 q1 U) (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K δ0 : ℝ, 0 < K ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∀ k : ℤ, dalQ q₀ δ k ∈ J →
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
          (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
          (fun j => g (dalQ q₀ δ j) * airyBi (a2Xh ζ g q1 δ (dalQ q₀ δ j))) k| ≤
        K * δ ^ 9 * airyBiWt (a2Xh ζ g q1 δ (dalQ q₀ δ k)) :=
  airy2_shifted_defect isAirySol_airyBi_shift (Cy := 450) (Cy' := 2385000) (by norm_num) (by norm_num)
    (fun x => (airyBiWt_pos x).le) (fun x => (apx_airyBi_global x).1) (fun x => (apx_airyBi_global x).2)
    (fun h1 h2 => airyBiWt_le_of_close h1 h2) hU hζ hA hA2 hg hq1c hc2 hrel hq1 hJ hJU

/-- info: 'FormalResearch.Special.airy2_shifted_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_shifted_defect

/-- info: 'FormalResearch.Special.airy2_shifted_defect_Ai' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_shifted_defect_Ai

/-- info: 'FormalResearch.Special.airy2_shifted_defect_Bi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_shifted_defect_Bi

end FormalResearch.Special
