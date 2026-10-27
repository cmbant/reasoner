import Mathlib

/-!
# The planar sign inequality

Lemma `lem:planarsign` of `ResearchNotes/QI/antiunitary_occupation/planar_sign_inequality.tex`:
for `v₁, …, v_m ∈ ℂ` there are signs `s_i = ±1` with
`‖∑ s_i v_i‖² ≥ (1/3) ((∑ ‖v_i‖)² + ∑ ‖v_i‖²)`
(`planar_sign`; `planar_sign4` is the case `m = 4`), and the equality case
(`planar_sign_equality_iff`): the bound is attained exactly when the nonzero `v_i` are two of equal
modulus on perpendicular lines, or three of equal modulus on lines at mutual angles `π/3`
(or none).

The proof is not the zonotope/variational argument of the paper but an elementary one.

* *Reduction.* Put `M = max_s ‖∑ s_i v_i‖`. After sign changes the `v_i = a_i e^{iθ_i}` have
  `0 ≤ θ_1 ≤ … ≤ θ_m < π`, and the `m` vertices `X_k = ∑_{i ≤ k} v_i - ∑_{i > k} v_i` of the zonogon
  (with `X_m = -X_0`) satisfy `‖X_k‖ ≤ M` (`planar_bound`, `polar_sorted`, `seq_bound`).
* *Angle sum* (`arcsin_sum_le`). `∑ arcsin (a_i / M) ≤ π/2`. Project the endpoints `X_{i-1}, X_i` of the
  edge `2 v_i` on its direction: the projections `p, q` satisfy `p - q = 2 a_i`, `|p|, |q| ≤ M`, hence
  `arcsin (a_i/M) ≤ (arcsin (p/M) + arcsin (-q/M)) / 2` (`edge_real`). At each vertex the two
  projections (onto the incoming and outgoing edge, turned by `δ ∈ [0, π]`) satisfy
  `arcsin (p/M) + arcsin (-q'/M) ≤ δ` (`vertex_real`); the turning angles sum to `π`.
* *Inscribed polygons* (`Glist_le`). For angles `β_k ≥ 0` with `∑ β_k ≤ π/2`,
  `(∑ sin β_k)² + ∑ sin² β_k ≤ 3`. Four or more angles: two of them have sum `≤ π/4` and merging
  them does not decrease the left side, and increases it strictly if both are positive
  (`merge_ineq`); at most three angles are the case `G3_le` (equality at `(π/6, π/6, π/6)` and
  `(π/4, π/4, 0)`, `G3_le_eq`), proved by convexity in the difference of two angles
  (`planar_poly_aux`, `planar_poly_eq`).
* *Equality.* `Glist_eq` classifies the angle lists with `G = 3`; `seq_eq`, `planar_bound_eq` turn this
  into "every `‖v_i‖` is `0` or `M/√2`" or "`0` or `M/2`". Counting nonzero vectors from
  `L² + Q = 3 M²` gives two or three of them, and the sign vectors on those indices give the
  orthogonality (two) and `|Re (v_i v̄_j)| ≤ ‖v‖²/2` (three), which with the vanishing Gram determinant
  of three planar vectors (`gram_det`, `gram_aux`) forces `(2 Re (v_i v̄_j))² = ‖v‖⁴`.
  `planar_sign_equality_of` is the converse.
-/

open Real

namespace FormalResearch.FrameFree

/-- The one-variable polynomial inequality behind the three-angle case. -/
theorem planar_poly_aux (s c k : ℝ) (hs : 1 / 2 ≤ s) (hs2 : 2 * s ^ 2 ≤ 1) (hc0 : 0 ≤ c)
    (hcs : c ^ 2 + s ^ 2 = 1) (hck : c ≤ k) (hk1 : k ≤ 1) :
    (8 * s ^ 2 - 2) * k ^ 2 + 4 * s * (1 - 2 * s ^ 2) * k + (1 - 10 * s ^ 2 + 8 * s ^ 4) ≤ 0 := by
  have hc1 : c < 1 := by
    by_contra h
    have h := not_lt.1 h
    nlinarith
  have hf1 : (8 * s ^ 2 - 2) * 1 ^ 2 + 4 * s * (1 - 2 * s ^ 2) * 1 + (1 - 10 * s ^ 2 + 8 * s ^ 4) ≤ 0 := by
    have : (8 * s ^ 2 - 2) * 1 ^ 2 + 4 * s * (1 - 2 * s ^ 2) * 1 + (1 - 10 * s ^ 2 + 8 * s ^ 4)
        = (2 * s - 1) ^ 2 * (2 * s ^ 2 - 1) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  have hfc : (8 * s ^ 2 - 2) * c ^ 2 + 4 * s * (1 - 2 * s ^ 2) * c + (1 - 10 * s ^ 2 + 8 * s ^ 4) ≤ 0 := by
    have hc2 : c ^ 2 = 1 - s ^ 2 := by linarith
    have : (8 * s ^ 2 - 2) * c ^ 2 + 4 * s * (1 - 2 * s ^ 2) * c + (1 - 10 * s ^ 2 + 8 * s ^ 4)
        = -(c ^ 2 - 2 * s * c - s ^ 2) ^ 2 := by
      have h3 : c ^ 4 = (1 - s ^ 2) ^ 2 := by rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
      have h4 : c ^ 3 = c * (1 - s ^ 2) := by rw [show c ^ 3 = c * c ^ 2 by ring, hc2]
      nlinarith [h3, h4, hc2]
    rw [this]
    exact neg_nonpos.2 (sq_nonneg _)
  have hA : 0 ≤ 8 * s ^ 2 - 2 := by nlinarith
  have key : (1 - c) * ((8 * s ^ 2 - 2) * k ^ 2 + 4 * s * (1 - 2 * s ^ 2) * k + (1 - 10 * s ^ 2 + 8 * s ^ 4))
      = ((8 * s ^ 2 - 2) * c ^ 2 + 4 * s * (1 - 2 * s ^ 2) * c + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (1 - k)
        + ((8 * s ^ 2 - 2) * 1 ^ 2 + 4 * s * (1 - 2 * s ^ 2) * 1 + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (k - c)
        + (8 * s ^ 2 - 2) * (1 - c) * (k - c) * (k - 1) := by ring
  have h1 : ((8 * s ^ 2 - 2) * c ^ 2 + 4 * s * (1 - 2 * s ^ 2) * c + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (1 - k) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hfc (by linarith)
  have h2 : ((8 * s ^ 2 - 2) * 1 ^ 2 + 4 * s * (1 - 2 * s ^ 2) * 1 + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (k - c) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hf1 (by linarith)
  have h3 : (8 * s ^ 2 - 2) * (1 - c) * (k - c) * (k - 1) ≤ 0 := by
    have : 0 ≤ (8 * s ^ 2 - 2) * (1 - c) * (k - c) := by
      apply mul_nonneg (mul_nonneg hA (by linarith)) (by linarith)
    exact mul_nonpos_of_nonneg_of_nonpos this (by linarith)
  have : (1 - c) * ((8 * s ^ 2 - 2) * k ^ 2 + 4 * s * (1 - 2 * s ^ 2) * k + (1 - 10 * s ^ 2 + 8 * s ^ 4)) ≤ 0 := by
    rw [key]; linarith
  by_contra hpos
  have hpos := not_le.1 hpos
  have := mul_pos (sub_pos.2 hc1) hpos
  linarith

theorem poly_eq_aux (s c : ℝ) (hs : 1 / 2 ≤ s) (hs2 : 2 * s ^ 2 ≤ 1) (hc0 : 0 ≤ c)
    (hcs : c ^ 2 + s ^ 2 = 1) : c ^ 2 - 2 * s * c - s ^ 2 < 0 := by
  have hs14 : 1 / 4 ≤ s ^ 2 := by nlinarith
  have hc_gt : 1 / 2 < c := by nlinarith
  have h2sc : c ≤ 2 * s * c := by nlinarith
  nlinarith

/-- Equality in the polynomial inequality of the three-angle case. -/
theorem planar_poly_eq (s c k : ℝ) (hs : 1 / 2 ≤ s) (hs2 : 2 * s ^ 2 ≤ 1) (hc0 : 0 ≤ c)
    (hcs : c ^ 2 + s ^ 2 = 1) (hck : c ≤ k) (hk1 : k ≤ 1)
    (hf : (8 * s ^ 2 - 2) * k ^ 2 + 4 * s * (1 - 2 * s ^ 2) * k + (1 - 10 * s ^ 2 + 8 * s ^ 4) = 0) :
    k = 1 ∧ (s = 1 / 2 ∨ 2 * s ^ 2 = 1) := by
  have hc1 : c < 1 := by
    by_contra h
    have h := not_lt.1 h
    nlinarith
  have hf1 : (8 * s ^ 2 - 2) * 1 ^ 2 + 4 * s * (1 - 2 * s ^ 2) * 1 + (1 - 10 * s ^ 2 + 8 * s ^ 4)
      = (2 * s - 1) ^ 2 * (2 * s ^ 2 - 1) := by ring
  have hc2 : c ^ 2 = 1 - s ^ 2 := by linarith
  have hfc : (8 * s ^ 2 - 2) * c ^ 2 + 4 * s * (1 - 2 * s ^ 2) * c + (1 - 10 * s ^ 2 + 8 * s ^ 4)
      = -(c ^ 2 - 2 * s * c - s ^ 2) ^ 2 := by
    have h3 : c ^ 4 = (1 - s ^ 2) ^ 2 := by rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
    have h4 : c ^ 3 = c * (1 - s ^ 2) := by rw [show c ^ 3 = c * c ^ 2 by ring, hc2]
    nlinarith [h3, h4, hc2]
  have hA : 0 ≤ 8 * s ^ 2 - 2 := by nlinarith
  have hneg := poly_eq_aux s c hs hs2 hc0 hcs
  by_cases hk : k = 1
  · refine ⟨hk, ?_⟩
    subst hk
    rw [hf1] at hf
    rcases mul_eq_zero.1 hf with h | h
    · left
      have : 2 * s - 1 = 0 := by nlinarith [sq_nonneg (2 * s - 1)]
      linarith
    · right; linarith
  · exfalso
    have hk' : k < 1 := lt_of_le_of_ne hk1 hk
    have key : (1 - c) * ((8 * s ^ 2 - 2) * k ^ 2 + 4 * s * (1 - 2 * s ^ 2) * k + (1 - 10 * s ^ 2 + 8 * s ^ 4))
        = ((8 * s ^ 2 - 2) * c ^ 2 + 4 * s * (1 - 2 * s ^ 2) * c + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (1 - k)
          + ((8 * s ^ 2 - 2) * 1 ^ 2 + 4 * s * (1 - 2 * s ^ 2) * 1 + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (k - c)
          + (8 * s ^ 2 - 2) * (1 - c) * (k - c) * (k - 1) := by ring
    rw [hf, mul_zero] at key
    have hT1 : ((8 * s ^ 2 - 2) * c ^ 2 + 4 * s * (1 - 2 * s ^ 2) * c + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (1 - k) < 0 := by
      rw [hfc]
      have : 0 < (c ^ 2 - 2 * s * c - s ^ 2) ^ 2 := by nlinarith [hneg]
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have hT2 : ((8 * s ^ 2 - 2) * 1 ^ 2 + 4 * s * (1 - 2 * s ^ 2) * 1 + (1 - 10 * s ^ 2 + 8 * s ^ 4)) * (k - c) ≤ 0 := by
      rw [hf1]; exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)) (by linarith)
    have hT3 : (8 * s ^ 2 - 2) * (1 - c) * (k - c) * (k - 1) ≤ 0 := by
      have : 0 ≤ (8 * s ^ 2 - 2) * (1 - c) * (k - c) :=
        mul_nonneg (mul_nonneg hA (by linarith)) (by linarith)
      exact mul_nonpos_of_nonneg_of_nonpos this (by linarith)
    linarith

/-- The inscribed quantity `G(β) = (∑ sin β)² + ∑ sin² β` for three angles. -/
noncomputable def G3 (a b c : ℝ) : ℝ :=
  (sin a + sin b + sin c) ^ 2 + sin a ^ 2 + sin b ^ 2 + sin c ^ 2

theorem G3_pair_formula (u d : ℝ) :
    G3 (u + d) (u - d) (π / 2 - 2 * u)
      = 3 + ((8 * sin u ^ 2 - 2) * cos d ^ 2 + 4 * sin u * (1 - 2 * sin u ^ 2) * cos d
        + (1 - 10 * sin u ^ 2 + 8 * sin u ^ 4)) := by
  have hsd : sin d ^ 2 = 1 - cos d ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq d]
  have hcu : cos u ^ 2 = 1 - sin u ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq u]
  have h1 : sin (u + d) = sin u * cos d + cos u * sin d := Real.sin_add u d
  have h2 : sin (u - d) = sin u * cos d - cos u * sin d := Real.sin_sub u d
  have h3 : sin (π / 2 - 2 * u) = 1 - 2 * sin u ^ 2 := by
    rw [Real.sin_pi_div_two_sub, Real.cos_two_mul, Real.cos_sq']; ring
  unfold G3
  rw [h1, h2, h3]
  linear_combination (2 * sin d ^ 2) * hcu + (2 * (1 - sin u ^ 2)) * hsd

/-- Elementary facts about `u ∈ [π/6, π/4]`, `|d| ≤ u`. -/
theorem G3_pair_hyps (u d : ℝ) (hu6 : π / 6 ≤ u) (hu4 : u ≤ π / 4) (hd : |d| ≤ u) :
    1 / 2 ≤ sin u ∧ 2 * sin u ^ 2 ≤ 1 ∧ 0 ≤ cos u ∧ cos u ^ 2 + sin u ^ 2 = 1 ∧
      cos u ≤ cos d ∧ cos d ≤ 1 := by
  have hpi := Real.pi_pos
  have hs : 1 / 2 ≤ sin u := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 6) (y := u) (by linarith) (by linarith) hu6
    rw [Real.sin_pi_div_six] at h; exact h
  have hs2 : 2 * sin u ^ 2 ≤ 1 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := u) (y := π / 4) (by linarith) (by linarith) hu4
    rw [Real.sin_pi_div_four] at h
    have h0 : 0 ≤ sin u := by linarith
    have : sin u ^ 2 ≤ (√2 / 2) ^ 2 := pow_le_pow_left₀ h0 h 2
    have h22 : (√2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    linarith
  refine ⟨hs, hs2, Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩,
    Real.cos_sq_add_sin_sq u, ?_, Real.cos_le_one d⟩
  rw [← Real.cos_abs d]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg d) (by linarith) hd

theorem G3_pair (u d : ℝ) (hu6 : π / 6 ≤ u) (hu4 : u ≤ π / 4) (hd : |d| ≤ u) :
    G3 (u + d) (u - d) (π / 2 - 2 * u) ≤ 3 := by
  obtain ⟨hs, hs2, hc0, hcs, hck, hk1⟩ := G3_pair_hyps u d hu6 hu4 hd
  have hpoly := planar_poly_aux (sin u) (cos u) (cos d) hs hs2 hc0 hcs hck hk1
  rw [G3_pair_formula]
  linarith

theorem G3_symm12 (a b c : ℝ) : G3 a b c = G3 b a c := by unfold G3; ring
theorem G3_symm23 (a b c : ℝ) : G3 a b c = G3 a c b := by unfold G3; ring

theorem G3_of_pair (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = π / 2)
    (hab : π / 3 ≤ a + b) : G3 a b c ≤ 3 := by
  have h := G3_pair ((a + b) / 2) ((a - b) / 2) (by linarith) (by linarith)
    (by rw [abs_le]; constructor <;> linarith)
  have e1 : (a + b) / 2 + (a - b) / 2 = a := by ring
  have e2 : (a + b) / 2 - (a - b) / 2 = b := by ring
  have e3 : π / 2 - 2 * ((a + b) / 2) = c := by linarith
  rwa [e1, e2, e3] at h

/-- Three angles summing to `π/2`: `G ≤ 3` (equality at `(π/6, π/6, π/6)` and `(π/4, π/4, 0)`). -/
theorem G3_eq (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = π / 2) :
    G3 a b c ≤ 3 := by
  have hpi := Real.pi_pos
  by_cases h1 : π / 3 ≤ a + b
  · exact G3_of_pair a b c ha hb hc hsum h1
  by_cases h2 : π / 3 ≤ b + c
  · have := G3_of_pair b c a hb hc ha (by linarith) h2
    unfold G3 at this ⊢; nlinarith [this]
  have h3 : π / 3 ≤ a + c := by
    by_contra h
    have h := not_le.1 h
    have h1 := not_le.1 h1
    have h2 := not_le.1 h2
    linarith
  have := G3_of_pair a c b ha hc hb (by linarith) h3
  unfold G3 at this ⊢; nlinarith [this]

theorem G3_mono (a b c c' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcc : c ≤ c')
    (hc' : c' ≤ π / 2) (ha2 : a ≤ π / 2) (hb2 : b ≤ π / 2) : G3 a b c ≤ G3 a b c' := by
  have hpi := Real.pi_pos
  have hsa : 0 ≤ sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith)
  have hsb : 0 ≤ sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb (by linarith)
  have hsc : 0 ≤ sin c := Real.sin_nonneg_of_nonneg_of_le_pi hc (by linarith)
  have hle : sin c ≤ sin c' :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hc' hcc
  unfold G3
  nlinarith [mul_nonneg (sub_nonneg.2 hle) (add_nonneg hsa hsb), mul_nonneg (sub_nonneg.2 hle) hsc]

theorem G3_mono_strict (a b c c' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcc : c < c')
    (hc' : c' ≤ π / 2) (ha2 : a ≤ π / 2) (hb2 : b ≤ π / 2) : G3 a b c < G3 a b c' := by
  have hpi := Real.pi_pos
  have hsa : 0 ≤ sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith)
  have hsb : 0 ≤ sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb (by linarith)
  have hsc : 0 ≤ sin c := Real.sin_nonneg_of_nonneg_of_le_pi hc (by linarith)
  have hlt : sin c < sin c' :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hc' hcc
  unfold G3
  nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < sin c' + sin c' + sin c),
    mul_nonneg (sub_nonneg.2 hlt.le) (add_nonneg hsa hsb)]

/-- Three nonnegative angles with sum at most `π/2`: `G ≤ 3`. -/
theorem G3_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c ≤ π / 2) :
    G3 a b c ≤ 3 := by
  have hpi := Real.pi_pos
  have h := G3_mono a b c (π / 2 - a - b) ha hb hc (by linarith) (by linarith) (by linarith)
    (by linarith)
  exact h.trans (G3_eq a b (π / 2 - a - b) ha hb (by linarith) (by ring))

theorem G3_pair_eq (u d : ℝ) (hu6 : π / 6 ≤ u) (hu4 : u ≤ π / 4) (hd : |d| ≤ u)
    (h : G3 (u + d) (u - d) (π / 2 - 2 * u) = 3) : d = 0 ∧ (u = π / 6 ∨ u = π / 4) := by
  have hpi := Real.pi_pos
  obtain ⟨hs, hs2, hc0, hcs, hck, hk1⟩ := G3_pair_hyps u d hu6 hu4 hd
  rw [G3_pair_formula] at h
  have hf : (8 * sin u ^ 2 - 2) * cos d ^ 2 + 4 * sin u * (1 - 2 * sin u ^ 2) * cos d
        + (1 - 10 * sin u ^ 2 + 8 * sin u ^ 4) = 0 := by linarith
  obtain ⟨hk, hsu⟩ := planar_poly_eq (sin u) (cos u) (cos d) hs hs2 hc0 hcs hck hk1 hf
  have hd0 : d = 0 := by
    have := (Real.cos_eq_one_iff_of_lt_of_lt (x := d) (by linarith [abs_le.1 hd |>.1]) (by linarith [abs_le.1 hd |>.2])).1 hk
    exact this
  refine ⟨hd0, ?_⟩
  rcases hsu with h1 | h1
  · left
    apply Real.injOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    rw [Real.sin_pi_div_six]; exact h1
  · right
    apply Real.injOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    rw [Real.sin_pi_div_four]
    have h0 : 0 ≤ sin u := by linarith
    have : sin u ^ 2 = (√2 / 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; linarith
    exact (sq_eq_sq₀ h0 (by positivity)).1 this

/-- Three angles summing to `π/2` with `G = 3`: the three possible shapes. -/
theorem G3_eq_cases (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = π / 2)
    (h : G3 a b c = 3) :
    (a = π / 6 ∧ b = π / 6 ∧ c = π / 6) ∨ (a = π / 4 ∧ b = π / 4 ∧ c = 0) ∨
    (a = 0 ∧ b = π / 4 ∧ c = π / 4) ∨ (a = π / 4 ∧ b = 0 ∧ c = π / 4) := by
  have hpi := Real.pi_pos
  have hpair : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → x + y + z = π / 2 → π / 3 ≤ x + y →
      G3 x y z = 3 → (x = π / 6 ∧ y = π / 6 ∧ z = π / 6) ∨ (x = π / 4 ∧ y = π / 4 ∧ z = 0) := by
    intro x y z hx hy hz hxyz hxy hG
    have h1 := G3_pair_eq ((x + y) / 2) ((x - y) / 2) (by linarith) (by linarith)
      (by rw [abs_le]; constructor <;> linarith)
    have e1 : (x + y) / 2 + (x - y) / 2 = x := by ring
    have e2 : (x + y) / 2 - (x - y) / 2 = y := by ring
    have e3 : π / 2 - 2 * ((x + y) / 2) = z := by linarith
    rw [e1, e2, e3] at h1
    obtain ⟨hd, hu⟩ := h1 hG
    have hxy' : x = y := by linarith
    rcases hu with hu | hu
    · left; refine ⟨by linarith, by linarith, by linarith⟩
    · right; refine ⟨by linarith, by linarith, by linarith⟩
  by_cases h1 : π / 3 ≤ a + b
  · rcases hpair a b c ha hb hc hsum h1 h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  by_cases h2 : π / 3 ≤ b + c
  · have hG : G3 b c a = 3 := by
      have e : G3 b c a = G3 a b c := by unfold G3; ring
      rw [e]; exact h
    rcases hpair b c a hb hc ha (by linarith) h2 hG with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h3, h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h3, h1, h2⟩))
  have h3 : π / 3 ≤ a + c := by
    by_contra h'
    have h' := not_le.1 h'
    have h1 := not_le.1 h1
    have h2 := not_le.1 h2
    linarith
  have hG : G3 a c b = 3 := by
    have e : G3 a c b = G3 a b c := by unfold G3; ring
    rw [e]; exact h
  rcases hpair a c b ha hc hb (by linarith) h3 hG with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h3, h2⟩
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h3, h2⟩))

/-- Three nonnegative angles with `∑ ≤ π/2` and `G = 3`. -/
theorem G3_le_eq (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c ≤ π / 2)
    (h : G3 a b c = 3) :
    (a = π / 6 ∧ b = π / 6 ∧ c = π / 6) ∨ (a = π / 4 ∧ b = π / 4 ∧ c = 0) ∨
    (a = 0 ∧ b = π / 4 ∧ c = π / 4) ∨ (a = π / 4 ∧ b = 0 ∧ c = π / 4) := by
  have hpi := Real.pi_pos
  have hsum' : a + b + c = π / 2 := by
    by_contra hne
    have hlt : a + b + c < π / 2 := lt_of_le_of_ne hsum hne
    have h1 := G3_mono_strict a b c (π / 2 - a - b) ha hb hc (by linarith) (by linarith)
      (by linarith) (by linarith)
    have h2 := G3_eq a b (π / 2 - a - b) ha hb (by linarith) (by ring)
    linarith
  exact G3_eq_cases a b c ha hb hc hsum' h

/-- Numerical core of the merging step. -/
theorem merge_num (e S : ℝ) (he0 : 0 ≤ e) (he : e ≤ π / 8) (hS0 : 0 ≤ S) (hS : S ≤ π / 2) :
    S * sin e < cos e * cos (2 * e) := by
  have hpi : π < 3.1416 := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have h1 : sin e ≤ e := Real.sin_le he0
  have h2 : 1 - e ^ 2 / 2 ≤ cos e := Real.one_sub_sq_div_two_le_cos
  have h3 : 1 - (2 * e) ^ 2 / 2 ≤ cos (2 * e) := Real.one_sub_sq_div_two_le_cos
  have he' : e ≤ 0.3927 := by linarith
  have hA : S * sin e ≤ (π / 2) * e := by
    calc S * sin e ≤ S * e := mul_le_mul_of_nonneg_left h1 hS0
      _ ≤ (π / 2) * e := mul_le_mul_of_nonneg_right hS he0
  have hpoly : (π / 2) * e < (1 - e ^ 2 / 2) * (1 - (2 * e) ^ 2 / 2) := by
    have : (π / 2) * e ≤ 1.5708 * e := by nlinarith
    nlinarith [mul_nonneg he0 (sub_nonneg.2 he'), mul_nonneg (mul_nonneg he0 he0) (sub_nonneg.2 he'),
      mul_nonneg (mul_nonneg he0 he0) (mul_nonneg he0 (sub_nonneg.2 he'))]
  have hpos1 : 0 ≤ 1 - e ^ 2 / 2 := by nlinarith
  have hpos2 : 0 ≤ 1 - (2 * e) ^ 2 / 2 := by nlinarith
  calc S * sin e ≤ (π / 2) * e := hA
    _ < (1 - e ^ 2 / 2) * (1 - (2 * e) ^ 2 / 2) := hpoly
    _ ≤ cos e * cos (2 * e) := mul_le_mul h2 h3 hpos2 (le_trans hpos1 h2)

theorem merge_ineq_half (A B T Q : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hAB : A + B ≤ π / 8)
    (hT : 0 ≤ T) (hS : sin (2 * A) + sin (2 * B) + T ≤ π / 2) :
    (sin (2 * A) + sin (2 * B) + T) ^ 2 + sin (2 * A) ^ 2 + sin (2 * B) ^ 2 + Q
      ≤ (sin (2 * A + 2 * B) + T) ^ 2 + sin (2 * A + 2 * B) ^ 2 + Q ∧
    (0 < A → 0 < B →
      (sin (2 * A) + sin (2 * B) + T) ^ 2 + sin (2 * A) ^ 2 + sin (2 * B) ^ 2 + Q
        < (sin (2 * A + 2 * B) + T) ^ 2 + sin (2 * A + 2 * B) ^ 2 + Q) := by
  have hpi := Real.pi_pos
  have he0 : 0 ≤ A + B := by linarith
  have hsA : 0 ≤ sin A := Real.sin_nonneg_of_nonneg_of_le_pi hA0 (by linarith)
  have hsB : 0 ≤ sin B := Real.sin_nonneg_of_nonneg_of_le_pi hB0 (by linarith)
  have hcA : 0 ≤ cos A := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hcB : 0 ≤ cos B := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsa : 0 ≤ sin (2 * A) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsb : 0 ≤ sin (2 * B) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hS0 : 0 ≤ sin (2 * A) + sin (2 * B) + T := by linarith
  have hA1 : sin A ^ 2 + cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
  have hB1 : sin B ^ 2 + cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
  have hδ : sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B) = 4 * sin A * sin B * sin (A + B) := by
    rw [Real.sin_add (2 * A) (2 * B), Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul,
      Real.cos_two_mul, Real.sin_add]
    linear_combination (-4 * sin B * cos B) * hA1 + (-4 * sin A * cos A) * hB1
  have hcab : cos (2 * A + 2 * B) = cos (2 * (A + B)) := by ring_nf
  have hsq : sin (2 * A + 2 * B) ^ 2 - sin (2 * A) ^ 2 - sin (2 * B) ^ 2
      = 2 * sin (2 * A) * sin (2 * B) * cos (2 * A + 2 * B) := by
    rw [Real.sin_add, Real.cos_add]
    have h1 := Real.sin_sq_add_cos_sq (2 * A)
    have h2 := Real.sin_sq_add_cos_sq (2 * B)
    nlinarith [h1, h2]
  have hnum := merge_num (A + B) (sin (2 * A) + sin (2 * B) + T) he0 hAB hS0 hS
  have hcAcB : cos (A + B) ≤ cos A * cos B := by
    rw [Real.cos_add]; nlinarith [mul_nonneg hsA hsB]
  have hc2 : 0 ≤ cos (2 * (A + B)) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsAB : 0 ≤ sin (A + B) := Real.sin_nonneg_of_nonneg_of_le_pi he0 (by linarith)
  have h4 : 0 ≤ 4 * sin A * sin B := by positivity
  have hδ0 : 0 ≤ sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B) := by
    rw [hδ]; exact mul_nonneg h4 hsAB
  have e1 : sin (2 * A) * sin (2 * B) * cos (2 * A + 2 * B)
      = 4 * sin A * sin B * (cos A * cos B * cos (2 * (A + B))) := by
    rw [hcab, Real.sin_two_mul, Real.sin_two_mul]; ring
  have h5 : (sin (2 * A) + sin (2 * B) + T) * sin (A + B) < cos A * cos B * cos (2 * (A + B)) :=
    lt_of_lt_of_le hnum (by nlinarith [mul_le_mul_of_nonneg_right hcAcB hc2])
  have key : (sin (2 * A) + sin (2 * B) + T) * (sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B))
      ≤ sin (2 * A) * sin (2 * B) * cos (2 * A + 2 * B) := by
    rw [e1, hδ]
    have := mul_le_mul_of_nonneg_left h5.le h4
    linarith
  have hid : (sin (2 * A + 2 * B) + T) ^ 2 + sin (2 * A + 2 * B) ^ 2 + Q
      = (sin (2 * A) + sin (2 * B) + T) ^ 2 + sin (2 * A) ^ 2 + sin (2 * B) ^ 2 + Q
        + 2 * (sin (2 * A) * sin (2 * B) * cos (2 * A + 2 * B)
          - (sin (2 * A) + sin (2 * B) + T) * (sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B)))
        + (sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B)) ^ 2 := by
    linear_combination hsq
  constructor
  · rw [hid]; linarith [key, sq_nonneg (sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B))]
  · intro hApos hBpos
    have hsApos : 0 < sin A := Real.sin_pos_of_pos_of_lt_pi hApos (by linarith)
    have hsBpos : 0 < sin B := Real.sin_pos_of_pos_of_lt_pi hBpos (by linarith)
    have h4' : 0 < 4 * sin A * sin B := by positivity
    have key' : (sin (2 * A) + sin (2 * B) + T) * (sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B))
        < sin (2 * A) * sin (2 * B) * cos (2 * A + 2 * B) := by
      rw [e1, hδ]
      have := mul_lt_mul_of_pos_left h5 h4'
      linarith
    rw [hid]; linarith [key', sq_nonneg (sin (2 * A) + sin (2 * B) - sin (2 * A + 2 * B))]

/-- Merging two angles of total at most `π/4` does not decrease `G`, and increases it
strictly when both angles are positive. -/
theorem merge_ineq (a b T Q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ π / 4) (hT : 0 ≤ T)
    (hS : sin a + sin b + T ≤ π / 2) :
    (sin a + sin b + T) ^ 2 + sin a ^ 2 + sin b ^ 2 + Q
      ≤ (sin (a + b) + T) ^ 2 + sin (a + b) ^ 2 + Q ∧
    (0 < a → 0 < b → (sin a + sin b + T) ^ 2 + sin a ^ 2 + sin b ^ 2 + Q
      < (sin (a + b) + T) ^ 2 + sin (a + b) ^ 2 + Q) := by
  have h := merge_ineq_half (a / 2) (b / 2) T Q (by linarith) (by linarith) (by linarith) hT
    (by rwa [mul_div_cancel₀ _ (two_ne_zero), mul_div_cancel₀ _ (two_ne_zero)])
  rw [mul_div_cancel₀ _ (two_ne_zero), mul_div_cancel₀ _ (two_ne_zero)] at h
  refine ⟨h.1, fun ha' hb' => h.2 (by linarith) (by linarith)⟩

/-- `G(β) = (∑ sin β_k)² + ∑ sin² β_k` for a list of angles. -/
noncomputable def Glist (l : List ℝ) : ℝ :=
  (l.map sin).sum ^ 2 + (l.map (fun x => sin x ^ 2)).sum

theorem sin_sum_le (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x) : (l.map sin).sum ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have := Real.sin_le (hl a (by simp))
    have := ih (fun x hx => hl x (by simp [hx]))
    linarith

theorem sin_sum_nonneg (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x) (hs : l.sum ≤ π / 2) :
    0 ≤ (l.map sin).sum := by
  have hpi := Real.pi_pos
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons] at hs ⊢
    have ha := hl a (by simp)
    have ht : 0 ≤ t.sum := List.sum_nonneg (fun x hx => hl x (by simp [hx]))
    have h1 : 0 ≤ sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith)
    have := ih (fun x hx => hl x (by simp [hx])) (by linarith)
    linarith

theorem Glist_le (n : ℕ) : ∀ l : List ℝ, l.length = n → (∀ x ∈ l, 0 ≤ x) → l.sum ≤ π / 2 →
    Glist l ≤ 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen hnn hsum
    have hpi := Real.pi_pos
    match l, hlen, hnn, hsum with
    | [], _, _, _ => simp [Glist]
    | [a], _, hnn, hsum =>
      have := G3_le a 0 0 (hnn a (by simp)) le_rfl le_rfl (by simpa using hsum)
      simp only [Glist, G3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        Real.sin_zero] at this ⊢
      nlinarith [this]
    | [a, b], _, hnn, hsum =>
      have := G3_le a b 0 (hnn a (by simp)) (hnn b (by simp)) le_rfl (by simpa using hsum)
      simp only [Glist, G3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        Real.sin_zero] at this ⊢
      nlinarith [this]
    | [a, b, c], _, hnn, hsum =>
      have := G3_le a b c (hnn a (by simp)) (hnn b (by simp)) (hnn c (by simp))
        (by simpa [add_assoc] using hsum)
      simp only [Glist, G3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at this ⊢
      nlinarith [this]
    | a :: b :: c :: d :: rest, hlen, hnn, hsum =>
      have ha := hnn a (by simp)
      have hb := hnn b (by simp)
      have hc := hnn c (by simp)
      have hd := hnn d (by simp)
      have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => hnn x (by simp [hx])
      have hrs : 0 ≤ rest.sum := List.sum_nonneg hrest
      have hsum' : a + b + c + d + rest.sum ≤ π / 2 := by
        simp only [List.sum_cons] at hsum; linarith
      -- sines
      have hsin : ∀ x, 0 ≤ x → x ≤ π / 2 → 0 ≤ sin x := fun x h0 h1 =>
        Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
      have hsa := hsin a ha (by linarith)
      have hsb := hsin b hb (by linarith)
      have hsc := hsin c hc (by linarith)
      have hsd := hsin d hd (by linarith)
      have hT : 0 ≤ (rest.map sin).sum :=
        sin_sum_nonneg rest hrest (by linarith)
      have hTle : (rest.map sin).sum ≤ rest.sum := sin_sum_le rest hrest
      have hsa' := Real.sin_le ha
      have hsb' := Real.sin_le hb
      have hsc' := Real.sin_le hc
      have hsd' := Real.sin_le hd
      have hlenr : rest.length + 4 = n := by simpa using hlen
      have hG : Glist (a :: b :: c :: d :: rest)
          = (sin a + sin b + sin c + sin d + (rest.map sin).sum) ^ 2 + sin a ^ 2 + sin b ^ 2
            + sin c ^ 2 + sin d ^ 2 + (rest.map (fun x => sin x ^ 2)).sum := by
        simp only [Glist, List.map_cons, List.sum_cons]; ring
      rcases le_or_gt (a + b) (π / 4) with hab | hab
      · -- merge a and b
        have hlen' : (((a + b) :: c :: d :: rest)).length < n := by simp; omega
        have hnn' : ∀ x ∈ ((a + b) :: c :: d :: rest), 0 ≤ x := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · linarith
          · exact hc
          · exact hd
          · exact hrest x hx
        have hsum'' : (((a + b) :: c :: d :: rest)).sum ≤ π / 2 := by
          simp only [List.sum_cons]; linarith
        have h1 := ih _ hlen' _ rfl hnn' hsum''
        have h2 := (merge_ineq a b (sin c + sin d + (rest.map sin).sum)
          (sin c ^ 2 + sin d ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) ha hb hab
          (by linarith) (by linarith)).1
        have hG' : Glist ((a + b) :: c :: d :: rest)
            = (sin (a + b) + (sin c + sin d + (rest.map sin).sum)) ^ 2 + sin (a + b) ^ 2
              + (sin c ^ 2 + sin d ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) := by
          simp only [Glist, List.map_cons, List.sum_cons]; ring
        rw [hG]
        rw [hG'] at h1
        nlinarith [h1, h2]
      · have hcd : c + d ≤ π / 4 := by linarith
        have hlen' : ((a :: b :: (c + d) :: rest)).length < n := by simp; omega
        have hnn' : ∀ x ∈ (a :: b :: (c + d) :: rest), 0 ≤ x := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · exact ha
          · exact hb
          · linarith
          · exact hrest x hx
        have hsum'' : ((a :: b :: (c + d) :: rest)).sum ≤ π / 2 := by
          simp only [List.sum_cons]; linarith
        have h1 := ih _ hlen' _ rfl hnn' hsum''
        have h2 := (merge_ineq c d (sin a + sin b + (rest.map sin).sum)
          (sin a ^ 2 + sin b ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) hc hd hcd
          (by linarith) (by linarith)).1
        have hG' : Glist (a :: b :: (c + d) :: rest)
            = (sin (c + d) + (sin a + sin b + (rest.map sin).sum)) ^ 2 + sin (c + d) ^ 2
              + (sin a ^ 2 + sin b ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) := by
          simp only [Glist, List.map_cons, List.sum_cons]; ring
        rw [hG]
        rw [hG'] at h1
        nlinarith [h1, h2]

theorem Glist_perm {l₁ l₂ : List ℝ} (h : l₁.Perm l₂) : Glist l₁ = Glist l₂ := by
  unfold Glist
  rw [(h.map sin).sum_eq, (h.map (fun x => sin x ^ 2)).sum_eq]

theorem Glist_erase_zero (l : List ℝ) (h0 : (0 : ℝ) ∈ l) :
    Glist (l.erase 0) = Glist l ∧ (l.erase 0).sum = l.sum ∧ (l.erase 0).length + 1 = l.length := by
  have hp := List.perm_cons_erase h0
  refine ⟨?_, ?_, ?_⟩
  · rw [Glist_perm hp]; simp [Glist]
  · rw [hp.sum_eq]; simp
  · rw [List.length_erase_of_mem h0]
    have : 0 < l.length := List.length_pos_of_mem h0
    omega

/-- Equality in `G ≤ 3`: every angle is `0` or `π/4`, or every angle is `0` or `π/6`. -/
theorem Glist_eq (n : ℕ) : ∀ l : List ℝ, l.length = n → (∀ x ∈ l, 0 ≤ x) → l.sum ≤ π / 2 →
    Glist l = 3 → (∀ x ∈ l, x = 0 ∨ x = π / 4) ∨ (∀ x ∈ l, x = 0 ∨ x = π / 6) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen hnn hsum hG3
    have hpi := Real.pi_pos
    match l, hlen, hnn, hsum, hG3 with
    | [], _, _, _, hG3 => simp [Glist] at hG3
    | [a], _, hnn, hsum, hG3 =>
      exfalso
      have := G3_le a 0 0 (hnn a (by simp)) le_rfl le_rfl (by simpa using hsum)
      have e : Glist [a] = G3 a 0 0 := by
        simp only [Glist, G3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, Real.sin_zero]
        ring
      have h2 := Real.sin_sq_add_cos_sq a
      unfold G3 at e
      rw [hG3] at e
      simp only [Real.sin_zero] at e
      nlinarith [sq_nonneg (cos a)]
    | [a, b], _, hnn, hsum, hG3 =>
      have e : Glist [a, b] = G3 a b 0 := by
        simp only [Glist, G3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, Real.sin_zero]
        ring
      rw [e] at hG3
      rcases G3_le_eq a b 0 (hnn a (by simp)) (hnn b (by simp)) le_rfl (by simpa using hsum) hG3
        with ⟨_, _, h3⟩ | ⟨h1, h2, _⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
      · exfalso; linarith
      · left; intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [h1, h2]
      · exfalso; linarith
      · exfalso; linarith
    | [a, b, c], _, hnn, hsum, hG3 =>
      have e : Glist [a, b, c] = G3 a b c := by
        simp only [Glist, G3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
        ring
      rw [e] at hG3
      rcases G3_le_eq a b c (hnn a (by simp)) (hnn b (by simp)) (hnn c (by simp))
        (by simpa [add_assoc] using hsum) hG3
        with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · right; intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [h1, h2, h3]
      · left; intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [h1, h2, h3]
      · left; intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [h1, h2, h3]
      · left; intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [h1, h2, h3]
    | a :: b :: c :: d :: rest, hlen, hnn, hsum, hG3 =>
      have ha := hnn a (by simp)
      have hb := hnn b (by simp)
      have hc := hnn c (by simp)
      have hd := hnn d (by simp)
      have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => hnn x (by simp [hx])
      have hrs : 0 ≤ rest.sum := List.sum_nonneg hrest
      have hsum' : a + b + c + d + rest.sum ≤ π / 2 := by
        simp only [List.sum_cons] at hsum; linarith
      have hsin : ∀ x, 0 ≤ x → x ≤ π / 2 → 0 ≤ sin x := fun x h0 h1 =>
        Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
      have hsa := hsin a ha (by linarith)
      have hsb := hsin b hb (by linarith)
      have hsc := hsin c hc (by linarith)
      have hsd := hsin d hd (by linarith)
      have hT : 0 ≤ (rest.map sin).sum := sin_sum_nonneg rest hrest (by linarith)
      have hTle : (rest.map sin).sum ≤ rest.sum := sin_sum_le rest hrest
      have hsa' := Real.sin_le ha
      have hsb' := Real.sin_le hb
      have hsc' := Real.sin_le hc
      have hsd' := Real.sin_le hd
      have hlenr : rest.length + 4 = n := by simpa using hlen
      have hG : Glist (a :: b :: c :: d :: rest)
          = (sin a + sin b + sin c + sin d + (rest.map sin).sum) ^ 2 + sin a ^ 2 + sin b ^ 2
            + sin c ^ 2 + sin d ^ 2 + (rest.map (fun x => sin x ^ 2)).sum := by
        simp only [Glist, List.map_cons, List.sum_cons]; ring
      rcases le_or_gt (a + b) (π / 4) with hab | hab
      · have hlen' : (((a + b) :: c :: d :: rest)).length < n := by simp; omega
        have hnn' : ∀ x ∈ ((a + b) :: c :: d :: rest), 0 ≤ x := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · linarith
          · exact hc
          · exact hd
          · exact hrest x hx
        have hsum'' : (((a + b) :: c :: d :: rest)).sum ≤ π / 2 := by
          simp only [List.sum_cons]; linarith
        have h1 := Glist_le _ _ rfl hnn' hsum''
        obtain ⟨h2, h2s⟩ := merge_ineq a b (sin c + sin d + (rest.map sin).sum)
          (sin c ^ 2 + sin d ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) ha hb hab
          (by linarith) (by linarith)
        have hG' : Glist ((a + b) :: c :: d :: rest)
            = (sin (a + b) + (sin c + sin d + (rest.map sin).sum)) ^ 2 + sin (a + b) ^ 2
              + (sin c ^ 2 + sin d ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) := by
          simp only [Glist, List.map_cons, List.sum_cons]; ring
        rw [hG'] at h1
        have hnotboth : ¬ (0 < a ∧ 0 < b) := by
          rintro ⟨hapos, hbpos⟩
          have := h2s hapos hbpos
          rw [hG] at hG3
          nlinarith [this, h1]
        have hab0 : a = 0 ∨ b = 0 := by
          by_contra hcon
          push Not at hcon
          exact hnotboth ⟨lt_of_le_of_ne ha (Ne.symm hcon.1), lt_of_le_of_ne hb (Ne.symm hcon.2)⟩
        have h0 : (0 : ℝ) ∈ (a :: b :: c :: d :: rest) := by
          rcases hab0 with h | h
          · simp [h]
          · simp [h]
        obtain ⟨hGe, hse, hle⟩ := Glist_erase_zero _ h0
        have hsub : ∀ x ∈ (a :: b :: c :: d :: rest).erase 0, x ∈ (a :: b :: c :: d :: rest) :=
          fun x hx => List.mem_of_mem_erase hx
        have := ih _ (by simp at hle hlen ⊢; omega) _ rfl (fun x hx => hnn x (hsub x hx))
          (by rw [hse]; exact hsum) (by rw [hGe]; exact hG3)
        rcases this with h | h
        · left; intro x hx
          by_cases hx0 : x = 0
          · left; exact hx0
          · exact h x (List.mem_erase_of_ne hx0 |>.2 hx)
        · right; intro x hx
          by_cases hx0 : x = 0
          · left; exact hx0
          · exact h x (List.mem_erase_of_ne hx0 |>.2 hx)
      · have hcd : c + d ≤ π / 4 := by linarith
        have hlen' : ((a :: b :: (c + d) :: rest)).length < n := by simp; omega
        have hnn' : ∀ x ∈ (a :: b :: (c + d) :: rest), 0 ≤ x := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · exact ha
          · exact hb
          · linarith
          · exact hrest x hx
        have hsum'' : ((a :: b :: (c + d) :: rest)).sum ≤ π / 2 := by
          simp only [List.sum_cons]; linarith
        have h1 := Glist_le _ _ rfl hnn' hsum''
        obtain ⟨h2, h2s⟩ := merge_ineq c d (sin a + sin b + (rest.map sin).sum)
          (sin a ^ 2 + sin b ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) hc hd hcd
          (by linarith) (by linarith)
        have hG' : Glist (a :: b :: (c + d) :: rest)
            = (sin (c + d) + (sin a + sin b + (rest.map sin).sum)) ^ 2 + sin (c + d) ^ 2
              + (sin a ^ 2 + sin b ^ 2 + (rest.map (fun x => sin x ^ 2)).sum) := by
          simp only [Glist, List.map_cons, List.sum_cons]; ring
        rw [hG'] at h1
        have hnotboth : ¬ (0 < c ∧ 0 < d) := by
          rintro ⟨hcpos, hdpos⟩
          have := h2s hcpos hdpos
          rw [hG] at hG3
          nlinarith [this, h1]
        have hcd0 : c = 0 ∨ d = 0 := by
          by_contra hcon
          push Not at hcon
          exact hnotboth ⟨lt_of_le_of_ne hc (Ne.symm hcon.1), lt_of_le_of_ne hd (Ne.symm hcon.2)⟩
        have h0 : (0 : ℝ) ∈ (a :: b :: c :: d :: rest) := by
          rcases hcd0 with h | h
          · simp [h]
          · simp [h]
        obtain ⟨hGe, hse, hle⟩ := Glist_erase_zero _ h0
        have hsub : ∀ x ∈ (a :: b :: c :: d :: rest).erase 0, x ∈ (a :: b :: c :: d :: rest) :=
          fun x hx => List.mem_of_mem_erase hx
        have := ih _ (by simp at hle hlen ⊢; omega) _ rfl (fun x hx => hnn x (hsub x hx))
          (by rw [hse]; exact hsum) (by rw [hGe]; exact hG3)
        rcases this with h | h
        · left; intro x hx
          by_cases hx0 : x = 0
          · left; exact hx0
          · exact h x (List.mem_erase_of_ne hx0 |>.2 hx)
        · right; intro x hx
          by_cases hx0 : x = 0
          · left; exact hx0
          · exact h x (List.mem_erase_of_ne hx0 |>.2 hx)

/-- Vertex lemma: a point of the unit disc, seen from two edge directions turned by `δ ∈ [0, π]`. -/
theorem vertex_real (x y δ : ℝ) (h : x ^ 2 + y ^ 2 ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ π) :
    arcsin x + arcsin (-(x * cos δ + y * sin δ)) ≤ δ := by
  have hpi := Real.pi_pos
  have hx1 : x ≤ 1 := by nlinarith
  have hx2 : -1 ≤ x := by nlinarith
  set A := arcsin x with hA
  have hsA : sin A = x := Real.sin_arcsin hx2 hx1
  have hcA : cos A = √(1 - x ^ 2) := Real.cos_arcsin x
  have hAle : A ≤ π / 2 := Real.arcsin_le_pi_div_two x
  have hAge : -(π / 2) ≤ A := Real.neg_pi_div_two_le_arcsin x
  have hsd : 0 ≤ sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ0 hδ1
  have hy : |y| ≤ √(1 - x ^ 2) := by
    apply Real.abs_le_sqrt; nlinarith
  have hw : -(x * cos δ + y * sin δ) ≤ sin (δ - A) := by
    rw [Real.sin_sub, hsA, hcA]
    have : -y ≤ √(1 - x ^ 2) := by linarith [neg_abs_le y]
    nlinarith [mul_le_mul_of_nonneg_right this hsd]
  by_cases hcase : δ - A ≤ π / 2
  · have hwb : -(x * cos δ + y * sin δ) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> nlinarith [sq_nonneg (x * sin δ - y * cos δ), Real.sin_sq_add_cos_sq δ]
    have := (Real.arcsin_le_iff_le_sin hwb ⟨by linarith, hcase⟩).2 hw
    linarith
  · have := Real.arcsin_le_pi_div_two (-(x * cos δ + y * sin δ))
    linarith

/-- Edge lemma: a half-edge of length `a ≤ M` with endpoints' projections `p, q`. -/
theorem edge_real (p q M a : ℝ) (hM : 0 < M) (hp : |p| ≤ M) (hq : |q| ≤ M) (ha : 0 ≤ a)
    (hpq : 2 * a = p - q) :
    a ≤ M ∧ arcsin (a / M) ≤ (arcsin (p / M) + arcsin (-q / M)) / 2 := by
  have hpi := Real.pi_pos
  have hp1 : p / M ≤ 1 := by rw [div_le_one hM]; exact (le_abs_self p).trans hp
  have hp2 : -1 ≤ p / M := by
    rw [le_div_iff₀ hM]; linarith [neg_abs_le p]
  have hq1 : -q / M ≤ 1 := by rw [div_le_one hM]; linarith [neg_abs_le q]
  have hq2 : -1 ≤ -q / M := by
    rw [le_div_iff₀ hM]; linarith [le_abs_self q]
  set U' := arcsin (p / M) with hU'
  set U := arcsin (-q / M) with hU
  have hsU' : sin U' = p / M := Real.sin_arcsin hp2 hp1
  have hsU : sin U = -q / M := Real.sin_arcsin hq2 hq1
  have hU'a : U' ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hU'b : -(π / 2) ≤ U' := Real.neg_pi_div_two_le_arcsin _
  have hUa : U ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hUb : -(π / 2) ≤ U := Real.neg_pi_div_two_le_arcsin _
  have hsum : sin U' + sin U = 2 * a / M := by
    rw [hsU', hsU, hpq]; field_simp; ring
  have hsum0 : 0 ≤ sin U' + sin U := by rw [hsum]; positivity
  have hUU : 0 ≤ U + U' := by
    by_contra hneg
    have hneg := not_le.1 hneg
    have : U < -U' := by linarith
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) this
    rw [Real.sin_neg] at this
    linarith
  set y := (U + U') / 2 with hy
  set d := (U - U') / 2 with hd
  have hUy : U = y + d := by rw [hy, hd]; ring
  have hU'y : U' = y - d := by rw [hy, hd]; ring
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hy1 : y ≤ π / 2 := by rw [hy]; linarith
  have hd1 : |d| ≤ π / 2 := by rw [abs_le, hd]; constructor <;> linarith
  have hcd : 0 ≤ cos d := Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.1 hd1).1], by linarith [(abs_le.1 hd1).2]⟩
  have hcd1 : cos d ≤ 1 := Real.cos_le_one d
  have hsy : 0 ≤ sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith)
  have hsy1 : sin y ≤ 1 := Real.sin_le_one y
  have hprod : a / M = sin y * cos d := by
    have : sin U' + sin U = 2 * sin y * cos d := by
      rw [hUy, hU'y, Real.sin_add, Real.sin_sub]; ring
    have h2 : 2 * a / M = 2 * sin y * cos d := by rw [← hsum, this]
    have : a / M = sin y * cos d := by
      have : 2 * (a / M) = 2 * (sin y * cos d) := by
        rw [mul_div_assoc] at h2; linarith
      linarith
    exact this
  have hle1 : a / M ≤ 1 := by rw [hprod]; nlinarith
  constructor
  · rw [div_le_one hM] at hle1; exact hle1
  · have hle : a / M ≤ sin y := by rw [hprod]; nlinarith
    have := (Real.arcsin_le_iff_le_sin ⟨by rw [hprod]; nlinarith, hle1⟩ ⟨by linarith, hy1⟩).2 hle
    rw [hy] at this
    linarith

/-- Projection of the point `(x, y)` onto the direction at angle `σ`. -/
noncomputable def proj (x y σ : ℝ) : ℝ := x * cos σ + y * sin σ

theorem proj_abs_le (x y σ M : ℝ) (hM : 0 ≤ M) (h : x ^ 2 + y ^ 2 ≤ M ^ 2) : |proj x y σ| ≤ M := by
  apply abs_le_of_sq_le_sq _ hM
  unfold proj
  nlinarith [sq_nonneg (x * sin σ - y * cos σ), Real.sin_sq_add_cos_sq σ]

theorem proj_vertex (x y σ δ M : ℝ) (hM : 0 < M) (h : x ^ 2 + y ^ 2 ≤ M ^ 2) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ π) :
    arcsin (proj x y σ / M) + arcsin (-proj x y (σ + δ) / M) ≤ δ := by
  have key := vertex_real ((x * cos σ + y * sin σ) / M) ((-x * sin σ + y * cos σ) / M) δ
    (by
      have : ((x * cos σ + y * sin σ) / M) ^ 2 + ((-x * sin σ + y * cos σ) / M) ^ 2
          = (x ^ 2 + y ^ 2) / M ^ 2 := by
        field_simp
        nlinarith [Real.sin_sq_add_cos_sq σ]
      rw [this, div_le_one (by positivity)]; exact h) hδ0 hδ1
  have e : -proj x y (σ + δ) / M
      = -(((x * cos σ + y * sin σ) / M) * cos δ + ((-x * sin σ + y * cos σ) / M) * sin δ) := by
    unfold proj
    rw [Real.cos_add, Real.sin_add]
    field_simp
    ring
  rw [e]
  exact key

/-- `proj` flips sign under `σ ↦ σ - π`. -/
theorem proj_sub_pi (x y σ : ℝ) : proj x y (σ - π) = -proj x y σ := by
  unfold proj
  rw [Real.cos_sub_pi, Real.sin_sub_pi]; ring

/-- Signed partial sums of `x`-components along an ordered family: `vx n k = ∑_{j<n} s_k(j) a_j cos θ_j`
with `s_k(j) = +1` for `j < k` and `-1` otherwise. -/
noncomputable def vx (A Θ : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (if j < k then (1 : ℝ) else -1) * (A j * cos (Θ j))

noncomputable def vy (A Θ : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (if j < k then (1 : ℝ) else -1) * (A j * sin (Θ j))

theorem vx_succ (A Θ : ℕ → ℝ) (n k : ℕ) (hk : k < n) :
    vx A Θ n (k + 1) = vx A Θ n k + 2 * (A k * cos (Θ k)) := by
  unfold vx
  have : ∀ j ∈ Finset.range n, (if j < k + 1 then (1 : ℝ) else -1) * (A j * cos (Θ j))
      = (if j < k then (1 : ℝ) else -1) * (A j * cos (Θ j)) + (if j = k then 2 else 0) * (A j * cos (Θ j)) := by
    intro j _
    by_cases h1 : j < k
    · have : ¬ j = k := by omega
      simp [h1, this, show j < k + 1 by omega]
    · by_cases h2 : j = k
      · subst h2; simp; ring
      · have : ¬ j < k + 1 := by omega
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.2 hk) h

theorem vy_succ (A Θ : ℕ → ℝ) (n k : ℕ) (hk : k < n) :
    vy A Θ n (k + 1) = vy A Θ n k + 2 * (A k * sin (Θ k)) := by
  unfold vy
  have : ∀ j ∈ Finset.range n, (if j < k + 1 then (1 : ℝ) else -1) * (A j * sin (Θ j))
      = (if j < k then (1 : ℝ) else -1) * (A j * sin (Θ j)) + (if j = k then 2 else 0) * (A j * sin (Θ j)) := by
    intro j _
    by_cases h1 : j < k
    · have : ¬ j = k := by omega
      simp [h1, this, show j < k + 1 by omega]
    · by_cases h2 : j = k
      · subst h2; simp; ring
      · have : ¬ j < k + 1 := by omega
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.2 hk) h

theorem vx_last (A Θ : ℕ → ℝ) (n : ℕ) : vx A Θ n n = - vx A Θ n 0 := by
  unfold vx
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have := Finset.mem_range.1 hj
  simp [this]

theorem vy_last (A Θ : ℕ → ℝ) (n : ℕ) : vy A Θ n n = - vy A Θ n 0 := by
  unfold vy
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have := Finset.mem_range.1 hj
  simp [this]

theorem arcsin_sum_le (n : ℕ) (A Θ : ℕ → ℝ) (M : ℝ) (hM : 0 < M)
    (hA : ∀ j < n, 0 ≤ A j)
    (hmono : ∀ i j, i ≤ j → j < n → Θ i ≤ Θ j)
    (hspan : ∀ i j, i < n → j < n → Θ j ≤ Θ i + π)
    (hX : ∀ k ≤ n, vx A Θ n k ^ 2 + vy A Θ n k ^ 2 ≤ M ^ 2) :
    (∀ j < n, A j ≤ M) ∧ ∑ j ∈ Finset.range n, arcsin (A j / M) ≤ π / 2 := by
  have hpi := Real.pi_pos
  -- edge data
  have hedge : ∀ k < n, A k ≤ M ∧ arcsin (A k / M) ≤
      (arcsin (proj (vx A Θ n (k + 1)) (vy A Θ n (k + 1)) (Θ k) / M)
        + arcsin (-proj (vx A Θ n k) (vy A Θ n k) (Θ k) / M)) / 2 := by
    intro k hk
    apply edge_real _ _ M _ hM
    · exact proj_abs_le _ _ _ M hM.le (hX (k + 1) (by omega))
    · exact proj_abs_le _ _ _ M hM.le (hX k (by omega))
    · exact hA k hk
    · unfold proj
      rw [vx_succ A Θ n k hk, vy_succ A Θ n k hk]
      linear_combination (-(2 * A k)) * Real.sin_sq_add_cos_sq (Θ k)
  refine ⟨fun j hj => (hedge j hj).1, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ k, u k
      = arcsin (-proj (vx A Θ (m + 1) k) (vy A Θ (m + 1) k) (Θ k) / M) := ⟨_, fun _ => rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : ℕ → ℝ, ∀ k, u' k
      = arcsin (proj (vx A Θ (m + 1) (k + 1)) (vy A Θ (m + 1) (k + 1)) (Θ k) / M) :=
    ⟨_, fun _ => rfl⟩
  have hsum1 : ∑ k ∈ Finset.range (m + 1), arcsin (A k / M)
      ≤ ∑ k ∈ Finset.range (m + 1), (u' k + u k) / 2 := by
    apply Finset.sum_le_sum
    intro k hk
    have := (hedge k (Finset.mem_range.1 hk)).2
    rw [hu, hu']; exact this
  -- interior vertices
  have hint : ∀ j < m, u (j + 1) + u' j ≤ Θ (j + 1) - Θ j := by
    intro j hj
    have hd0 : 0 ≤ Θ (j + 1) - Θ j := by
      have := hmono j (j + 1) (by omega) (by omega); linarith
    have hd1 : Θ (j + 1) - Θ j ≤ π := by
      have := hspan j (j + 1) (by omega) (by omega); linarith
    have := proj_vertex (vx A Θ (m + 1) (j + 1)) (vy A Θ (m + 1) (j + 1)) (Θ j)
      (Θ (j + 1) - Θ j) M hM (hX (j + 1) (by omega)) hd0 hd1
    rw [show Θ j + (Θ (j + 1) - Θ j) = Θ (j + 1) by ring] at this
    rw [hu, hu']; linarith
  -- boundary vertex
  have hbd : u 0 + u' m ≤ Θ 0 - Θ m + π := by
    have hd0 : 0 ≤ Θ 0 - Θ m + π := by
      have := hspan 0 m (by omega) (by omega); linarith
    have hd1 : Θ 0 - Θ m + π ≤ π := by
      have := hmono 0 m (by omega) (by omega); linarith
    have := proj_vertex (vx A Θ (m + 1) 0) (vy A Θ (m + 1) 0) (Θ m - π)
      (Θ 0 - Θ m + π) M hM (hX 0 (by omega)) hd0 hd1
    rw [show Θ m - π + (Θ 0 - Θ m + π) = Θ 0 by ring, proj_sub_pi] at this
    have e : proj (vx A Θ (m + 1) (m + 1)) (vy A Θ (m + 1) (m + 1)) (Θ m)
        = -proj (vx A Θ (m + 1) 0) (vy A Θ (m + 1) 0) (Θ m) := by
      unfold proj
      rw [vx_last, vy_last]; ring
    rw [hu, hu', e]
    have : -(-proj (vx A Θ (m + 1) 0) (vy A Θ (m + 1) 0) (Θ m)) / M
        = proj (vx A Θ (m + 1) 0) (vy A Θ (m + 1) 0) (Θ m) / M := by ring
    linarith [this]
  have hsplit : ∑ k ∈ Finset.range (m + 1), (u' k + u k) / 2
      = ((u 0 + u' m) + ∑ j ∈ Finset.range m, (u (j + 1) + u' j)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_range_succ' u,
      Finset.sum_range_succ u', Finset.sum_add_distrib]
    ring
  have htel : ∑ j ∈ Finset.range m, (Θ (j + 1) - Θ j) = Θ m - Θ 0 := Finset.sum_range_sub Θ m
  have hsumint : ∑ j ∈ Finset.range m, (u (j + 1) + u' j)
      ≤ ∑ j ∈ Finset.range m, (Θ (j + 1) - Θ j) :=
    Finset.sum_le_sum (fun j hj => hint j (Finset.mem_range.1 hj))
  rw [hsplit] at hsum1
  linarith

theorem list_range_sum (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The list of inscribed angles `β_j = arcsin (a_j / M)` of an ordered polygon. -/
theorem seq_data (n : ℕ) (A Θ : ℕ → ℝ) (M : ℝ) (hM : 0 < M)
    (hA : ∀ j < n, 0 ≤ A j)
    (hmono : ∀ i j, i ≤ j → j < n → Θ i ≤ Θ j)
    (hspan : ∀ i j, i < n → j < n → Θ j ≤ Θ i + π)
    (hX : ∀ k ≤ n, vx A Θ n k ^ 2 + vy A Θ n k ^ 2 ≤ M ^ 2) :
    ∃ l : List ℝ, (∀ x ∈ l, 0 ≤ x) ∧ l.sum ≤ π / 2 ∧
      Glist l * M ^ 2 = (∑ j ∈ Finset.range n, A j) ^ 2 + ∑ j ∈ Finset.range n, A j ^ 2 ∧
      (∀ j < n, arcsin (A j / M) ∈ l) ∧ (∀ j < n, sin (arcsin (A j / M)) = A j / M) := by
  obtain ⟨hAM, hsum⟩ := arcsin_sum_le n A Θ M hM hA hmono hspan hX
  have hb : ∀ j ∈ Finset.range n, A j / M ∈ Set.Icc (-1 : ℝ) 1 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    constructor
    · have : 0 ≤ A j / M := div_nonneg (hA j hj') hM.le
      linarith
    · rw [div_le_one hM]; exact hAM j hj'
  have hnn : ∀ x ∈ (List.range n).map (fun j => arcsin (A j / M)), 0 ≤ x := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact Real.arcsin_nonneg.2 (div_nonneg (hA j (List.mem_range.1 hj)) hM.le)
  have hl : ((List.range n).map (fun j => arcsin (A j / M))).sum ≤ π / 2 := by
    rw [list_range_sum]; exact hsum
  refine ⟨(List.range n).map (fun j => arcsin (A j / M)), hnn, hl, ?_, ?_, ?_⟩
  · unfold Glist
    rw [List.map_map, List.map_map, list_range_sum, list_range_sum]
    have e1 : ∑ j ∈ Finset.range n, (sin ∘ fun j => arcsin (A j / M)) j = (∑ j ∈ Finset.range n, A j) / M := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Function.comp]
      exact Real.sin_arcsin (hb j hj).1 (hb j hj).2
    have e2 : ∑ j ∈ Finset.range n, ((fun x => sin x ^ 2) ∘ fun j => arcsin (A j / M)) j
        = (∑ j ∈ Finset.range n, A j ^ 2) / M ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Function.comp]
      rw [Real.sin_arcsin (hb j hj).1 (hb j hj).2, div_pow]
    rw [e1, e2, div_pow]
    field_simp
  · intro j hj
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  · intro j hj
    exact Real.sin_arcsin (hb j (Finset.mem_range.2 hj)).1 (hb j (Finset.mem_range.2 hj)).2

/-- The ordered-polygon inequality: `L² + Q ≤ 3 M²`. -/
theorem seq_bound (n : ℕ) (A Θ : ℕ → ℝ) (M : ℝ) (hM : 0 < M)
    (hA : ∀ j < n, 0 ≤ A j)
    (hmono : ∀ i j, i ≤ j → j < n → Θ i ≤ Θ j)
    (hspan : ∀ i j, i < n → j < n → Θ j ≤ Θ i + π)
    (hX : ∀ k ≤ n, vx A Θ n k ^ 2 + vy A Θ n k ^ 2 ≤ M ^ 2) :
    (∑ j ∈ Finset.range n, A j) ^ 2 + ∑ j ∈ Finset.range n, A j ^ 2 ≤ 3 * M ^ 2 := by
  obtain ⟨l, hnn, hl, hG, -, -⟩ := seq_data n A Θ M hM hA hmono hspan hX
  have := Glist_le _ l rfl hnn hl
  have hM2 : 0 < M ^ 2 := by positivity
  nlinarith

/-- Equality in the ordered-polygon inequality forces the moduli to be `0` or one common value:
`M/√2` (the square) or `M/2` (the regular hexagon). -/
theorem seq_eq (n : ℕ) (A Θ : ℕ → ℝ) (M : ℝ) (hM : 0 < M)
    (hA : ∀ j < n, 0 ≤ A j)
    (hmono : ∀ i j, i ≤ j → j < n → Θ i ≤ Θ j)
    (hspan : ∀ i j, i < n → j < n → Θ j ≤ Θ i + π)
    (hX : ∀ k ≤ n, vx A Θ n k ^ 2 + vy A Θ n k ^ 2 ≤ M ^ 2)
    (hΦ : (∑ j ∈ Finset.range n, A j) ^ 2 + ∑ j ∈ Finset.range n, A j ^ 2 = 3 * M ^ 2) :
    (∀ j < n, A j = 0 ∨ A j = M * (√2 / 2)) ∨ (∀ j < n, A j = 0 ∨ A j = M / 2) := by
  obtain ⟨l, hnn, hl, hG, hmem, hsin⟩ := seq_data n A Θ M hM hA hmono hspan hX
  have hM2 : 0 < M ^ 2 := by positivity
  have hG3 : Glist l = 3 := by
    have : Glist l * M ^ 2 = 3 * M ^ 2 := by rw [hG, hΦ]
    exact mul_right_cancel₀ hM2.ne' this
  have hdiv : ∀ j < n, A j = M * (A j / M) := by
    intro j _; field_simp
  rcases Glist_eq _ l rfl hnn hl hG3 with h | h
  · left
    intro j hj
    have h1 := h _ (hmem j hj)
    have h2 := hsin j hj
    rcases h1 with h1 | h1
    · left; rw [h1, Real.sin_zero] at h2
      rw [hdiv j hj, ← h2]; ring
    · right; rw [h1, Real.sin_pi_div_four] at h2
      rw [hdiv j hj, ← h2]
  · right
    intro j hj
    have h1 := h _ (hmem j hj)
    have h2 := hsin j hj
    rcases h1 with h1 | h1
    · left; rw [h1, Real.sin_zero] at h2
      rw [hdiv j hj, ← h2]; ring
    · right; rw [h1, Real.sin_pi_div_six] at h2
      rw [hdiv j hj, ← h2]; ring

/-- Every complex number is a real sign times a vector with argument in `[0, π)`. -/
theorem polar_halfplane (z : ℂ) : ∃ ε θ : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 ≤ θ ∧ θ < π ∧
    z = (ε : ℂ) * ((‖z‖ : ℂ) * ((cos θ : ℂ) + (sin θ : ℂ) * Complex.I)) := by
  have hz := Complex.norm_mul_cos_add_sin_mul_I z
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  by_cases hc : 0 ≤ z.arg ∧ z.arg < π
  · refine ⟨1, z.arg, Or.inl rfl, hc.1, hc.2, ?_⟩
    simp only [Complex.ofReal_one, one_mul]
    rw [← hz]; simp [Complex.ofReal_cos, Complex.ofReal_sin]
  · by_cases hneg : z.arg < 0
    · refine ⟨-1, z.arg + π, Or.inr rfl, by linarith, by linarith, ?_⟩
      rw [Real.cos_add_pi, Real.sin_add_pi]
      simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_cos,
        Complex.ofReal_sin]
      linear_combination (-1 : ℂ) * hz
    · have : z.arg = π := by
        have hc' : π ≤ z.arg := by
          by_contra hlt
          exact hc ⟨by linarith [not_lt.1 hneg], not_le.1 hlt⟩
        linarith
      refine ⟨-1, 0, Or.inr rfl, le_rfl, hpi, ?_⟩
      conv_lhs => rw [← hz]
      rw [this]
      simp

/-- Sorted polar data: the vertex sums of the polygon of an ordered family are signed sums. -/
theorem polar_sorted_seq {m : ℕ} (v : Fin m → ℂ) (ε θ : Fin m → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i < π) (hmono : Monotone θ)
    (hv : ∀ i, v i = (ε i : ℂ) * ((‖v i‖ : ℂ) * ((cos (θ i) : ℂ) + (sin (θ i) : ℂ) * Complex.I)))
    (M : ℝ)
    (hH : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v i‖ ≤ M) :
    ∃ A Θ : ℕ → ℝ, (∀ j < m, 0 ≤ A j) ∧ (∀ i j, i ≤ j → j < m → Θ i ≤ Θ j) ∧
      (∀ i j, i < m → j < m → Θ j ≤ Θ i + π) ∧
      (∀ k ≤ m, vx A Θ m k ^ 2 + vy A Θ m k ^ 2 ≤ M ^ 2) ∧
      (∀ i : Fin m, A i = ‖v i‖) := by
  have hpi := Real.pi_pos
  classical
  let A : ℕ → ℝ := fun j => if h : j < m then ‖v ⟨j, h⟩‖ else 0
  let Θ : ℕ → ℝ := fun j => if h : j < m then θ ⟨j, h⟩ else 0
  have hAi : ∀ i : Fin m, A i = ‖v i‖ := by intro i; simp [A, i.isLt]
  have hΘi : ∀ i : Fin m, Θ i = θ i := by intro i; simp [Θ, i.isLt]
  refine ⟨A, Θ, ?_, ?_, ?_, ?_, hAi⟩
  · intro j hj; simp only [A, hj, ↓reduceDIte]; exact norm_nonneg _
  · intro i j hij hj
    have hi : i < m := lt_of_le_of_lt hij hj
    simp only [Θ, hi, hj, ↓reduceDIte]
    exact hmono (Fin.mk_le_mk.2 hij)
  · intro i j hi hj
    simp only [Θ, hi, hj, ↓reduceDIte]
    linarith [hθ0 ⟨i, hi⟩, hθ1 ⟨j, hj⟩]
  · intro k hk
    let t : Fin m → ℝ := fun i => if (i : ℕ) < k then 1 else -1
    let s : Fin m → ℝ := fun i => ε i * t i
    have hs : ∀ i, s i = 1 ∨ s i = -1 := by
      intro i
      simp only [s, t]
      rcases hε i with h | h <;> split_ifs <;> simp [h]
    have hZ := hH s hs
    have hterm : ∀ i, (s i : ℂ) * v i
        = ((t i * (‖v i‖ * cos (θ i)) : ℝ) : ℂ) + ((t i * (‖v i‖ * sin (θ i)) : ℝ) : ℂ) * Complex.I := by
      intro i
      have h1 : (ε i) * (ε i) = 1 := by rcases hε i with h | h <;> simp [h]
      conv_lhs => rw [hv i]
      have : (s i : ℂ) * ((ε i : ℂ) * ((‖v i‖ : ℂ) * ((cos (θ i) : ℂ) + (sin (θ i) : ℂ) * Complex.I)))
          = ((s i * ε i : ℝ) : ℂ) * ((‖v i‖ : ℂ) * ((cos (θ i) : ℂ) + (sin (θ i) : ℂ) * Complex.I)) := by
        push_cast; ring
      rw [this]
      have h2 : s i * ε i = t i := by
        simp only [s]; calc ε i * t i * ε i = (ε i * ε i) * t i := by ring
          _ = t i := by rw [h1]; ring
      rw [h2]
      push_cast; ring
    have hre : (∑ i, (s i : ℂ) * v i).re = vx A Θ m k := by
      unfold vx
      rw [← Fin.sum_univ_eq_sum_range (fun j => (if j < k then (1 : ℝ) else -1) * (A j * cos (Θ j))) m,
        Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hterm i]
      simp [hAi, hΘi, t]
    have him : (∑ i, (s i : ℂ) * v i).im = vy A Θ m k := by
      unfold vy
      rw [← Fin.sum_univ_eq_sum_range (fun j => (if j < k then (1 : ℝ) else -1) * (A j * sin (Θ j))) m,
        Complex.im_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hterm i]
      simp [hAi, hΘi, t]
    rw [← hre, ← him]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hZ
    have h3 : ‖∑ i, (s i : ℂ) * v i‖ ^ 2 ≤ M ^ 2 := by
      have := norm_nonneg (∑ i, (s i : ℂ) * v i)
      nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply] at h3
    nlinarith [h3]

theorem sum_fin_range {m : ℕ} (v : Fin m → ℂ) (A : ℕ → ℝ) (hAi : ∀ i : Fin m, A i = ‖v i‖) :
    ∑ j ∈ Finset.range m, A j = ∑ i, ‖v i‖ ∧ ∑ j ∈ Finset.range m, A j ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  constructor
  · rw [← Fin.sum_univ_eq_sum_range A m]
    exact Finset.sum_congr rfl (fun i _ => hAi i)
  · rw [← Fin.sum_univ_eq_sum_range (fun j => A j ^ 2) m]
    exact Finset.sum_congr rfl (fun i _ => by rw [hAi i])

theorem polar_sorted {m : ℕ} (v : Fin m → ℂ) (ε θ : Fin m → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i < π) (hmono : Monotone θ)
    (hv : ∀ i, v i = (ε i : ℂ) * ((‖v i‖ : ℂ) * ((cos (θ i) : ℂ) + (sin (θ i) : ℂ) * Complex.I)))
    (M : ℝ) (hM : 0 < M)
    (hH : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v i‖ ≤ M) :
    (∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2 ≤ 3 * M ^ 2 := by
  obtain ⟨A, Θ, hA, hm, hs, hX, hAi⟩ := polar_sorted_seq v ε θ hε hθ0 hθ1 hmono hv M hH
  have hmain := seq_bound m A Θ M hM hA hm hs hX
  obtain ⟨e1, e2⟩ := sum_fin_range v A hAi
  rw [e1, e2] at hmain
  exact hmain

/-- Equality case of `polar_sorted`: all moduli are `0` or `M/√2`, or all are `0` or `M/2`. -/
theorem polar_sorted_eq {m : ℕ} (v : Fin m → ℂ) (ε θ : Fin m → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i < π) (hmono : Monotone θ)
    (hv : ∀ i, v i = (ε i : ℂ) * ((‖v i‖ : ℂ) * ((cos (θ i) : ℂ) + (sin (θ i) : ℂ) * Complex.I)))
    (M : ℝ) (hM : 0 < M)
    (hH : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v i‖ ≤ M)
    (hΦ : (∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2 = 3 * M ^ 2) :
    (∀ i, ‖v i‖ = 0 ∨ ‖v i‖ = M * (√2 / 2)) ∨ (∀ i, ‖v i‖ = 0 ∨ ‖v i‖ = M / 2) := by
  obtain ⟨A, Θ, hA, hm, hs, hX, hAi⟩ := polar_sorted_seq v ε θ hε hθ0 hθ1 hmono hv M hH
  obtain ⟨e1, e2⟩ := sum_fin_range v A hAi
  have := seq_eq m A Θ M hM hA hm hs hX (by rw [e1, e2]; exact hΦ)
  rcases this with h | h
  · left; intro i; have := h i i.isLt; rwa [hAi i] at this
  · right; intro i; have := h i i.isLt; rwa [hAi i] at this

/-- Sorting the polar data of `v`: a permutation `σ` of the indices with signs `ε` and angles `θ ∈ [0, π)`
nondecreasing along `σ`. -/
theorem sorted_polar {m : ℕ} (v : Fin m → ℂ) (M : ℝ)
    (hH : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v i‖ ≤ M) :
    ∃ (σ : Equiv.Perm (Fin m)) (ε θ : Fin m → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i, 0 ≤ θ i) ∧
      (∀ i, θ i < π) ∧ Monotone θ ∧
      (∀ i, v (σ i) = (ε i : ℂ) * ((‖v (σ i)‖ : ℂ) * ((cos (θ i) : ℂ) + (sin (θ i) : ℂ) * Complex.I))) ∧
      (∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v (σ i)‖ ≤ M) := by
  choose ε θ hε hθ0 hθ1 hv using fun i => polar_halfplane (v i)
  set σ := Tuple.sort θ with hσ
  refine ⟨σ, fun i => ε (σ i), fun i => θ (σ i), fun i => hε _, fun i => hθ0 _, fun i => hθ1 _,
    Tuple.monotone_sort θ, fun i => hv _, ?_⟩
  intro s hs
  have := hH (fun i' => s (σ.symm i')) (fun i => hs _)
  have e : ∑ i, ((s i : ℝ) : ℂ) * v (σ i) = ∑ i', ((s (σ.symm i') : ℝ) : ℂ) * v i' := by
    rw [← Equiv.sum_comp σ (fun i' => ((s (σ.symm i') : ℝ) : ℂ) * v i')]
    simp
  rw [e]; exact this

/-- The bound in terms of the maximal signed-sum modulus `M`. -/
theorem planar_bound {m : ℕ} (v : Fin m → ℂ) (M : ℝ)
    (hH : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v i‖ ≤ M) :
    (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2) ≤ M ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hH (fun _ => 1) (fun _ => Or.inl rfl))
  rcases hM0.eq_or_lt with hM | hM
  · -- `M = 0`: all `v i = 0`
    subst hM
    have hz : ∀ i, ‖v i‖ ≤ 0 := by
      intro i
      have h1 := hH (fun _ => 1) (fun _ => Or.inl rfl)
      have h2 := hH (fun j => if j = i then -1 else 1) (by intro j; by_cases h : j = i <;> simp [h])
      have hdiff : ∑ j, ((1 : ℝ) : ℂ) * v j - ∑ j, ((if j = i then -1 else 1 : ℝ) : ℂ) * v j
          = 2 * v i := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single i]
        · simp; ring
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_univ i) h
      have h3 : ‖(2 : ℂ) * v i‖ ≤ ‖∑ j, ((1 : ℝ) : ℂ) * v j‖
          + ‖∑ j, ((if j = i then -1 else 1 : ℝ) : ℂ) * v j‖ := by
        rw [← hdiff]; exact norm_sub_le _ _
      rw [norm_mul] at h3
      have h2n : ‖(2 : ℂ)‖ = 2 := by simp
      have h1' : ‖∑ j, ((1 : ℝ) : ℂ) * v j‖ ≤ 0 := h1
      rw [h2n] at h3
      linarith
    have : ∀ i, ‖v i‖ = 0 := fun i => le_antisymm (hz i) (norm_nonneg _)
    simp [this]
  · obtain ⟨σ, ε, θ, hε, hθ0, hθ1, hmono, hv, hH'⟩ := sorted_polar v M hH
    have := polar_sorted (fun i => v (σ i)) ε θ hε hθ0 hθ1 hmono hv M hM hH'
    have e1 : ∑ i, ‖v (σ i)‖ = ∑ i, ‖v i‖ := Equiv.sum_comp σ (fun i => ‖v i‖)
    have e2 : ∑ i, ‖v (σ i)‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := Equiv.sum_comp σ (fun i => ‖v i‖ ^ 2)
    simp only [e1, e2] at this
    linarith

/-- Equality case of `planar_bound` (with `M > 0`): all moduli are `0` or `M/√2`, or all are `0` or `M/2`. -/
theorem planar_bound_eq {m : ℕ} (v : Fin m → ℂ) (M : ℝ) (hM : 0 < M)
    (hH : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v i‖ ≤ M)
    (hΦ : (∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2 = 3 * M ^ 2) :
    (∀ i, ‖v i‖ = 0 ∨ ‖v i‖ = M * (√2 / 2)) ∨ (∀ i, ‖v i‖ = 0 ∨ ‖v i‖ = M / 2) := by
  obtain ⟨σ, ε, θ, hε, hθ0, hθ1, hmono, hv, hH'⟩ := sorted_polar v M hH
  have e1 : ∑ i, ‖v (σ i)‖ = ∑ i, ‖v i‖ := Equiv.sum_comp σ (fun i => ‖v i‖)
  have e2 : ∑ i, ‖v (σ i)‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := Equiv.sum_comp σ (fun i => ‖v i‖ ^ 2)
  have := polar_sorted_eq (fun i => v (σ i)) ε θ hε hθ0 hθ1 hmono hv M hM hH' (by
    simp only [e1, e2]; exact hΦ)
  rcases this with h | h
  · left; intro i; simpa using h (σ.symm i)
  · right; intro i; simpa using h (σ.symm i)

/-- **Planar sign inequality.** For any `v₁, …, v_m ∈ ℂ` there are signs `s_i = ±1` with
`‖∑ s_i v_i‖² ≥ (1/3)((∑‖v_i‖)² + ∑‖v_i‖²)`. -/
theorem planar_sign {m : ℕ} (v : Fin m → ℂ) :
    ∃ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, (s i : ℂ) * v i‖ ^ 2 := by
  classical
  let sg : (Fin m → Bool) → Fin m → ℝ := fun b i => if b i then 1 else -1
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m → Bool))
    (fun b => ‖∑ i, (sg b i : ℂ) * v i‖) ⟨fun _ => true, Finset.mem_univ _⟩
  refine ⟨sg b, fun i => by by_cases h : b i <;> simp [sg, h], ?_⟩
  have := planar_bound v ‖∑ i, (sg b i : ℂ) * v i‖ (by
    intro s hs
    have := hb (fun i => decide (s i = 1)) (Finset.mem_univ _)
    have e : sg (fun i => decide (s i = 1)) = s := by
      funext i
      simp only [sg]
      rcases hs i with h | h
      · simp [h]
      · simp [h]; norm_num
    rwa [e] at this)
  exact this

/-- The case `m = 4` of the planar sign inequality. -/
theorem planar_sign4 (v : Fin 4 → ℂ) :
    ∃ s : Fin 4 → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, (s i : ℂ) * v i‖ ^ 2 :=
  planar_sign v

/-! ### The equality case -/

theorem gram_aux (p q r : ℝ) (hp : |p| ≤ 1 / 2) (hq : |q| ≤ 1 / 2) (hr : |r| ≤ 1 / 2)
    (h : 1 + 2 * p * q * r - p ^ 2 - q ^ 2 - r ^ 2 = 0) :
    p ^ 2 = 1 / 4 ∧ q ^ 2 = 1 / 4 ∧ r ^ 2 = 1 / 4 := by
  have hp2 : p ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg p, sq_abs p]
  have hq2 : q ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg q, sq_abs q]
  have hr2 : r ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg r, sq_abs r]
  have hD : (1 - p ^ 2) * (1 - q ^ 2) = (r - p * q) ^ 2 := by nlinarith [h]
  -- |r - p q| ≤ 3/4
  have hpq : |p * q| ≤ 1 / 4 := by
    rw [abs_mul]; nlinarith [abs_nonneg p, abs_nonneg q]
  have hrpq : |r - p * q| ≤ 3 / 4 := by
    calc |r - p * q| ≤ |r| + |p * q| := abs_sub _ _
      _ ≤ 3 / 4 := by linarith
  have hsq : (r - p * q) ^ 2 ≤ 9 / 16 := by
    have := sq_abs (r - p * q)
    nlinarith [abs_nonneg (r - p * q)]
  have hL : 9 / 16 ≤ (1 - p ^ 2) * (1 - q ^ 2) := by nlinarith
  have hp_eq : p ^ 2 = 1 / 4 := by
    by_contra hne
    have hlt : p ^ 2 < 1 / 4 := lt_of_le_of_ne hp2 hne
    nlinarith [mul_nonneg (sub_nonneg.2 hq2) (sub_nonneg.2 hq2), mul_pos (sub_pos.2 hlt) (by linarith : (0:ℝ) < 1 - q ^ 2)]
  have hq_eq : q ^ 2 = 1 / 4 := by
    by_contra hne
    have hlt : q ^ 2 < 1 / 4 := lt_of_le_of_ne hq2 hne
    nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : (0:ℝ) < 1 - p ^ 2)]
  refine ⟨hp_eq, hq_eq, ?_⟩
  -- now (r - p q)^2 = 9/16 and |p q| = 1/4
  have hpq2 : (p * q) ^ 2 = 1 / 16 := by rw [mul_pow, hp_eq, hq_eq]; norm_num
  have hr_sq : (r - p * q) ^ 2 = 9 / 16 := by rw [← hD, hp_eq, hq_eq]; norm_num
  by_contra hne
  have hlt : r ^ 2 < 1 / 4 := lt_of_le_of_ne hr2 hne
  nlinarith [abs_nonneg r, sq_abs r, abs_nonneg (p * q), sq_abs (p * q), abs_nonneg (r - p * q), sq_abs (r - p * q),
    abs_sub (r) (p * q)]

/-- `‖z + w‖² = ‖z‖² + ‖w‖² + 2 Re (z w̄)`. -/
theorem norm_add_sq' (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * (starRingEnd ℂ) w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem norm_sub_sq' (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (z * (starRingEnd ℂ) w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Gram determinant of three vectors in the plane vanishes. -/
theorem gram_det (p q r : ℂ) :
    ‖p‖ ^ 2 * ‖q‖ ^ 2 * ‖r‖ ^ 2
      + 2 * (p * (starRingEnd ℂ) q).re * (p * (starRingEnd ℂ) r).re * (q * (starRingEnd ℂ) r).re
      - ‖p‖ ^ 2 * (q * (starRingEnd ℂ) r).re ^ 2 - ‖q‖ ^ 2 * (p * (starRingEnd ℂ) r).re ^ 2
      - ‖r‖ ^ 2 * (p * (starRingEnd ℂ) q).re ^ 2 = 0 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem two_orth (x y : ℂ) (a M : ℝ) (hx : ‖x‖ = a) (hy : ‖y‖ = a) (hM : M ^ 2 = 2 * a ^ 2)
    (h1 : ‖x + y‖ ≤ M) (h2 : ‖x - y‖ ≤ M) (hM0 : 0 ≤ M) : (x * (starRingEnd ℂ) y).re = 0 := by
  have e1 := norm_add_sq' x y
  have e2 := norm_sub_sq' x y
  have h1' : ‖x + y‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (x + y)]
  have h2' : ‖x - y‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (x - y)]
  rw [hx, hy] at e1 e2
  nlinarith

theorem three_bound (p q r : ℂ) (a : ℝ) (hp : ‖p‖ = a) (hq : ‖q‖ = a) (hr : ‖r‖ = a)
    (h1 : ‖r + (p + q)‖ ≤ 2 * a) (h2 : ‖r - (p + q)‖ ≤ 2 * a)
    (h3 : ‖r + (p - q)‖ ≤ 2 * a) (h4 : ‖r - (p - q)‖ ≤ 2 * a) (ha : 0 ≤ a) :
    |(p * (starRingEnd ℂ) q).re| ≤ a ^ 2 / 2 := by
  have e1 := norm_add_sq' r (p + q)
  have e2 := norm_sub_sq' r (p + q)
  have e3 := norm_add_sq' r (p - q)
  have e4 := norm_sub_sq' r (p - q)
  have f1 := norm_add_sq' p q
  have f2 := norm_sub_sq' p q
  have h1' : ‖r + (p + q)‖ ^ 2 ≤ (2 * a) ^ 2 := by nlinarith [norm_nonneg (r + (p + q))]
  have h2' : ‖r - (p + q)‖ ^ 2 ≤ (2 * a) ^ 2 := by nlinarith [norm_nonneg (r - (p + q))]
  have h3' : ‖r + (p - q)‖ ^ 2 ≤ (2 * a) ^ 2 := by nlinarith [norm_nonneg (r + (p - q))]
  have h4' : ‖r - (p - q)‖ ^ 2 ≤ (2 * a) ^ 2 := by nlinarith [norm_nonneg (r - (p - q))]
  rw [abs_le]
  constructor
  · rw [hp, hq] at f2
    rw [hr] at e3 e4
    nlinarith
  · rw [hp, hq] at f1
    rw [hr] at e1 e2
    nlinarith

/-- A sign pattern prescribed on three indices (and `1` elsewhere). -/
def sg3 {m : ℕ} (i j l : Fin m) (a b c : ℝ) : Fin m → ℝ :=
  fun k => if k = i then a else if k = j then b else if k = l then c else 1

theorem sg3_sign {m : ℕ} (i j l : Fin m) (a b c : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) : ∀ k, sg3 i j l a b c k = 1 ∨ sg3 i j l a b c k = -1 := by
  intro k
  unfold sg3
  split_ifs
  · exact ha
  · exact hb
  · exact hc
  · exact Or.inl rfl

theorem sum_sg3 {m : ℕ} (v : Fin m → ℂ) (i j l : Fin m) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (h0 : ∀ k, k ≠ i → k ≠ j → k ≠ l → v k = 0) (a b c : ℝ) :
    ∑ k, (sg3 i j l a b c k : ℂ) * v k = (a : ℂ) * v i + (b : ℂ) * v j + (c : ℂ) * v l := by
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin m)), k ∉ ({i, j, l} : Finset (Fin m)) →
      (sg3 i j l a b c k : ℂ) * v k = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [h0 k hk.1 hk.2.1 hk.2.2, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ {i, j, l}) hsub]
  rw [Finset.sum_insert (by simp [hij, hil]), Finset.sum_insert (by simp [hjl]), Finset.sum_singleton]
  have e1 : sg3 i j l a b c i = a := by simp [sg3]
  have e2 : sg3 i j l a b c j = b := by simp [sg3, hij.symm]
  have e3 : sg3 i j l a b c l = c := by simp [sg3, hil.symm, hjl.symm]
  rw [e1, e2, e3]; ring

/-- A sign pattern prescribed on two indices (and `1` elsewhere). -/
def sg2 {m : ℕ} (i j : Fin m) (a b : ℝ) : Fin m → ℝ :=
  fun k => if k = i then a else if k = j then b else 1

theorem sg2_sign {m : ℕ} (i j : Fin m) (a b : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    ∀ k, sg2 i j a b k = 1 ∨ sg2 i j a b k = -1 := by
  intro k
  unfold sg2
  split_ifs
  · exact ha
  · exact hb
  · exact Or.inl rfl

theorem sum_sg2 {m : ℕ} (v : Fin m → ℂ) (i j : Fin m) (hij : i ≠ j)
    (h0 : ∀ k, k ≠ i → k ≠ j → v k = 0) (a b : ℝ) :
    ∑ k, (sg2 i j a b k : ℂ) * v k = (a : ℂ) * v i + (b : ℂ) * v j := by
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin m)), k ∉ ({i, j} : Finset (Fin m)) →
      (sg2 i j a b k : ℂ) * v k = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [h0 k hk.1 hk.2, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ {i, j}) hsub]
  rw [Finset.sum_insert (by simp [hij]), Finset.sum_singleton]
  have e1 : sg2 i j a b i = a := by simp [sg2]
  have e2 : sg2 i j a b j = b := by simp [sg2, hij.symm]
  rw [e1, e2]

/-- Counting the nonzero vectors, when all moduli are `0` or `a`. -/
theorem count_aux {m : ℕ} (v : Fin m → ℂ) (a : ℝ) (hval : ∀ i, ‖v i‖ = 0 ∨ ‖v i‖ = a) :
    ∑ i, ‖v i‖ = ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℝ) * a ∧
    ∑ i, ‖v i‖ ^ 2 = ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℝ) * a ^ 2 := by
  classical
  have h1 : ∀ i, ‖v i‖ = a * (if v i ≠ 0 then 1 else 0) := by
    intro i
    by_cases h : v i = 0
    · simp [h]
    · rcases hval i with h' | h'
      · exact absurd (norm_eq_zero.1 h') h
      · simp [h, h']
  have h2 : ∀ i, ‖v i‖ ^ 2 = a ^ 2 * (if v i ≠ 0 then 1 else 0) := by
    intro i
    by_cases h : v i = 0
    · simp [h]
    · rcases hval i with h' | h'
      · exact absurd (norm_eq_zero.1 h') h
      · simp [h, h']
  constructor
  · rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum, Finset.sum_boole]; ring
  · rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.mul_sum, Finset.sum_boole]; ring

theorem nat_pair_six (N : ℕ) (h : (N : ℝ) * (N + 1) = 6) : N = 2 := by
  have h' : N * (N + 1) = 6 := by exact_mod_cast h
  have hN : N ≤ 2 := by
    by_contra hc
    have : 3 ≤ N := by omega
    nlinarith
  interval_cases N <;> omega

theorem nat_pair_twelve (N : ℕ) (h : (N : ℝ) * (N + 1) = 12) : N = 3 := by
  have h' : N * (N + 1) = 12 := by exact_mod_cast h
  have hN : N ≤ 3 := by
    by_contra hc
    have : 4 ≤ N := by omega
    nlinarith
  interval_cases N <;> omega

theorem fin_aux (a r : ℝ) (hb : a ^ 2 ≠ 0) (hr : (r / a ^ 2) ^ 2 = 1 / 4) : (2 * r) ^ 2 = a ^ 4 := by
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hb)] at hr
  nlinarith [hr]

/-- **Equality case of the planar sign inequality.** If the maximal signed sum equals the bound,
the nonzero `v_i` are: none; or exactly two, of equal modulus and orthogonal; or exactly three,
of equal modulus with pairwise `(2 Re (v_i v̄_j))² = ‖v_i‖⁴`, i.e. on lines at mutual angles `π/3`. -/
theorem planar_sign_equality {m : ℕ} (v : Fin m → ℂ)
    (h : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      ‖∑ i, (s i : ℂ) * v i‖ ^ 2 ≤ (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2)) :
    (∀ i, v i = 0) ∨
    (∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0) ∧ v i ≠ 0 ∧ ‖v i‖ = ‖v j‖ ∧
      (v i * (starRingEnd ℂ) (v j)).re = 0) ∨
    (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (∀ l, l ≠ i → l ≠ j → l ≠ k → v l = 0) ∧ v i ≠ 0 ∧
      ‖v i‖ = ‖v j‖ ∧ ‖v i‖ = ‖v k‖ ∧
      (2 * (v i * (starRingEnd ℂ) (v j)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v i * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v j * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4) := by
  classical
  by_cases hL0 : ∑ i, ‖v i‖ = 0
  · left
    intro i
    have h1 : ‖v i‖ ≤ ∑ i, ‖v i‖ :=
      Finset.single_le_sum (f := fun j => ‖v j‖) (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i)
    exact norm_eq_zero.1 (le_antisymm (by linarith) (norm_nonneg _))
  right
  have hLpos : 0 < ∑ i, ‖v i‖ :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => norm_nonneg _) (Ne.symm hL0)
  have hQ0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  set T : ℝ := (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2) with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  set M : ℝ := √T with hMdef
  have hMpos : 0 < M := Real.sqrt_pos.2 hTpos
  have hM2 : M ^ 2 = T := Real.sq_sqrt hTpos.le
  have hH : ∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ‖∑ i, (s i : ℂ) * v i‖ ≤ M := by
    intro s hs
    have := h s hs
    rw [← hM2] at this
    exact (abs_le_of_sq_le_sq' this hMpos.le).2
  have hΦ : (∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2 = 3 * M ^ 2 := by rw [hM2, hT]; ring
  have hpat := planar_bound_eq v M hMpos hH hΦ
  set S : Finset (Fin m) := Finset.univ.filter (fun i => v i ≠ 0) with hS
  have hmemS : ∀ k, k ∈ S ↔ v k ≠ 0 := by intro k; simp [hS]
  rcases hpat with hI | hII
  · -- the square: two orthogonal vectors of modulus `M/√2`
    set a : ℝ := M * (√2 / 2) with ha
    have ha2 : a ^ 2 = M ^ 2 / 2 := by
      rw [ha, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    have hapos : 0 < a := by positivity
    obtain ⟨hc1, hc2⟩ := count_aux v a hI
    have hN : ((S.card : ℝ)) * (S.card + 1) = 6 := by
      have h3 : a ^ 2 * ((S.card : ℝ) * (S.card + 1)) = 3 * M ^ 2 := by
        rw [← hΦ, hc1, hc2]; ring
      rw [ha2] at h3
      have hM2' : 0 < M ^ 2 := by positivity
      nlinarith
    have hN2 : S.card = 2 := nat_pair_six _ hN
    obtain ⟨x, y, hxy, hSxy⟩ := Finset.card_eq_two.1 hN2
    have hk : ∀ k, v k ≠ 0 ↔ k = x ∨ k = y := by
      intro k; rw [← hmemS, hSxy]; simp
    have h0 : ∀ k, k ≠ x → k ≠ y → v k = 0 := by
      intro k h1 h2; by_contra hne
      rcases (hk k).1 hne with h | h
      · exact h1 h
      · exact h2 h
    have hvx : v x ≠ 0 := (hk x).2 (Or.inl rfl)
    have hvy : v y ≠ 0 := (hk y).2 (Or.inr rfl)
    have hnx : ‖v x‖ = a := (hI x).resolve_left (norm_ne_zero_iff.2 hvx)
    have hny : ‖v y‖ = a := (hI y).resolve_left (norm_ne_zero_iff.2 hvy)
    refine Or.inl ⟨x, y, hxy, h0, hvx, by rw [hnx, hny], ?_⟩
    have h1 := hH (sg2 x y 1 1) (sg2_sign x y 1 1 (Or.inl rfl) (Or.inl rfl))
    have h2 := hH (sg2 x y 1 (-1)) (sg2_sign x y 1 (-1) (Or.inl rfl) (Or.inr rfl))
    rw [sum_sg2 v x y hxy h0] at h1 h2
    have e1 : ((1 : ℝ) : ℂ) * v x + ((1 : ℝ) : ℂ) * v y = v x + v y := by push_cast; ring
    have e2 : ((1 : ℝ) : ℂ) * v x + ((-1 : ℝ) : ℂ) * v y = v x - v y := by push_cast; ring
    rw [e1] at h1
    rw [e2] at h2
    exact two_orth (v x) (v y) a M hnx hny (by rw [ha2]; ring) h1 h2 hMpos.le
  · -- the hexagon: three vectors of modulus `M/2`
    set a : ℝ := M / 2 with ha
    have ha2 : a ^ 2 = M ^ 2 / 4 := by rw [ha]; ring
    have hapos : 0 < a := by positivity
    obtain ⟨hc1, hc2⟩ := count_aux v a hII
    have hN : ((S.card : ℝ)) * (S.card + 1) = 12 := by
      have h3 : a ^ 2 * ((S.card : ℝ) * (S.card + 1)) = 3 * M ^ 2 := by
        rw [← hΦ, hc1, hc2]; ring
      rw [ha2] at h3
      have hM2' : 0 < M ^ 2 := by positivity
      nlinarith
    have hN3 : S.card = 3 := nat_pair_twelve _ hN
    obtain ⟨x, y, z, hxy, hxz, hyz, hSxyz⟩ := Finset.card_eq_three.1 hN3
    have hk : ∀ k, v k ≠ 0 ↔ k = x ∨ k = y ∨ k = z := by
      intro k; rw [← hmemS, hSxyz]; simp
    have h0 : ∀ k, k ≠ x → k ≠ y → k ≠ z → v k = 0 := by
      intro k h1 h2 h3; by_contra hne
      rcases (hk k).1 hne with h | h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
    have hvx : v x ≠ 0 := (hk x).2 (Or.inl rfl)
    have hvy : v y ≠ 0 := (hk y).2 (Or.inr (Or.inl rfl))
    have hvz : v z ≠ 0 := (hk z).2 (Or.inr (Or.inr rfl))
    have hnx : ‖v x‖ = a := (hII x).resolve_left (norm_ne_zero_iff.2 hvx)
    have hny : ‖v y‖ = a := (hII y).resolve_left (norm_ne_zero_iff.2 hvy)
    have hnz : ‖v z‖ = a := (hII z).resolve_left (norm_ne_zero_iff.2 hvz)
    have hM2a : M = 2 * a := by rw [ha]; ring
    have key : ∀ (c₁ c₂ c₃ : ℝ), (c₁ = 1 ∨ c₁ = -1) → (c₂ = 1 ∨ c₂ = -1) → (c₃ = 1 ∨ c₃ = -1) →
        ∀ w : ℂ, w = (c₁ : ℂ) * v x + (c₂ : ℂ) * v y + (c₃ : ℂ) * v z → ‖w‖ ≤ 2 * a := by
      intro c₁ c₂ c₃ h1 h2 h3 w hw
      have := hH (sg3 x y z c₁ c₂ c₃) (sg3_sign x y z c₁ c₂ c₃ h1 h2 h3)
      rw [sum_sg3 v x y z hxy hxz hyz h0] at this
      rw [hw, ← hM2a]; exact this
    have s1 : ((1 : ℝ) = 1 ∨ (1 : ℝ) = -1) := Or.inl rfl
    have sm : ((-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) := Or.inr rfl
    have bxy := three_bound (v x) (v y) (v z) a hnx hny hnz
      (key 1 1 1 s1 s1 s1 _ (by push_cast; ring)) (key (-1) (-1) 1 sm sm s1 _ (by push_cast; ring))
      (key 1 (-1) 1 s1 sm s1 _ (by push_cast; ring)) (key (-1) 1 1 sm s1 s1 _ (by push_cast; ring))
      hapos.le
    have bxz := three_bound (v x) (v z) (v y) a hnx hnz hny
      (key 1 1 1 s1 s1 s1 _ (by push_cast; ring)) (key (-1) 1 (-1) sm s1 sm _ (by push_cast; ring))
      (key 1 1 (-1) s1 s1 sm _ (by push_cast; ring)) (key (-1) 1 1 sm s1 s1 _ (by push_cast; ring))
      hapos.le
    have byz := three_bound (v y) (v z) (v x) a hny hnz hnx
      (key 1 1 1 s1 s1 s1 _ (by push_cast; ring)) (key 1 (-1) (-1) s1 sm sm _ (by push_cast; ring))
      (key 1 1 (-1) s1 s1 sm _ (by push_cast; ring)) (key 1 (-1) 1 s1 sm s1 _ (by push_cast; ring))
      hapos.le
    have hg := gram_det (v x) (v y) (v z)
    rw [hnx, hny, hnz] at hg
    set r₁ := (v x * (starRingEnd ℂ) (v y)).re with hr₁
    set r₂ := (v x * (starRingEnd ℂ) (v z)).re with hr₂
    set r₃ := (v y * (starRingEnd ℂ) (v z)).re with hr₃
    have ha2pos : 0 < a ^ 2 := by positivity
    have hnorm : ∀ r : ℝ, |r| ≤ a ^ 2 / 2 → |r / a ^ 2| ≤ 1 / 2 := by
      intro r hr
      rw [abs_div, abs_of_pos ha2pos, div_le_iff₀ ha2pos]; linarith
    have hb : a ^ 2 ≠ 0 := ha2pos.ne'
    have hgeq : 1 + 2 * (r₁ / a ^ 2) * (r₂ / a ^ 2) * (r₃ / a ^ 2) - (r₁ / a ^ 2) ^ 2
        - (r₂ / a ^ 2) ^ 2 - (r₃ / a ^ 2) ^ 2 = 0 := by
      have e : 1 + 2 * (r₁ / a ^ 2) * (r₂ / a ^ 2) * (r₃ / a ^ 2) - (r₁ / a ^ 2) ^ 2
          - (r₂ / a ^ 2) ^ 2 - (r₃ / a ^ 2) ^ 2
          = (a ^ 2 * a ^ 2 * a ^ 2 + 2 * r₁ * r₂ * r₃ - a ^ 2 * r₃ ^ 2 - a ^ 2 * r₂ ^ 2
              - a ^ 2 * r₁ ^ 2) / (a ^ 2) ^ 3 := by
        field_simp
        ring
      rw [e, hg, zero_div]
    have hgr := gram_aux (r₁ / a ^ 2) (r₂ / a ^ 2) (r₃ / a ^ 2) (hnorm _ bxy) (hnorm _ bxz) (hnorm _ byz)
      hgeq
    obtain ⟨g1, g2, g3⟩ := hgr
    have fin : ∀ r : ℝ, (r / a ^ 2) ^ 2 = 1 / 4 → (2 * r) ^ 2 = a ^ 4 := fun r hr => fin_aux a r hb hr
    refine Or.inr ⟨x, y, z, hxy, hxz, hyz, h0, hvx, by rw [hnx, hny], by rw [hnx, hnz], ?_, ?_, ?_⟩
    · rw [hnx]; exact fin _ g1
    · rw [hnx]; exact fin _ g2
    · rw [hnx]; exact fin _ g3

theorem sum_support2 {m : ℕ} {α : Type*} [AddCommMonoid α] (f : Fin m → α) (i j : Fin m) (hij : i ≠ j)
    (h0 : ∀ k, k ≠ i → k ≠ j → f k = 0) : ∑ k, f k = f i + f j := by
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin m)), k ∉ ({i, j} : Finset (Fin m)) → f k = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact h0 k hk.1 hk.2
  rw [← Finset.sum_subset (Finset.subset_univ {i, j}) hsub, Finset.sum_insert (by simp [hij]),
    Finset.sum_singleton]

theorem sum_support3 {m : ℕ} {α : Type*} [AddCommMonoid α] (f : Fin m → α) (i j l : Fin m)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (h0 : ∀ k, k ≠ i → k ≠ j → k ≠ l → f k = 0) :
    ∑ k, f k = f i + f j + f l := by
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin m)), k ∉ ({i, j, l} : Finset (Fin m)) → f k = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact h0 k hk.1 hk.2.1 hk.2.2
  rw [← Finset.sum_subset (Finset.subset_univ {i, j, l}) hsub, Finset.sum_insert (by simp [hij, hil]),
    Finset.sum_insert (by simp [hjl]), Finset.sum_singleton]
  abel

/-- If a real `t` satisfies `t² = c²` (`c ≥ 0`) then `t = c` or `t = -c`. -/
theorem sq_cases (t c : ℝ) (h : t ^ 2 = c ^ 2) : t = c ∨ t = -c := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Three signed terms with pairwise products `t₁ t₂ t₃ = -c³`, `tᵢ² = c²`: the sum is at most `c`. -/
theorem three_signs (t₁ t₂ t₃ c : ℝ) (hc : 0 < c) (h1 : t₁ ^ 2 = c ^ 2) (h2 : t₂ ^ 2 = c ^ 2)
    (h3 : t₃ ^ 2 = c ^ 2) (hp : t₁ * t₂ * t₃ = -c ^ 3) : t₁ + t₂ + t₃ ≤ c := by
  rcases sq_cases _ _ h1 with a | a <;> rcases sq_cases _ _ h2 with b | b <;>
    rcases sq_cases _ _ h3 with d | d <;> subst a <;> subst b <;> subst d <;> nlinarith [pow_pos hc 3]

theorem norm_real_mul_sq (x : ℝ) (p : ℂ) (hx : x ^ 2 = 1) : ‖(x : ℂ) * p‖ ^ 2 = ‖p‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hx, one_mul]

theorem re_real_mul_conj (p q : ℂ) (x y : ℝ) :
    ((x : ℂ) * p * (starRingEnd ℂ) ((y : ℂ) * q)).re = x * y * (p * (starRingEnd ℂ) q).re := by
  simp only [map_mul, Complex.conj_ofReal]
  have : (x : ℂ) * p * ((y : ℂ) * (starRingEnd ℂ) q)
      = ((x * y : ℝ) : ℂ) * (p * (starRingEnd ℂ) q) := by push_cast; ring
  rw [this, Complex.re_ofReal_mul]

/-- Converse of `planar_sign_equality`: the three configurations attain the bound. -/
theorem planar_sign_equality_of {m : ℕ} (v : Fin m → ℂ)
    (hv : (∀ i, v i = 0) ∨
    (∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0) ∧ v i ≠ 0 ∧ ‖v i‖ = ‖v j‖ ∧
      (v i * (starRingEnd ℂ) (v j)).re = 0) ∨
    (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (∀ l, l ≠ i → l ≠ j → l ≠ k → v l = 0) ∧ v i ≠ 0 ∧
      ‖v i‖ = ‖v j‖ ∧ ‖v i‖ = ‖v k‖ ∧
      (2 * (v i * (starRingEnd ℂ) (v j)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v i * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v j * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4))
    (s : Fin m → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    ‖∑ i, (s i : ℂ) * v i‖ ^ 2 ≤ (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2) := by
  have hs2 : ∀ i, s i ^ 2 = 1 := by intro i; rcases hs i with h | h <;> simp [h]
  rcases hv with h | ⟨i, j, hij, h0, hvi, hn, hor⟩ | ⟨i, j, l, hij, hil, hjl, h0, hvi, hnj, hnl, e1, e2, e3⟩
  · simp [h]
  · have hsum : ∑ k, (s k : ℂ) * v k = (s i : ℂ) * v i + (s j : ℂ) * v j :=
      sum_support2 (fun k => (s k : ℂ) * v k) i j hij (fun k h1 h2 => by simp [h0 k h1 h2])
    have hL : ∑ k, ‖v k‖ = ‖v i‖ + ‖v j‖ :=
      sum_support2 (fun k => ‖v k‖) i j hij (fun k h1 h2 => by simp [h0 k h1 h2])
    have hQ : ∑ k, ‖v k‖ ^ 2 = ‖v i‖ ^ 2 + ‖v j‖ ^ 2 :=
      sum_support2 (fun k => ‖v k‖ ^ 2) i j hij (fun k h1 h2 => by simp [h0 k h1 h2])
    rw [hsum, hL, hQ, ← hn]
    have : ‖(s i : ℂ) * v i + (s j : ℂ) * v j‖ ^ 2 = 2 * ‖v i‖ ^ 2 := by
      rw [norm_add_sq', norm_real_mul_sq _ _ (hs2 i), norm_real_mul_sq _ _ (hs2 j),
        re_real_mul_conj, hor, ← hn]
      ring
    rw [this]; nlinarith [sq_nonneg ‖v i‖]
  · have hsum : ∑ k, (s k : ℂ) * v k = (s i : ℂ) * v i + (s j : ℂ) * v j + (s l : ℂ) * v l :=
      sum_support3 (fun k => (s k : ℂ) * v k) i j l hij hil hjl
        (fun k h1 h2 h3 => by simp [h0 k h1 h2 h3])
    have hL : ∑ k, ‖v k‖ = ‖v i‖ + ‖v j‖ + ‖v l‖ :=
      sum_support3 (fun k => ‖v k‖) i j l hij hil hjl (fun k h1 h2 h3 => by simp [h0 k h1 h2 h3])
    have hQ : ∑ k, ‖v k‖ ^ 2 = ‖v i‖ ^ 2 + ‖v j‖ ^ 2 + ‖v l‖ ^ 2 :=
      sum_support3 (fun k => ‖v k‖ ^ 2) i j l hij hil hjl (fun k h1 h2 h3 => by simp [h0 k h1 h2 h3])
    rw [hsum, hL, hQ, ← hnj, ← hnl]
    set a := ‖v i‖ with ha
    have hapos : 0 < a := norm_pos_iff.2 hvi
    set R1 := (v i * (starRingEnd ℂ) (v j)).re with hR1
    set R2 := (v i * (starRingEnd ℂ) (v l)).re with hR2
    set R3 := (v j * (starRingEnd ℂ) (v l)).re with hR3
    have hsq : ‖(s i : ℂ) * v i + (s j : ℂ) * v j + (s l : ℂ) * v l‖ ^ 2
        = 3 * a ^ 2 + 2 * (s i * s j * R1 + s i * s l * R2 + s j * s l * R3) := by
      have c12 : (((s i : ℂ) * v i + (s j : ℂ) * v j) * (starRingEnd ℂ) ((s l : ℂ) * v l)).re
          = s i * s l * R2 + s j * s l * R3 := by
        rw [add_mul, Complex.add_re, re_real_mul_conj, re_real_mul_conj]
      rw [norm_add_sq', norm_add_sq', c12, re_real_mul_conj, norm_real_mul_sq _ _ (hs2 i),
        norm_real_mul_sq _ _ (hs2 j), norm_real_mul_sq _ _ (hs2 l), ← hnj, ← hnl]
      ring
    rw [hsq]
    have hg := gram_det (v i) (v j) (v l)
    rw [← hnj, ← hnl] at hg
    have ha4 : a ^ 4 = (a ^ 2) ^ 2 := by ring
    have hR1' : R1 ^ 2 = (a ^ 2 / 2) ^ 2 := by linear_combination (1 / 4) * e1
    have hR2' : R2 ^ 2 = (a ^ 2 / 2) ^ 2 := by linear_combination (1 / 4) * e2
    have hR3' : R3 ^ 2 = (a ^ 2 / 2) ^ 2 := by linear_combination (1 / 4) * e3
    have hprod : R1 * R2 * R3 = -(a ^ 2 / 2) ^ 3 := by
      have : a ^ 2 * a ^ 2 * a ^ 2 + 2 * R1 * R2 * R3 - a ^ 2 * R3 ^ 2 - a ^ 2 * R2 ^ 2
          - a ^ 2 * R1 ^ 2 = 0 := hg
      rw [hR1', hR2', hR3'] at this
      linear_combination (1 / 2) * this
    have hc : 0 < a ^ 2 / 2 := by positivity
    have key := three_signs (s i * s j * R1) (s i * s l * R2) (s j * s l * R3) (a ^ 2 / 2) hc
      (by rw [mul_pow, mul_pow, hs2, hs2, one_mul, one_mul, hR1'])
      (by rw [mul_pow, mul_pow, hs2, hs2, one_mul, one_mul, hR2'])
      (by rw [mul_pow, mul_pow, hs2, hs2, one_mul, one_mul, hR3'])
      (by
        have : s i * s j * R1 * (s i * s l * R2) * (s j * s l * R3)
            = (s i ^ 2) * (s j ^ 2) * (s l ^ 2) * (R1 * R2 * R3) := by ring
        rw [this, hs2, hs2, hs2, hprod]; ring)
    linarith [key]

/-- **Equality case of the planar sign inequality, as an equivalence.** The maximal signed sum meets the
bound `(1/3)((∑‖v_i‖)² + ∑‖v_i‖²)` exactly in the three configurations of `planar_sign_equality`. -/
theorem planar_sign_equality_iff {m : ℕ} (v : Fin m → ℂ) :
    (∀ s : Fin m → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      ‖∑ i, (s i : ℂ) * v i‖ ^ 2 ≤ (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2)) ↔
    ((∀ i, v i = 0) ∨
    (∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0) ∧ v i ≠ 0 ∧ ‖v i‖ = ‖v j‖ ∧
      (v i * (starRingEnd ℂ) (v j)).re = 0) ∨
    (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (∀ l, l ≠ i → l ≠ j → l ≠ k → v l = 0) ∧ v i ≠ 0 ∧
      ‖v i‖ = ‖v j‖ ∧ ‖v i‖ = ‖v k‖ ∧
      (2 * (v i * (starRingEnd ℂ) (v j)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v i * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v j * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4)) :=
  ⟨planar_sign_equality v, fun hv s hs => planar_sign_equality_of v hv s hs⟩

/-- The case `m = 4` of the equality characterisation. -/
theorem planar_sign4_equality_iff (v : Fin 4 → ℂ) :
    (∀ s : Fin 4 → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      ‖∑ i, (s i : ℂ) * v i‖ ^ 2 ≤ (1 / 3) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2)) ↔
    ((∀ i, v i = 0) ∨
    (∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0) ∧ v i ≠ 0 ∧ ‖v i‖ = ‖v j‖ ∧
      (v i * (starRingEnd ℂ) (v j)).re = 0) ∨
    (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (∀ l, l ≠ i → l ≠ j → l ≠ k → v l = 0) ∧ v i ≠ 0 ∧
      ‖v i‖ = ‖v j‖ ∧ ‖v i‖ = ‖v k‖ ∧
      (2 * (v i * (starRingEnd ℂ) (v j)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v i * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4 ∧
      (2 * (v j * (starRingEnd ℂ) (v k)).re) ^ 2 = ‖v i‖ ^ 4)) :=
  planar_sign_equality_iff v

end FormalResearch.FrameFree

