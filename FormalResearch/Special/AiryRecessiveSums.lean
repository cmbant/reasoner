module

public import FormalResearch.Special.AiryWt

/-!
# Lattice sums for the recessive Airy solution (part 1: exponential kernel sums)

Elementary estimates on a lattice window `X : ℤ → ℝ` (sites `Icc m (N+1)`, `X ≥ -1`, spacings `≥ c₁ δ`,
`X ≤ B δ⁻²`, `δ = h^{1/3}`) that feed the Volterra kernel bound of `AiryRecessiveKernel`
(P3 appendices `A:1105-1124`, `lem:airy2-recessive`(i), and the weight sums of `prop:airy2-exact`, `A:1131-1133`).
Everything is **proved** with explicit (non-optimal) constants.  `ξ = airyXi = (2/3) X₊^{3/2}`.

* `airyWt_le_exp_mul` (`A:1112-1114`): `−1 ≤ X_j ≤ X_i ⇒ airyWt X_i ≤ (3/2) e^{−(ξ_i−ξ_j)} airyWt X_j`
  (the two-sided envelope `Ai ≍ (2+X)^{-1/4} e^{-ξ}` is replaced by the explicit weight `airyWt` of `AiryWt`).
* `airyWt_sq_le_exp_mul`: `Wt_i² ≤ (9/4) e^{−2(ξ_i−ξ_y)} Wt_x Wt_y` for `−1 ≤ x ≤ y ≤ z=X_i`.
* `airyXi_diff_ge`: `ξ(X) − ξ(Y) ≥ √max(Y,1) (X−Y) − 2` for `−1 ≤ Y ≤ X` (convexity of `ξ`; the constant `2`
  absorbs the part of the window with `Y < 1`).
* `expTail_le`: **the double-sum building block**
  `G_p := Σ_{i ∈ [p,N]} e^{−2(ξ_i − ξ_p)} ≤ e⁴ (1 + 1/(2 c₁ δ √max(X_p,1)))`  (geometric sum along the lattice;
  this is the paper's `Σ_j e^{-2(ξ_i-ξ_{j+1})} ≤ C h^{-1/3}(1+X⁺)^{-1/2}` in the order summed over `i`).
* `expTail_sum_le`: `Σ_{p ∈ [m+1,N]} G_p ≤ C_G δ⁻³` with the explicit
  `C_G = e⁴((B+1)/c₁ + √6/(2c₁) + √6 √(3+B)/c₁²)` (the paper's `Σ_i (1+X_i^+)^{-1/2} ≤ C h^{-2/3}`,
  here by comparison of the lattice sum with `∫ (3+x)^{-1/2}`, plus the lattice cardinality `≤ (B+1)/(c₁δ³)`).

Numerics (mpmath/numpy, recorded as a comment, not part of the proof): on lattices with `c₁ = 1`, `δ ∈ {0.1,0.05,0.02}`,
`B ∈ {1,3}` and random spacings in `[δ,4δ]`, `max_p G_p / (e⁴(1+1/(2δ s_p))) ≤ 0.062`, `δ³ Σ_p G_p ≤ 1.9`, and the
backward sums `G'_k = Σ_{p≤k} e^{-2(ξ_k-ξ_p)}` satisfy `δ (1+X_k^+)^{1/2} G'_k ≤ 1.8`.

**Not formalised** here: the *backward* sums `Σ_{p ≤ k} e^{-2(ξ_k-ξ_p)}` (for bounds on the growing second solution,
see `AiryRecessive`), and any comparison `airyWt ≍ M/E` on `X < −1`.
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- Lattice window `X_k`, `k ∈ [m, N+1]`: `X ≥ -1`, spacings `≥ c₁ δ`, `X ≤ B δ⁻²` (`δ = h^{1/3}`). -/
structure AiryLattice (X : ℤ → ℝ) (m N : ℤ) (c1 B δ : ℝ) : Prop where
  c1_pos : 0 < c1
  B_nonneg : 0 ≤ B
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  lo : ∀ k ∈ Icc m (N + 1), -1 ≤ X k
  gap : ∀ k ∈ Icc m N, c1 * δ ≤ X (k + 1) - X k
  hi : ∀ k ∈ Icc m (N + 1), X k ≤ B / δ ^ 2

/-- Upward induction on an integer half-line. -/
lemma airy_int_up_induction {P : ℤ → Prop} (m : ℤ) (h0 : P m) (step : ∀ k, m ≤ k → P k → P (k + 1)) :
    ∀ k, m ≤ k → P k := by
  have key : ∀ n : ℕ, P (m + n) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have := step (m + n) (by omega) ih
      simpa [add_assoc] using this
  intro k hk
  have := key (k - m).toNat
  have e : m + ((k - m).toNat : ℤ) = k := by omega
  rwa [e] at this

lemma AiryLattice.diff_ge {X : ℤ → ℝ} {m N : ℤ} {c1 B δ : ℝ} (hL : AiryLattice X m N c1 B δ) {p : ℤ}
    (hp : m ≤ p) : ∀ i : ℤ, p ≤ i → i ≤ N + 1 → c1 * δ * ((i : ℝ) - p) ≤ X i - X p := by
  refine airy_int_up_induction (P := fun i => i ≤ N + 1 → c1 * δ * ((i : ℝ) - p) ≤ X i - X p) p
    (fun _ => by simp) ?_
  intro i hpi ih hi
  have h1 := ih (by omega)
  have h2 := hL.gap i (by simp only [mem_Icc]; omega)
  push_cast
  linarith

lemma AiryLattice.mono {X : ℤ → ℝ} {m N : ℤ} {c1 B δ : ℝ} (hL : AiryLattice X m N c1 B δ) {p i : ℤ}
    (hp : m ≤ p) (hpi : p ≤ i) (hi : i ≤ N + 1) : X p ≤ X i := by
  have h := hL.diff_ge hp i hpi hi
  have hpi' : (p : ℝ) ≤ i := by exact_mod_cast hpi
  have : 0 ≤ c1 * δ * ((i : ℝ) - p) :=
    mul_nonneg (mul_pos hL.c1_pos hL.δ_pos).le (by linarith)
  linarith

/-! ### Monotonicity and convexity of `ξ` -/

lemma airyXi_eq_sqrt_pow (X : ℝ) : airyXi X = 2 / 3 * (√(max X 0)) ^ 3 := by
  unfold airyXi
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (le_max_right X 0)]
  norm_num

lemma airyXi_mono {x y : ℝ} (h : x ≤ y) : airyXi x ≤ airyXi y := by
  rw [airyXi_eq_sqrt_pow, airyXi_eq_sqrt_pow]
  have : √(max x 0) ≤ √(max y 0) := Real.sqrt_le_sqrt (max_le_max h le_rfl)
  have h0 := Real.sqrt_nonneg (max x 0)
  have : (√(max x 0)) ^ 3 ≤ (√(max y 0)) ^ 3 := pow_le_pow_left₀ h0 this 3
  linarith

/-- `ξ(X) − ξ(Y) ≥ √max(Y,1) (X − Y) − 2` for `−1 ≤ Y ≤ X`. -/
theorem airyXi_diff_ge {X Y : ℝ} (hY : -1 ≤ Y) (hXY : Y ≤ X) :
    √(max Y 1) * (X - Y) - 2 ≤ airyXi X - airyXi Y := by
  rw [airyXi_eq_sqrt_pow, airyXi_eq_sqrt_pow]
  set u := √(max X 0) with hu
  set v := √(max Y 0) with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = max X 0 := Real.sq_sqrt (le_max_right _ _)
  have hv2 : v ^ 2 = max Y 0 := Real.sq_sqrt (le_max_right _ _)
  by_cases hY1 : 1 ≤ Y
  · have hX1 : 1 ≤ X := hY1.trans hXY
    have hXu : u ^ 2 = X := by rw [hu2, max_eq_left (by linarith)]
    have hYv : v ^ 2 = Y := by rw [hv2, max_eq_left (by linarith)]
    have hs : √(max Y 1) = v := by
      rw [max_eq_left hY1, hv, max_eq_left (by linarith)]
    rw [hs, ← hXu, ← hYv]
    have : v ≤ u := by nlinarith [sq_nonneg (u - v), sq_nonneg (u + v)]
    nlinarith [mul_nonneg (sq_nonneg (u - v)) (by linarith : 0 ≤ 2 * u + v)]
  · rw [not_le] at hY1
    have hs : √(max Y 1) = 1 := by rw [max_eq_right hY1.le]; simp
    rw [hs]
    have hvle : v ^ 2 ≤ 1 := by rw [hv2]; exact max_le hY1.le (by norm_num)
    have hv1 : v ≤ 1 := by nlinarith
    have hXu : X ≤ u ^ 2 := by rw [hu2]; exact le_max_left _ _
    have h1 : 0 ≤ (u - 1) ^ 2 * (2 * u + 1) := by positivity
    have h2 : v ^ 3 ≤ 1 := by
      have := pow_le_pow_left₀ hv0 hv1 3
      simpa using this
    nlinarith

/-- Linear lower bound (all `X ≥ Y ≥ -1`): `ξ(X) − ξ(Y) ≥ (2/3)(X − Y) − 4/3`. -/
theorem airyXi_diff_ge_lin {X Y : ℝ} (hY : -1 ≤ Y) (hXY : Y ≤ X) :
    2 / 3 * (X - Y) - 4 / 3 ≤ airyXi X - airyXi Y := by
  have hm := airyXi_mono hXY
  rw [airyXi_eq_sqrt_pow, airyXi_eq_sqrt_pow] at hm ⊢
  set u := √(max X 0) with hu
  set v := √(max Y 0) with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = max X 0 := Real.sq_sqrt (le_max_right _ _)
  have hv2 : v ^ 2 = max Y 0 := Real.sq_sqrt (le_max_right _ _)
  rcases le_or_gt 0 Y with hY0 | hY0
  · have hYv : v ^ 2 = Y := by rw [hv2, max_eq_left hY0]
    have hX0 : 0 ≤ X := hY0.trans hXY
    have hXu : u ^ 2 = X := by rw [hu2, max_eq_left hX0]
    rcases le_or_gt 1 X with hX1 | hX1
    · have hu1 : 1 ≤ u := by nlinarith
      have hvu : v ≤ u := by nlinarith
      have h1 : 0 ≤ v ^ 2 * (u - v) := mul_nonneg (sq_nonneg v) (by linarith)
      have h2 : u * (X - Y) ≤ u ^ 3 - v ^ 3 := by
        rw [← hXu, ← hYv]; nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 hXY) (sub_nonneg.2 hu1)]
    · nlinarith
  · have hY0' : v ^ 2 = 0 := by rw [hv2, max_eq_right hY0.le]
    have hv00 : v = 0 := by nlinarith
    rw [hv00] at hm ⊢
    rcases le_or_gt 1 X with hX1 | hX1
    · have hXu : u ^ 2 = X := by rw [hu2, max_eq_left (by linarith)]
      have hu1 : 1 ≤ u := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 hu1) hu0, mul_nonneg (mul_nonneg (sub_nonneg.2 hu1) hu0) hu0]
    · nlinarith

/-! ### The weight ratio -/

lemma two_add_abs_le {x z : ℝ} (hx : -1 ≤ x) (hxz : x ≤ z) : 2 + |x| ≤ 3 / 2 * (2 + |z|) := by
  rcases le_or_gt x 0 with h0 | h0
  · have : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith [abs_nonneg z]
  · rw [abs_of_pos h0, abs_of_pos (h0.trans_le hxz)]
    linarith

lemma rpow_neg_quarter_le {x z : ℝ} (hx : -1 ≤ x) (hxz : x ≤ z) :
    (2 + |z|) ^ (-(1 / 4) : ℝ) ≤ 3 / 2 * (2 + |x|) ^ (-(1 / 4) : ℝ) := by
  have hx2 : 0 < 2 + |x| := by positivity
  have hz2 : 0 < 2 + |z| := by positivity
  have h1 : 2 / 3 * (2 + |x|) ≤ 2 + |z| := by linarith [two_add_abs_le hx hxz]
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2 / 3 * (2 + |x|)) h1
    (by norm_num : -(1 / 4 : ℝ) ≤ 0)
  rw [Real.mul_rpow (by norm_num) hx2.le] at h2
  have h3 : (2 / 3 : ℝ) ^ (-(1 / 4) : ℝ) ≤ 3 / 2 := by
    rw [Real.rpow_neg (by norm_num), show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      inv_inv]
    calc (3 / 2 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 / 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 / 2 := by simp
  have hp : 0 < (2 + |x|) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx2 _
  calc (2 + |z|) ^ (-(1 / 4) : ℝ) ≤ (2 / 3 : ℝ) ^ (-(1 / 4) : ℝ) * (2 + |x|) ^ (-(1 / 4) : ℝ) := h2
    _ ≤ 3 / 2 * (2 + |x|) ^ (-(1 / 4) : ℝ) := by gcongr

/-- **Envelope decay relation** (`A:1112-1114`): `−1 ≤ x ≤ z ⇒ airyWt z ≤ (3/2) e^{−(ξ z − ξ x)} airyWt x`. -/
theorem airyWt_le_exp_mul {x z : ℝ} (hx : -1 ≤ x) (hxz : x ≤ z) :
    airyWt z ≤ 3 / 2 * Real.exp (-(airyXi z - airyXi x)) * airyWt x := by
  unfold airyWt
  have hE : Real.exp (-airyXi z) = Real.exp (-(airyXi z - airyXi x)) * Real.exp (-airyXi x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hE]
  have h := rpow_neg_quarter_le hx hxz
  have h0 := Real.exp_pos (-(airyXi z - airyXi x))
  have h1 := Real.exp_pos (-airyXi x)
  calc (2 + |z|) ^ (-(1 / 4) : ℝ) * (Real.exp (-(airyXi z - airyXi x)) * Real.exp (-airyXi x))
      ≤ (3 / 2 * (2 + |x|) ^ (-(1 / 4) : ℝ)) * (Real.exp (-(airyXi z - airyXi x)) * Real.exp (-airyXi x)) := by
        gcongr
    _ = _ := by ring

/-- `Wt_z² ≤ (9/4) e^{−2(ξ_z−ξ_y)} Wt_x Wt_y` for `−1 ≤ x ≤ y ≤ z`. -/
theorem airyWt_sq_le_exp_mul {x y z : ℝ} (hx : -1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    airyWt z ^ 2 ≤ 9 / 4 * Real.exp (-2 * (airyXi z - airyXi y)) * (airyWt x * airyWt y) := by
  have h1 := airyWt_le_exp_mul hx (hxy.trans hyz)
  have h2 := airyWt_le_exp_mul (hx.trans hxy) hyz
  have hxi : airyXi x ≤ airyXi y := airyXi_mono hxy
  have e1 : Real.exp (-(airyXi z - airyXi x)) ≤ Real.exp (-(airyXi z - airyXi y)) :=
    Real.exp_le_exp.2 (by linarith)
  have hz0 := (airyWt_pos z).le
  have hy0 := (airyWt_pos y).le
  have hx0 := (airyWt_pos x).le
  have hE : Real.exp (-2 * (airyXi z - airyXi y)) =
      Real.exp (-(airyXi z - airyXi y)) * Real.exp (-(airyXi z - airyXi y)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hE, sq]
  have h1' : airyWt z ≤ 3 / 2 * Real.exp (-(airyXi z - airyXi y)) * airyWt x := by
    refine h1.trans ?_
    gcongr
  calc airyWt z * airyWt z ≤ (3 / 2 * Real.exp (-(airyXi z - airyXi y)) * airyWt x) *
        (3 / 2 * Real.exp (-(airyXi z - airyXi y)) * airyWt y) :=
        mul_le_mul h1' h2 hz0 (by positivity)
    _ = _ := by ring

/-! ### Geometric tails along the lattice -/

/-- Geometric sum along a lattice: `Σ_{i ∈ [p,N]} e^{-t (i-p)} ≤ 1 + 1/t` for `t > 0`. -/
theorem sum_exp_geom_le {t : ℝ} (ht : 0 < t) (p N : ℤ) :
    ∑ i ∈ Icc p N, Real.exp (-t * ((i : ℝ) - p)) ≤ 1 + 1 / t := by
  set r := Real.exp (-t) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    calc r < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have h1r : 0 < 1 - r := by linarith
  have key : ∀ M : ℤ, p - 1 ≤ M →
      ∑ i ∈ Icc p M, Real.exp (-t * ((i : ℝ) - p)) ≤
        (1 - Real.exp (-t * ((M : ℝ) + 1 - p))) / (1 - r) := by
    refine airy_int_up_induction (p - 1) ?_ ?_
    · rw [Icc_eq_empty (by omega)]
      simp
    · intro M hM ih
      have hI : Icc p (M + 1) = insert (M + 1) (Icc p M) := by
        ext i; simp only [mem_Icc, mem_insert]; omega
      rw [hI, sum_insert (by simp)]
      set E := Real.exp (-t * ((M : ℝ) + 1 - p)) with hE
      have e1 : Real.exp (-t * (((M + 1 : ℤ) : ℝ) - p)) = E := by
        rw [hE]; congr 1; push_cast; ring
      have e2 : Real.exp (-t * (((M + 1 : ℤ) : ℝ) + 1 - p)) = E * r := by
        rw [hE, hr, ← Real.exp_add]; congr 1; push_cast; ring
      rw [e1, e2]
      have : (1 - E) / (1 - r) + E = (1 - E * r) / (1 - r) := by field_simp; ring
      linarith
  have hbound : 1 / (1 - r) ≤ 1 + 1 / t := by
    have hrt : r * Real.exp t = 1 := by rw [hr, ← Real.exp_add]; simp
    have hte : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
    rw [div_le_iff₀ h1r]
    have : r * (t + 1) ≤ 1 := by nlinarith
    have h3 : (1 + 1 / t) * (1 - r) = 1 + (1 - r * (t + 1)) / t := by field_simp; ring
    rw [h3]
    have : 0 ≤ (1 - r * (t + 1)) / t := div_nonneg (by linarith) ht.le
    linarith
  by_cases hN : p - 1 ≤ N
  · have h2 := key N hN
    have hE0 := (Real.exp_pos (-t * ((N : ℝ) + 1 - p))).le
    have : (1 - Real.exp (-t * ((N : ℝ) + 1 - p))) / (1 - r) ≤ 1 / (1 - r) :=
      div_le_div_of_nonneg_right (by linarith) h1r.le
    linarith
  · rw [Icc_eq_empty (by omega)]
    simp only [sum_empty]
    have : 0 ≤ 1 / t := by positivity
    linarith

/-- **Exponential tail along the lattice.**  For `p ∈ [m, N+1]`,
`Σ_{i ∈ [p,N]} e^{−2(ξ(X_i) − ξ(X_p))} ≤ e⁴ (1 + 1/(2 c₁ δ √max(X_p,1)))`. -/
theorem expTail_le {X : ℤ → ℝ} {m N : ℤ} {c1 B δ : ℝ} (hL : AiryLattice X m N c1 B δ) {p : ℤ}
    (hp : m ≤ p) :
    ∑ i ∈ Icc p N, Real.exp (-2 * (airyXi (X i) - airyXi (X p))) ≤
      Real.exp 4 * (1 + 1 / (2 * c1 * δ * √(max (X p) 1))) := by
  by_cases hpN : p ≤ N + 1
  swap
  · rw [Icc_eq_empty (by omega)]
    simp only [sum_empty]
    have := hL.c1_pos; have := hL.δ_pos
    positivity
  set s := √(max (X p) 1) with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (le_max_right _ _)
  have hc := hL.c1_pos
  have hδ := hL.δ_pos
  have ht : 0 < 2 * s * (c1 * δ) := by positivity
  have hterm : ∀ i ∈ Icc p N, Real.exp (-2 * (airyXi (X i) - airyXi (X p))) ≤
      Real.exp 4 * Real.exp (-(2 * s * (c1 * δ)) * ((i : ℝ) - p)) := by
    intro i hi
    rw [mem_Icc] at hi
    have hXp := hL.lo p (by simp only [mem_Icc]; omega)
    have hmono := hL.mono hp hi.1 (by omega)
    have hd := airyXi_diff_ge hXp hmono
    have hdg := hL.diff_ge hp i hi.1 (by omega)
    have hs0 : 0 ≤ s := by linarith
    have h1 : s * (c1 * δ * ((i : ℝ) - p)) ≤ s * (X i - X p) := mul_le_mul_of_nonneg_left hdg hs0
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have h := sum_exp_geom_le ht p N
  have : 1 / (2 * s * (c1 * δ)) = 1 / (2 * c1 * δ * s) := by ring
  rw [this] at h
  gcongr

/-! ### Sums over the lattice -/

private lemma inv_sqrt_step' {x y g : ℝ} (hx : 0 < x) (hxy : x + g ≤ y) (hg : 0 < g) :
    (√y)⁻¹ * g ≤ 2 * (√y - √x) := by
  have hy : 0 < y := by linarith
  have hu : 0 < √y := Real.sqrt_pos.2 hy
  have huv : √x ≤ √y := Real.sqrt_le_sqrt (by linarith)
  have h1 : (√y) ^ 2 = y := Real.sq_sqrt hy.le
  have h2 : (√x) ^ 2 = x := Real.sq_sqrt hx.le
  have hv := Real.sqrt_nonneg x
  have : (√y)⁻¹ * g ≤ (√y)⁻¹ * (y - x) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine this.trans ?_
  rw [inv_mul_le_iff₀ hu]
  nlinarith [sq_nonneg (√y - √x)]

/-- Lattice sum of `(3+X)^{-1/2}` against a `c₁δ`-separated lattice (`a ≤ b` in the window):
`Σ_{p ∈ [a,b]} (√(3+X_p))⁻¹ ≤ 1 + (2/(c₁δ)) (√(3+X_b) − √(3+X_a))`. -/
theorem sum_inv_sqrt_lattice {X : ℤ → ℝ} {m N : ℤ} {c1 B δ : ℝ} (hL : AiryLattice X m N c1 B δ)
    {a : ℤ} (ha : m ≤ a) :
    ∀ b : ℤ, a ≤ b → b ≤ N + 1 →
      ∑ p ∈ Icc a b, (√(3 + X p))⁻¹ ≤ 1 + 2 / (c1 * δ) * (√(3 + X b) - √(3 + X a)) := by
  have hg : 0 < c1 * δ := mul_pos hL.c1_pos hL.δ_pos
  refine airy_int_up_induction (P := fun b => b ≤ N + 1 →
      ∑ p ∈ Icc a b, (√(3 + X p))⁻¹ ≤ 1 + 2 / (c1 * δ) * (√(3 + X b) - √(3 + X a))) a ?_ ?_
  · intro _
    rw [Icc_self, sum_singleton]
    have hXa := hL.lo a (by simp only [mem_Icc]; omega)
    have h2 : (1 : ℝ) ≤ √(3 + X a) := Real.one_le_sqrt.2 (by linarith)
    have : (√(3 + X a))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
    simpa using this
  · intro b hab ih hb
    have hI : Icc a (b + 1) = insert (b + 1) (Icc a b) := by
      ext i; simp only [mem_Icc, mem_insert]; omega
    rw [hI, sum_insert (by simp)]
    have ih' := ih (by omega)
    have hXb := hL.lo b (by simp only [mem_Icc]; omega)
    have hgap := hL.gap b (by simp only [mem_Icc]; omega)
    have hstep := inv_sqrt_step' (x := 3 + X b) (y := 3 + X (b + 1)) (g := c1 * δ)
      (by linarith) (by linarith) hg
    have : (√(3 + X (b + 1)))⁻¹ ≤ 2 / (c1 * δ) * (√(3 + X (b + 1)) - √(3 + X b)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hg]; linarith
    linarith

/-- Lattice cardinality: `(N - m) c₁ δ ≤ B δ⁻² + 1`. -/
theorem AiryLattice.card_le {X : ℤ → ℝ} {m N : ℤ} {c1 B δ : ℝ} (hL : AiryLattice X m N c1 B δ)
    (hmN : m ≤ N) : ((N : ℝ) - m) * (c1 * δ) ≤ B / δ ^ 2 + 1 := by
  have h := hL.diff_ge (le_refl m) N hmN (by omega)
  have h1 := hL.hi N (by simp only [mem_Icc]; omega)
  have h2 := hL.lo m (by simp only [mem_Icc]; omega)
  nlinarith

/-- The constant `C_G` of `expTail_sum_le`. -/
noncomputable def expTailConst (c1 B : ℝ) : ℝ :=
  Real.exp 4 * ((B + 1) / c1 + √6 / (2 * c1) + √6 * √(3 + B) / c1 ^ 2)

/-- **The double kernel sum** (`A:1119-1124` in the order summed over `i` first):
`Σ_{p ∈ [m+1,N]} Σ_{i ∈ [p,N]} e^{−2(ξ_i − ξ_p)} ≤ C_G δ⁻³`. -/
theorem expTail_sum_le {X : ℤ → ℝ} {m N : ℤ} {c1 B δ : ℝ} (hL : AiryLattice X m N c1 B δ) :
    ∑ p ∈ Icc (m + 1) N, ∑ i ∈ Icc p N, Real.exp (-2 * (airyXi (X i) - airyXi (X p))) ≤
      expTailConst c1 B / δ ^ 3 := by
  have hc := hL.c1_pos
  have hδ := hL.δ_pos
  have hB := hL.B_nonneg
  have hδ1 := hL.δ_le_one
  have hCG : 0 ≤ expTailConst c1 B / δ ^ 3 := by unfold expTailConst; positivity
  by_cases hmN : m + 1 ≤ N
  swap
  · rw [Icc_eq_empty (by omega)]; simpa using hCG
  have hs6 : (0 : ℝ) < √6 := Real.sqrt_pos.2 (by norm_num)
  -- pointwise bound
  have h1 : ∀ p ∈ Icc (m + 1) N, ∑ i ∈ Icc p N, Real.exp (-2 * (airyXi (X i) - airyXi (X p))) ≤
      Real.exp 4 * (1 + √6 / (2 * c1 * δ) * (√(3 + X p))⁻¹) := by
    intro p hp
    rw [mem_Icc] at hp
    refine (expTail_le hL (by omega)).trans ?_
    have hXp := hL.lo p (by simp only [mem_Icc]; omega)
    set s := √(max (X p) 1) with hs
    have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (le_max_right _ _)
    have hle : √(3 + X p) ≤ √6 * s := by
      rw [hs, ← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      rcases le_total (X p) 1 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hpos : 0 < √(3 + X p) := Real.sqrt_pos.2 (by linarith)
    have h0 : 1 / (2 * c1 * δ * s) ≤ √6 / (2 * c1 * δ) * (√(3 + X p))⁻¹ := by
      have e : √6 / (2 * c1 * δ) * (√(3 + X p))⁻¹ = √6 / (2 * c1 * δ * √(3 + X p)) := by
        field_simp
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * c1 * δ)]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 4).le
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum, sum_add_distrib, ← mul_sum]
  -- the two sums
  have hcard : ∑ p ∈ Icc (m + 1) N, (1 : ℝ) = (N : ℝ) - m := by
    rw [sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
    have : (0 : ℤ) ≤ N + 1 - (m + 1) := by omega
    rw [show ((N + 1 - (m + 1)).toNat : ℝ) = (((N + 1 - (m + 1)).toNat : ℤ) : ℝ) by norm_cast,
      Int.toNat_of_nonneg this]
    push_cast; ring
  have hS := sum_inv_sqrt_lattice hL (a := m + 1) (by omega) N hmN (by omega)
  have hXN := hL.hi N (by simp only [mem_Icc]; omega)
  have hXN0 := hL.lo N (by simp only [mem_Icc]; omega)
  have hsq : √(3 + X N) ≤ √(3 + B) / δ := by
    rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt (by linarith)]
    have h1 : (1 : ℝ) ≤ 1 / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hXN' : X N * δ ^ 2 ≤ B := (le_div_iff₀ (by positivity)).1 hXN
    rw [le_div_iff₀ (by positivity)] at h1 ⊢
    nlinarith
  have hcl := hL.card_le (by omega : m ≤ N)
  have hδ3 : 0 < δ ^ 3 := by positivity
  have e1 : (N : ℝ) - m ≤ (B + 1) / c1 / δ ^ 3 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    calc ((N : ℝ) - m) * (c1 * δ ^ 3) = (((N : ℝ) - m) * (c1 * δ)) * δ ^ 2 := by ring
      _ ≤ (B / δ ^ 2 + 1) * δ ^ 2 := by gcongr
      _ = B + δ ^ 2 := by field_simp
      _ ≤ B + 1 := by nlinarith
  have hSN : ∑ p ∈ Icc (m + 1) N, (√(3 + X p))⁻¹ ≤ 1 + 2 / (c1 * δ) * √(3 + X N) := by
    have := Real.sqrt_nonneg (3 + X (m + 1))
    have h2 : 0 ≤ 2 / (c1 * δ) * √(3 + X (m + 1)) := by positivity
    nlinarith
  have e2 : √6 / (2 * c1 * δ) * 1 ≤ √6 / (2 * c1) / δ ^ 3 := by
    rw [div_div, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have : δ ^ 3 ≤ δ := by nlinarith [pow_le_one₀ hδ.le hδ1 (n := 2)]
    nlinarith [mul_pos hs6 hc]
  have e3 : √6 / (2 * c1 * δ) * (2 / (c1 * δ) * √(3 + X N)) ≤ √6 * √(3 + B) / c1 ^ 2 / δ ^ 3 := by
    have h4 : √6 / (2 * c1 * δ) * (2 / (c1 * δ) * √(3 + X N)) ≤
        √6 / (2 * c1 * δ) * (2 / (c1 * δ) * (√(3 + B) / δ)) := by gcongr
    refine h4.trans (le_of_eq ?_)
    field_simp
  have hmain : ((N : ℝ) - m) + √6 / (2 * c1 * δ) * ∑ p ∈ Icc (m + 1) N, (√(3 + X p))⁻¹ ≤
      ((B + 1) / c1 + √6 / (2 * c1) + √6 * √(3 + B) / c1 ^ 2) / δ ^ 3 := by
    have hq : 0 ≤ √6 / (2 * c1 * δ) := by positivity
    have := mul_le_mul_of_nonneg_left hSN hq
    have e4 : ((B + 1) / c1 + √6 / (2 * c1) + √6 * √(3 + B) / c1 ^ 2) / δ ^ 3 =
        (B + 1) / c1 / δ ^ 3 + √6 / (2 * c1) / δ ^ 3 + √6 * √(3 + B) / c1 ^ 2 / δ ^ 3 := by ring
    rw [e4]
    have e5 : √6 / (2 * c1 * δ) * (1 + 2 / (c1 * δ) * √(3 + X N)) =
        √6 / (2 * c1 * δ) * 1 + √6 / (2 * c1 * δ) * (2 / (c1 * δ) * √(3 + X N)) := by ring
    linarith
  rw [hcard]
  unfold expTailConst
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hmain (Real.exp_pos 4).le

/-- Backward geometric sum along a lattice: `Σ_{p ∈ [m,k]} e^{-t (k-p)} ≤ 1 + 1/t` for `t > 0`. -/
theorem sum_exp_geom_back_le {t : ℝ} (ht : 0 < t) (m k : ℤ) :
    ∑ p ∈ Icc m k, Real.exp (-t * ((k : ℝ) - p)) ≤ 1 + 1 / t := by
  have h := sum_exp_geom_le ht 0 (k - m)
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_nbij' (fun p => k - p) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
  · intro p hp; simp only [mem_Icc] at hp ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro p _; simp
  · intro i _; simp
  · intro p _; push_cast; congr 2; ring

/-- **Backward exponential tail** (uniform form): for `k ≤ N+1`,
`Σ_{p ∈ (m,k]} e^{-2(ξ_k − ξ_p)} ≤ e^{8/3}(1 + 3/(4 c₁ δ))`. -/
theorem expBack_le {X : ℤ → ℝ} {m N : ℤ} {c1 B δ : ℝ} (hL : AiryLattice X m N c1 B δ) {k : ℤ}
    (hkN : k ≤ N + 1) :
    ∑ p ∈ Ioc m k, Real.exp (-2 * (airyXi (X k) - airyXi (X p))) ≤
      Real.exp (8 / 3) * (1 + 3 / (4 * c1 * δ)) := by
  have hc := hL.c1_pos
  have hδ := hL.δ_pos
  have ht : 0 < 4 / 3 * (c1 * δ) := by positivity
  have hterm : ∀ p ∈ Ioc m k, Real.exp (-2 * (airyXi (X k) - airyXi (X p))) ≤
      Real.exp (8 / 3) * Real.exp (-(4 / 3 * (c1 * δ)) * ((k : ℝ) - p)) := by
    intro p hp
    rw [mem_Ioc] at hp
    have hXp := hL.lo p (by simp only [mem_Icc]; omega)
    have hmono := hL.mono (by omega) hp.2 hkN
    have hd := airyXi_diff_ge_lin hXp hmono
    have hdg := hL.diff_ge (by omega : m ≤ p) k hp.2 hkN
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have h := sum_exp_geom_back_le ht m k
  have hsub : ∑ p ∈ Ioc m k, Real.exp (-(4 / 3 * (c1 * δ)) * ((k : ℝ) - p)) ≤
      ∑ p ∈ Icc m k, Real.exp (-(4 / 3 * (c1 * δ)) * ((k : ℝ) - p)) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp; simp only [mem_Ioc, mem_Icc] at hp ⊢; omega
    · intro p _ _; exact (Real.exp_pos _).le
  have e : 1 / (4 / 3 * (c1 * δ)) = 3 / (4 * c1 * δ) := by field_simp
  rw [e] at h
  gcongr
  linarith

/-- info: 'FormalResearch.Special.airyWt_le_exp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyWt_le_exp_mul

/-- info: 'FormalResearch.Special.airyWt_sq_le_exp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyWt_sq_le_exp_mul

/-- info: 'FormalResearch.Special.airyXi_diff_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyXi_diff_ge

/-- info: 'FormalResearch.Special.airyXi_diff_ge_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyXi_diff_ge_lin

/-- info: 'FormalResearch.Special.expTail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.expTail_le

/-- info: 'FormalResearch.Special.expTail_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.expTail_sum_le

/-- info: 'FormalResearch.Special.expBack_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.expBack_le

end FormalResearch.Special
