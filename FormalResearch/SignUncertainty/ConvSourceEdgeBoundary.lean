module

public import FormalResearch.SignUncertainty.ConvSourceEdgeProduct
public import FormalResearch.SignUncertainty.ConvSourceSymbolBounds
public import FormalResearch.CohnElkies.SeedSymbolDerivs

/-!
# The boundary passage `δ ↓ 0` for Laplace transforms of weights (M6, `ceo:conv` (4), `(ceo:conv.5)`)

For a weight `w` integrable on `(0, ∞)` the moment transforms `convSD w k` are the successive complex derivatives of `lapW w` on `Re z > 0`
(`ConvSourceSymbol`).  `(ceo:conv.5)` of the paper is first proved there on `Re z = δ > 0` uniformly in `δ` and then passed to the boundary `δ ↓ 0`
("dominated convergence for `ℒ w_h`, equicontinuity of the derivatives").  This module does the passage once and for all:

* `ConvInterior w C`: the interior estimates (large `‖z‖`: `‖z‖^{-k-1}`; small: `‖z‖^{1/2-k}`; `‖lapW‖ ≤ C`; the `1/2`-Hölder bound at `0`);
* `lapBounds_of_interior`: if `w` satisfies `ConvInterior w C` and `a ≥ 1`, then `v ↦ lapW w (i a v)` satisfies `LapBounds (2 C a³)` on the real line: it is `C³`
  off `0` and has the bounds of `(ceo:conv.5)` (class: proved).  The derivatives are the boundary limits `∂_v^k = i^k lim_{n} convSD w k` along `1/(n+1) + i a v`, and
  the passage is `boundary_step` of `SeedSymbolDerivs` (uniform Lipschitz bound of the next derivative on `{‖z‖ > r}`).

The interior estimates for `w_h` and the exponential term, and the assembly with the seed symbol, are in `ConvSourceEdgeLap`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `lapW w` is continuous on the closed right half plane (dominated convergence). -/
theorem continuousOn_lapW {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) :
    ContinuousOn (lapW w) {z : ℂ | 0 ≤ z.re} := by
  unfold lapW
  refine continuousOn_of_dominated (bound := fun y => ‖w y‖) (fun z hz => (integrableOn_lapW hw hz).1) ?_ hw.norm ?_
  · intro z hz
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    rw [norm_mul, Complex.norm_real]
    calc ‖w y‖ * ‖Complex.exp (-(z * (y : ℂ)))‖ ≤ ‖w y‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_exp_neg_mul_le hz (le_of_lt hy)) (norm_nonneg _)
      _ = ‖w y‖ := mul_one _
  · exact Eventually.of_forall fun y => (by fun_prop : Continuous fun z : ℂ => (w y : ℂ) * Complex.exp (-(z * (y : ℂ)))).continuousOn

/-- The moment transform rescaled by `a`: `a^k convSD w k (a z)`, so that `∂_z convSDs k = convSDs (k+1)`. -/
noncomputable def convSDs (w : ℝ → ℝ) (a : ℝ) (k : ℕ) (z : ℂ) : ℂ := (a : ℂ) ^ k * convSD w k ((a : ℂ) * z)

lemma convSDs_zero (w : ℝ → ℝ) (a : ℝ) (z : ℂ) : convSDs w a 0 z = lapW w ((a : ℂ) * z) := by
  simp [convSDs, convSD_zero]

lemma convSDs_hasDerivAt {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) {a : ℝ} (ha : 0 < a) (k : ℕ) {z : ℂ}
    (hz : 0 < z.re) : HasDerivAt (convSDs w a k) (convSDs w a (k + 1) z) z := by
  have hre : 0 < ((a : ℂ) * z).re := by simpa [Complex.mul_re] using mul_pos ha hz
  have h1 := convSD_hasDerivAt hw k hre
  have h2 : HasDerivAt (fun z : ℂ => (a : ℂ) * z) (a : ℂ) z := by simpa using (hasDerivAt_id z).const_mul (a : ℂ)
  have h3 := (h1.comp z h2).const_mul ((a : ℂ) ^ k)
  have e : convSDs w a (k + 1) z = (a : ℂ) ^ k * (convSD w (k + 1) ((a : ℂ) * z) * (a : ℂ)) := by
    unfold convSDs; ring
  rw [e]
  exact h3

/-- The boundary limit `lim_n G(1/(n+1) + ω i)` (junk value if it does not exist). -/
noncomputable def bdLim (G : ℂ → ℂ) (ω : ℝ) : ℂ := limUnder atTop (fun n : ℕ => G (bpt n ω))

/-- One boundary step: if `G` has derivative `G1`, `G1` has derivative `G2` bounded over `{|Im y| > r}` and `G(bpt n ω)` converges for `|ω| > r`, then
`G1(bpt n ω)` converges there and `bdLim G` has derivative `i · bdLim G1`. -/
lemma bd_step {G G1 G2 : ℂ → ℂ} {r M : ℝ} (hM0 : 0 ≤ M)
    (hG : ∀ y : ℂ, 0 < y.re → HasDerivAt G (G1 y) y) (hG1 : ∀ y : ℂ, 0 < y.re → HasDerivAt G1 (G2 y) y)
    (hM : ∀ y : ℂ, 0 < y.re → r < |y.im| → ‖G2 y‖ ≤ M)
    (h0 : ∀ ω : ℝ, r < |ω| → Tendsto (fun n : ℕ => G (bpt n ω)) atTop (𝓝 (bdLim G ω))) :
    (∀ ω : ℝ, r < |ω| → Tendsto (fun n : ℕ => G1 (bpt n ω)) atTop (𝓝 (bdLim G1 ω))) ∧
      ∀ ω : ℝ, r < |ω| → HasDerivAt (bdLim G) (Complex.I * bdLim G1 ω) ω := by
  have hs : IsOpen {ω : ℝ | r < |ω|} := isOpen_lt continuous_const continuous_abs
  obtain ⟨h, hh, hd⟩ := boundary_step (F := G) (F1 := G1) (F2 := G2) hs hM0 (fun y hy _ => hG y hy)
    (fun y hy _ => hG1 y hy) (fun y hy hs' => hM y hy hs') (g := bdLim G) (fun ω hω => h0 ω hω)
  have heq : ∀ ω : ℝ, r < |ω| → bdLim G1 ω = h ω := fun ω hω => (hh ω hω).limUnder_eq
  refine ⟨fun ω hω => ?_, fun ω hω => ?_⟩
  · rw [heq ω hω]; exact hh ω hω
  · rw [heq ω hω]; exact hd ω hω

lemma tendsto_norm_bpt (ω : ℝ) : Tendsto (fun n : ℕ => ‖bpt n ω‖) atTop (𝓝 |ω|) := by
  have := (tendsto_bpt ω).norm
  simpa using this

/-- Passing a norm bound along `bpt` to the limit. -/
lemma norm_le_of_bpt {G : ℂ → ℂ} {ω : ℝ} {y : ℂ} (hy : Tendsto (fun n : ℕ => G (bpt n ω)) atTop (𝓝 y))
    {φ : ℝ → ℝ} (hφ : ContinuousAt φ |ω|) (hb : ∀ᶠ n : ℕ in atTop, ‖G (bpt n ω)‖ ≤ φ ‖bpt n ω‖) :
    ‖y‖ ≤ φ |ω| :=
  le_of_tendsto_of_tendsto hy.norm (hφ.tendsto.comp (tendsto_norm_bpt ω)) hb

/-- The interior estimates of `(ceo:conv.5)` for a weight `w`, with one constant `C`. -/
structure ConvInterior (w : ℝ → ℝ) (C : ℝ) : Prop where
  integrable : IntegrableOn w (Ioi 0)
  nonneg : 0 ≤ C
  big : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ z : ℂ, 0 < z.re → ‖convSD w k z‖ ≤ C * ‖z‖ ^ (-(k : ℝ) - 1)
  small : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ z : ℂ, 0 < z.re → ‖z‖ ≤ 1 → ‖convSD w k z‖ ≤ C * ‖z‖ ^ (1 / 2 - (k : ℝ))
  bdd : ∀ z : ℂ, 0 ≤ z.re → ‖lapW w z‖ ≤ C
  hold : ∀ z : ℂ, 0 < z.re → ‖z‖ ≤ 1 → ‖lapW w z - lapW w 0‖ ≤ C * ‖z‖ ^ (1 / 2 : ℝ)

section scaled

variable {w : ℝ → ℝ} {C a : ℝ}

lemma norm_ofReal_mul' (a : ℝ) (ha : 0 < a) (z : ℂ) : ‖(a : ℂ) * z‖ = a * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

lemma convSDs_big (h : ConvInterior w C) (ha : 1 ≤ a) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {z : ℂ} (hz : 0 < z.re) :
    ‖convSDs w a k z‖ ≤ C * ‖z‖ ^ (-(k : ℝ) - 1) := by
  have ha0 : 0 < a := by linarith
  have hre : 0 < ((a : ℂ) * z).re := by simpa [Complex.mul_re] using mul_pos ha0 hz
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h1 := h.big k hk1 hk4 _ hre
  rw [norm_ofReal_mul' a ha0, Real.mul_rpow ha0.le hzn.le] at h1
  unfold convSDs
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  have hp : 0 ≤ ‖z‖ ^ (-(k : ℝ) - 1) := Real.rpow_nonneg hzn.le _
  have ha1 : a ^ k * a ^ (-(k : ℝ) - 1) = a ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha0]; congr 1; ring
  have ha2 : a ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by norm_num)
  calc a ^ k * ‖convSD w k ((a : ℂ) * z)‖ ≤ a ^ k * (C * (a ^ (-(k : ℝ) - 1) * ‖z‖ ^ (-(k : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * (a ^ k * a ^ (-(k : ℝ) - 1)) * ‖z‖ ^ (-(k : ℝ) - 1) := by ring
    _ = C * a ^ (-1 : ℝ) * ‖z‖ ^ (-(k : ℝ) - 1) := by rw [ha1]
    _ ≤ C * 1 * ‖z‖ ^ (-(k : ℝ) - 1) := by gcongr; exact h.nonneg
    _ = _ := by ring

lemma convSDs_small (h : ConvInterior w C) (ha : 1 ≤ a) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {z : ℂ} (hz : 0 < z.re)
    (hz1 : ‖z‖ ≤ 1) : ‖convSDs w a k z‖ ≤ C * a ^ 3 * ‖z‖ ^ (1 / 2 - (k : ℝ)) := by
  have ha0 : 0 < a := by linarith
  have hre : 0 < ((a : ℂ) * z).re := by simpa [Complex.mul_re] using mul_pos ha0 hz
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hC := h.nonneg
  have hk1' : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk1
  have hk3' : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
  have hpz : 0 ≤ ‖z‖ ^ (1 / 2 - (k : ℝ)) := Real.rpow_nonneg hzn.le _
  have hpz1 : 1 ≤ ‖z‖ ^ (1 / 2 - (k : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hzn hz1 (by linarith)
  have hak : a ^ k ≤ a ^ 3 := pow_le_pow_right₀ ha hk3
  have ha3 : 0 ≤ a ^ 3 := by positivity
  unfold convSDs
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  by_cases hs : a * ‖z‖ ≤ 1
  · have h1 := h.small k hk1 hk3 _ hre (by rw [norm_ofReal_mul' a ha0]; exact hs)
    rw [norm_ofReal_mul' a ha0, Real.mul_rpow ha0.le hzn.le] at h1
    have ha1 : a ^ k * a ^ (1 / 2 - (k : ℝ)) = a ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ha0]; congr 1; ring
    have ha2 : a ^ (1 / 2 : ℝ) ≤ a ^ 3 := by
      calc a ^ (1 / 2 : ℝ) ≤ a ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
        _ = a ^ 3 := by norm_cast
    calc a ^ k * ‖convSD w k ((a : ℂ) * z)‖ ≤ a ^ k * (C * (a ^ (1 / 2 - (k : ℝ)) * ‖z‖ ^ (1 / 2 - (k : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C * (a ^ k * a ^ (1 / 2 - (k : ℝ))) * ‖z‖ ^ (1 / 2 - (k : ℝ)) := by ring
      _ = C * a ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 / 2 - (k : ℝ)) := by rw [ha1]
      _ ≤ C * a ^ 3 * ‖z‖ ^ (1 / 2 - (k : ℝ)) := by gcongr
  · rw [not_le] at hs
    have h1 := h.big k hk1 (by omega) _ hre
    rw [norm_ofReal_mul' a ha0] at h1
    have hr : (a * ‖z‖) ^ (-(k : ℝ) - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hs.le (by linarith)
    calc a ^ k * ‖convSD w k ((a : ℂ) * z)‖ ≤ a ^ k * (C * 1) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hr hC
      _ ≤ a ^ 3 * C * 1 := by
          have := mul_le_mul_of_nonneg_right hak hC
          nlinarith
      _ ≤ C * a ^ 3 * ‖z‖ ^ (1 / 2 - (k : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hpz1 (mul_nonneg hC ha3)
          nlinarith

end scaled

/-- **The boundary passage** (`(ceo:conv.5)` on `Re z = 0`): if `w` has the interior estimates `ConvInterior w C` and `a ≥ 1`, then `v ↦ lapW w (i a v)`
satisfies `LapBounds (2 C a³)`: it is three times differentiable off `0` with the bounds of `(ceo:conv.5)`.  The derivatives are
`i^k` times the boundary limits of `convSDs w a k` along `1/(n+1) + i v`. -/
theorem lapBounds_of_interior {w : ℝ → ℝ} {C a : ℝ} (ha : 1 ≤ a) (h : ConvInterior w C) :
    LapBounds (2 * C * a ^ 3) (fun v : ℝ => lapW w ((((a * v : ℝ)) : ℂ) * Complex.I)) := by
  have ha0 : 0 < a := by linarith
  have hw := h.integrable
  have hC := h.nonneg
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
  have hCa : 0 ≤ C * a ^ 3 := by positivity
  -- the zeroth boundary limit
  have h0 : ∀ ω : ℝ, Tendsto (fun n : ℕ => convSDs w a 0 (bpt n ω)) atTop
      (𝓝 (lapW w ((((a * ω : ℝ)) : ℂ) * Complex.I))) := by
    intro ω
    have ht : Tendsto (fun n : ℕ => (a : ℂ) * bpt n ω) atTop (𝓝 ((a : ℂ) * ((ω : ℂ) * Complex.I))) :=
      (tendsto_bpt ω).const_mul _
    have hmem : ∀ n : ℕ, (a : ℂ) * bpt n ω ∈ {z : ℂ | 0 ≤ z.re} := fun n => by
      show 0 ≤ ((a : ℂ) * bpt n ω).re
      have : ((a : ℂ) * bpt n ω).re = a * (bpt n ω).re := by simp [Complex.mul_re]
      rw [this, bpt_re]; positivity
    have hlim : ((a : ℂ) * ((ω : ℂ) * Complex.I)) ∈ {z : ℂ | 0 ≤ z.re} := by
      show 0 ≤ ((a : ℂ) * ((ω : ℂ) * Complex.I)).re
      simp [Complex.mul_re]
    have := ((continuousOn_lapW hw) _ hlim).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hmem⟩)
    have e : (a : ℂ) * ((ω : ℂ) * Complex.I) = (((a * ω : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [e] at this
    have e2 : (fun n : ℕ => convSDs w a 0 (bpt n ω)) = lapW w ∘ fun n : ℕ => (a : ℂ) * bpt n ω := by
      funext n; simp [convSDs_zero]
    rw [e2]; exact this
  have hΛ : ∀ ω : ℝ, bdLim (convSDs w a 0) ω = lapW w ((((a * ω : ℝ)) : ℂ) * Complex.I) := fun ω => (h0 ω).limUnder_eq
  have h0' : ∀ ω : ℝ, Tendsto (fun n : ℕ => convSDs w a 0 (bpt n ω)) atTop (𝓝 (bdLim (convSDs w a 0) ω)) := fun ω => by
    rw [hΛ]; exact h0 ω
  -- the chain of boundary steps
  have chain : ∀ ω : ℝ, ω ≠ 0 →
      (∀ k : ℕ, k ≤ 3 → Tendsto (fun n : ℕ => convSDs w a k (bpt n ω)) atTop (𝓝 (bdLim (convSDs w a k) ω))) ∧
      HasDerivAt (bdLim (convSDs w a 0)) (Complex.I * bdLim (convSDs w a 1) ω) ω ∧
      HasDerivAt (bdLim (convSDs w a 1)) (Complex.I * bdLim (convSDs w a 2) ω) ω ∧
      HasDerivAt (bdLim (convSDs w a 2)) (Complex.I * bdLim (convSDs w a 3) ω) ω := by
    intro ω hω
    set r : ℝ := |ω| / 2 with hr
    have hr0 : 0 < r := by have := abs_pos.mpr hω; positivity
    have hrω : r < |ω| := by have := abs_pos.mpr hω; linarith
    have hbd : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ y : ℂ, 0 < y.re → r < |y.im| →
        ‖convSDs w a j y‖ ≤ C * r ^ (-(j : ℝ) - 1) := by
      intro j hj1 hj4 y hy hry
      refine (convSDs_big h ha hj1 hj4 hy).trans ?_
      have hyn : r ≤ ‖y‖ := hry.le.trans (Complex.abs_im_le_norm y)
      have hj : (1 : ℝ) ≤ j := Nat.one_le_cast.mpr hj1
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr0 hyn (by linarith)) hC
    have hM : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → 0 ≤ C * r ^ (-(j : ℝ) - 1) := fun j _ _ =>
      mul_nonneg hC (Real.rpow_nonneg hr0.le _)
    obtain ⟨t1, d0⟩ := bd_step (G := convSDs w a 0) (G1 := convSDs w a 1) (G2 := convSDs w a 2) (r := r)
      (hM 2 (by norm_num) (by norm_num)) (fun y hy => convSDs_hasDerivAt hw ha0 0 hy)
      (fun y hy => convSDs_hasDerivAt hw ha0 1 hy) (fun y hy hry => by simpa using hbd 2 (by norm_num) (by norm_num) y hy hry)
      (fun ω' _ => h0' ω')
    obtain ⟨t2, d1⟩ := bd_step (G := convSDs w a 1) (G1 := convSDs w a 2) (G2 := convSDs w a 3) (r := r)
      (hM 3 (by norm_num) (by norm_num)) (fun y hy => convSDs_hasDerivAt hw ha0 1 hy)
      (fun y hy => convSDs_hasDerivAt hw ha0 2 hy) (fun y hy hry => by simpa using hbd 3 (by norm_num) (by norm_num) y hy hry)
      t1
    obtain ⟨t3, d2⟩ := bd_step (G := convSDs w a 2) (G1 := convSDs w a 3) (G2 := convSDs w a 4) (r := r)
      (hM 4 (by norm_num) (by norm_num)) (fun y hy => convSDs_hasDerivAt hw ha0 2 hy)
      (fun y hy => convSDs_hasDerivAt hw ha0 3 hy) (fun y hy hry => by simpa using hbd 4 (by norm_num) (by norm_num) y hy hry)
      t2
    refine ⟨fun k hk => ?_, d0 ω hrω, d1 ω hrω, d2 ω hrω⟩
    interval_cases k
    · exact h0' ω
    · exact t1 ω hrω
    · exact t2 ω hrω
    · exact t3 ω hrω
  -- norm bounds of the boundary limits
  have hbigL : ∀ ω : ℝ, ω ≠ 0 → ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
      ‖bdLim (convSDs w a k) ω‖ ≤ C * |ω| ^ (-(k : ℝ) - 1) := by
    intro ω hω k hk1 hk3
    have hne : |ω| ≠ 0 := abs_ne_zero.mpr hω
    refine norm_le_of_bpt ((chain ω hω).1 k hk3) (φ := fun t : ℝ => C * t ^ (-(k : ℝ) - 1))
      (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hne))) (Eventually.of_forall fun n => ?_)
    exact convSDs_big h ha hk1 (by omega) (by rw [bpt_re]; positivity)
  have hsmallL : ∀ ω : ℝ, ω ≠ 0 → |ω| < 1 → ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
      ‖bdLim (convSDs w a k) ω‖ ≤ C * a ^ 3 * |ω| ^ (1 / 2 - (k : ℝ)) := by
    intro ω hω hω1 k hk1 hk3
    have hne : |ω| ≠ 0 := abs_ne_zero.mpr hω
    refine norm_le_of_bpt ((chain ω hω).1 k hk3) (φ := fun t : ℝ => C * a ^ 3 * t ^ (1 / 2 - (k : ℝ)))
      (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hne))) ?_
    filter_upwards [(tendsto_norm_bpt ω).eventually (gt_mem_nhds hω1)] with n hn
    exact convSDs_small h ha hk1 hk3 (by rw [bpt_re]; positivity) hn.le
  -- the Hölder bound
  have hH : ∀ ω : ℝ, 0 < |ω| → |ω| ≤ 1 →
      ‖lapW w ((((a * ω : ℝ)) : ℂ) * Complex.I) - lapW w ((((a * (0 : ℝ) : ℝ)) : ℂ) * Complex.I)‖ ≤
        2 * C * a ^ 3 * |ω| ^ (1 / 2 : ℝ) := by
    intro ω hω0 hω1
    have hz0 : (((a * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = 0 := by simp
    rw [hz0]
    have hpw : 0 ≤ |ω| ^ (1 / 2 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have hsq : a ^ (1 / 2 : ℝ) ≤ a ^ 3 := by
      calc a ^ (1 / 2 : ℝ) ≤ a ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
        _ = a ^ 3 := by norm_cast
    have hsplit : (a * |ω|) ^ (1 / 2 : ℝ) = a ^ (1 / 2 : ℝ) * |ω| ^ (1 / 2 : ℝ) :=
      Real.mul_rpow ha0.le (abs_nonneg _)
    by_cases hs : a * |ω| < 1
    · have hlim : Tendsto (fun n : ℕ => convSDs w a 0 (bpt n ω) - lapW w 0) atTop
          (𝓝 (lapW w ((((a * ω : ℝ)) : ℂ) * Complex.I) - lapW w 0)) := (h0 ω).sub_const _
      have hcont : ContinuousAt (fun t : ℝ => C * (a * t) ^ (1 / 2 : ℝ)) |ω| :=
        continuousAt_const.mul (ContinuousAt.rpow_const (continuousAt_const.mul continuousAt_id) (Or.inr (by norm_num)))
      have hev : ∀ᶠ n : ℕ in atTop, ‖convSDs w a 0 (bpt n ω) - lapW w 0‖ ≤ C * (a * ‖bpt n ω‖) ^ (1 / 2 : ℝ) := by
        have hlt : |ω| < 1 / a := by rw [lt_div_iff₀ ha0]; linarith
        filter_upwards [(tendsto_norm_bpt ω).eventually (gt_mem_nhds hlt)] with n hn
        have hre : 0 < ((a : ℂ) * bpt n ω).re := by
          have : ((a : ℂ) * bpt n ω).re = a * (bpt n ω).re := by simp [Complex.mul_re]
          rw [this, bpt_re]; positivity
        have hn1 : ‖(a : ℂ) * bpt n ω‖ ≤ 1 := by
          rw [norm_ofReal_mul' a ha0]
          have := (lt_div_iff₀ ha0).mp hn
          linarith
        have := h.hold _ hre hn1
        rw [norm_ofReal_mul' a ha0] at this
        rwa [convSDs_zero]
      have h1 := norm_le_of_bpt (G := fun z => convSDs w a 0 z - lapW w 0) hlim hcont hev
      refine h1.trans ?_
      show C * (a * |ω|) ^ (1 / 2 : ℝ) ≤ _
      rw [hsplit]
      have : C * (a ^ (1 / 2 : ℝ) * |ω| ^ (1 / 2 : ℝ)) ≤ C * (a ^ 3 * |ω| ^ (1 / 2 : ℝ)) := by gcongr
      nlinarith [mul_nonneg hC (mul_nonneg (by positivity : (0 : ℝ) ≤ a ^ 3) hpw)]
    · rw [not_lt] at hs
      have hb1 := h.bdd (((a * ω : ℝ) : ℂ) * Complex.I) (by simp)
      have hb2 := h.bdd 0 (by simp)
      have hge : 1 ≤ a ^ (1 / 2 : ℝ) * |ω| ^ (1 / 2 : ℝ) := by
        rw [← hsplit]; exact Real.one_le_rpow hs (by norm_num)
      have hnorm := norm_sub_le (lapW w ((((a * ω : ℝ)) : ℂ) * Complex.I)) (lapW w 0)
      have h2 : 2 * C ≤ 2 * C * (a ^ (1 / 2 : ℝ) * |ω| ^ (1 / 2 : ℝ)) := by
        nlinarith [mul_nonneg hC (by norm_num : (0 : ℝ) ≤ 2)]
      have h3 : 2 * C * (a ^ (1 / 2 : ℝ) * |ω| ^ (1 / 2 : ℝ)) ≤ 2 * C * (a ^ 3 * |ω| ^ (1 / 2 : ℝ)) := by gcongr
      nlinarith
  have hfun : (fun v : ℝ => lapW w ((((a * v : ℝ)) : ℂ) * Complex.I)) = bdLim (convSDs w a 0) := by
    funext v; rw [hΛ]
  refine ⟨fun s => Complex.I * bdLim (convSDs w a 1) s, fun s => Complex.I * (Complex.I * bdLim (convSDs w a 2) s),
    fun s => Complex.I * (Complex.I * (Complex.I * bdLim (convSDs w a 3) s)), fun s hs => ?_, fun s => ?_,
    fun s hs hs1 => ?_, fun s hs => ?_, fun s hs hs1 => ?_⟩
  · obtain ⟨_, d0, d1, d2⟩ := chain s hs
    rw [hfun]
    exact ⟨d0, d1.const_mul Complex.I, (d2.const_mul Complex.I).const_mul Complex.I⟩
  · refine (h.bdd _ (by simp)).trans ?_
    nlinarith
  · have hne : s ≠ 0 := abs_pos.mp hs
    have key : ∀ (k : ℕ) (e : ℝ), 1 ≤ k → k ≤ 3 → e = 1 / 2 - (k : ℝ) →
        ‖bdLim (convSDs w a k) s‖ ≤ 2 * C * a ^ 3 * |s| ^ e := by
      intro k e hk1 hk3 he
      subst he
      have hp : 0 ≤ |s| ^ (1 / 2 - (k : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
      rcases hs1.lt_or_eq with hlt | heq
      · refine (hsmallL s hne hlt k hk1 hk3).trans ?_
        nlinarith [mul_nonneg hCa hp]
      · have := hbigL s hne k hk1 hk3
        rw [heq] at this ⊢
        simp only [Real.one_rpow, mul_one] at this ⊢
        nlinarith
    have k1 := key 1 (-(1 / 2)) le_rfl (by norm_num) (by norm_num)
    have k2 := key 2 (-(3 / 2)) (by norm_num) (by norm_num) (by norm_num)
    have k3 := key 3 (-(5 / 2)) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_I, one_mul]; exact k1
    · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]; exact k2
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul, one_mul]; exact k3
  · have hne : s ≠ 0 := by intro h0; rw [h0, abs_zero] at hs; linarith
    have key : ∀ (k : ℕ) (e : ℝ), 1 ≤ k → k ≤ 3 → e = -(k : ℝ) - 1 →
        ‖bdLim (convSDs w a k) s‖ ≤ 2 * C * a ^ 3 * |s| ^ e := by
      intro k e hk1 hk3 he
      subst he
      have hp : 0 ≤ |s| ^ (-(k : ℝ) - 1) := Real.rpow_nonneg (abs_nonneg _) _
      refine (hbigL s hne k hk1 hk3).trans ?_
      nlinarith [mul_nonneg hC hp]
    have k1 := key 1 (-2) le_rfl (by norm_num) (by norm_num)
    have k2 := key 2 (-3) (by norm_num) (by norm_num) (by norm_num)
    have k3 := key 3 (-4) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_I, one_mul]; exact k1
    · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]; exact k2
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul, one_mul]; exact k3
  · exact hH s hs hs1

/-- info: 'FormalResearch.SignUncertainty.lapBounds_of_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lapBounds_of_interior

end FormalResearch.SignUncertainty
