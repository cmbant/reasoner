module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCPositive

/-!
# Paper J, Layer 4 (phase B2, `beyond` derivative bound): `|U'(a, z)| <= 4 sqrt(k2(a, z)) U(a, z)` beyond the turning point

For the actual function `pcU a z = Re U(a, z)` (`Charts/PCExact.lean`), we prove the first conjunct of the
`beyond` field of `PCEnvelopeFacts` (`Charts/ParabolicCylinder.lean`):

* `pcUD_nonpos_beyond`: `deriv (pcU a) z <= 0` for `z >= 2 sqrt(max(-a, 0))` (since `U > 0`, `U'' = p U >= 0`
  makes `U'` nondecreasing, and `U'(z0) > 0` would force `U` nondecreasing and `>= U(z0) > 0`, contradicting
  `tendsto_pcU`).
* `pcU_beyond_deriv`: `|deriv (pcU a) z| <= 4 * Real.sqrt (k2 a z) * pcU a z` (and `pcU_beyond_deriv_abs`
  with `|pcU a z|`) for all `a` and `z >= 2 sqrt(max(-a, 0))`.

Proof of `pcU_beyond_deriv`: `m := -U'/U >= 0` satisfies the Riccati ODE `m' = m^2 - p` with `p(z) = z^2/4 + a >= 0`.
With `L := max |a| 1 ^ (1/3)` and `B(z) := sqrt(p(z) + L)`, we have `B(z) <= sqrt 2 * sqrt(k2 a z) <= 4 * sqrt(k2 a z)`
and `B'(z) = z / (4 B(z)) <= L = B(z)^2 - p(z)`. If `m(z1) > B(z1)` at some `z1 >= 2 sqrt(max(-a, 0))`, then
`g := m - B` satisfies `g' >= m^2 - B^2 >= g^2 > 0` as long as `g > 0`, so `g > 0` persists on `[z1, oo)` and
`(1 / g)' <= -1`, forcing `1 / g(z) <= -1` for `z = z1 + 1 / g(z1) + 1`, a contradiction.

**What is not proved here:** the second conjunct of `beyond` in `PCEnvelopeFacts`
(`cPC / sqrt 17 * Erec a z * Mbal a z <= |kappaBal a * pcU a z|`), which requires the Liouville-Green /
exponential-zone lower bound.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set Real Filter Topology

/-- Beyond the turning point `z >= 2 sqrt(max(-a, 0))`, `pcU a` is nonincreasing: `pcUD a z <= 0`. -/
theorem pcUD_nonpos_beyond {a z : ℝ} (hz : 2 * Real.sqrt (max (-a) 0) ≤ z) :
    pcUD a z ≤ 0 := by
  set zt := 2 * Real.sqrt (max (-a) 0)
  have hp : ∀ x, zt ≤ x → 0 ≤ x ^ 2 / 4 + a := by
    intro x hx
    have h2s : zt ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hx 2
    have h4 : zt ^ 2 = 4 * Real.sqrt (max (-a) 0) ^ 2 := by dsimp [zt]; ring
    rw [h4, Real.sq_sqrt (le_max_right _ _)] at h2s
    linarith [le_max_left (-a) 0]
  have hmono_D : MonotoneOn (pcUD a) (Ici zt) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici zt)
      (f' := fun x => (x ^ 2 / 4 + a) * pcU a x) ?_ ?_ ?_
    · exact fun x _ => (hasDerivAt_pcUD a x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_pcUD a x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact mul_nonneg (hp x (Set.mem_Ioi.mp hx).le) (pcU_pos_beyond a x (Set.mem_Ioi.mp hx).le).le
  by_contra hpos
  have hpos' : 0 < pcUD a z := not_le.mp hpos
  have hmono_U : MonotoneOn (pcU a) (Ici z) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici z)
      (f' := pcUD a) ?_ ?_ ?_
    · exact fun x _ => (hasDerivAt_pcU a x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_pcU a x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hzx : z ≤ x := (Set.mem_Ioi.mp hx).le
      exact hpos'.le.trans (hmono_D (Set.mem_Ici.mpr hz) (Set.mem_Ici.mpr (hz.trans hzx)) hzx)
  have hle : pcU a z ≤ 0 :=
    ge_of_tendsto (tendsto_pcU a) ((eventually_ge_atTop z).mono fun y hy =>
      hmono_U (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy)
  linarith [pcU_pos_beyond a z hz]

/-- The Riccati barrier `B(z) = sqrt(z^2/4 + a + max |a| 1 ^ (1/3))` bounds `-pcUD a z / pcU a z`
for all `z >= 2 sqrt(max(-a, 0))`. -/
theorem pcU_beyond_riccati_le {a z : ℝ} (hz : 2 * Real.sqrt (max (-a) 0) ≤ z) :
    -pcUD a z / pcU a z ≤ Real.sqrt (z ^ 2 / 4 + a + max |a| 1 ^ ((1 : ℝ) / 3)) := by
  set zt := 2 * Real.sqrt (max (-a) 0)
  set L : ℝ := max |a| 1 ^ ((1 : ℝ) / 3)
  let p : ℝ → ℝ := fun x => x ^ 2 / 4 + a
  let B : ℝ → ℝ := fun x => Real.sqrt (p x + L)
  let m : ℝ → ℝ := fun x => -pcUD a x / pcU a x
  have hL1 : 1 ≤ L := Real.one_le_rpow (le_max_right |a| 1) (by norm_num)
  have hL3 : L ^ 3 = max |a| 1 := by
    dsimp [L]
    rw [← Real.rpow_natCast (max |a| 1 ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (by positivity)]
    norm_num
  have hp_nonneg : ∀ x, zt ≤ x → 0 ≤ p x := by
    intro x hx
    have h2s : zt ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hx 2
    have h4 : zt ^ 2 = 4 * Real.sqrt (max (-a) 0) ^ 2 := by dsimp [zt]; ring
    rw [h4, Real.sq_sqrt (le_max_right _ _)] at h2s
    dsimp [p]; linarith [le_max_left (-a) 0]
  have hB_pos : ∀ x, zt ≤ x → 0 < B x := fun x hx =>
    Real.sqrt_pos.mpr (by linarith [hp_nonneg x hx, hL1])
  have hB_deriv : ∀ x, zt ≤ x → HasDerivAt B (x / (4 * B x)) x := by
    intro x hx
    have hpL : p x + L ≠ 0 := ne_of_gt (by linarith [hp_nonneg x hx, hL1])
    have hp_deriv : HasDerivAt (fun y => p y + L) (x / 2) x := by
      have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 4 + a + L) ((2 * x ^ 1) / 4) x := by
        simpa using (((hasDerivAt_pow 2 x).div_const 4).add_const a).add_const L
      refine h1.congr_deriv ?_
      ring
    refine (hp_deriv.sqrt hpL).congr_deriv ?_
    dsimp [B]
    ring
  have hB_ineq : ∀ x, zt ≤ x → x / (4 * B x) ≤ B x ^ 2 - p x := by
    intro x hx
    have hpx : 0 ≤ p x := hp_nonneg x hx
    have hBx : 0 < B x := hB_pos x hx
    have hBsq : B x ^ 2 = p x + L := Real.sq_sqrt (by linarith)
    have hx_nonneg : 0 ≤ x :=
      le_trans (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hx
    have h_sq : x ^ 2 ≤ (4 * L * B x) ^ 2 := by
      have hxa : x ^ 2 = 4 * (p x - a) := by dsimp [p]; ring
      have ha_le : -a ≤ L ^ 3 := by
        rw [hL3]
        exact (neg_le_abs a).trans (le_max_left |a| 1)
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
      have h1 : x ^ 2 ≤ 4 * p x + 4 * L ^ 3 := by linarith
      have h2 : 4 * p x ≤ 16 * L ^ 2 * p x := by nlinarith
      have h3 : (4 * L * B x) ^ 2 = 16 * L ^ 2 * p x + 16 * L ^ 3 := by
        calc (4 * L * B x) ^ 2 = 16 * L ^ 2 * B x ^ 2 := by ring
          _ = 16 * L ^ 2 * (p x + L) := by rw [hBsq]
          _ = 16 * L ^ 2 * p x + 16 * L ^ 3 := by ring
      nlinarith [pow_pos (by linarith : 0 < L) 3]
    have hx_le : x ≤ 4 * L * B x := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * L) hBx.le]
    rw [hBsq, show p x + L - p x = L by ring, div_le_iff₀ (by positivity)]
    linarith
  have hm_deriv : ∀ x, zt ≤ x → HasDerivAt m (m x ^ 2 - p x) x := by
    intro x hx
    have hU : pcU a x ≠ 0 := (pcU_pos_beyond a x hx).ne'
    have h1 := ((hasDerivAt_pcUD a x).neg).div (hasDerivAt_pcU a x) hU
    refine h1.congr_deriv ?_
    dsimp [m, p]
    field_simp [hU]
    ring
  let g : ℝ → ℝ := fun x => m x - B x
  have hg_deriv : ∀ x, zt ≤ x → HasDerivAt g (m x ^ 2 - p x - x / (4 * B x)) x :=
    fun x hx => (hm_deriv x hx).sub (hB_deriv x hx)
  by_contra hlt
  have hg_pos_z : 0 < g z := sub_pos.mpr (not_le.mp hlt)
  have hg_pos_all : ∀ x, z ≤ x → 0 < g x := by
    intro x hx
    by_contra hle
    have hle' : g x ≤ 0 := not_lt.mp hle
    let S : Set ℝ := {y ∈ Icc z x | g y ≤ 0}
    have hS_closed : IsClosed S := by
      have hcont : ContinuousOn g (Icc z x) := fun y hy =>
        (hg_deriv y (hz.trans hy.1)).continuousAt.continuousWithinAt
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hS_ne : S.Nonempty := ⟨x, ⟨hx, le_rfl⟩, hle'⟩
    have hS_bdd : BddBelow S := ⟨z, fun _ hy => hy.1.1⟩
    set y0 := sInf S
    have hy0_mem : y0 ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
    have hy0_gt : z < y0 := by
      refine lt_of_le_of_ne hy0_mem.1.1 ?_
      intro heq
      have := hy0_mem.2
      rw [← heq] at this
      linarith
    have hg_nonneg_on : ∀ y ∈ Ioo z y0, 0 < g y := by
      intro y hy
      by_contra hny
      have hmem : y ∈ S := ⟨⟨hy.1.le, hy.2.le.trans hy0_mem.1.2⟩, not_lt.mp hny⟩
      exact absurd (csInf_le hS_bdd hmem) (not_le.mpr hy.2)
    have hg_mono : MonotoneOn g (Icc z y0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc z y0)
        (f' := fun y => m y ^ 2 - p y - y / (4 * B y)) ?_ ?_ ?_
      · exact fun y hy => (hg_deriv y (hz.trans hy.1)).continuousAt.continuousWithinAt
      · exact fun y hy => (hg_deriv y (hz.trans (interior_subset hy).1)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hgy : 0 < g y := hg_nonneg_on y hy
        have hy_zt : zt ≤ y := hz.trans hy.1.le
        have hB_le := hB_ineq y hy_zt
        have hm_gt_B : B y < m y := sub_pos.mp hgy
        have hBy_pos : 0 < B y := hB_pos y hy_zt
        nlinarith
    have h_le := hg_mono ⟨le_rfl, hy0_gt.le⟩ ⟨hy0_gt.le, le_rfl⟩ hy0_gt.le
    linarith [hy0_mem.2]
  -- Now `0 < g x` for all `x >= z`, so `(1/g)' <= -1`, giving a finite-time blowup contradiction.
  let h : ℝ → ℝ := fun x => (g x)⁻¹ + x
  have hh_anti : AntitoneOn h (Ici z) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici z)
      (f' := fun x => -(m x ^ 2 - p x - x / (4 * B x)) / g x ^ 2 + 1) ?_ ?_ ?_
    · intro x hx
      have hgx : g x ≠ 0 := (hg_pos_all x hx).ne'
      exact (((hg_deriv x (hz.trans hx)).inv hgx).add (hasDerivAt_id x)).continuousAt.continuousWithinAt
    · intro x hx
      have hgx : g x ≠ 0 := (hg_pos_all x (interior_subset hx)).ne'
      exact (((hg_deriv x (hz.trans (interior_subset hx))).inv hgx).add (hasDerivAt_id x)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hgx : 0 < g x := hg_pos_all x (Set.mem_Ioi.mp hx).le
      have hx_zt : zt ≤ x := hz.trans (Set.mem_Ioi.mp hx).le
      have hB_le := hB_ineq x hx_zt
      have hBy_pos : 0 < B x := hB_pos x hx_zt
      have hgm : m x ^ 2 - B x ^ 2 ≥ g x ^ 2 := by
        have : m x ^ 2 - B x ^ 2 - g x ^ 2 = 2 * B x * g x := by dsimp [g]; ring
        nlinarith
      have hg' : g x ^ 2 ≤ m x ^ 2 - p x - x / (4 * B x) := by linarith
      have : -(m x ^ 2 - p x - x / (4 * B x)) / g x ^ 2 + 1
          = (g x ^ 2 - (m x ^ 2 - p x - x / (4 * B x))) / g x ^ 2 := by
        field_simp [hgx.ne']
        ring
      rw [this]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  set x1 : ℝ := z + (g z)⁻¹ + 1
  have hx1_ge : z ≤ x1 := by
    have : 0 < (g z)⁻¹ := inv_pos.mpr hg_pos_z
    dsimp [x1]; linarith
  have hh_le : h x1 ≤ h z := hh_anti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx1_ge) hx1_ge
  have hinv_pos : 0 < (g x1)⁻¹ := inv_pos.mpr (hg_pos_all x1 hx1_ge)
  dsimp [h, x1] at hh_le
  linarith

/-- First conjunct of `beyond` in `PCEnvelopeFacts` (`Charts/ParabolicCylinder.lean`) for `pcU`:
for all `a` and `z >= 2 sqrt(max(-a, 0))`, `|deriv (pcU a) z| <= 4 sqrt(k2 a z) * pcU a z`.
(In fact the constant `sqrt 2` holds.) -/
theorem pcU_beyond_deriv : ∀ a z : ℝ, 2 * Real.sqrt (max (-a) 0) ≤ z →
    |deriv (pcU a) z| ≤ 4 * Real.sqrt (k2 a z) * pcU a z := by
  intro a z hz
  have hU_pos : 0 < pcU a z := pcU_pos_beyond a z hz
  have hD_nonpos : pcUD a z ≤ 0 := pcUD_nonpos_beyond hz
  rw [congrFun (deriv_pcU a) z, abs_of_nonpos hD_nonpos]
  have hric := pcU_beyond_riccati_le hz
  have hp_nonneg : 0 ≤ z ^ 2 / 4 + a := by
    have h2s : (2 * Real.sqrt (max (-a) 0)) ^ 2 ≤ z ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hz 2
    have h4 : (2 * Real.sqrt (max (-a) 0)) ^ 2 = 4 * Real.sqrt (max (-a) 0) ^ 2 := by ring
    rw [h4, Real.sq_sqrt (le_max_right _ _)] at h2s
    linarith [le_max_left (-a) 0]
  have hk2 : z ^ 2 / 4 + a + max |a| 1 ^ ((1 : ℝ) / 3) ≤ 16 * k2 a z := by
    dsimp [k2]
    rw [abs_of_nonneg hp_nonneg]
    have hk_nonneg : 0 ≤ max (z ^ 2 / 4 + a) (max |a| 1 ^ ((1 : ℝ) / 3)) :=
      le_max_of_le_left hp_nonneg
    linarith [le_max_left (z ^ 2 / 4 + a) (max |a| 1 ^ ((1 : ℝ) / 3)),
              le_max_right (z ^ 2 / 4 + a) (max |a| 1 ^ ((1 : ℝ) / 3))]
  have hsqrt : Real.sqrt (z ^ 2 / 4 + a + max |a| 1 ^ ((1 : ℝ) / 3)) ≤ 4 * Real.sqrt (k2 a z) := by
    calc Real.sqrt (z ^ 2 / 4 + a + max |a| 1 ^ ((1 : ℝ) / 3))
        ≤ Real.sqrt (16 * k2 a z) := Real.sqrt_le_sqrt hk2
      _ = Real.sqrt (4 ^ 2 * k2 a z) := by norm_num
      _ = 4 * Real.sqrt (k2 a z) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hdiv : -pcUD a z / pcU a z ≤ 4 * Real.sqrt (k2 a z) := hric.trans hsqrt
  exact (div_le_iff₀ hU_pos).mp hdiv

/-- Exact shape of the first conjunct of `PCEnvelopeFacts.beyond` (`|pcU a z|` on the RHS). -/
theorem pcU_beyond_deriv_abs : ∀ a z : ℝ, 2 * Real.sqrt (max (-a) 0) ≤ z →
    |deriv (pcU a) z| ≤ 4 * Real.sqrt (k2 a z) * |pcU a z| := by
  intro a z hz
  rw [abs_of_pos (pcU_pos_beyond a z hz)]
  exact pcU_beyond_deriv a z hz

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcUD_nonpos_beyond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcUD_nonpos_beyond

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcU_beyond_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcU_beyond_deriv

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcU_beyond_deriv_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcU_beyond_deriv_abs

end FormalResearch.JacobiEigenvectors.Charts
