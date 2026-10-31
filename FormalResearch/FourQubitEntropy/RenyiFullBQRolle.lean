import Mathlib

/-!
# A Rolle argument for the second divided difference at `0, v, 1`

Let `g` vanish at `0` and `1`, be `C²` on `(0,1)` and continuous on `[0,1]`, with `g''` strictly
increasing.  Then `v ↦ g(v)/(v(1-v))` is strictly decreasing on `(0,1)`.  (For `g = D_q - v` this is
the monotonicity of `A_q`, `lem:fqe-binary-quartic`: `g/(v(1-v)) = [0,v,1]g`, and the third divided
difference at `0, v, v', 1` is positive when `g'' ` is increasing; no Hermite--Genocchi formula is needed.)
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

theorem divdiff_strictAntiOn {g g1 g2 : ℝ → ℝ} (hc : ContinuousOn g (Set.Icc 0 1))
    (h0 : g 0 = 0) (h1 : g 1 = 0)
    (hd1 : ∀ v ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g1 v) v)
    (hd2 : ∀ v ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g1 (g2 v) v)
    (hm : StrictMonoOn g2 (Set.Ioo 0 1)) :
    StrictAntiOn (fun v => g v / (v * (1 - v))) (Set.Ioo 0 1) := by
  intro v hv v' hv' hvv'
  simp only
  by_contra hcon
  push Not at hcon
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨hv'0, hv'1⟩ := hv'
  set B := g v / (v * (1 - v)) with hB
  set B' := g v' / (v' * (1 - v')) with hB'
  set β := (B' - B) / (v' - v) with hβ
  set α := B - β * v with hα
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) (by linarith)
  have hvB : g v = v * (1 - v) * B := by
    rw [hB]; field_simp
  have hvB' : g v' = v' * (1 - v') * B' := by
    rw [hB']; field_simp
  have hB'e : B' = α + β * v' := by
    rw [hα, hβ]; field_simp; ring
  -- the cubic p and h = g - p
  let p : ℝ → ℝ := fun w => α * w - α * w ^ 2 + β * w ^ 2 - β * w ^ 3
  let p1 : ℝ → ℝ := fun w => α - 2 * α * w + 2 * β * w - 3 * β * w ^ 2
  let p2 : ℝ → ℝ := fun w => -2 * α + 2 * β - 6 * β * w
  have hp1 : ∀ w, HasDerivAt p (p1 w) w := by
    intro w
    have h : HasDerivAt p (deriv p w) w := (by fun_prop : DifferentiableAt ℝ p w).hasDerivAt
    refine h.congr_deriv ?_
    simp (disch := fun_prop) [p, p1]
    ring
  have hp2 : ∀ w, HasDerivAt p1 (p2 w) w := by
    intro w
    have h : HasDerivAt p1 (deriv p1 w) w := (by fun_prop : DifferentiableAt ℝ p1 w).hasDerivAt
    refine h.congr_deriv ?_
    simp (disch := fun_prop) [p1, p2]
    ring
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → Set.Icc a b ⊆ Set.Icc 0 1 := by
    intro a b ha hb x hx; exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hsubo : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → Set.Ioo a b ⊆ Set.Ioo 0 1 := by
    intro a b ha hb x hx
    exact ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  have hpc : Continuous p := by fun_prop
  have hcont1 : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → ContinuousOn (fun w => g w - p w) (Set.Icc a b) :=
    fun a b ha hb => (hc.mono (hsub ha hb)).sub hpc.continuousOn
  have hp0 : p 0 = 0 := by simp [p]
  have hp1' : p 1 = 0 := by simp [p]
  have hpv : g v - p v = 0 := by
    have : p v = v * (1 - v) * B := by
      simp only [p]; rw [hα]; ring
    rw [hvB, this]; ring
  have hpv' : g v' - p v' = 0 := by
    have : p v' = v' * (1 - v') * B' := by
      simp only [p]; rw [hB'e]; ring
    rw [hvB', this]; ring
  have rolle1 : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → g a - p a = g b - p b →
      ∃ c ∈ Set.Ioo a b, g1 c - p1 c = 0 := by
    intro a b ha hab hb hab'
    apply exists_hasDerivAt_eq_zero hab (hcont1 a b ha hb) hab'
    intro x hx
    exact (hd1 x (hsubo ha hb hx)).sub (hp1 x)
  obtain ⟨a1, ha1, e1⟩ := rolle1 0 v le_rfl hv0 hv1.le (by rw [h0, hp0, hpv]; norm_num)
  obtain ⟨a2, ha2, e2⟩ := rolle1 v v' hv0.le hvv' hv'1.le (by rw [hpv, hpv'])
  obtain ⟨a3, ha3, e3⟩ := rolle1 v' 1 hv'0.le hv'1 le_rfl (by rw [hpv', h1, hp1', sub_zero])
  have hcont2 : ∀ a b : ℝ, 0 < a → b < 1 → ContinuousOn (fun w => g1 w - p1 w) (Set.Icc a b) := by
    intro a b ha hb x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    exact ((hd2 x hx').continuousAt.sub (hp2 x).continuousAt).continuousWithinAt
  have rolle2 : ∀ a b : ℝ, 0 < a → a < b → b < 1 → g1 a - p1 a = 0 → g1 b - p1 b = 0 →
      ∃ c ∈ Set.Ioo a b, g2 c - p2 c = 0 := by
    intro a b ha hab hb ea eb
    apply exists_hasDerivAt_eq_zero hab (hcont2 a b ha hb) (by rw [ea, eb])
    intro x hx
    exact (hd2 x ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩).sub (hp2 x)
  obtain ⟨b1, hb1, f1⟩ := rolle2 a1 a2 ha1.1 (by linarith [ha1.2, ha2.1])
    (by linarith [ha2.2]) e1 e2
  obtain ⟨b2, hb2, f2⟩ := rolle2 a2 a3 (by linarith [ha1.1, ha1.2, ha2.1]) (by linarith [ha2.2, ha3.1])
    (by linarith [ha3.2]) e2 e3
  have hb12 : b1 < b2 := lt_trans hb1.2 hb2.1
  have hb1m : b1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ha1.1, hb1.1], by linarith [ha2.2, ha3.2, hb1.2, hb2.2]⟩
  have hb2m : b2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ha1.1, hb1.1, hb12], by linarith [ha3.2, hb2.2]⟩
  have hlt := hm hb1m hb2m hb12
  have : p2 b2 - p2 b1 = -6 * β * (b2 - b1) := by simp [p2]; ring
  nlinarith [mul_nonneg hβ0 (sub_nonneg.2 hb12.le)]

end FormalResearch.FourQubitEntropy.RenyiFull
