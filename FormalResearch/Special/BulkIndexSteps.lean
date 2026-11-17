module

public import FormalResearch.Special.BulkKappaHahnInst
public import FormalResearch.Special.BulkIndexCount

/-!
# Bulk index, part 3: the phase steps of the physical `3j` chain

For `τ = +1`, `0 < x < 1`, `q_* = √(1 - x²)`, `[a, b] ⊂ (0, q_*)`: the Hahn phase `Φ(q) = bkPhase 1 0 1 x q_* q =
∫_q^{q_*} arccos(x/√(1-t²)) dt` has the integrand between `δ₁ = arccos(x/√(1-b²)) > 0` and `δ₂ = arccos x < π/2` on `[0, b]`
(`hrU 1 0 1 x t = x/√(1-t²)` increases in `t`), so that

* `bix_phase_step`: for `0 ≤ q ≤ q' ≤ b`, `δ₁ (q' - q) ≤ Φ(q) - Φ(q') ≤ δ₂ (q' - q)`.

This is the phase step `θ_j - θ_{j+1} ∈ [δ₁, δ₂]` of the Bohr-Sommerfeld lattice at the lattice spacing `h = 1/N`
(`θ_j = Φ(q_j)/h - π/4`), the input `BixWin.hd` of `BulkIndexCount`.

**Claim class: proved.**  Not formalised: `τ = -1` and the half-integer lattice (the same estimates with `|x|`).
-/

@[expose] public section

open Finset Real FormalResearch.Racah FormalResearch.Racah.P3
open scoped Real

namespace FormalResearch.Special

theorem bix_hrU (x t : ℝ) : hrU 1 0 1 x t = x / √(1 - t ^ 2) := by
  unfold hrU etilde
  simp

theorem bix_f_contOn {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousOn (fun t => Real.arccos (hrU 1 0 1 x t)) (Set.Icc 0 (√(1 - x ^ 2))) := by
  have h1 : 0 < 1 - x ^ 2 := by nlinarith
  have hq2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1.le
  simp_rw [bix_hrU]
  apply Real.continuous_arccos.comp_continuousOn
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro t ht
    have : t ^ 2 ≤ 1 - x ^ 2 := by rw [← hq2]; exact pow_le_pow_left₀ ht.1 ht.2 2
    exact (Real.sqrt_pos.2 (by nlinarith)).ne'

theorem bix_lt_one {x b : ℝ} (hb0 : 0 ≤ b) (hb : b < √(1 - x ^ 2)) : x / √(1 - b ^ 2) < 1 := by
  have h1 : 0 < 1 - x ^ 2 := by
    by_contra h; push Not at h
    have : √(1 - x ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos h
    linarith
  have : b ^ 2 < 1 - x ^ 2 := by
    have := pow_lt_pow_left₀ hb hb0 (two_ne_zero)
    rwa [Real.sq_sqrt h1.le] at this
  have hp : 0 < √(1 - b ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rw [div_lt_one hp]
  apply lt_of_pow_lt_pow_left₀ 2 hp.le
  rw [Real.sq_sqrt (by nlinarith)]
  nlinarith

/-- The two-sided bound of the integrand on `[0, b]`. -/
theorem bix_f_bounds {x b t : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hb : b < √(1 - x ^ 2)) (ht0 : 0 ≤ t) (htb : t ≤ b) :
    Real.arccos (x / √(1 - b ^ 2)) ≤ Real.arccos (hrU 1 0 1 x t) ∧ Real.arccos (hrU 1 0 1 x t) ≤ Real.arccos x := by
  have h1 : 0 < 1 - x ^ 2 := by nlinarith
  have hb0 : 0 ≤ b := ht0.trans htb
  have hb2 : b ^ 2 < 1 - x ^ 2 := by
    have := pow_lt_pow_left₀ hb hb0 (two_ne_zero)
    rwa [Real.sq_sqrt h1.le] at this
  have hp : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hpb : 0 < √(1 - b ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rw [bix_hrU]
  constructor
  · apply Real.arccos_le_arccos
    apply div_le_div_of_nonneg_left hx0.le hpb
    apply Real.sqrt_le_sqrt; nlinarith
  · apply Real.arccos_le_arccos
    rw [le_div_iff₀ hp]
    have : √(1 - t ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]; nlinarith
    nlinarith

/-- **Phase step.**  For `0 ≤ q ≤ q' ≤ b < q_*`: `δ₁ (q' - q) ≤ Φ(q) - Φ(q') ≤ δ₂ (q' - q)` with `δ₁ = arccos (x/√(1-b²))`,
`δ₂ = arccos x`. -/
theorem bix_phase_step {x b q q' : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hb : b < √(1 - x ^ 2)) (hq : 0 ≤ q) (hqq : q ≤ q')
    (hq' : q' ≤ b) :
    Real.arccos (x / √(1 - b ^ 2)) * (q' - q) ≤ bkPhase 1 0 1 x (√(1 - x ^ 2)) q - bkPhase 1 0 1 x (√(1 - x ^ 2)) q' ∧
    bkPhase 1 0 1 x (√(1 - x ^ 2)) q - bkPhase 1 0 1 x (√(1 - x ^ 2)) q' ≤ Real.arccos x * (q' - q) := by
  have hcont := bix_f_contOn hx0 hx1
  have hqs : q' ≤ √(1 - x ^ 2) := by linarith
  have hI : ∀ c d : ℝ, 0 ≤ c → c ≤ √(1 - x ^ 2) → 0 ≤ d → d ≤ √(1 - x ^ 2) →
      IntervalIntegrable (fun t => Real.arccos (hrU 1 0 1 x t)) MeasureTheory.volume c d := by
    intro c d hc hc' hd hd'
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have e : bkPhase 1 0 1 x (√(1 - x ^ 2)) q - bkPhase 1 0 1 x (√(1 - x ^ 2)) q' =
      ∫ t in q..q', Real.arccos (hrU 1 0 1 x t) := by
    unfold bkPhase
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI q q' hq (by linarith) (by linarith) (by linarith))
      (hI q' (√(1 - x ^ 2)) (by linarith) (by linarith) (by positivity) le_rfl)]
    ring
  rw [e]
  have hIqq := hI q q' hq (by linarith) (by linarith) (by linarith)
  constructor
  · have := intervalIntegral.integral_mono_on hqq (intervalIntegrable_const (c := Real.arccos (x / √(1 - b ^ 2)))) hIqq
      (fun t ht => (bix_f_bounds hx0 hx1 hb (hq.trans ht.1) (ht.2.trans hq')).1)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hqq hIqq (intervalIntegrable_const (c := Real.arccos x))
      (fun t ht => (bix_f_bounds hx0 hx1 hb (hq.trans ht.1) (ht.2.trans hq')).2)
    simpa [mul_comm] using this

end FormalResearch.Special
