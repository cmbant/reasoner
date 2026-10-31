import Mathlib

/-!
# Taylor lower bounds used by the near-uniform entropy estimates

Paper E, `lem:fqe-near-uniform-moment` (`sup_renyi.tex`, `sec:sup-nu-moment`): "the sixth derivative of
`z^q` is positive, so Taylor's formula through degree five at `z = 1/4` gives a lower bound".

* `Del_sign`: for every real exponent `a`, the Taylor remainder `Δ_n^a(u) = (1+u)^a - Σ_{k<n} C(a,k) u^k`
  satisfies `ff_n(a) Δ_n^a(u) ≥ 0` for `u ≥ 0` and `(-1)^n ff_n(a) Δ_n^a(u) ≥ 0` for `-1 < u ≤ 0`
  (`ff_n(a) = a(a-1)⋯(a-n+1)`), by induction on `n` using `Δ_{n+1}^a{}' = a Δ_n^{a-1}`;
* `taylor_rpow`: for `1 < q < 2` and `u ≥ -1`, `(1+u)^q ≥ Σ_{k<6} C(q,k) u^k`;
* `log_ge_taylor4`: `ln(1+z) ≥ z - z²/2 + z³/3 - z⁴/4` for `z ≥ 0`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Finset


/-- falling factorial `a (a-1) ... (a-n+1)`. -/
noncomputable def ff (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ff a n * (a - n)

theorem ff_succ' (a : ℝ) (n : ℕ) : ff a (n + 1) = a * ff (a - 1) n := by
  induction n with
  | zero => simp [ff]
  | succ n ih =>
    rw [ff, ih, ff]
    push_cast
    ring_nf

/-- Taylor coefficient `ff a k / k!`. -/
noncomputable def cf (a : ℝ) (k : ℕ) : ℝ := ff a k / (k.factorial : ℝ)

theorem cf_succ (a : ℝ) (k : ℕ) : ((k : ℝ) + 1) * cf a (k + 1) = a * cf (a - 1) k := by
  unfold cf
  rw [ff_succ', Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Taylor remainder of order `n` of `(1+u)^a`. -/
noncomputable def Del (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ a - ∑ k ∈ range n, cf a k * u ^ k

theorem Del_zero (a : ℝ) (n : ℕ) (hn : 0 < n) : Del a n 0 = 0 := by
  unfold Del
  rw [Finset.sum_eq_single 0]
  · simp [cf, ff]
  · intro k _ hk; simp [zero_pow hk]
  · intro h; exact absurd (mem_range.2 hn) h

theorem hasDerivAt_Del (a : ℝ) (n : ℕ) {u : ℝ} (hu : -1 < u) :
    HasDerivAt (Del a (n + 1)) (a * Del (a - 1) n u) u := by
  have h1 : HasDerivAt (fun u : ℝ => (1 + u) ^ a) (a * (1 + u) ^ (a - 1)) u := by
    have h := ((hasDerivAt_id u).const_add 1).rpow_const (p := a) (Or.inl (by simp; linarith))
    simpa using h
  have h2 : HasDerivAt (fun u : ℝ => ∑ k ∈ range (n + 1), cf a k * u ^ k)
      (∑ k ∈ range (n + 1), cf a k * ((k : ℝ) * u ^ (k - 1))) u := by
    apply HasDerivAt.fun_sum
    intro k _
    exact (hasDerivAt_pow k u).const_mul _
  have h3 : ∑ k ∈ range (n + 1), cf a k * ((k : ℝ) * u ^ (k - 1)) =
      a * ∑ k ∈ range n, cf (a - 1) k * u ^ k := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    have h0 : cf a 0 * ((((0 : ℕ) : ℝ)) * u ^ (0 - 1)) = 0 := by simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    have := cf_succ a k
    have e : (k + 1 - 1 : ℕ) = k := by omega
    rw [e]
    push_cast
    linear_combination u ^ k * this
  have := h1.sub h2
  rw [h3] at this
  unfold Del
  convert this using 1
  ring


theorem Del_continuousOn (a : ℝ) (n : ℕ) : ContinuousOn (Del a n) (Set.Ioi (-1)) := by
  intro u hu
  have hu' : -1 < u := hu
  have : ContinuousAt (Del a n) u := by
    have h1 : ContinuousAt (fun u : ℝ => (1 + u) ^ a) u :=
      ((continuous_const.add continuous_id).continuousAt).rpow_const (Or.inl (by simp; linarith))
    have h2 : ContinuousAt (fun u : ℝ => ∑ k ∈ range n, cf a k * u ^ k) u := by
      apply Continuous.continuousAt; fun_prop
    exact h1.sub h2
  exact this.continuousWithinAt

theorem Del_sign (n : ℕ) : ∀ (a u : ℝ), -1 < u →
    (0 ≤ u → 0 ≤ ff a n * Del a n u) ∧ (u ≤ 0 → 0 ≤ (-1) ^ n * (ff a n * Del a n u)) := by
  induction n with
  | zero =>
    intro a u hu
    have : 0 ≤ Del a 0 u := by
      unfold Del
      simp only [range_zero, sum_empty, sub_zero]
      exact Real.rpow_nonneg (by linarith) _
    simp [ff, this]
  | succ n ih =>
    intro a u hu
    have hder : ∀ s : ℝ, -1 < s → HasDerivAt (fun u => ff a (n + 1) * Del a (n + 1) u)
        (a * a * (ff (a - 1) n * Del (a - 1) n s)) s := by
      intro s hs
      have := (hasDerivAt_Del a n hs).const_mul (ff a (n + 1))
      rw [ff_succ'] at this ⊢
      convert this using 1
      ring
    set f : ℝ → ℝ := fun u => ff a (n + 1) * Del a (n + 1) u with hf
    have f0 : f 0 = 0 := by simp [hf, Del_zero a (n + 1) (Nat.succ_pos n)]
    have fcont : ContinuousOn f (Set.Ioi (-1)) := continuousOn_const.mul (Del_continuousOn a (n + 1))
    constructor
    · intro hu0
      have hmono : MonotoneOn f (Set.Ici 0) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
          (fcont.mono (fun x hx => by simp at hx ⊢; linarith))
          (f' := fun s => a * a * (ff (a - 1) n * Del (a - 1) n s))
        · intro s hs
          rw [interior_Ici] at hs ⊢
          exact (hder s (by simp at hs; linarith)).hasDerivWithinAt
        · intro s hs
          rw [interior_Ici] at hs
          have hs' : 0 ≤ s := le_of_lt hs
          have := (ih (a - 1) s (by linarith)).1 hs'
          have := mul_nonneg (mul_self_nonneg a) this
          exact this
      have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu0) hu0
      rw [f0] at this
      exact this
    · intro hu0
      set g : ℝ → ℝ := fun u => (-1) ^ n * f u with hg
      have hmono : MonotoneOn g (Set.Ioc (-1) 0) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc (-1) 0)
          (((continuousOn_const (c := ((-1 : ℝ) ^ n))).mul fcont).mono (fun x hx => hx.1))
          (f' := fun s => (-1) ^ n * (a * a * (ff (a - 1) n * Del (a - 1) n s)))
        · intro s hs
          rw [interior_Ioc] at hs ⊢
          have := (hder s hs.1).const_mul ((-1 : ℝ) ^ n)
          exact this.hasDerivWithinAt
        · intro s hs
          rw [interior_Ioc] at hs
          have := (ih (a - 1) s hs.1).2 hs.2.le
          have h2 := mul_nonneg (mul_self_nonneg a) this
          calc (0 : ℝ) ≤ a * a * ((-1) ^ n * (ff (a - 1) n * Del (a - 1) n s)) := h2
            _ = _ := by ring
      have := hmono (⟨hu, hu0⟩ : u ∈ Set.Ioc (-1 : ℝ) 0) (⟨by norm_num, le_rfl⟩ : (0 : ℝ) ∈ Set.Ioc (-1 : ℝ) 0) hu0
      have g0 : g 0 = 0 := by simp [hg, f0]
      rw [g0] at this
      simp only [hg] at this
      -- `(-1)^n * f u ≤ 0`, goal `0 ≤ (-1)^(n+1) * f u`
      have e : (-1 : ℝ) ^ (n + 1) * f u = -((-1) ^ n * f u) := by ring
      show 0 ≤ (-1) ^ (n + 1) * f u
      rw [e]; linarith


theorem ff_six (q : ℝ) : ff q 6 = q * (q - 1) * (q - 2) * (q - 3) * (q - 4) * (q - 5) := by
  simp [ff]

/-- Positive-order Taylor remainder: `(1+u)^q ≥ Σ_{k<6} C(q,k) u^k` for `1 < q < 2`, `-1 < u`. -/
theorem taylor_rpow_gt {q : ℝ} (h1 : 1 < q) (h2 : q < 2) {u : ℝ} (hu : -1 < u) :
    ∑ k ∈ range 6, cf q k * u ^ k ≤ (1 + u) ^ q := by
  have hs := Del_sign 6 q u hu
  have hpos : 0 < ff q 6 := by
    rw [ff_six]
    have a1 : 0 < q := by linarith
    have a2 : 0 < q - 1 := by linarith
    have a3 : q - 2 < 0 := by linarith
    have a4 : q - 3 < 0 := by linarith
    have a5 : q - 4 < 0 := by linarith
    have a6 : q - 5 < 0 := by linarith
    have := mul_pos (mul_pos a1 a2) (mul_pos_of_neg_of_neg a3 a4)
    have := mul_pos this (mul_pos_of_neg_of_neg a5 a6)
    nlinarith
  have hD : 0 ≤ Del q 6 u := by
    rcases le_total 0 u with h | h
    · exact nonneg_of_mul_nonneg_right (hs.1 h) hpos
    · have := hs.2 h
      norm_num at this
      exact nonneg_of_mul_nonneg_right this hpos
  unfold Del at hD
  linarith

/-- Same, including the endpoint `u = -1` (by continuity). -/
theorem taylor_rpow {q : ℝ} (h1 : 1 < q) (h2 : q < 2) {u : ℝ} (hu : -1 ≤ u) :
    ∑ k ∈ range 6, cf q k * u ^ k ≤ (1 + u) ^ q := by
  rcases hu.eq_or_lt with h | h
  · subst h
    have hcont : ContinuousAt (fun u : ℝ => (1 + u) ^ q - ∑ k ∈ range 6, cf q k * u ^ k) (-1) := by
      have a1 : ContinuousAt (fun u : ℝ => (1 + u) ^ q) (-1) :=
        ((continuous_const.add continuous_id).continuousAt).rpow_const (Or.inr (by linarith))
      have a2 : ContinuousAt (fun u : ℝ => ∑ k ∈ range 6, cf q k * u ^ k) (-1) := by
        apply Continuous.continuousAt; fun_prop
      exact a1.sub a2
    have hnn : ∀ᶠ u in nhdsWithin (-1 : ℝ) (Set.Ioi (-1)), 0 ≤ (1 + u) ^ q - ∑ k ∈ range 6, cf q k * u ^ k :=
      eventually_nhdsWithin_of_forall (fun u hu => by
        have := taylor_rpow_gt h1 h2 (Set.mem_Ioi.1 hu); linarith)
    have := ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hnn
    simpa using this
  · exact taylor_rpow_gt h1 h2 h

theorem log_ge_taylor4 {z : ℝ} (hz : 0 ≤ z) :
    z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 ≤ Real.log (1 + z) := by
  set f : ℝ → ℝ := fun z => Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4) with hf
  have hder : ∀ s : ℝ, -1 < s → HasDerivAt f (s ^ 4 / (1 + s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s := by
      have := ((hasDerivAt_id s).const_add 1).log (by simp; linarith)
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4)
        (1 - s + s ^ 2 - s ^ 3) s := by
      have a := (hasDerivAt_id s)
      have b := (hasDerivAt_pow 2 s).div_const 2
      have c := (hasDerivAt_pow 3 s).div_const 3
      have d := (hasDerivAt_pow 4 s).div_const 4
      refine (((a.sub b).add c).sub d).congr_deriv ?_
      norm_num
    have := h1.sub h2
    convert this using 1
    have h1s : (1 + s) ≠ 0 := by linarith
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun s => s ^ 4 / (1 + s))
    · intro s hs
      have hs0 : -1 < s := by
        have : 0 ≤ s := hs
        linarith
      exact (hder s hs0).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : -1 < s := by
        have : 0 < s := by simpa using hs
        linarith
      exact (hder s hs0).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have : 0 < s := by simpa using hs
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
  simp [hf] at this
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
