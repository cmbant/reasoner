module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCLaplace
public import FormalResearch.JacobiEigenvectors.Charts.PCOrigin
public import FormalResearch.JacobiEigenvectors.Charts.PCSmooth

/-!
# Paper J, Layer 4 (phase B2, `U_pos`): positivity of `U(a, z)` beyond the turning point

For the actual functions `pcU a z = Re U(a, z)` (`Charts/PCExact.lean`):

* `pcU_ne_zero_beyond`: for `x0 >= 2 sqrt(max(-a, 0))` we have `U(a, x0) != 0`.  Proof: `p(x) = x^2/4 + a >= 0` on `[x0, oo)`,
  `g = U U'` has `g' = U'^2 + p U^2 >= 0` there, so from `U(a, x0) = 0` the function `U^2` is nondecreasing on `[x0, oo)`;
  since `U^2 -> 0` (`tendsto_pcU`) it vanishes on `[x0, oo)`, and the Wronskian (`pc_wronsk`) is then `0 != sqrt(2/pi)`.
* `pcU_pos_beyond` (the field `U_pos` of `PCEnvelopeFacts`, with `U := pcU`): `U(a, z) > 0` for `z >= 2 sqrt(max(-a, 0))`.
  Proof: the sign at the turning point `a |-> U(a, 2 sqrt(max(-a,0)))` is continuous and nonvanishing, hence positive
  (intermediate value theorem, anchored at `pcU_zero_zero_pos`); then `z |-> U(a, z)` is nonvanishing on `[x0, oo)` and positive at `x0`.
* `cont_pcUD`, `cont_pcVD`: joint continuity of `(a, z) |-> deriv (pcU a) z` and `(a, z) |-> deriv (pcV a) z`, from the
  joint continuity of `pcU, pcV` (`pcSmoothFacts`) and the shift identities `pc_shift_U_dn`, `pc_shift_V_up`.

Classes: all proved (unconditional, for every real `a`, `z`); no numerical input.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set Real Filter Topology

/-- No zero of `U(a, .)` at or beyond the turning point `2 sqrt(max(-a, 0))` (proof in the module docstring). -/
theorem pcU_ne_zero_beyond {a x0 : ℝ} (hx0 : 2 * Real.sqrt (max (-a) 0) ≤ x0) : pcU a x0 ≠ 0 := by
  intro h0
  have hs0 : 0 ≤ Real.sqrt (max (-a) 0) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (max (-a) 0) ^ 2 = max (-a) 0 := Real.sq_sqrt (le_max_right _ _)
  -- `p(x) = x^2/4 + a >= 0` on `[x0, oo)`
  have hp : ∀ x, x0 ≤ x → 0 ≤ x ^ 2 / 4 + a := by
    intro x hx
    have h2s : (2 * Real.sqrt (max (-a) 0)) ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 : (2 * Real.sqrt (max (-a) 0)) ^ 2 = 4 * Real.sqrt (max (-a) 0) ^ 2 := by ring
    have hm := le_max_left (-a) 0
    rw [h4, hs2] at h2s
    linarith
  -- `g = U U'` is nondecreasing on `[x0, oo)`, since `g' = U'^2 + p U^2 >= 0` there
  have hg : MonotoneOn (fun x => pcU a x * pcUD a x) (Ici x0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici x0)
      (f' := fun x => pcUD a x * pcUD a x + pcU a x * ((x ^ 2 / 4 + a) * pcU a x)) ?_ ?_ ?_
    · exact fun x _ => ((hasDerivAt_pcU a x).mul (hasDerivAt_pcUD a x)).continuousAt.continuousWithinAt
    · intro x _
      exact ((hasDerivAt_pcU a x).mul (hasDerivAt_pcUD a x)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hxp := hp x (Set.mem_Ioi.mp hx).le
      show 0 ≤ pcUD a x * pcUD a x + pcU a x * ((x ^ 2 / 4 + a) * pcU a x)
      have e : pcU a x * ((x ^ 2 / 4 + a) * pcU a x) = (x ^ 2 / 4 + a) * (pcU a x * pcU a x) := by ring
      rw [e]
      exact add_nonneg (mul_self_nonneg _) (mul_nonneg hxp (mul_self_nonneg _))
  -- `g(x0) = 0`, hence `g >= 0` on `[x0, oo)`
  have hg0 : ∀ x, x0 ≤ x → 0 ≤ pcU a x * pcUD a x := by
    intro x hx
    have h1 := hg (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
    dsimp only at h1
    rw [h0, zero_mul] at h1
    exact h1
  -- `F = U^2` is nondecreasing on `[x0, oo)`, since `F' = 2 g >= 0` there
  have hF : MonotoneOn (fun x => pcU a x * pcU a x) (Ici x0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici x0)
      (f' := fun x => pcUD a x * pcU a x + pcU a x * pcUD a x) ?_ ?_ ?_
    · exact fun x _ => ((hasDerivAt_pcU a x).mul (hasDerivAt_pcU a x)).continuousAt.continuousWithinAt
    · intro x _
      exact ((hasDerivAt_pcU a x).mul (hasDerivAt_pcU a x)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have h1 := hg0 x (Set.mem_Ioi.mp hx).le
      show 0 ≤ pcUD a x * pcU a x + pcU a x * pcUD a x
      have e : pcUD a x * pcU a x + pcU a x * pcUD a x = 2 * (pcU a x * pcUD a x) := by ring
      rw [e]
      exact mul_nonneg (by norm_num) h1
  -- `U^2 -> 0`, and `U^2` nondecreasing, so `U^2 <= 0` on `[x0, oo)`
  have hlim : Tendsto (fun x => pcU a x * pcU a x) atTop (𝓝 0) := by
    have h := (tendsto_pcU a).mul (tendsto_pcU a)
    rw [mul_zero] at h
    exact h
  have hle : ∀ x, x0 ≤ x → pcU a x * pcU a x ≤ 0 := fun x hx =>
    ge_of_tendsto hlim ((eventually_ge_atTop x).mono fun y hy =>
      hF (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_trans hx hy)) hy)
  have hz : ∀ x, x0 ≤ x → pcU a x = 0 := fun x hx => by
    have h2 : pcU a x * pcU a x = 0 := le_antisymm (hle x hx) (mul_self_nonneg _)
    exact mul_self_eq_zero.mp h2
  -- `U` vanishes near `x0 + 1`, so `U' = 0` there, contradicting the Wronskian
  have hev : pcU a =ᶠ[𝓝 (x0 + 1)] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds (show x0 < x0 + 1 by linarith)] with y hy
    exact hz y (Set.mem_Ioi.mp hy).le
  have hd : pcUD a (x0 + 1) = 0 := by
    have h0' : HasDerivAt (pcU a) 0 (x0 + 1) :=
      (hasDerivAt_const (x0 + 1) (0 : ℝ)).congr_of_eventuallyEq hev
    exact (hasDerivAt_pcU a (x0 + 1)).unique h0'
  have hw := pc_wronsk a (x0 + 1)
  rw [congrFun (deriv_pcU a) (x0 + 1), hd, hz (x0 + 1) (by linarith)] at hw
  simp only [zero_mul, sub_zero] at hw
  have hpos : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  linarith

/-- Composition helpers, stated in the composed form so that no unfolding of `pcU, pcV` is needed. -/
theorem continuous_pcU_comp {α : Type*} [TopologicalSpace α] {f g : α → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => pcU (f x) (g x) := by
  have h : Continuous ((fun p : ℝ × ℝ => pcU p.1 p.2) ∘ fun x => (f x, g x)) :=
    continuous_pcU.comp (hf.prodMk hg)
  exact h

theorem continuous_pcV_comp {α : Type*} [TopologicalSpace α] {f g : α → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => pcV (f x) (g x) := by
  have h : Continuous ((fun p : ℝ × ℝ => pcV p.1 p.2) ∘ fun x => (f x, g x)) :=
    continuous_pcV.comp (hf.prodMk hg)
  exact h

/-- `U_pos` of `PCEnvelopeFacts` for the actual function `U = pcU`: `U(a, z) > 0` for `z >= 2 sqrt(max(-a, 0))`. -/
theorem pcU_pos_beyond : ∀ a z : ℝ, 2 * Real.sqrt (max (-a) 0) ≤ z → 0 < pcU a z := by
  -- the sign on the turning-point curve `a |-> U(a, 2 sqrt(max(-a,0)))`
  have hpos0 : ∀ a : ℝ, 0 < pcU a (2 * Real.sqrt (max (-a) 0)) := by
    have hcont : Continuous (fun a : ℝ => pcU a (2 * Real.sqrt (max (-a) 0))) := by
      have hs : Continuous (fun a : ℝ => 2 * Real.sqrt (max (-a) 0)) :=
        continuous_const.mul (Real.continuous_sqrt.comp (continuous_neg.max continuous_const))
      exact continuous_pcU_comp continuous_id hs
    have hne : ∀ a : ℝ, pcU a (2 * Real.sqrt (max (-a) 0)) ≠ 0 := fun a => pcU_ne_zero_beyond (le_refl _)
    have h0 : 0 < pcU 0 (2 * Real.sqrt (max (-(0 : ℝ)) 0)) := by
      have e : 2 * Real.sqrt (max (-(0 : ℝ)) 0) = 0 := by simp
      rw [e]
      exact pcU_zero_zero_pos
    intro a
    by_contra hle
    have hlt : pcU a (2 * Real.sqrt (max (-a) 0)) < 0 :=
      lt_of_le_of_ne (not_lt.mp hle) (hne a)
    have hmem : (0 : ℝ) ∈ uIcc (pcU a (2 * Real.sqrt (max (-a) 0)))
        (pcU 0 (2 * Real.sqrt (max (-(0 : ℝ)) 0))) :=
      mem_uIcc.mpr (Or.inl ⟨hlt.le, h0.le⟩)
    obtain ⟨c, _, hc⟩ := intermediate_value_uIcc
      (f := fun a : ℝ => pcU a (2 * Real.sqrt (max (-a) 0))) (a := a) (b := 0)
      hcont.continuousOn hmem
    exact hne c hc
  intro a z hz
  by_contra hle
  have hle' : pcU a z ≤ 0 := not_lt.mp hle
  have hcz : Continuous (fun y : ℝ => pcU a y) :=
    continuous_pcU_comp continuous_const continuous_id
  have hmem : (0 : ℝ) ∈ Icc (pcU a z) (pcU a (2 * Real.sqrt (max (-a) 0))) :=
    ⟨hle', (hpos0 a).le⟩
  obtain ⟨c, hc, hcz0⟩ := intermediate_value_Icc' (f := fun y : ℝ => pcU a y)
    (a := 2 * Real.sqrt (max (-a) 0)) (b := z) hz hcz.continuousOn hmem
  exact pcU_ne_zero_beyond hc.1 hcz0

/-- Joint continuity of `(a, z) |-> deriv (pcU a) z`, from `pc_shift_U_dn`: `U' = (z/2) U - U(a-1)`. -/
theorem cont_pcUD : Continuous (fun p : ℝ × ℝ => deriv (pcU p.1) p.2) := by
  have h2 : Continuous (fun p : ℝ × ℝ => pcU (p.1 - 1) p.2) :=
    continuous_pcU_comp (continuous_fst.sub continuous_const) continuous_snd
  have hc : Continuous (fun p : ℝ × ℝ => p.2 / 2 * pcU p.1 p.2 - pcU (p.1 - 1) p.2) :=
    ((continuous_snd.div_const 2).mul continuous_pcU).sub h2
  refine hc.congr fun p => ?_
  have := pc_shift_U_dn p.1 p.2
  linarith

/-- Joint continuity of `(a, z) |-> deriv (pcV a) z`, from `pc_shift_V_up`: `V' = V(a+1) - (z/2) V`. -/
theorem cont_pcVD : Continuous (fun p : ℝ × ℝ => deriv (pcV p.1) p.2) := by
  have h1 : Continuous (fun p : ℝ × ℝ => pcV (p.1 + 1) p.2) :=
    continuous_pcV_comp (continuous_fst.add continuous_const) continuous_snd
  have hc : Continuous (fun p : ℝ × ℝ => pcV (p.1 + 1) p.2 - p.2 / 2 * pcV p.1 p.2) :=
    h1.sub ((continuous_snd.div_const 2).mul continuous_pcV)
  refine hc.congr fun p => ?_
  have := pc_shift_V_up p.1 p.2
  linarith

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcU_pos_beyond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcU_pos_beyond

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.cont_pcUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cont_pcUD

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.cont_pcVD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cont_pcVD

end FormalResearch.JacobiEigenvectors.Charts
