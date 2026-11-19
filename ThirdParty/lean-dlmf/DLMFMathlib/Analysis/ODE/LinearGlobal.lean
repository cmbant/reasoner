/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness

/-!
# Global existence for linear ODEs with continuous coefficients on `ℝ`

Linear `2 × 2` systems and second-order linear equations with continuous coefficients have
solutions on a compact interval or on all of `ℝ`, with data prescribed at any point.

## Main results

* `exists_linear_system_Icc_of_mem`: a linear `2 × 2` system with coefficients continuous on
  `[a, b]` has a solution on `[a, b]` with data prescribed at any `t₀ ∈ [a, b]` (forward
  existence from `ODE.exists_linear_system_Icc` on `[t₀, b]`, and on `[a, t₀]` by reflection).
* `exists_linear_system`: with coefficients continuous on `ℝ`, a global solution on `ℝ`
  with data at any `t₀` (solutions on `[t₀ - N, t₀ + N]` patched by uniqueness,
  `ODE.eqOn_Icc_of_linear_system`).
* `exists_linear_ode`: the same for the second-order equation `y'' = p y' + q y`, in the
  form used by `ODE.eq_of_linear_ode`.
-/

@[expose] public section

open Set Filter Topology

namespace ODE

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedSpace 𝕜 E]

/-- **Existence for linear `2 × 2` systems on a compact interval with data at any point**:
with coefficients `aᵢⱼ` continuous on `[a, b]` and `t₀ ∈ [a, b]`, the system
`u' = a₁₁ u + a₁₂ v`, `v' = a₂₁ u + a₂₂ v` has a solution on `[a, b]` (one-sided derivatives at
the endpoints) with `u(t₀) = u₀`, `v(t₀) = v₀`. -/
theorem exists_linear_system_Icc_of_mem {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ → 𝕜} (c₁₁ : ContinuousOn a₁₁ (Icc a b))
    (c₁₂ : ContinuousOn a₁₂ (Icc a b)) (c₂₁ : ContinuousOn a₂₁ (Icc a b))
    (c₂₂ : ContinuousOn a₂₂ (Icc a b)) (u₀ v₀ : E) :
    ∃ u v : ℝ → E, u t₀ = u₀ ∧ v t₀ = v₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt u (a₁₁ t • u t + a₁₂ t • v t) (Icc a b) t ∧
      HasDerivWithinAt v (a₂₁ t • u t + a₂₂ t • v t) (Icc a b) t := by
  have hR : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  have hL : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  obtain ⟨u₁, v₁, hu₁, hv₁, h₁⟩ := exists_linear_system_Icc ht₀.2 (c₁₁.mono hR) (c₁₂.mono hR)
    (c₂₁.mono hR) (c₂₂.mono hR) u₀ v₀
  have hmaps : MapsTo (fun s : ℝ => -s) (Icc (-t₀) (-a)) (Icc a t₀) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hmaps' : MapsTo (fun s : ℝ => -s) (Icc a t₀) (Icc (-t₀) (-a)) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have cneg : ∀ {f : ℝ → 𝕜}, ContinuousOn f (Icc a b) →
      ContinuousOn (fun s => -f (-s)) (Icc (-t₀) (-a)) := fun hf =>
    ((hf.mono hL).comp continuous_neg.continuousOn hmaps).neg
  obtain ⟨U, V, hU, hV, h₂⟩ := exists_linear_system_Icc (neg_le_neg ht₀.1) (cneg c₁₁)
    (cneg c₁₂) (cneg c₂₁) (cneg c₂₂) u₀ v₀
  -- the reflected solution on `[a, t₀]`
  have hback : ∀ t ∈ Icc a t₀,
      HasDerivWithinAt (fun t => U (-t)) (a₁₁ t • U (-t) + a₁₂ t • V (-t)) (Icc a t₀) t ∧
      HasDerivWithinAt (fun t => V (-t)) (a₂₁ t • U (-t) + a₂₂ t • V (-t)) (Icc a t₀) t := by
    intro t ht
    have hn : HasDerivWithinAt (fun s : ℝ => -s) (-1) (Icc a t₀) t :=
      (hasDerivAt_neg t).hasDerivWithinAt
    obtain ⟨k1, k2⟩ := h₂ (-t) (hmaps' ht)
    refine ⟨?_, ?_⟩
    · have := k1.scomp t hn hmaps'
      convert this using 1
      · rfl
      · rw [neg_neg, neg_one_smul, neg_smul, neg_smul, neg_add, neg_neg, neg_neg]
    · have := k2.scomp t hn hmaps'
      convert this using 1
      · rfl
      · rw [neg_neg, neg_one_smul, neg_smul, neg_smul, neg_add, neg_neg, neg_neg]
  refine ⟨fun t => if t ≤ t₀ then U (-t) else u₁ t, fun t => if t ≤ t₀ then V (-t) else v₁ t,
    by simp [hU], by simp [hV], fun t ht => ?_⟩
  have e1 : ∀ s ∈ Icc a t₀, (fun t => if t ≤ t₀ then U (-t) else u₁ t) s = U (-s) ∧
      (fun t => if t ≤ t₀ then V (-t) else v₁ t) s = V (-s) := fun s hs => by simp [hs.2]
  have e2 : ∀ s ∈ Icc t₀ b, (fun t => if t ≤ t₀ then U (-t) else u₁ t) s = u₁ s ∧
      (fun t => if t ≤ t₀ then V (-t) else v₁ t) s = v₁ s := fun s hs => by
    by_cases hst : s ≤ t₀
    · have : s = t₀ := le_antisymm hst hs.1
      simp [this, hU, hV, hu₁, hv₁]
    · simp [hst]
  rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  constructor
  · refine HasDerivWithinAt.union ?_ ?_
    · by_cases htc : t ≤ t₀
      · have hm : t ∈ Icc a t₀ := ⟨ht.1, htc⟩
        have := (hback t hm).1.congr_of_mem (fun s hs => (e1 s hs).1) hm
        rwa [(e1 t hm).1, (e1 t hm).2]
      · refine HasFDerivWithinAt.of_notMem_closure ?_
        rw [closure_Icc]; exact fun h' => htc h'.2
    · by_cases htc : t₀ ≤ t
      · have hm : t ∈ Icc t₀ b := ⟨htc, ht.2⟩
        have := (h₁ t hm).1.congr_of_mem (fun s hs => (e2 s hs).1) hm
        rwa [(e2 t hm).1, (e2 t hm).2]
      · refine HasFDerivWithinAt.of_notMem_closure ?_
        rw [closure_Icc]; exact fun h' => htc h'.1
  · refine HasDerivWithinAt.union ?_ ?_
    · by_cases htc : t ≤ t₀
      · have hm : t ∈ Icc a t₀ := ⟨ht.1, htc⟩
        have := (hback t hm).2.congr_of_mem (fun s hs => (e1 s hs).2) hm
        rwa [(e1 t hm).1, (e1 t hm).2]
      · refine HasFDerivWithinAt.of_notMem_closure ?_
        rw [closure_Icc]; exact fun h' => htc h'.2
    · by_cases htc : t₀ ≤ t
      · have hm : t ∈ Icc t₀ b := ⟨htc, ht.2⟩
        have := (h₁ t hm).2.congr_of_mem (fun s hs => (e2 s hs).2) hm
        rwa [(e2 t hm).1, (e2 t hm).2]
      · refine HasFDerivWithinAt.of_notMem_closure ?_
        rw [closure_Icc]; exact fun h' => htc h'.1

/-- **Global existence for linear `2 × 2` systems on `ℝ`**: with coefficients `aᵢⱼ`
continuous on `ℝ`, the system `u' = a₁₁ u + a₁₂ v`, `v' = a₂₁ u + a₂₂ v` has a solution on
`ℝ` with `u(t₀) = u₀`, `v(t₀) = v₀`. (Uniqueness: `ODE.eqOn_Icc_of_linear_system`.) -/
theorem exists_linear_system {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ → 𝕜} (c₁₁ : Continuous a₁₁)
    (c₁₂ : Continuous a₁₂) (c₂₁ : Continuous a₂₁) (c₂₂ : Continuous a₂₂) (t₀ : ℝ) (u₀ v₀ : E) :
    ∃ u v : ℝ → E, u t₀ = u₀ ∧ v t₀ = v₀ ∧ ∀ t,
      HasDerivAt u (a₁₁ t • u t + a₁₂ t • v t) t ∧
      HasDerivAt v (a₂₁ t • u t + a₂₂ t • v t) t := by
  set I : ℕ → Set ℝ := fun N => Icc (t₀ - N) (t₀ + N)
  have hI : ∀ N : ℕ, t₀ ∈ I N := fun N => ⟨by simp, by simp⟩
  choose U V hU hV hUV using fun N : ℕ => exists_linear_system_Icc_of_mem (E := E) (hI N)
    c₁₁.continuousOn c₁₂.continuousOn c₂₁.continuousOn c₂₂.continuousOn u₀ v₀
  have hmono : ∀ {N M : ℕ}, N ≤ M → I N ⊆ I M := fun {N M} h =>
    Icc_subset_Icc (by have : (N : ℝ) ≤ M := by exact_mod_cast h
                       linarith) (by have : (N : ℝ) ≤ M := by exact_mod_cast h
                                     linarith)
  have hcons : ∀ {N M : ℕ}, N ≤ M → EqOn (U M) (U N) (I N) ∧ EqOn (V M) (V N) (I N) := by
    intro N M h
    exact eqOn_Icc_of_linear_system (hI N) c₁₁.continuousOn c₁₂.continuousOn c₂₁.continuousOn
      c₂₂.continuousOn (fun t ht => ⟨(hUV M t (hmono h ht)).1.mono (hmono h),
        (hUV M t (hmono h ht)).2.mono (hmono h)⟩) (hUV N) (by rw [hU, hU]) (by rw [hV, hV])
  set n : ℝ → ℕ := fun t => ⌈|t - t₀|⌉₊
  have hn : ∀ t, t ∈ I (n t) := fun t => by
    have h := Nat.le_ceil |t - t₀|
    have h1 := le_abs_self (t - t₀)
    have h2 := neg_abs_le (t - t₀)
    exact ⟨by simp only [n] at h ⊢; linarith, by simp only [n] at h ⊢; linarith⟩
  have hall : ∀ M t, t ∈ I M → U (n t) t = U M t ∧ V (n t) t = V M t := by
    intro M t ht
    have k1 := hcons (le_max_left (n t) M)
    have k2 := hcons (le_max_right (n t) M)
    exact ⟨(k1.1 (hn t)).symm.trans (k2.1 ht), (k1.2 (hn t)).symm.trans (k2.2 ht)⟩
  refine ⟨fun t => U (n t) t, fun t => V (n t) t, ?_, ?_, fun t => ?_⟩
  · exact (hall 0 t₀ (hI 0)).1.trans (hU 0)
  · exact (hall 0 t₀ (hI 0)).2.trans (hV 0)
  set M := n t + 1
  have hnhds : I M ∈ 𝓝 t := by
    have h := hn t
    simp only [I, M] at h ⊢
    push_cast
    exact Icc_mem_nhds (by linarith [h.1]) (by linarith [h.2])
  have hev : (fun t => U (n t) t) =ᶠ[𝓝 t] U M ∧ (fun t => V (n t) t) =ᶠ[𝓝 t] V M :=
    ⟨Filter.eventually_of_mem hnhds fun s hs => (hall M s hs).1,
      Filter.eventually_of_mem hnhds fun s hs => (hall M s hs).2⟩
  have htM := mem_of_mem_nhds hnhds
  obtain ⟨k1, k2⟩ := hUV M t htM
  beta_reduce
  rw [(hall M t htM).1, (hall M t htM).2]
  exact ⟨(k1.hasDerivAt hnhds).congr_of_eventuallyEq hev.1,
    (k2.hasDerivAt hnhds).congr_of_eventuallyEq hev.2⟩

/-- **Global existence for second-order linear ODEs on `ℝ`**: with `p`, `q` continuous, for
every `t₀`, `y₀`, `y₁` there are `f`, `f'` with `f'` the derivative of `f` and
`(f')' = p f' + q f` on `ℝ`, `f(t₀) = y₀` and `f'(t₀) = y₁`. (Uniqueness:
`ODE.eq_of_linear_ode`.) -/
theorem exists_linear_ode {p q : ℝ → 𝕜} (hp : Continuous p) (hq : Continuous q) (t₀ : ℝ)
    (y₀ y₁ : E) :
    ∃ f f' : ℝ → E, f t₀ = y₀ ∧ f' t₀ = y₁ ∧
      ∀ t, HasDerivAt f (f' t) t ∧ HasDerivAt f' (p t • f' t + q t • f t) t := by
  obtain ⟨u, v, hu, hv, h⟩ := exists_linear_system (E := E) (a₁₁ := fun _ => (0 : 𝕜))
    (a₁₂ := fun _ => (1 : 𝕜)) continuous_const continuous_const hq hp t₀ y₀ y₁
  refine ⟨u, v, hu, hv, fun t => ⟨?_, ?_⟩⟩
  · simpa using (h t).1
  · simpa [add_comm] using (h t).2

end ODE
