module

public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# Variation of constants for the discrete Jacobi row operator against an approximate fundamental pair

Airy-free (pure sequences `ℤ → ℝ`).  Let `φ, ψ` be two sequences (an *approximate fundamental pair*: the defects
`ε_k = jac a c φ k`, `ε̃_k = jac a c ψ k` are small, not zero) with non-vanishing Casoratian
`D_k = cas a φ ψ k = a_{k+1}(φ_k ψ_{k+1} - φ_{k+1} ψ_k)`.  For an *exact* solution `Y` (`jac a c Y = 0`) put

* `vocA Y k = cas a Y ψ k / D_k`, `vocB Y k = cas a φ Y k / D_k`   (Cramer coefficients).

Then `Y_k = α_k φ_k + β_k ψ_k` and `Y_{k+1} = α_k φ_{k+1} + β_k ψ_{k+1}` (`voc_repr`), and from the Lagrange identity
`cas_sub` the coefficients move only through the defects:

* up:   `α_k - α_{k-1} =  ψ_k (α_{k-1} ε_k + β_{k-1} ε̃_k) / D_k`,   `β_k - β_{k-1} = -φ_k (α_{k-1} ε_k + β_{k-1} ε̃_k) / D_k`;
* down: `α_{k-1} - α_k = -ψ_k (α_k ε_k + β_k ε̃_k) / D_{k-1}`,   `β_{k-1} - β_k =  φ_k (α_k ε_k + β_k ε̃_k) / D_{k-1}`.

`voc_march_up` / `voc_march_down` turn this into a discrete Grönwall bound in the weighted `ℓ¹` norm
`ω_k |α_k| + |β_k|` upward (`ω` non-increasing in `k`) and `|α_k| + ω_k |β_k|` downward (`ω` non-decreasing in `k`), which is how
a growing partner `ψ ~ e^{ξ}` and a decaying partner `φ ~ e^{-ξ}` are balanced (`ω = e^{-2ξ}` upward, `e^{+2ξ}` downward): if the step quantities satisfy
`(ω_k|ψ_k| + |φ_k|) |ε_k| ≤ λ_k γ ω_{k-1}`, `(ω_k|ψ_k| + |φ_k|) |ε̃_k| ≤ λ_k γ` and `|D_k| ≥ γ`, then
`ω_k |α_k - α_m| + |β_k - β_m| ≤ (ω_m |α_m| + |β_m|) (e^Λ - 1)` with `Λ ≥ Σ λ`.  This is the
"amplitude-adapted" Grönwall that replaces the `ℓ¹` difference norm of `DiscreteJacobiExtrasGronwall` (which carries the
factor `e^{O(A₀²)}`): the total growth exponent is `Σ λ_k`, `λ_k ≍ δ⁵ (2+|X_k|)^{-1/2}` in the Airy application, hence `O(δ³)`.

**Claim class: proved** (exact algebra and induction; no asymptotics).  **Not formalised** here: any Airy input (the pair,
its defect, its Casoratian), which is supplied in the downstream `DiscreteAiryOsc*` modules.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Cramer coefficient `α_k = cas(Y, ψ)_k / cas(φ, ψ)_k`. -/
noncomputable def vocA (a Y φ ψ : ℤ → ℝ) (k : ℤ) : ℝ := cas a Y ψ k / cas a φ ψ k

/-- Cramer coefficient `β_k = cas(φ, Y)_k / cas(φ, ψ)_k`. -/
noncomputable def vocB (a Y φ ψ : ℤ → ℝ) (k : ℤ) : ℝ := cas a φ Y k / cas a φ ψ k

/-- `Y = α φ + β ψ` on the two sites `k, k+1` of the bond `k`. -/
theorem voc_repr (a Y φ ψ : ℤ → ℝ) (k : ℤ) (hD : cas a φ ψ k ≠ 0) :
    Y k = vocA a Y φ ψ k * φ k + vocB a Y φ ψ k * ψ k ∧
      Y (k + 1) = vocA a Y φ ψ k * φ (k + 1) + vocB a Y φ ψ k * ψ (k + 1) := by
  unfold vocA vocB
  constructor
  · field_simp; unfold cas; ring
  · field_simp; unfold cas; ring

/-- The identity `Y_k = α_{k-1} φ_k + β_{k-1} ψ_k` (second site of the bond `k-1`). -/
theorem voc_repr' (a Y φ ψ : ℤ → ℝ) (k : ℤ) (hD : cas a φ ψ (k - 1) ≠ 0) :
    Y k = vocA a Y φ ψ (k - 1) * φ k + vocB a Y φ ψ (k - 1) * ψ k := by
  have := (voc_repr a Y φ ψ (k - 1) hD).2
  simpa using this

/-- Upward step of the Cramer coefficients (bond `k-1` to bond `k`). -/
theorem voc_step_up (a c Y φ ψ : ℤ → ℝ) (k : ℤ) (hY : jac a c Y k = 0) (hD1 : cas a φ ψ (k - 1) ≠ 0)
    (hD : cas a φ ψ k ≠ 0) :
    vocA a Y φ ψ k - vocA a Y φ ψ (k - 1) =
        ψ k * (vocA a Y φ ψ (k - 1) * jac a c φ k + vocB a Y φ ψ (k - 1) * jac a c ψ k) / cas a φ ψ k ∧
      vocB a Y φ ψ k - vocB a Y φ ψ (k - 1) =
        -(φ k * (vocA a Y φ ψ (k - 1) * jac a c φ k + vocB a Y φ ψ (k - 1) * jac a c ψ k)) /
          cas a φ ψ k := by
  have hrep := voc_repr' a Y φ ψ k hD1
  have eP := cas_sub a c Y ψ k
  have eQ := cas_sub a c φ Y k
  have eD := cas_sub a c φ ψ k
  rw [hY] at eP eQ
  have hα : cas a Y ψ (k - 1) = vocA a Y φ ψ (k - 1) * cas a φ ψ (k - 1) := by
    unfold vocA; field_simp
  have hβ : cas a φ Y (k - 1) = vocB a Y φ ψ (k - 1) * cas a φ ψ (k - 1) := by
    unfold vocB; field_simp
  have key1 : cas a Y ψ k = vocA a Y φ ψ (k - 1) * cas a φ ψ k +
      ψ k * (vocA a Y φ ψ (k - 1) * jac a c φ k + vocB a Y φ ψ (k - 1) * jac a c ψ k) := by
    linear_combination eP + hα - vocA a Y φ ψ (k - 1) * eD + jac a c ψ k * hrep
  have key2 : cas a φ Y k = vocB a Y φ ψ (k - 1) * cas a φ ψ k -
      φ k * (vocA a Y φ ψ (k - 1) * jac a c φ k + vocB a Y φ ψ (k - 1) * jac a c ψ k) := by
    linear_combination eQ + hβ - vocB a Y φ ψ (k - 1) * eD - jac a c φ k * hrep
  constructor
  · have : vocA a Y φ ψ k = cas a Y ψ k / cas a φ ψ k := rfl
    rw [this, key1]; field_simp; ring
  · have : vocB a Y φ ψ k = cas a φ Y k / cas a φ ψ k := rfl
    rw [this, key2]; field_simp; ring

/-- Downward step of the Cramer coefficients (bond `k` to bond `k-1`). -/
theorem voc_step_down (a c Y φ ψ : ℤ → ℝ) (k : ℤ) (hY : jac a c Y k = 0) (hD1 : cas a φ ψ (k - 1) ≠ 0)
    (hD : cas a φ ψ k ≠ 0) :
    vocA a Y φ ψ (k - 1) - vocA a Y φ ψ k =
        -(ψ k * (vocA a Y φ ψ k * jac a c φ k + vocB a Y φ ψ k * jac a c ψ k)) / cas a φ ψ (k - 1) ∧
      vocB a Y φ ψ (k - 1) - vocB a Y φ ψ k =
        φ k * (vocA a Y φ ψ k * jac a c φ k + vocB a Y φ ψ k * jac a c ψ k) / cas a φ ψ (k - 1) := by
  have hrep := (voc_repr a Y φ ψ k hD).1
  have eP := cas_sub a c Y ψ k
  have eQ := cas_sub a c φ Y k
  have eD := cas_sub a c φ ψ k
  rw [hY] at eP eQ
  have hα : cas a Y ψ k = vocA a Y φ ψ k * cas a φ ψ k := by
    unfold vocA; field_simp
  have hβ : cas a φ Y k = vocB a Y φ ψ k * cas a φ ψ k := by
    unfold vocB; field_simp
  have key1 : cas a Y ψ (k - 1) = vocA a Y φ ψ k * cas a φ ψ (k - 1) -
      ψ k * (vocA a Y φ ψ k * jac a c φ k + vocB a Y φ ψ k * jac a c ψ k) := by
    linear_combination (-1) * eP + hα + vocA a Y φ ψ k * eD - jac a c ψ k * hrep
  have key2 : cas a φ Y (k - 1) = vocB a Y φ ψ k * cas a φ ψ (k - 1) +
      φ k * (vocA a Y φ ψ k * jac a c φ k + vocB a Y φ ψ k * jac a c ψ k) := by
    linear_combination (-1) * eQ + hβ + vocB a Y φ ψ k * eD + jac a c φ k * hrep
  constructor
  · have : vocA a Y φ ψ (k - 1) = cas a Y ψ (k - 1) / cas a φ ψ (k - 1) := rfl
    rw [this, key1]; field_simp; ring
  · have : vocB a Y φ ψ (k - 1) = cas a φ Y (k - 1) / cas a φ ψ (k - 1) := rfl
    rw [this, key2]; field_simp; ring

/-- Upward induction on an integer half-line. -/
lemma voc_int_up_induction {P : ℤ → Prop} (m : ℤ) (h0 : P m) (step : ∀ k, m ≤ k → P k → P (k + 1)) :
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

/-- Downward induction on an integer half-line. -/
lemma voc_int_down_induction {P : ℤ → Prop} (m : ℤ) (h0 : P m) (step : ∀ k, k ≤ m → P k → P (k - 1)) :
    ∀ k, k ≤ m → P k := by
  have key : ∀ n : ℕ, P (m - n) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have := step (m - n) (by omega) ih
      have e : m - (n : ℤ) - 1 = m - ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [e] at this
  intro k hk
  have := key (m - k).toNat
  have e : m - ((m - k).toNat : ℤ) = k := by omega
  rwa [e] at this

/-- One weighted step: `ω |Δα| + |Δβ| ≤ λ (ω' |α'| + |β'|)` from the step hypotheses. -/
lemma voc_step_bound {ω ω' γ lam ψk φk ε ε' D α' β' : ℝ} (hγ : 0 < γ) (hD : γ ≤ |D|) (hlam : 0 ≤ lam)
    (hω : 0 ≤ ω) (hω' : 0 ≤ ω')
    (h1 : (ω * |ψk| + |φk|) * |ε| ≤ lam * γ * ω') (h2 : (ω * |ψk| + |φk|) * |ε'| ≤ lam * γ) :
    ω * |ψk * (α' * ε + β' * ε') / D| + |-(φk * (α' * ε + β' * ε')) / D| ≤
      lam * (ω' * |α'| + |β'|) := by
  have hD0 : 0 < |D| := hγ.trans_le hD
  have e : ω * |ψk * (α' * ε + β' * ε') / D| + |-(φk * (α' * ε + β' * ε')) / D| =
      (ω * |ψk| + |φk|) * |α' * ε + β' * ε'| / |D| := by
    simp only [abs_div, abs_neg, abs_mul]; field_simp
  rw [e, div_le_iff₀ hD0]
  have hR : |α' * ε + β' * ε'| ≤ |α'| * |ε| + |β'| * |ε'| := by
    refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
  have hT : 0 ≤ ω * |ψk| + |φk| := by positivity
  calc (ω * |ψk| + |φk|) * |α' * ε + β' * ε'| ≤ (ω * |ψk| + |φk|) * (|α'| * |ε| + |β'| * |ε'|) :=
        mul_le_mul_of_nonneg_left hR hT
    _ = |α'| * ((ω * |ψk| + |φk|) * |ε|) + |β'| * ((ω * |ψk| + |φk|) * |ε'|) := by ring
    _ ≤ |α'| * (lam * γ * ω') + |β'| * (lam * γ) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = lam * (ω' * |α'| + |β'|) * γ := by ring
    _ ≤ lam * (ω' * |α'| + |β'|) * |D| := by
        apply mul_le_mul_of_nonneg_left hD
        positivity

/-- **Forward Grönwall march** in the weighted norm `ω |α| + |β|` (see the module docstring). -/
theorem voc_march_up {a c Y φ ψ ω lam : ℤ → ℝ} {m K : ℤ} {γ Λ : ℝ} (hγ : 0 < γ)
    (hY : ∀ k ∈ Icc (m + 1) K, jac a c Y k = 0) (hD : ∀ k ∈ Icc m K, γ ≤ |cas a φ ψ k|)
    (hω0 : 0 < ω m) (hω : ∀ k ∈ Icc (m + 1) K, 0 < ω k ∧ ω k ≤ ω (k - 1))
    (hlam : ∀ k ∈ Icc (m + 1) K, 0 ≤ lam k)
    (h1 : ∀ k ∈ Icc (m + 1) K, (ω k * |ψ k| + |φ k|) * |jac a c φ k| ≤ lam k * γ * ω (k - 1))
    (h2 : ∀ k ∈ Icc (m + 1) K, (ω k * |ψ k| + |φ k|) * |jac a c ψ k| ≤ lam k * γ)
    (hΛ : ∀ k ∈ Icc m K, ∑ i ∈ Ioc m k, lam i ≤ Λ) :
    ∀ k ∈ Icc m K, ω k * |vocA a Y φ ψ k| + |vocB a Y φ ψ k| ≤
        (ω m * |vocA a Y φ ψ m| + |vocB a Y φ ψ m|) * Real.exp Λ ∧
      ω k * |vocA a Y φ ψ k - vocA a Y φ ψ m| + |vocB a Y φ ψ k - vocB a Y φ ψ m| ≤
        (ω m * |vocA a Y φ ψ m| + |vocB a Y φ ψ m|) * (Real.exp Λ - 1) := by
  set n0 : ℝ := ω m * |vocA a Y φ ψ m| + |vocB a Y φ ψ m| with hn0
  have hn00 : 0 ≤ n0 := by positivity
  have main : ∀ k : ℤ, m ≤ k → k ≤ K →
      ω k * |vocA a Y φ ψ k| + |vocB a Y φ ψ k| ≤ n0 * Real.exp (∑ i ∈ Ioc m k, lam i) ∧
      ω k * |vocA a Y φ ψ k - vocA a Y φ ψ m| + |vocB a Y φ ψ k - vocB a Y φ ψ m| ≤
        n0 * (Real.exp (∑ i ∈ Ioc m k, lam i) - 1) := by
    intro k hk
    refine voc_int_up_induction (P := fun k => k ≤ K →
      ω k * |vocA a Y φ ψ k| + |vocB a Y φ ψ k| ≤ n0 * Real.exp (∑ i ∈ Ioc m k, lam i) ∧
      ω k * |vocA a Y φ ψ k - vocA a Y φ ψ m| + |vocB a Y φ ψ k - vocB a Y φ ψ m| ≤
        n0 * (Real.exp (∑ i ∈ Ioc m k, lam i) - 1)) m ?_ ?_ k hk
    · intro _
      simp [hn0]
    · intro k hmk ih hk1
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hkmem : k + 1 ∈ Icc (m + 1) K := by rw [mem_Icc]; omega
      have hDk : γ ≤ |cas a φ ψ k| := hD k (by rw [mem_Icc]; omega)
      have hDk1 : γ ≤ |cas a φ ψ (k + 1)| := hD (k + 1) (by rw [mem_Icc]; omega)
      have hne : cas a φ ψ k ≠ 0 := fun h => by rw [h, abs_zero] at hDk; linarith
      have hne1 : cas a φ ψ (k + 1) ≠ 0 := fun h => by rw [h, abs_zero] at hDk1; linarith
      have hst := voc_step_up a c Y φ ψ (k + 1) (hY _ hkmem) (by simpa using hne) hne1
      simp only [add_sub_cancel_right] at hst
      obtain ⟨hA, hB⟩ := hst
      obtain ⟨hωp, hωle⟩ := hω (k + 1) hkmem
      have hωk : 0 < ω k := by
        have := hωp; simp only [add_sub_cancel_right] at hωle; linarith
      have hb := voc_step_bound (ω := ω (k + 1)) (ω' := ω k) (hγ) hDk1 (hlam _ hkmem) hωp.le hωk.le
        (by simpa using h1 _ hkmem) (h2 _ hkmem)
        (ψk := ψ (k + 1)) (φk := φ (k + 1)) (ε := jac a c φ (k + 1)) (ε' := jac a c ψ (k + 1))
        (α' := vocA a Y φ ψ k) (β' := vocB a Y φ ψ k)
      rw [← hA, ← hB] at hb
      simp only [add_sub_cancel_right] at hωle
      have hsum : ∑ i ∈ Ioc m (k + 1), lam i = ∑ i ∈ Ioc m k, lam i + lam (k + 1) := by
        have hI : Ioc m (k + 1) = insert (k + 1) (Ioc m k) := by
          ext i; simp only [mem_Ioc, mem_insert]; omega
        rw [hI, sum_insert (by simp), add_comm]
      rw [hsum]
      set S := ∑ i ∈ Ioc m k, lam i with hS
      set l := lam (k + 1) with hl
      have hl0 : 0 ≤ l := hlam _ hkmem
      set αk := vocA a Y φ ψ k
      set βk := vocB a Y φ ψ k
      set αk1 := vocA a Y φ ψ (k + 1)
      set βk1 := vocB a Y φ ψ (k + 1)
      set α0 := vocA a Y φ ψ m
      set β0 := vocB a Y φ ψ m
      have hnk : ω k * |αk| + |βk| ≤ n0 * Real.exp S := ih1
      have hexp : Real.exp (S + l) = Real.exp S * Real.exp l := Real.exp_add S l
      have hel : 1 + l ≤ Real.exp l := by linarith [Real.add_one_le_exp l]
      have hES : 0 < Real.exp S := Real.exp_pos S
      -- the increment
      have hinc : ω (k + 1) * |αk1 - αk| + |βk1 - βk| ≤ l * (ω k * |αk| + |βk|) := hb
      have t1 : ω (k + 1) * |αk1| ≤ ω (k + 1) * |αk| + ω (k + 1) * |αk1 - αk| := by
        have : |αk1| ≤ |αk| + |αk1 - αk| := by
          have := abs_add_le αk (αk1 - αk); simpa using this
        nlinarith [hωp]
      have t2 : |βk1| ≤ |βk| + |βk1 - βk| := by
        have := abs_add_le βk (βk1 - βk); simpa using this
      have t3 : ω (k + 1) * |αk| ≤ ω k * |αk| := mul_le_mul_of_nonneg_right hωle (abs_nonneg _)
      have u1 : ω (k + 1) * |αk1 - α0| ≤ ω (k + 1) * |αk - α0| + ω (k + 1) * |αk1 - αk| := by
        have : |αk1 - α0| ≤ |αk - α0| + |αk1 - αk| := by
          have := abs_add_le (αk - α0) (αk1 - αk); simpa using this
        nlinarith [hωp]
      have u2 : |βk1 - β0| ≤ |βk - β0| + |βk1 - βk| := by
        have := abs_add_le (βk - β0) (βk1 - βk); simpa using this
      have u3 : ω (k + 1) * |αk - α0| ≤ ω k * |αk - α0| := mul_le_mul_of_nonneg_right hωle (abs_nonneg _)
      constructor
      · calc ω (k + 1) * |αk1| + |βk1| ≤ (ω k * |αk| + |βk|) + l * (ω k * |αk| + |βk|) := by linarith
          _ = (ω k * |αk| + |βk|) * (1 + l) := by ring
          _ ≤ (n0 * Real.exp S) * Real.exp l :=
              mul_le_mul hnk hel (by linarith) (by positivity)
          _ = n0 * (Real.exp S * Real.exp l) := by ring
          _ = _ := by rw [hexp]
      · calc ω (k + 1) * |αk1 - α0| + |βk1 - β0|
            ≤ (ω k * |αk - α0| + |βk - β0|) + l * (ω k * |αk| + |βk|) := by linarith
          _ ≤ n0 * (Real.exp S - 1) + l * (n0 * Real.exp S) := by
              have := mul_le_mul_of_nonneg_left hnk hl0
              linarith
          _ = n0 * (Real.exp S * (1 + l) - 1) := by ring
          _ ≤ n0 * (Real.exp S * Real.exp l - 1) := by
              have : Real.exp S * (1 + l) ≤ Real.exp S * Real.exp l := mul_le_mul_of_nonneg_left hel hES.le
              nlinarith
          _ = _ := by rw [hexp]
  intro k hk
  rw [mem_Icc] at hk
  obtain ⟨a1, a2⟩ := main k hk.1 hk.2
  have hle := Real.exp_le_exp.2 (hΛ k (by rw [mem_Icc]; exact hk))
  exact ⟨a1.trans (mul_le_mul_of_nonneg_left hle hn00),
    a2.trans (mul_le_mul_of_nonneg_left (by linarith) hn00)⟩

/-- One weighted downward step: `|Δα| + ω' |Δβ| ≤ λ (|α'| + ω |β'|)` from the step hypotheses. -/
lemma voc_step_bound_down {ω ω' γ lam ψk φk ε ε' D α' β' : ℝ} (hγ : 0 < γ) (hD : γ ≤ |D|) (hlam : 0 ≤ lam)
    (hω : 0 ≤ ω) (hω' : 0 ≤ ω')
    (h1 : (|ψk| + ω' * |φk|) * |ε| ≤ lam * γ) (h2 : (|ψk| + ω' * |φk|) * |ε'| ≤ lam * γ * ω) :
    |-(ψk * (α' * ε + β' * ε')) / D| + ω' * |φk * (α' * ε + β' * ε') / D| ≤
      lam * (|α'| + ω * |β'|) := by
  have hD0 : 0 < |D| := hγ.trans_le hD
  have e : |-(ψk * (α' * ε + β' * ε')) / D| + ω' * |φk * (α' * ε + β' * ε') / D| =
      (|ψk| + ω' * |φk|) * |α' * ε + β' * ε'| / |D| := by
    simp only [abs_div, abs_neg, abs_mul]; field_simp
  rw [e, div_le_iff₀ hD0]
  have hR : |α' * ε + β' * ε'| ≤ |α'| * |ε| + |β'| * |ε'| := by
    refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
  have hT : 0 ≤ |ψk| + ω' * |φk| := by positivity
  calc (|ψk| + ω' * |φk|) * |α' * ε + β' * ε'| ≤ (|ψk| + ω' * |φk|) * (|α'| * |ε| + |β'| * |ε'|) :=
        mul_le_mul_of_nonneg_left hR hT
    _ = |α'| * ((|ψk| + ω' * |φk|) * |ε|) + |β'| * ((|ψk| + ω' * |φk|) * |ε'|) := by ring
    _ ≤ |α'| * (lam * γ) + |β'| * (lam * γ * ω) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = lam * (|α'| + ω * |β'|) * γ := by ring
    _ ≤ lam * (|α'| + ω * |β'|) * |D| := by
        apply mul_le_mul_of_nonneg_left hD
        positivity

/-- **Downward Grönwall march** in the weighted norm `|α| + ω |β|`, `ω` non-decreasing in the index
(non-increasing in the direction of the march): from the bond `m` down to the bond `J`. -/
theorem voc_march_down {a c Y φ ψ ω lam : ℤ → ℝ} {J m : ℤ} {γ Λ : ℝ} (hγ : 0 < γ)
    (hY : ∀ k ∈ Icc (J + 1) m, jac a c Y k = 0) (hD : ∀ k ∈ Icc J m, γ ≤ |cas a φ ψ k|)
    (hω0 : 0 < ω m) (hω : ∀ k ∈ Icc (J + 1) m, 0 < ω (k - 1) ∧ ω (k - 1) ≤ ω k)
    (hlam : ∀ k ∈ Icc (J + 1) m, 0 ≤ lam k)
    (h1 : ∀ k ∈ Icc (J + 1) m, (|ψ k| + ω (k - 1) * |φ k|) * |jac a c φ k| ≤ lam k * γ)
    (h2 : ∀ k ∈ Icc (J + 1) m, (|ψ k| + ω (k - 1) * |φ k|) * |jac a c ψ k| ≤ lam k * γ * ω k)
    (hΛ : ∀ k ∈ Icc J m, ∑ i ∈ Icc (k + 1) m, lam i ≤ Λ) :
    ∀ k ∈ Icc J m, |vocA a Y φ ψ k| + ω k * |vocB a Y φ ψ k| ≤
        (|vocA a Y φ ψ m| + ω m * |vocB a Y φ ψ m|) * Real.exp Λ ∧
      |vocA a Y φ ψ k - vocA a Y φ ψ m| + ω k * |vocB a Y φ ψ k - vocB a Y φ ψ m| ≤
        (|vocA a Y φ ψ m| + ω m * |vocB a Y φ ψ m|) * (Real.exp Λ - 1) := by
  set n0 : ℝ := |vocA a Y φ ψ m| + ω m * |vocB a Y φ ψ m| with hn0
  have hn00 : 0 ≤ n0 := by positivity
  have main : ∀ k : ℤ, k ≤ m → J ≤ k →
      |vocA a Y φ ψ k| + ω k * |vocB a Y φ ψ k| ≤ n0 * Real.exp (∑ i ∈ Icc (k + 1) m, lam i) ∧
      |vocA a Y φ ψ k - vocA a Y φ ψ m| + ω k * |vocB a Y φ ψ k - vocB a Y φ ψ m| ≤
        n0 * (Real.exp (∑ i ∈ Icc (k + 1) m, lam i) - 1) := by
    intro k hk
    refine voc_int_down_induction (P := fun k => J ≤ k →
      |vocA a Y φ ψ k| + ω k * |vocB a Y φ ψ k| ≤ n0 * Real.exp (∑ i ∈ Icc (k + 1) m, lam i) ∧
      |vocA a Y φ ψ k - vocA a Y φ ψ m| + ω k * |vocB a Y φ ψ k - vocB a Y φ ψ m| ≤
        n0 * (Real.exp (∑ i ∈ Icc (k + 1) m, lam i) - 1)) m ?_ ?_ k hk
    · intro _
      simp [hn0]
    · intro k hkm ih hJk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hkmem : k ∈ Icc (J + 1) m := by rw [mem_Icc]; omega
      have hDk : γ ≤ |cas a φ ψ k| := hD k (by rw [mem_Icc]; omega)
      have hDk1 : γ ≤ |cas a φ ψ (k - 1)| := hD (k - 1) (by rw [mem_Icc]; omega)
      have hne : cas a φ ψ k ≠ 0 := fun h => by rw [h, abs_zero] at hDk; linarith
      have hne1 : cas a φ ψ (k - 1) ≠ 0 := fun h => by rw [h, abs_zero] at hDk1; linarith
      obtain ⟨hA, hB⟩ := voc_step_down a c Y φ ψ k (hY _ hkmem) hne1 hne
      obtain ⟨hωk1, hωle⟩ := hω k hkmem
      have hωk : 0 < ω k := lt_of_lt_of_le hωk1 hωle
      have hb := voc_step_bound_down (ω := ω k) (ω' := ω (k - 1)) hγ hDk1 (hlam _ hkmem) hωk.le hωk1.le
        (h1 _ hkmem) (h2 _ hkmem)
        (ψk := ψ k) (φk := φ k) (ε := jac a c φ k) (ε' := jac a c ψ k)
        (α' := vocA a Y φ ψ k) (β' := vocB a Y φ ψ k)
      have e1 : |vocA a Y φ ψ (k - 1) - vocA a Y φ ψ k| =
          |-(ψ k * (vocA a Y φ ψ k * jac a c φ k + vocB a Y φ ψ k * jac a c ψ k)) / cas a φ ψ (k - 1)| := by
        rw [hA]
      have e2 : |vocB a Y φ ψ (k - 1) - vocB a Y φ ψ k| =
          |φ k * (vocA a Y φ ψ k * jac a c φ k + vocB a Y φ ψ k * jac a c ψ k) / cas a φ ψ (k - 1)| := by
        rw [hB]
      rw [← e1, ← e2] at hb
      have hsum : ∑ i ∈ Icc (k - 1 + 1) m, lam i = lam k + ∑ i ∈ Icc (k + 1) m, lam i := by
        have hI : Icc (k - 1 + 1) m = insert k (Icc (k + 1) m) := by
          ext i; simp only [mem_Icc, mem_insert]; omega
        rw [hI, sum_insert (by simp)]
      rw [hsum]
      set S := ∑ i ∈ Icc (k + 1) m, lam i with hS
      set l := lam k with hl
      have hl0 : 0 ≤ l := hlam _ hkmem
      set αk := vocA a Y φ ψ k
      set βk := vocB a Y φ ψ k
      set αk1 := vocA a Y φ ψ (k - 1)
      set βk1 := vocB a Y φ ψ (k - 1)
      set α0 := vocA a Y φ ψ m
      set β0 := vocB a Y φ ψ m
      have hexp : Real.exp (l + S) = Real.exp S * Real.exp l := by rw [add_comm]; exact Real.exp_add S l
      have hel : 1 + l ≤ Real.exp l := by linarith [Real.add_one_le_exp l]
      have hES : 0 < Real.exp S := Real.exp_pos S
      have t1 : |αk1| ≤ |αk| + |αk1 - αk| := by
        have := abs_add_le αk (αk1 - αk); simpa using this
      have t2 : ω (k - 1) * |βk1| ≤ ω (k - 1) * |βk| + ω (k - 1) * |βk1 - βk| := by
        have : |βk1| ≤ |βk| + |βk1 - βk| := by
          have := abs_add_le βk (βk1 - βk); simpa using this
        nlinarith [hωk1]
      have t3 : ω (k - 1) * |βk| ≤ ω k * |βk| := mul_le_mul_of_nonneg_right hωle (abs_nonneg _)
      have u1 : |αk1 - α0| ≤ |αk - α0| + |αk1 - αk| := by
        have := abs_add_le (αk - α0) (αk1 - αk); simpa using this
      have u2 : ω (k - 1) * |βk1 - β0| ≤ ω (k - 1) * |βk - β0| + ω (k - 1) * |βk1 - βk| := by
        have : |βk1 - β0| ≤ |βk - β0| + |βk1 - βk| := by
          have := abs_add_le (βk - β0) (βk1 - βk); simpa using this
        nlinarith [hωk1]
      have u3 : ω (k - 1) * |βk - β0| ≤ ω k * |βk - β0| := mul_le_mul_of_nonneg_right hωle (abs_nonneg _)
      constructor
      · calc |αk1| + ω (k - 1) * |βk1| ≤ (|αk| + ω k * |βk|) + l * (|αk| + ω k * |βk|) := by linarith
          _ = (|αk| + ω k * |βk|) * (1 + l) := by ring
          _ ≤ (n0 * Real.exp S) * Real.exp l :=
              mul_le_mul ih1 hel (by linarith) (by positivity)
          _ = n0 * (Real.exp S * Real.exp l) := by ring
          _ = _ := by rw [hexp]
      · calc |αk1 - α0| + ω (k - 1) * |βk1 - β0|
            ≤ (|αk - α0| + ω k * |βk - β0|) + l * (|αk| + ω k * |βk|) := by linarith
          _ ≤ n0 * (Real.exp S - 1) + l * (n0 * Real.exp S) := by
              have := mul_le_mul_of_nonneg_left ih1 hl0
              linarith
          _ = n0 * (Real.exp S * (1 + l) - 1) := by ring
          _ ≤ n0 * (Real.exp S * Real.exp l - 1) := by
              have : Real.exp S * (1 + l) ≤ Real.exp S * Real.exp l := mul_le_mul_of_nonneg_left hel hES.le
              nlinarith
          _ = _ := by rw [hexp]
  intro k hk
  rw [mem_Icc] at hk
  obtain ⟨a1, a2⟩ := main k hk.2 hk.1
  have hle := Real.exp_le_exp.2 (hΛ k (by rw [mem_Icc]; exact hk))
  exact ⟨a1.trans (mul_le_mul_of_nonneg_left hle hn00),
    a2.trans (mul_le_mul_of_nonneg_left (by linarith) hn00)⟩

/-- info: 'FormalResearch.Special.voc_step_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.voc_step_up

/-- info: 'FormalResearch.Special.voc_step_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.voc_step_down

/-- info: 'FormalResearch.Special.voc_march_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.voc_march_up

/-- info: 'FormalResearch.Special.voc_march_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.voc_march_down

end FormalResearch.Special
