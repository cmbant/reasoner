module

public import FormalResearch.Special.DiscreteAiryKappaSharpGeom
public import FormalResearch.Special.RacahKappaConst
public import FormalResearch.Special.RacahKappaHLgMatch

/-!
# Half-integer Racah chains: the profile and its Riemann sum on the shifted lattice

Twins of `kpU`, `kpα`, `kpP` (`DiscreteAiryKappaProfile`), `kr_sum_bounds` (`DiscreteAiryKappaRiemann`), `ksg_sv` (`DiscreteAiryKappaSharpGeom`), `rk_w_sq_kpP` (`RacahKappaConst`) for the lattice `q_k = (k + 1) h`
(`kpUH h k = (k+1)h`; declarations carry the suffix `H`).

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The lattice position `q_k = (k + ½)h`. -/
noncomputable def kpUH (h : ℝ) (k : ℤ) : ℝ := ((k : ℝ) + 1) * h

/-- The profile radius `α_k = √(q_*² - q_k²)`. -/
noncomputable def kpαH (qs h : ℝ) (k : ℤ) : ℝ := Real.sqrt (qs ^ 2 - kpUH h k ^ 2)

/-- The Ermakov profile `P_k = ρ_k² = 2/α_k` of the Hahn chain. -/
noncomputable def kpPH (qs h : ℝ) (k : ℤ) : ℝ := 2 / kpαH qs h k

lemma kpU_succH (h : ℝ) (k : ℤ) : kpUH h (k + 1) - h = kpUH h k := by unfold kpUH; push_cast; ring

lemma kpU_predH (h : ℝ) (k : ℤ) : kpUH h k - h = kpUH h (k - 1) := by unfold kpUH; push_cast; ring

/-- **Riemann sums of `1/α`** (see the module docstring): for `k₀ ≥ 1`, `h > 0`, `q_{k₀+m+1} < q_*`,
`arcsin(q_{k₀+m}/q_*) - arcsin(q_{k₀-1}/q_*) ≤ h Σ_{i≤m} 1/α_{k₀+i} ≤ arcsin(q_{k₀+m+1}/q_*) - arcsin(q_{k₀}/q_*)`. -/
theorem kr_sum_boundsH {qs h : ℝ} {k0 : ℤ} (m : ℕ) (hq : 0 < qs) (hh : 0 < h) (hk0 : 1 ≤ k0)
    (hend : kpUH h (k0 + (m : ℤ) + 1) < qs) :
    Real.arcsin (kpUH h (k0 + (m : ℤ)) / qs) - Real.arcsin (kpUH h (k0 - 1) / qs) ≤
        h * ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ)) ∧
      h * ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ)) ≤
        Real.arcsin (kpUH h (k0 + (m : ℤ) + 1) / qs) - Real.arcsin (kpUH h k0 / qs) := by
  have hk' : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hU : ∀ i : ℕ, i ≤ m + 1 → 0 < kpUH h (k0 + (i : ℤ) - 1) ∧ kpUH h (k0 + (i : ℤ)) < qs := by
    intro i hi
    refine ⟨?_, ?_⟩
    · unfold kpUH; push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      exact mul_pos (by linarith) hh
    · have : kpUH h (k0 + (i : ℤ)) ≤ kpUH h (k0 + (m : ℤ) + 1) := by
        unfold kpUH; push_cast
        have : (i : ℝ) ≤ m + 1 := by exact_mod_cast hi
        nlinarith
      linarith
  have hstep : ∀ i : ℕ, i ≤ m →
      h / kpαH qs h (k0 + (i : ℤ)) ≤ Real.arcsin (kpUH h (k0 + (i : ℤ) + 1) / qs) - Real.arcsin (kpUH h (k0 + (i : ℤ)) / qs) ∧
      Real.arcsin (kpUH h (k0 + (i : ℤ)) / qs) - Real.arcsin (kpUH h (k0 + (i : ℤ) - 1) / qs) ≤ h / kpαH qs h (k0 + (i : ℤ)) := by
    intro i hi
    have hUi := hU i (by omega)
    have hUi1 := hU (i + 1) (by omega)
    have hsucc : kpUH h (k0 + ((i + 1 : ℕ) : ℤ) - 1) = kpUH h (k0 + (i : ℤ)) := by unfold kpUH; push_cast; ring
    rw [hsucc] at hUi1
    have h1 : kpUH h (k0 + (i : ℤ) + 1) = kpUH h (k0 + (i : ℤ)) + h := by unfold kpUH; push_cast; ring
    have h2 : kpUH h (k0 + (i : ℤ) - 1) = kpUH h (k0 + (i : ℤ)) - h := by unfold kpUH; push_cast; ring
    have hlt1 : kpUH h (k0 + (i : ℤ) + 1) < qs := by
      have := hU (i + 1) (by omega)
      have e : kpUH h (k0 + ((i + 1 : ℕ) : ℤ)) = kpUH h (k0 + (i : ℤ) + 1) := by unfold kpUH; push_cast; ring
      rw [e] at this; exact this.2
    have hUk : 0 < kpUH h (k0 + (i : ℤ)) := by rw [h2] at hUi; linarith [hUi.1]
    have hUm : 0 < kpUH h (k0 + (i : ℤ) - 1) := hUi.1
    have hlk : kpUH h (k0 + (i : ℤ)) < qs := hUi.2
    have hαk : kpαH qs h (k0 + (i : ℤ)) = Real.sqrt (qs ^ 2 - kpUH h (k0 + (i : ℤ)) ^ 2) := rfl
    constructor
    · have := (kr_arcsin_mvt (qs := qs) (a := kpUH h (k0 + (i : ℤ))) (b := kpUH h (k0 + (i : ℤ) + 1)) hq hUk.le
        (by rw [h1]; linarith) hlt1).1
      rw [h1, add_sub_cancel_left] at this
      rw [hαk, h1]; exact this
    · have := (kr_arcsin_mvt (qs := qs) (a := kpUH h (k0 + (i : ℤ) - 1)) (b := kpUH h (k0 + (i : ℤ))) hq hUm.le
        (by rw [h2]; linarith) hlk).2
      rw [hαk]
      rw [h2] at this ⊢
      rwa [sub_sub_cancel] at this
  have hsum : h * ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ)) = ∑ i ∈ range (m + 1), h / kpαH qs h (k0 + (i : ℤ)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have e1 : ∑ i ∈ range (m + 1), (Real.arcsin (kpUH h (k0 + (i : ℤ) + 1) / qs) - Real.arcsin (kpUH h (k0 + (i : ℤ)) / qs)) =
      Real.arcsin (kpUH h (k0 + (m : ℤ) + 1) / qs) - Real.arcsin (kpUH h k0 / qs) := by
    have := Finset.sum_range_sub (fun i : ℕ => Real.arcsin (kpUH h (k0 + (i : ℤ)) / qs)) (m + 1)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at this
    simpa [add_assoc] using this
  have e2 : ∑ i ∈ range (m + 1), (Real.arcsin (kpUH h (k0 + (i : ℤ)) / qs) - Real.arcsin (kpUH h (k0 + (i : ℤ) - 1) / qs)) =
      Real.arcsin (kpUH h (k0 + (m : ℤ)) / qs) - Real.arcsin (kpUH h (k0 - 1) / qs) := by
    set g : ℕ → ℝ := fun i => Real.arcsin (kpUH h (k0 + (i : ℤ) - 1) / qs) with hg
    have e : ∀ i : ℕ, Real.arcsin (kpUH h (k0 + (i : ℤ)) / qs) = g (i + 1) := by
      intro i; rw [hg]; simp only []; congr 2; unfold kpUH; push_cast; ring
    have key : ∀ i : ℕ, Real.arcsin (kpUH h (k0 + (i : ℤ)) / qs) - Real.arcsin (kpUH h (k0 + (i : ℤ) - 1) / qs) = g (i + 1) - g i := by
      intro i; rw [e i]
    simp only [key]
    rw [Finset.sum_range_sub g (m + 1), e m]
    simp [hg]
  constructor
  · rw [← e2]; exact Finset.sum_le_sum fun i hi => (hstep i (by have := Finset.mem_range.1 hi; omega)).2
  · rw [← e1]; exact Finset.sum_le_sum fun i hi => (hstep i (by have := Finset.mem_range.1 hi; omega)).1

/-- **The band sum of the profile**: `(π/2)N(1 - a) ≤ Σ P/2 ≤ (π/2)N`. -/
theorem ksg_svH {qs h : ℝ} {k0 : ℤ} (m : ℕ) (hq : 0 < qs) (hh : 0 < h) (hk0 : 1 ≤ k0)
    (hend : kpUH h (k0 + (m : ℤ) + 1) < qs) :
    ∑ i ∈ range (m + 1), kpPH qs h (k0 + (i : ℤ)) / 2 ≤ Real.pi / 2 * (1 / h) ∧
    Real.pi / 2 * (1 / h) * (1 - (kpUH h (k0 - 1) / qs + √(1 - (kpUH h (k0 + (m : ℤ)) / qs) ^ 2))) ≤
      ∑ i ∈ range (m + 1), kpPH qs h (k0 + (i : ℤ)) / 2 := by
  obtain ⟨hlo, hhi⟩ := kr_sum_boundsH (qs := qs) (h := h) (k0 := k0) m hq hh hk0 hend
  have hk' : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hsum : ∑ i ∈ range (m + 1), kpPH qs h (k0 + (i : ℤ)) / 2 = ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold kpPH
    ring
  rw [hsum]
  have hπ := Real.pi_pos
  have hU0 : ∀ j : ℤ, 1 ≤ j → 0 < kpUH h j := fun j hj => by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    unfold kpUH; positivity
  have hUm : kpUH h (k0 + (m : ℤ)) < qs := by
    have : kpUH h (k0 + (m : ℤ)) ≤ kpUH h (k0 + (m : ℤ) + 1) := by unfold kpUH; push_cast; nlinarith
    linarith
  have hUm0 : 0 < kpUH h (k0 + (m : ℤ)) := hU0 _ (by omega)
  have hU1 : 0 ≤ kpUH h (k0 - 1) := by unfold kpUH; push_cast; nlinarith
  have hU1q : kpUH h (k0 - 1) ≤ kpUH h (k0 + (m : ℤ)) := by unfold kpUH; push_cast; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; nlinarith
  have e1 : 1 / h * (h * ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ))) = ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ)) := by
    field_simp
  constructor
  · have hA0 : 0 ≤ Real.arcsin (kpUH h k0 / qs) := Real.arcsin_nonneg.2 (by have := hU0 k0 hk0; positivity)
    have hA1 : Real.arcsin (kpUH h (k0 + (m : ℤ) + 1) / qs) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
    have : h * ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ)) ≤ Real.pi / 2 := by linarith
    rw [← e1]
    exact mul_le_mul_of_nonneg_left this (by positivity) |>.trans (by rw [mul_comm])
  · have hw0 : 0 ≤ kpUH h (k0 + (m : ℤ)) / qs := by positivity
    have hw1 : kpUH h (k0 + (m : ℤ)) / qs ≤ 1 := by rw [div_le_one hq]; exact hUm.le
    have hz0 : 0 ≤ kpUH h (k0 - 1) / qs := by positivity
    have hz1 : kpUH h (k0 - 1) / qs ≤ 1 := by rw [div_le_one hq]; linarith
    have j1 := ksg_arccos_le hw0 hw1
    have j2 := ksg_arcsin_le hz0 hz1
    have key : Real.pi / 2 * (1 - (kpUH h (k0 - 1) / qs + √(1 - (kpUH h (k0 + (m : ℤ)) / qs) ^ 2))) ≤
        h * ∑ i ∈ range (m + 1), 1 / kpαH qs h (k0 + (i : ℤ)) := by nlinarith
    rw [← e1]
    have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 1 / h)
    calc Real.pi / 2 * (1 / h) * (1 - (kpUH h (k0 - 1) / qs + √(1 - (kpUH h (k0 + (m : ℤ)) / qs) ^ 2))) =
        1 / h * (Real.pi / 2 * (1 - (kpUH h (k0 - 1) / qs + √(1 - (kpUH h (k0 + (m : ℤ)) / qs) ^ 2)))) := by ring
      _ ≤ _ := this

/-- In terms of the Ermakov profile `kpPH = 2/α`: `w²(q_k) = kpPH/√s`. -/
lemma rk_w_sq_kpPH {P Q τ x qs h : ℝ} {k : ℤ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1)
    (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2) (hq : 0 ≤ kpUH h k) (hqq : kpUH h k < qs)
    (hint : 0 < (1 - P * kpUH h k ^ 2) * (1 - Q * kpUH h k ^ 2)) (hspos : 0 < rkS P Q x) :
    dlgsW (hrA1 P Q) (hrU P Q τ x) (kpUH h k) ^ 2 = kpPH qs h k / Real.sqrt (rkS P Q x) := by
  rw [rk_w_sq hP hQ hτ hs hq hqq hint hspos]
  unfold kpPH kpαH
  ring


end FormalResearch.Special
