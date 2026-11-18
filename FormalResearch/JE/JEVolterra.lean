module

public import FormalResearch.JE.JECasoratian
public import FormalResearch.JE.JEKernel
public import Mathlib

/-!
# Paper J engine, JE4: Casoratian--Volterra stability, single patch (`thm:eng-volterra`(a), `P = 1`)

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/engine.tex`, Section 2, `thm:eng-volterra` (part (a), the
Volterra equation from the Abel and Cramer identities, `lem:eng-kernel`) and its proof in `app_engine.tex`
(`app:eng-twopatch`, the one-patch case with the two-node seed).  Branch `agents/m7-m1-global-racah` of QIprojects.

## Setting and conventions
* `Lh h A Q f j := h⁻¹ · Lop A Q f j` is the paper's `L_h` (`JECasoratian.Lop` is `h · L_h`).
* `cas A f g j` is the paper's Casoratian `𝒲_j(f,g)`.
* The sites are `{0,…,N}` (`N ≥ 1`), the equation sites are `I° = {1,…,N-1}` (the two-node seed: `ψ_0, ψ_1` are
  prescribed), and the residual of `φ^{(α)}` is `r^{(α)}_k = (L_h φ^{(α)})_k`.
* `volterraTheta h ω N ρ M = (h/ω) ∑_{k∈I°} ρ_k 𝖬_k²` is the paper's `Θ`, `volterraC cm CE K = (1+C_E²)(K²+K)/c₋`
  is the constant `C` of the theorem.

## Statement formalised (`volterra_single_patch`)
Assume, for the comparison pair `(φ¹,φ²) = (φ1,φ2)` on `{0,…,N}`:
* (S1) `c₋ ω ≤ |𝒲_j(φ¹,φ²)|` on the bonds `0 ≤ j < N` (the upper bound `c₊` is not used for `P = 1`);
* (S2) envelopes: `0 < 𝖬_j`, `0 < 𝖶_j`, `𝖶_k ≤ C_E 𝖶_j` for `k ≤ j`, `|φ¹_j| ≤ K 𝖶_j 𝖬_j`,
  `|φ²_j| ≤ K 𝖶_j⁻¹ 𝖬_j`, and the residual bounds `|r¹_k| ≤ ε ρ_k 𝖶_k 𝖬_k`, `|r²_k| ≤ ε ρ_k 𝖶_k⁻¹ 𝖬_k` on `I°`
  (`ε ≥ 0`, `ρ ≥ 0`);
* the seed `ψ_0 = φ¹_0`, `ψ_1 = φ¹_1`, and `(L_h ψ)_k = 0` on `I°` (the exact solution of the recurrence).
Conclusion: if `C · ε Θ ≤ 1` with `C = volterraC`, then `|ψ_j - φ¹_j| ≤ C · ε Θ · 𝖶_j 𝖬_j` for all `j ∈ {0,…,N}`.
So `c* = 1/C` and the constant `C` depend only on `K, c₋, C_E` (not on `c₊`, `Λ`, `P`).

The proof: the error `e = ψ - φ¹` satisfies the exact Volterra equation (Abel's identity `lem:eng-abel`(i) summed over
the window, then the first Cramer identity `lem:eng-abel`(ii)); the two kernel bounds of `lem:eng-kernel` (`JEKernel`)
bound its terms; an induction on the site index closes the bound `|e_m| ≤ c 𝖶_m 𝖬_m`, `c = C ε Θ`.  The induction
replaces the discrete Grönwall lemma: the coupling constant is `c ≤ 1`, so each step gives the same constant.

## Differences from the paper
1. Only the single patch `P = 1` with the two-node seed is formalised (the theorem's multi-patch part and the hard-edge
   seed are not).  The transfer condition (S3) is therefore absent.
2. The solution `ψ` is a hypothesis (any solution with the seed); existence and uniqueness (the recurrence with
   `A > 0`) are not used for the bound.  The bond positivity `A_j > 0` is not needed for the inequality.
3. The paper's constants `c*, C` are explicit here: `C = volterraC`, `c* = 1/C`.

## Non-vacuity
* `volterra_instance`: `ε = 0` and `ψ = φ¹` (the conclusion is `0 ≤ 0`); it checks the hypotheses only.
* `volterra_instance_perturbed`: `A = 1`, `Q = 2cosθ`, the comparison pair `φ¹_j = cos(jθ')`, `φ²_j = sin(jθ')`, so
  `ε = |2cosθ' - 2cosθ|/h > 0` when `cosθ' ≠ cosθ`, and the exact solution `ψ = pertSol θ θ'`
  (`ψ_j = cos(jθ) + ((cosθ'-cosθ)/sinθ) sin(jθ)`, `ψ_0 = φ¹_0`, `ψ_1 = φ¹_1`).  The smallness `C ε Θ ≤ 1` is the
  hypothesis `hsmall`; the conclusion bounds the non-zero error `ψ_j - φ¹_j`.
* `volterra_instance_perturbed_closed`: `ε Θ = |2cosθ'-2cosθ|(N-1)/|sinθ'|` does not depend on `h`, so the smallness
  is `4|2cosθ'-2cosθ|(N-1)/|sinθ'| ≤ 1` and the bound is `4|2cosθ'-2cosθ|(N-1)/|sinθ'|`.
* `volterra_instance_perturbed_nontrivial`: for `N ≥ 2` and `cosθ ≠ cosθ'` the right-hand side is positive; for
  `cosθ' ≠ 0` the error at `j = 2`, `ψ_2 - cos 2θ' = 2cosθ'(cosθ - cosθ')`, is non-zero, so `ψ ≠ φ¹`.

Not formalised: multi-patch stability, the hard-edge seed, the transfer matrices, and the application to the Weber and
parabolic-cylinder ladders.
-/

@[expose] public section

open Finset

namespace FormalResearch.JE

/-- The paper's residual operator `L_h f = h⁻¹ · Lop f` (the Jacobi operator with the factor `h⁻¹`). -/
noncomputable def Lh (h : ℝ) (A Q f : ℤ → ℝ) (j : ℤ) : ℝ := h⁻¹ * Lop A Q f j

/-- The constant `C = (1 + C_E²)(K² + K)/c₋` of `thm:eng-volterra`(a) for one patch. -/
noncomputable def volterraC (cm CE K : ℝ) : ℝ := (1 + CE ^ 2) * (K ^ 2 + K) / cm

/-- The modulus sum `Θ = (h/ω) ∑_{k ∈ I°} ρ_k 𝖬_k²` over the equation sites `I° = {1,…,N-1}`. -/
noncomputable def volterraTheta (h ω : ℝ) (N : ℤ) (ρ M : ℤ → ℝ) : ℝ :=
  h / ω * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2

lemma Lop_eq_h_mul_Lh (h : ℝ) (hh : h ≠ 0) (A Q f : ℤ → ℝ) (j : ℤ) :
    Lop A Q f j = h * Lh h A Q f j := by
  unfold Lh; field_simp

/-- The summed Abel identity with the residual of the error (`lem:eng-abel`(i), summed from `1`). -/
lemma flux_sum (h : ℝ) (hh : h ≠ 0) (A Q e φ r : ℤ → ℝ) (m : ℤ) (he0 : e 0 = 0) (he1 : e 1 = 0)
    (hm : 1 ≤ m) (hLe : ∀ j ∈ Icc 1 (m - 1), Lop A Q e j = -(h * r j)) :
    cas A e φ (m - 1) = -h * ∑ j ∈ Icc 1 (m - 1), (φ j * r j + e j * Lh h A Q φ j) := by
  have habel := abel_sum A Q e φ 1 (m - 1) (by omega)
  have hcas0 : cas A e φ (1 - 1) = 0 := by
    rw [show (1:ℤ) - 1 = 0 by norm_num]
    unfold cas; simp [he0, he1]
  have hterm : ∀ j ∈ Icc 1 (m - 1), φ j * Lop A Q e j - e j * Lop A Q φ j
      = -h * (φ j * r j + e j * Lh h A Q φ j) := by
    intro j hj
    rw [hLe j hj, Lop_eq_h_mul_Lh h hh A Q φ j]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at habel
  linarith [habel, hcas0]

/-- **Casoratian--Volterra stability, one patch, two-node seed** (`thm:eng-volterra`(a) with `P = 1`). -/
theorem volterra_single_patch (h ω cm CE K ε : ℝ) (N : ℤ) (A Q φ1 φ2 ψ ρ M W : ℤ → ℝ)
    (hh : 0 < h) (hω : 0 < ω) (hcm : 0 < cm) (hN : 1 ≤ N) (hε : 0 ≤ ε)
    (hS1 : ∀ j ∈ Ico 0 N, cm * ω ≤ |cas A φ1 φ2 j|)
    (hMpos : ∀ j ∈ Icc 0 N, 0 < M j) (hWpos : ∀ j ∈ Icc 0 N, 0 < W j)
    (hmono : ∀ k ∈ Icc 0 N, ∀ j ∈ Icc 0 N, k ≤ j → W k ≤ CE * W j)
    (hφ1 : ∀ j ∈ Icc 0 N, |φ1 j| ≤ K * W j * M j)
    (hφ2 : ∀ j ∈ Icc 0 N, |φ2 j| ≤ K * (W j)⁻¹ * M j)
    (hρ : ∀ k, 0 ≤ ρ k)
    (hr1 : ∀ k ∈ Icc 1 (N - 1), |Lh h A Q φ1 k| ≤ ε * ρ k * W k * M k)
    (hr2 : ∀ k ∈ Icc 1 (N - 1), |Lh h A Q φ2 k| ≤ ε * ρ k * (W k)⁻¹ * M k)
    (hψ0 : ψ 0 = φ1 0) (hψ1 : ψ 1 = φ1 1)
    (hsol : ∀ k ∈ Icc 1 (N - 1), Lh h A Q ψ k = 0)
    (hsmall : volterraC cm CE K * (ε * volterraTheta h ω N ρ M) ≤ 1) :
    ∀ j ∈ Icc 0 N, |ψ j - φ1 j| ≤ volterraC cm CE K * (ε * volterraTheta h ω N ρ M) * W j * M j := by
  have hhne : h ≠ 0 := hh.ne'
  -- the error and its boundary values
  obtain ⟨e, he⟩ : ∃ e : ℤ → ℝ, e = fun j => ψ j - φ1 j := ⟨_, rfl⟩
  have heq : ∀ j, e j = ψ j - φ1 j := fun j => by rw [he]
  have he0 : e 0 = 0 := by rw [heq, hψ0]; ring
  have he1 : e 1 = 0 := by rw [heq, hψ1]; ring
  -- the residual of the error on the equation sites
  have hLe : ∀ k ∈ Icc 1 (N - 1), Lop A Q e k = -(h * Lh h A Q φ1 k) := by
    intro k hk
    have h1 : Lop A Q e k = Lop A Q ψ k - Lop A Q φ1 k := by
      simp only [Lop, heq]; ring
    rw [h1, Lop_eq_h_mul_Lh h hhne A Q ψ k, hsol k hk, Lop_eq_h_mul_Lh h hhne A Q φ1 k]; ring
  -- the flux identities for φ¹ and φ²
  have hF1 : ∀ m : ℤ, 1 ≤ m → m ≤ N → cas A e φ1 (m - 1)
      = -h * ∑ j ∈ Icc 1 (m - 1), (φ1 j * Lh h A Q φ1 j + e j * Lh h A Q φ1 j) := by
    intro m hm1 hmN
    refine flux_sum h hhne A Q e φ1 (Lh h A Q φ1) m he0 he1 hm1 ?_
    intro j hj
    rw [mem_Icc] at hj
    exact hLe j (by rw [mem_Icc]; omega)
  have hF2 : ∀ m : ℤ, 1 ≤ m → m ≤ N → cas A e φ2 (m - 1)
      = -h * ∑ j ∈ Icc 1 (m - 1), (φ2 j * Lh h A Q φ1 j + e j * Lh h A Q φ2 j) := by
    intro m hm1 hmN
    refine flux_sum h hhne A Q e φ2 (Lh h A Q φ1) m he0 he1 hm1 ?_
    intro j hj
    rw [mem_Icc] at hj
    exact hLe j (by rw [mem_Icc]; omega)
  -- the Volterra equation: Cramer's identity with the two flux identities
  have hV : ∀ m : ℤ, 1 ≤ m → m ≤ N → e m * cas A φ1 φ2 (m - 1)
      = -h * ∑ k ∈ Icc 1 (m - 1), ((φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
          + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k) := by
    intro m hm1 hmN
    have hC := cramer_first e φ1 φ2 A (m - 1)
    rw [sub_add_cancel] at hC
    have hC' : e m * cas A φ1 φ2 (m - 1) = φ1 m * cas A e φ2 (m - 1) - φ2 m * cas A e φ1 (m - 1) := by
      linarith
    rw [hC', hF1 m hm1 hmN, hF2 m hm1 hmN]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  -- constants
  have h0mem : (0:ℤ) ∈ Icc 0 N := mem_Icc.mpr ⟨le_refl _, by omega⟩
  have hK0 : 0 ≤ K := by
    have h0 := hφ1 0 h0mem
    have hpos : 0 < W 0 * M 0 := mul_pos (hWpos 0 h0mem) (hMpos 0 h0mem)
    have : 0 ≤ K * W 0 * M 0 := (abs_nonneg _).trans h0
    nlinarith
  set Θ := volterraTheta h ω N ρ M with hΘdef
  set a := volterraC cm CE K with hadef
  have hΘ0 : 0 ≤ Θ := by
    rw [hΘdef, volterraTheta]
    exact mul_nonneg (div_nonneg hh.le hω.le) (Finset.sum_nonneg (fun k _ => mul_nonneg (hρ k) (sq_nonneg _)))
  have ha0 : 0 ≤ a := by
    rw [hadef, volterraC]
    exact div_nonneg (mul_nonneg (by positivity) (by nlinarith)) hcm.le
  have hacm : a * cm = (1 + CE ^ 2) * (K ^ 2 + K) := by
    rw [hadef, volterraC]; field_simp
  have hΘω : h * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2 = ω * Θ := by
    rw [hΘdef, volterraTheta]; field_simp
  set c := a * (ε * Θ) with hcdef
  have hc0 : 0 ≤ c := mul_nonneg ha0 (mul_nonneg hε hΘ0)
  have hc1 : c ≤ 1 := hsmall
  -- the Volterra bound by induction on the site index
  have key : ∀ n : ℕ, ∀ m : ℤ, 0 ≤ m → m ≤ N → m ≤ (n : ℤ) → |e m| ≤ c * W m * M m := by
    intro n
    induction n with
    | zero =>
      intro m hm0 hmN hmn
      have hm : m = 0 := by push_cast at hmn; omega
      subst hm
      rw [he0, abs_zero]
      exact mul_nonneg (mul_nonneg hc0 (hWpos 0 h0mem).le) (hMpos 0 h0mem).le
    | succ n ih =>
      intro m hm0 hmN hmn
      by_cases hmle : m ≤ (n : ℤ)
      · exact ih m hm0 hmN hmle
      rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with hm | hm | hm
      · subst hm
        rw [he0, abs_zero]
        exact mul_nonneg (mul_nonneg hc0 (hWpos 0 h0mem).le) (hMpos 0 h0mem).le
      · subst hm
        rw [he1, abs_zero]
        have h1mem : (1:ℤ) ∈ Icc 0 N := mem_Icc.mpr ⟨by norm_num, by omega⟩
        exact mul_nonneg (mul_nonneg hc0 (hWpos 1 h1mem).le) (hMpos 1 h1mem).le
      · have hmemm : m ∈ Icc 0 N := mem_Icc.mpr ⟨by omega, hmN⟩
        have hVm := hV m (by omega) hmN
        -- the bound on each summand of the Volterra sum
        have hTk : ∀ k ∈ Icc 1 (m - 1),
            |(φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
              + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k|
            ≤ (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * (ε * (ρ k * M k ^ 2)) := by
          intro k hk
          rw [mem_Icc] at hk
          have hkI : k ∈ Icc 1 (N - 1) := mem_Icc.mpr ⟨hk.1, by omega⟩
          have hk0 : k ∈ Icc 0 N := mem_Icc.mpr ⟨by omega, by omega⟩
          have hkn : k ≤ (n : ℤ) := by omega
          have hek : |e k| ≤ c * W k * M k := ih k (by omega) (by omega) hkn
          have hCE' : W k ≤ CE * W m := hmono k hk0 m hmemm (by omega)
          have hKa := kernel_bound_a CE (W m) (W k) (M m) (M k) K (φ1 m) (φ2 m) (φ1 k) (φ2 k)
            (hWpos m hmemm) (hWpos k hk0) (hMpos m hmemm) (hMpos k hk0) hCE'
            (hφ1 m hmemm) (hφ2 m hmemm) (hφ1 k hk0) (hφ2 k hk0)
          have hKb := kernel_bound_b CE (W m) (W k) (M m) (M k) K (φ1 m) (φ2 m)
            (Lh h A Q φ1 k) (Lh h A Q φ2 k) (e k) (ε * ρ k) c
            (hWpos m hmemm) (hWpos k hk0) (hMpos m hmemm) (hMpos k hk0) hCE'
            (hφ1 m hmemm) (hφ2 m hmemm) (hr1 k hkI) (hr2 k hkI) hek
          have hWk := hWpos k hk0
          have hX1 : |φ1 m * φ2 k - φ2 m * φ1 k| * |Lh h A Q φ1 k|
              ≤ (1 + CE ^ 2) * K ^ 2 * (W m * M m) * (ε * (ρ k * M k ^ 2)) := by
            have h1 : |φ1 m * φ2 k - φ2 m * φ1 k| * |Lh h A Q φ1 k| * W k
                ≤ ((1 + CE ^ 2) * K ^ 2 * (W m * M m) * (ε * (ρ k * M k ^ 2))) * W k := by
              calc |φ1 m * φ2 k - φ2 m * φ1 k| * |Lh h A Q φ1 k| * W k
                  = (|φ1 m * φ2 k - φ2 m * φ1 k| * W k) * |Lh h A Q φ1 k| := by ring
                _ ≤ ((1 + CE ^ 2) * K ^ 2 * W m * M m * M k) * |Lh h A Q φ1 k| :=
                    mul_le_mul_of_nonneg_right hKa (abs_nonneg _)
                _ ≤ ((1 + CE ^ 2) * K ^ 2 * W m * M m * M k) * (ε * ρ k * W k * M k) :=
                    mul_le_mul_of_nonneg_left (hr1 k hkI)
                      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg K))
                        (hWpos m hmemm).le) (hMpos m hmemm).le) (hMpos k hk0).le)
                _ = ((1 + CE ^ 2) * K ^ 2 * (W m * M m) * (ε * (ρ k * M k ^ 2))) * W k := by ring
            exact le_of_mul_le_mul_right h1 hWk
          have hX2 : |φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k| * |e k|
              ≤ (1 + CE ^ 2) * (c * K) * (ε * (ρ k * M k ^ 2)) * (W m * M m) := by
            calc |φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k| * |e k|
                ≤ (1 + CE ^ 2) * K * (ε * ρ k) * c * W m * M m * M k ^ 2 := hKb
              _ = (1 + CE ^ 2) * (c * K) * (ε * (ρ k * M k ^ 2)) * (W m * M m) := by ring
          calc |(φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
                + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k|
              ≤ |(φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k|
                + |(φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k| := abs_add_le _ _
            _ = |φ1 m * φ2 k - φ2 m * φ1 k| * |Lh h A Q φ1 k|
                + |φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k| * |e k| := by
                rw [abs_mul, abs_mul]
            _ ≤ (1 + CE ^ 2) * K ^ 2 * (W m * M m) * (ε * (ρ k * M k ^ 2))
                + (1 + CE ^ 2) * (c * K) * (ε * (ρ k * M k ^ 2)) * (W m * M m) := add_le_add hX1 hX2
            _ = (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * (ε * (ρ k * M k ^ 2)) := by ring
        -- sum over the window, then enlarge to all equation sites
        have hsub : Icc 1 (m - 1) ⊆ Icc 1 (N - 1) := Finset.Icc_subset_Icc (le_refl 1) (by omega)
        have hD0 : 0 ≤ (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) :=
          mul_nonneg (mul_nonneg (by positivity) (add_nonneg (sq_nonneg K) (mul_nonneg hc0 hK0)))
            (mul_nonneg (hWpos m hmemm).le (hMpos m hmemm).le)
        have hsum : ∑ k ∈ Icc 1 (m - 1), |(φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
              + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k|
            ≤ (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * (ε * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2) := by
          calc ∑ k ∈ Icc 1 (m - 1), |(φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
                + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k|
              ≤ ∑ k ∈ Icc 1 (m - 1), (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * (ε * (ρ k * M k ^ 2)) :=
                Finset.sum_le_sum hTk
            _ ≤ ∑ k ∈ Icc 1 (N - 1), (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * (ε * (ρ k * M k ^ 2)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub
                intro k _ _
                have := hρ k
                have : 0 ≤ ε * (ρ k * M k ^ 2) := mul_nonneg hε (mul_nonneg (hρ k) (sq_nonneg _))
                exact mul_nonneg hD0 this
            _ = (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * (ε * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2) := by
                rw [Finset.mul_sum, Finset.mul_sum]
        -- the Casoratian lower bound and the Volterra equation give the bound for e_m
        have hcas : cm * ω ≤ |cas A φ1 φ2 (m - 1)| := hS1 (m - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
        have habsV : |e m| * |cas A φ1 φ2 (m - 1)| = h * |∑ k ∈ Icc 1 (m - 1), ((φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
            + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k)| := by
          have := congrArg abs hVm
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos hh] at this
          exact this
        have hfin0 : |e m| * (cm * ω) ≤ h * ((1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m)
            * (ε * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2)) := by
          have hmul : |e m| * (cm * ω) ≤ |e m| * |cas A φ1 φ2 (m - 1)| :=
            mul_le_mul_of_nonneg_left hcas (abs_nonneg _)
          have habs2 : |∑ k ∈ Icc 1 (m - 1), ((φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
              + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k)|
              ≤ ∑ k ∈ Icc 1 (m - 1), |(φ1 m * φ2 k - φ2 m * φ1 k) * Lh h A Q φ1 k
              + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k| :=
            Finset.abs_sum_le_sum_abs _ _
          have := mul_le_mul_of_nonneg_left (habs2.trans hsum) hh.le
          linarith [hmul, habsV, this]
        -- divide by ω and by c_- and identify the constant
        have hfin1 : |e m| * cm * ω ≤ (a * cm) * (W m * M m) * (ε * Θ) * ω := by
          have hD' : (1 + CE ^ 2) * (K ^ 2 + c * K) ≤ (1 + CE ^ 2) * (K ^ 2 + K) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have : c * K ≤ K := mul_le_of_le_one_left hK0 hc1
            linarith
          have hS : h * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2 = ω * Θ := hΘω
          have hWM : 0 ≤ W m * M m := mul_nonneg (hWpos m hmemm).le (hMpos m hmemm).le
          have hε' : 0 ≤ ε * Θ := mul_nonneg hε hΘ0
          calc |e m| * cm * ω = |e m| * (cm * ω) := by ring
            _ ≤ h * ((1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * (ε * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2)) := hfin0
            _ = (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * ε * (h * ∑ k ∈ Icc 1 (N - 1), ρ k * M k ^ 2) := by ring
            _ = (1 + CE ^ 2) * (K ^ 2 + c * K) * (W m * M m) * ε * (ω * Θ) := by rw [hS]
            _ ≤ (1 + CE ^ 2) * (K ^ 2 + K) * (W m * M m) * ε * (ω * Θ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD' hWM) hε)
                  (mul_nonneg hω.le hΘ0)
            _ = (a * cm) * (W m * M m) * (ε * Θ) * ω := by rw [hacm]; ring
        have hA1 : |e m| * cm ≤ (a * cm) * (W m * M m) * (ε * Θ) :=
          le_of_mul_le_mul_right (by linarith [hfin1] : |e m| * cm * ω ≤ ((a * cm) * (W m * M m) * (ε * Θ)) * ω) hω
        have hA2 : |e m| * cm ≤ (c * W m * M m) * cm := by
          calc |e m| * cm ≤ (a * cm) * (W m * M m) * (ε * Θ) := hA1
            _ = (c * W m * M m) * cm := by rw [hcdef]; ring
        exact le_of_mul_le_mul_right hA2 hcm
  intro j hj
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (mem_Icc.mp hj).1
  have hk := key n n (by positivity) (mem_Icc.mp hj).2 le_rfl
  rw [heq] at hk
  exact hk

/-- Non-vacuity of the hypotheses of `volterra_single_patch`: the exact constant-coefficient pair `cos(jθ)`, `sin(jθ)`
(`A = 1`, `Q = 2 cos θ`, `JECasoratian.cos_sin_solutions`) with `ψ = φ¹`, `ε = 0`, `W = M = ρ = 1`, `K = C_E = c₋ = 1`
and `ω = |sin θ| ≠ 0` satisfies every hypothesis of `volterra_single_patch`, so the theorem applies to it (with
`ψ = φ¹` the conclusion `|ψ_j - φ¹_j| ≤ 0` is consistent). -/
theorem volterra_instance (h θ : ℝ) (N : ℤ) (hh : 0 < h) (hN : 1 ≤ N) (hθ : Real.sin θ ≠ 0) :
    ∀ j ∈ Icc 0 N, |(fun i : ℤ => Real.cos (i * θ)) j - (fun i : ℤ => Real.cos (i * θ)) j|
      ≤ volterraC 1 1 1 * (0 * volterraTheta h |Real.sin θ| N (fun _ => 1) (fun _ => 1))
          * (fun _ : ℤ => (1 : ℝ)) j * (fun _ : ℤ => (1 : ℝ)) j :=
  volterra_single_patch h |Real.sin θ| 1 1 1 0 N (fun _ => 1) (fun _ => 2 * Real.cos θ)
    (fun i => Real.cos (i * θ)) (fun i => Real.sin (i * θ)) (fun i => Real.cos (i * θ))
    (fun _ => 1) (fun _ => 1) (fun _ => 1) hh (abs_pos.mpr hθ) one_pos hN le_rfl
    (fun j _ => by
      rw [(cos_sin_solutions θ).2.2 j, abs_neg, one_mul])
    (fun _ _ => one_pos) (fun _ _ => one_pos)
    (fun _ _ j _ _ => by norm_num)
    (fun j _ => by rw [one_mul, one_mul]; exact Real.abs_cos_le_one _)
    (fun j _ => by rw [inv_one, mul_one, one_mul]; exact Real.abs_sin_le_one _)
    (fun _ => zero_le_one)
    (fun k _ => by rw [Lh, (cos_sin_solutions θ).1 k, mul_zero]; simp)
    (fun k _ => by rw [Lh, (cos_sin_solutions θ).2.1 k, mul_zero]; simp)
    rfl rfl
    (fun k _ => by rw [Lh, (cos_sin_solutions θ).1 k, mul_zero])
    (by norm_num)

/-! ### A non-trivial instance: the perturbed cosine pair (`ε > 0`, `ψ ≠ φ¹`) -/

/-- The residual of the comparison cosine `φ¹_j = cos(jθ')` for `A = 1`, `Q = 2cosθ`:
`Lop (cos(·θ')) k = (2cosθ' - 2cosθ) cos(kθ')`. -/
lemma Lop_cos_pert (θ θ' : ℝ) (k : ℤ) :
    Lop (fun _ => 1) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.cos (i * θ')) k
      = (2 * Real.cos θ' - 2 * Real.cos θ) * Real.cos (k * θ') := by
  have h1 : Real.cos (((k + 1 : ℤ) : ℝ) * θ')
      = Real.cos (k * θ') * Real.cos θ' - Real.sin (k * θ') * Real.sin θ' := by
    push_cast; rw [add_mul, one_mul, Real.cos_add]
  have h2 : Real.cos (((k - 1 : ℤ) : ℝ) * θ')
      = Real.cos (k * θ') * Real.cos θ' + Real.sin (k * θ') * Real.sin θ' := by
    push_cast; rw [sub_mul, one_mul, Real.cos_sub]
  simp only [Lop]
  rw [h1, h2]
  ring

/-- The residual of the comparison sine `φ²_j = sin(jθ')`: `Lop (sin(·θ')) k = (2cosθ' - 2cosθ) sin(kθ')`. -/
lemma Lop_sin_pert (θ θ' : ℝ) (k : ℤ) :
    Lop (fun _ => 1) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.sin (i * θ')) k
      = (2 * Real.cos θ' - 2 * Real.cos θ) * Real.sin (k * θ') := by
  have h1 : Real.sin (((k + 1 : ℤ) : ℝ) * θ')
      = Real.sin (k * θ') * Real.cos θ' + Real.cos (k * θ') * Real.sin θ' := by
    push_cast; rw [add_mul, one_mul, Real.sin_add]
  have h2 : Real.sin (((k - 1 : ℤ) : ℝ) * θ')
      = Real.sin (k * θ') * Real.cos θ' - Real.cos (k * θ') * Real.sin θ' := by
    push_cast; rw [sub_mul, one_mul, Real.sin_sub]
  simp only [Lop]
  rw [h1, h2]
  ring

/-- Size of the residual of `φ¹`: `|Lh φ¹_k| ≤ |2cosθ' - 2cosθ|/h`, since `|cos| ≤ 1`. -/
lemma abs_Lh_cos_pert (h θ θ' : ℝ) (hh : 0 < h) (k : ℤ) :
    |Lh h (fun _ => 1) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.cos (i * θ')) k|
      ≤ |2 * Real.cos θ' - 2 * Real.cos θ| / h := by
  unfold Lh
  rw [Lop_cos_pert, abs_mul, abs_mul, abs_inv, abs_of_pos hh, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    (inv_nonneg.mpr hh.le)

/-- Size of the residual of `φ²`: `|Lh φ²_k| ≤ |2cosθ' - 2cosθ|/h`, since `|sin| ≤ 1`. -/
lemma abs_Lh_sin_pert (h θ θ' : ℝ) (hh : 0 < h) (k : ℤ) :
    |Lh h (fun _ => 1) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.sin (i * θ')) k|
      ≤ |2 * Real.cos θ' - 2 * Real.cos θ| / h := by
  unfold Lh
  rw [Lop_sin_pert, abs_mul, abs_mul, abs_inv, abs_of_pos hh, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
    (inv_nonneg.mpr hh.le)

/-- The exact solution `ψ_j = cos(jθ) + ((cosθ' - cosθ)/sinθ) sin(jθ)` of the recurrence
`ψ_{j+1} + ψ_{j-1} = 2cosθ ψ_j`, with the seed `ψ_0 = 1 = φ¹_0`, `ψ_1 = cosθ' = φ¹_1`. -/
noncomputable def pertSol (θ θ' : ℝ) (j : ℤ) : ℝ :=
  Real.cos (j * θ) + ((Real.cos θ' - Real.cos θ) / Real.sin θ) * Real.sin (j * θ)

/-- The seed `ψ_1 = cosθ' = φ¹_1`. -/
lemma pertSol_one (θ θ' : ℝ) (hθ : Real.sin θ ≠ 0) : pertSol θ θ' 1 = Real.cos θ' := by
  have hc : (Real.cos θ' - Real.cos θ) / Real.sin θ * Real.sin θ = Real.cos θ' - Real.cos θ :=
    div_mul_cancel₀ _ hθ
  simp only [pertSol, Int.cast_one, one_mul]
  linear_combination hc

/-- `pertSol` solves the recurrence: `Lop (pertSol) k = 0`, i.e. `ψ_{k+1} + ψ_{k-1} - 2cosθ ψ_k = 0`. -/
lemma Lop_pertSol (θ θ' : ℝ) (k : ℤ) :
    Lop (fun _ => 1) (fun _ => 2 * Real.cos θ) (pertSol θ θ') k = 0 := by
  have h1 := (cos_sin_solutions θ).1 k
  have h2 := (cos_sin_solutions θ).2.1 k
  simp only [Lop] at h1 h2 ⊢
  simp only [pertSol]
  linear_combination h1 + ((Real.cos θ' - Real.cos θ) / Real.sin θ) * h2

lemma Lh_pertSol (h θ θ' : ℝ) (k : ℤ) :
    Lh h (fun _ => 1) (fun _ => 2 * Real.cos θ) (pertSol θ θ') k = 0 := by
  unfold Lh
  rw [Lop_pertSol, mul_zero]

/-- **Perturbed instance of `volterra_single_patch`.** The comparison pair `φ¹_j = cos(jθ')`, `φ²_j = sin(jθ')` for
`A = 1`, `Q = 2cosθ` (residual `ε = |2cosθ' - 2cosθ|/h`, so `ε > 0` when `cosθ' ≠ cosθ`), with `W = M = ρ = 1`,
`K = C_E = c₋ = 1`, `ω = |sinθ'|`, and the exact solution `ψ = pertSol θ θ'` (so `ψ_0 = φ¹_0`, `ψ_1 = φ¹_1`).  The
smallness `C ε Θ ≤ 1` is the hypothesis `hsmall`.  The conclusion bounds the error `ψ_j - φ¹_j`, which is non-zero
for `cosθ' ≠ cosθ` (see `volterra_instance_perturbed_nontrivial`). -/
theorem volterra_instance_perturbed (h θ θ' : ℝ) (N : ℤ) (hh : 0 < h) (hN : 1 ≤ N)
    (hθ : Real.sin θ ≠ 0) (hθ' : Real.sin θ' ≠ 0)
    (hsmall : volterraC 1 1 1 * (|2 * Real.cos θ' - 2 * Real.cos θ| / h
      * volterraTheta h |Real.sin θ'| N (fun _ => 1) (fun _ => 1)) ≤ 1) :
    ∀ j ∈ Icc 0 N, |pertSol θ θ' j - Real.cos (j * θ')|
      ≤ volterraC 1 1 1 * (|2 * Real.cos θ' - 2 * Real.cos θ| / h
          * volterraTheta h |Real.sin θ'| N (fun _ => 1) (fun _ => 1)) := by
  have key := volterra_single_patch h |Real.sin θ'| 1 1 1 (|2 * Real.cos θ' - 2 * Real.cos θ| / h) N
    (fun _ => 1) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.cos (i * θ')) (fun i : ℤ => Real.sin (i * θ'))
    (pertSol θ θ') (fun _ => 1) (fun _ => 1) (fun _ => 1) hh (abs_pos.mpr hθ') one_pos hN
    (div_nonneg (abs_nonneg _) hh.le)
    (fun j _ => by rw [(cos_sin_solutions θ').2.2 j, abs_neg, one_mul])
    (fun _ _ => one_pos) (fun _ _ => one_pos)
    (fun _ _ j _ _ => by norm_num)
    (fun j _ => by simp only [mul_one]; exact Real.abs_cos_le_one _)
    (fun j _ => by simp only [inv_one, mul_one]; exact Real.abs_sin_le_one _)
    (fun _ => zero_le_one)
    (fun k _ => by simp only [mul_one]; exact abs_Lh_cos_pert h θ θ' hh k)
    (fun k _ => by simp only [mul_one, inv_one]; exact abs_Lh_sin_pert h θ θ' hh k)
    (by simp [pertSol])
    (by rw [pertSol_one θ θ' hθ]; simp)
    (fun k _ => Lh_pertSol h θ θ' k) hsmall
  intro j hj
  simpa only [mul_one] using key j hj

/-- `C = volterraC 1 1 1 = (1+1)(1+1)/1 = 4`. -/
lemma volterraC_one_one_one : volterraC 1 1 1 = 4 := by
  norm_num [volterraC]

/-- With `ρ = M = 1` the modulus sum is `Θ = (h/ω)(N-1)` (the equation sites `1, …, N-1`). -/
lemma volterraTheta_const (h ω : ℝ) (N : ℤ) (hN : 1 ≤ N) :
    volterraTheta h ω N (fun _ => 1) (fun _ => 1) = h / ω * ((N : ℝ) - 1) := by
  have h6 : (((N - 1).toNat : ℕ) : ℤ) = N - 1 := Int.toNat_of_nonneg (by omega)
  have hcard : ((Icc 1 (N - 1)).card : ℝ) = (N : ℝ) - 1 := by
    rw [Int.card_Icc]
    have h3 : N - 1 + 1 - 1 = N - 1 := by ring
    rw [h3]
    exact_mod_cast h6
  unfold volterraTheta
  simp only [one_pow, mul_one, Finset.sum_const, nsmul_eq_mul, hcard]

/-- **Closed form of the perturbed instance.** Since `ε Θ = |2cosθ' - 2cosθ| (N-1)/|sinθ'|` does not depend on `h`, the
smallness is an explicit condition on `θ, θ', N` and the bound is `4 |2cosθ' - 2cosθ| (N-1)/|sinθ'|`. -/
theorem volterra_instance_perturbed_closed (h θ θ' : ℝ) (N : ℤ) (hh : 0 < h) (hN : 1 ≤ N)
    (hθ : Real.sin θ ≠ 0) (hθ' : Real.sin θ' ≠ 0)
    (hsmall : 4 * (|2 * Real.cos θ' - 2 * Real.cos θ| * ((N : ℝ) - 1) / |Real.sin θ'|) ≤ 1) :
    ∀ j ∈ Icc 0 N, |pertSol θ θ' j - Real.cos (j * θ')|
      ≤ 4 * (|2 * Real.cos θ' - 2 * Real.cos θ| * ((N : ℝ) - 1) / |Real.sin θ'|) := by
  have hh' : h ≠ 0 := hh.ne'
  have hs0 : |Real.sin θ'| ≠ 0 := abs_ne_zero.mpr hθ'
  have hεΘ : |2 * Real.cos θ' - 2 * Real.cos θ| / h
      * volterraTheta h |Real.sin θ'| N (fun _ => 1) (fun _ => 1)
      = |2 * Real.cos θ' - 2 * Real.cos θ| * ((N : ℝ) - 1) / |Real.sin θ'| := by
    rw [volterraTheta_const h |Real.sin θ'| N hN]
    field_simp
  have hs : volterraC 1 1 1 * (|2 * Real.cos θ' - 2 * Real.cos θ| / h
      * volterraTheta h |Real.sin θ'| N (fun _ => 1) (fun _ => 1)) ≤ 1 := by
    rw [hεΘ, volterraC_one_one_one]; linarith
  intro j hj
  have key := volterra_instance_perturbed h θ θ' N hh hN hθ hθ' hs j hj
  rw [hεΘ, volterraC_one_one_one] at key
  linarith

/-- The error at the site `j = 2`: `ψ_2 - cos(2θ') = 2cosθ'(cosθ - cosθ')` (since `ψ_2 = 2cosθ cosθ' - 1`). -/
lemma pertSol_two (θ θ' : ℝ) (hθ : Real.sin θ ≠ 0) :
    pertSol θ θ' 2 - Real.cos (2 * θ') = 2 * Real.cos θ' * (Real.cos θ - Real.cos θ') := by
  have hc : (Real.cos θ' - Real.cos θ) / Real.sin θ * Real.sin θ = Real.cos θ' - Real.cos θ :=
    div_mul_cancel₀ _ hθ
  simp only [pertSol]
  push_cast
  rw [Real.cos_two_mul, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (2 * Real.cos θ) * hc

/-- Non-triviality: if `cosθ' ≠ 0` and `cosθ ≠ cosθ'`, then `ψ_2 ≠ φ¹_2`, so `ψ ≠ φ¹`. -/
lemma pertSol_two_ne (θ θ' : ℝ) (hθ : Real.sin θ ≠ 0) (h0 : Real.cos θ' ≠ 0)
    (hne : Real.cos θ ≠ Real.cos θ') :
    pertSol θ θ' 2 ≠ Real.cos (2 * θ') := by
  intro heq
  have h2 := pertSol_two θ θ' hθ
  rw [heq, sub_self] at h2
  exact mul_ne_zero (mul_ne_zero two_ne_zero h0) (sub_ne_zero.mpr hne) h2.symm

/-- The error at the site `j = 3` when `cosθ' = 0`: `ψ_3 - cos(3θ') = -2cosθ`, from the recurrence with `ψ_1 = 0`,
`ψ_2 = -1` and `cos 3θ' = 0`. -/
lemma pertSol_three_of_cos_zero (θ θ' : ℝ) (hθ : Real.sin θ ≠ 0) (h0 : Real.cos θ' = 0) :
    pertSol θ θ' 3 - Real.cos (3 * θ') = -2 * Real.cos θ := by
  have hrec : pertSol θ θ' 3 + pertSol θ θ' 1 - 2 * Real.cos θ * pertSol θ θ' 2 = 0 := by
    have h := Lop_pertSol θ θ' 2
    have e3 : ((2 : ℤ) + 1) = 3 := by norm_num
    have e1 : ((2 : ℤ) - 1) = 1 := by norm_num
    simp only [Lop, e3, e1] at h
    linear_combination h
  have hP1 : pertSol θ θ' 1 = 0 := by rw [pertSol_one θ θ' hθ, h0]
  have hP2 : pertSol θ θ' 2 = 2 * Real.cos θ * Real.cos θ' - 1 := by
    have h := pertSol_two θ θ' hθ
    rw [Real.cos_two_mul] at h
    linear_combination h
  rw [h0] at hP2
  rw [Real.cos_three_mul, h0]
  linear_combination hrec - hP1 + 2 * Real.cos θ * hP2

/-- Non-triviality of the perturbed error for every `cosθ ≠ cosθ'`: `ψ_2 ≠ φ¹_2` when `cosθ' ≠ 0`, and `ψ_3 ≠ φ¹_3`
when `cosθ' = 0` (then `cosθ ≠ 0`).  So `ψ ≠ φ¹` as soon as `cosθ ≠ cosθ'`. -/
lemma pertSol_ne_of_cos_ne (θ θ' : ℝ) (hθ : Real.sin θ ≠ 0) (hne : Real.cos θ ≠ Real.cos θ') :
    pertSol θ θ' 2 ≠ Real.cos (2 * θ') ∨ pertSol θ θ' 3 ≠ Real.cos (3 * θ') := by
  by_cases h0 : Real.cos θ' = 0
  · right
    intro heq
    have h3 := pertSol_three_of_cos_zero θ θ' hθ h0
    rw [heq, sub_self] at h3
    exact hne (by linarith)
  · exact Or.inl (pertSol_two_ne θ θ' hθ h0 hne)

/-- **The bound is not trivial.** For `N ≥ 2` and `cosθ ≠ cosθ'` its right-hand side is strictly positive (so it is
not the trivial `0`); for `cosθ' ≠ 0` the error at `j = 2` is non-zero and is bounded by it. -/
theorem volterra_instance_perturbed_nontrivial (h θ θ' : ℝ) (N : ℤ) (hh : 0 < h) (hN : 2 ≤ N)
    (hθ : Real.sin θ ≠ 0) (hθ' : Real.sin θ' ≠ 0) (h0 : Real.cos θ' ≠ 0) (hne : Real.cos θ ≠ Real.cos θ')
    (hsmall : 4 * (|2 * Real.cos θ' - 2 * Real.cos θ| * ((N : ℝ) - 1) / |Real.sin θ'|) ≤ 1) :
    0 < 4 * (|2 * Real.cos θ' - 2 * Real.cos θ| * ((N : ℝ) - 1) / |Real.sin θ'|) ∧
    pertSol θ θ' 2 ≠ Real.cos (2 * θ') ∧
    |pertSol θ θ' 2 - Real.cos (2 * θ')|
      ≤ 4 * (|2 * Real.cos θ' - 2 * Real.cos θ| * ((N : ℝ) - 1) / |Real.sin θ'|) := by
  have ha : 0 < |2 * Real.cos θ' - 2 * Real.cos θ| :=
    abs_pos.mpr (by intro h'; apply hne; linarith)
  have hN' : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hpos : 0 < 4 * (|2 * Real.cos θ' - 2 * Real.cos θ| * ((N : ℝ) - 1) / |Real.sin θ'|) :=
    mul_pos (by norm_num) (div_pos (mul_pos ha hN') (abs_pos.mpr hθ'))
  have hmem : (2 : ℤ) ∈ Icc 0 N := Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
  have hb := volterra_instance_perturbed_closed h θ θ' N hh (by omega) hθ hθ' hsmall 2 hmem
  have e2 : ((2 : ℤ) : ℝ) = 2 := by norm_num
  rw [e2] at hb
  exact ⟨hpos, pertSol_two_ne θ θ' hθ h0 hne, hb⟩

-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JE.flux_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.flux_sum

/-- info: 'FormalResearch.JE.volterra_single_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_single_patch

/-- info: 'FormalResearch.JE.volterra_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_instance

/-- info: 'FormalResearch.JE.volterra_instance_perturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_instance_perturbed

/-- info: 'FormalResearch.JE.volterra_instance_perturbed_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_instance_perturbed_closed

/-- info: 'FormalResearch.JE.volterra_instance_perturbed_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_instance_perturbed_nontrivial

/-- info: 'FormalResearch.JE.pertSol_ne_of_cos_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.pertSol_ne_of_cos_ne


end FormalResearch.JE

end
