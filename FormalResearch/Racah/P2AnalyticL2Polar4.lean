module

public import FormalResearch.Racah.P2AnalyticL2Polar3

/-!
# `eq:SNpolar`, whitening and the headline `prop:betabinomialpolar` (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:betabinomialpolar`
(`eq:singularvaluesgeneral`, `eq:SNpolar`, `eq:physicalsingularvalues`), Appendix `app:beta-polar`
(`eq:physicalGaugeModes`, the whitening formulas `Λ_{N,M}`, `eq:SNwhitening`).

## Dictionary

| paper | Lean |
|---|---|
| `L²(ν_H)`, `𝒫_D = span{J_0..J_D}` | `L2nu`, `PD`, `JV` (orthonormal basis `J_n`) |
| `ℓ²(p_D)`, `H_n` | `EuclideanSpace ℝ (Fin (D+1))` via `q ↦ √p_D q`, `HB` |
| `T_D = C_D|_{𝒫_D}`, `s_n` | `TD`, `sing` |
| `U_D = T_D (T_D^*T_D)^{-1/2}` | `UD = Polar.polarFactor TD` |
| `G_c`, `G_d` | `Gc`, `Gd` |
| `S_N` | `SNmap M σ N (uN M σ)` |

## Theorems

`prop_betabinomialpolar` collects: `T_D J_n = s_n H_n`, `s_n > 0`, `T_D` invertible, `U_D` unitary with
`U_D J_n = H_n`, `S_N G_c = G_d U_D` (`eq:SNpolar`) and `s_n² = ∏ (N-r)/(N+r)`
(`eq:physicalsingularvalues`).  The whitening statements are `TdagT_JV`, `sing_sq_gamma`,
`CtildeN_JV`, `eq_SNwhitening` (`C̃_N = G_d T_D G_c^{-1}`, `C̃_N^*C̃_N = Λ_{N,M}(𝖧₀)`,
`S_N = C̃_N Λ^{-1/2}`, stated spectrally on the basis `J_n ↔ u_L`).
-/

@[expose] public section

namespace FormalResearch.Racah

open MeasureTheory Polar FormalResearch.Special FormalResearch.Wigner
open scoped InnerProductSpace

/-! ### Whitening -/

/-- `T_D^* T_D J_n = s_n² J_n` (`C_D^* C_D` is diagonal on the Jacobi modes). -/
theorem TdagT_JV (α β D : ℕ) (n : Fin (D + 1)) :
    LinearMap.adjoint (TD α β D) (TD α β D (JV α β D n)) = (sing α β D n ^ 2) • JV α β D n := by
  rw [TD_JV, map_smul, adjoint_apply_basis (JV α β D) (HB α β D) (TD_JV α β D) n, smul_smul, sq]

/-- `(T_D^*T_D)^{1/2} J_n = s_n J_n`. -/
theorem polarRoot_JV (α β D : ℕ) (n : Fin (D + 1)) :
    polarRoot (TD α β D) (JV α β D n) = sing α β D n • JV α β D n := by
  have hU := (UD_unitary α β D).2.1
  apply hU
  have h1 : UD α β D (polarRoot (TD α β D) (JV α β D n)) = TD α β D (JV α β D n) :=
    polarFactor_root _ _ _
  rw [h1, TD_JV, map_smul, UD_JV]

/-- The ratio `Γ(a)Γ(b)/(Γ(a-n)Γ(b+n)) = ∏_{k<n} (a-1-k)/(b+k)` for `n < a`, `b > 0`. -/
lemma gamma_ratio (a b : ℝ) (hb : 0 < b) (n : ℕ) (hn : (n : ℝ) < a) :
    Real.Gamma a * Real.Gamma b / (Real.Gamma (a - n) * Real.Gamma (b + n)) =
      ∏ k ∈ Finset.range n, ((a - 1 - k) / (b + k)) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, add_zero, Finset.range_zero, Finset.prod_empty]
    exact div_self (mul_pos (Real.Gamma_pos_of_pos (by simpa using hn))
      (Real.Gamma_pos_of_pos hb)).ne'
  | succ n ih =>
    have hn' : (n : ℝ) < a := by push_cast at hn; linarith
    have hs : 0 < a - n - 1 := by push_cast at hn; linarith
    rw [Finset.prod_range_succ, ← ih hn']
    have h1 : Real.Gamma (a - n) = (a - n - 1) * Real.Gamma (a - n - 1) := by
      have := Real.Gamma_add_one (s := a - n - 1) hs.ne'
      rw [show a - n - 1 + 1 = a - n by ring] at this
      exact this
    have hbn : 0 < b + n := by positivity
    have h2 : Real.Gamma (b + n + 1) = (b + n) * Real.Gamma (b + n) := by
      have := Real.Gamma_add_one (s := b + n) hbn.ne'
      exact this
    have g1 : 0 < Real.Gamma (a - n - 1) := Real.Gamma_pos_of_pos hs
    have g2 : 0 < Real.Gamma (b + n) := Real.Gamma_pos_of_pos hbn
    have e1 : a - ((n + 1 : ℕ) : ℝ) = a - n - 1 := by push_cast; ring
    have e2 : b + ((n + 1 : ℕ) : ℝ) = b + n + 1 := by push_cast; ring
    rw [e1, e2, h1, h2]
    have g3 := Real.Gamma_pos_of_pos (show 0 < a - n by linarith)
    rw [h1] at g3
    field_simp
    ring

/-- **Whitening weight** (`app:beta-polar`): `s_{L-M}² = Γ(N-M)Γ(N+M+1)/(Γ(N-L)Γ(N+L+1))`,
`L = M + n`, i.e. `Λ_{N,M}(L(L+1))`. -/
theorem sing_sq_gamma {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n : Fin (D + 1)) :
    sing α β D n ^ 2 =
      Real.Gamma ((N : ℝ) - M) * Real.Gamma ((N : ℝ) + M + 1) /
        (Real.Gamma ((N : ℝ) - ((M : ℝ) + (n : ℕ))) * Real.Gamma ((N : ℝ) + ((M : ℝ) + (n : ℕ)) + 1)) := by
  have hr := chamber_real hα hβ hD
  have hM0 : (0 : ℝ) ≤ M := by rw [hr.1]; positivity
  have hND : (N : ℝ) - M = (D : ℝ) + 1 := by rw [hr.2.2, hr.1]; ring
  have hnD : ((n : ℕ) : ℝ) < (N : ℝ) - M := by
    rw [hND]; have : (n : ℕ) ≤ D := by omega
    have : ((n : ℕ) : ℝ) ≤ D := by exact_mod_cast this
    linarith
  have hpos : (0 : ℝ) < (N : ℝ) + M + 1 := by
    have := hr.2.2
    have h3 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    linarith
  have h := gamma_ratio ((N : ℝ) - M) ((N : ℝ) + M + 1) hpos n hnD
  rw [sing_sq_physical hα hβ hD n]
  rw [show (N : ℝ) - M - n = (N : ℝ) - ((M : ℝ) + n) by ring,
    show (N : ℝ) + M + 1 + n = (N : ℝ) + ((M : ℝ) + n) + 1 by ring] at h
  rw [h]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1 <;> ring

/-- **`C̃_N = G_d T_D G_c^{-1}`** acts as `C̃_N u_L = s_{L-M} v_L` (`u_L = (-1)^α G_c J_n`). -/
theorem CtildeN_JV {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n : Fin (D + 1)) :
    ((-1 : ℝ) ^ α) • Gd N D (D + 1) (TD α β D (JV α β D n)) =
      sing α β D n • vN M σ N (K := D + 1) n := by
  rw [TD_JV, map_smul, vN_eq_Gd hα hβ hD, smul_smul, smul_smul, mul_comm]

/-- **`eq:SNwhitening`**: `S_N = C̃_N Λ_{N,M}(𝖧₀)^{-1/2}`, i.e. `S_N G_c p = G_d T_D (T_D^*T_D)^{-1/2} p`
for `p ∈ P_D` (`Λ^{-1/2}` is `(T_D^*T_D)^{-1/2}` under `G_c`: it acts as `s_n^{-1}` on `J_n`). -/
theorem eq_SNwhitening {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (p : PD α β D) :
    SNmap M σ N (uN M σ : Fin (D + 1) → L2m11) (Gc α β D p) =
      Gd N D (D + 1) (TD α β D ((rootEquiv (TD α β D) (TD_injective α β D)).symm p)) := by
  rw [eq_SNpolar hα hβ hD]
  rfl

/-! ### The headline -/

/-- **`prop:betabinomialpolar`** (`eq:singularvaluesgeneral`, `eq:SNpolar`,
`eq:physicalsingularvalues`), in the chamber `M ≥ |σ|` (`α = M-σ`, `β = M+σ`, `D = N-M-1` natural):

1. `T_D J_n = s_n H_n` with `s_n > 0`, so `T_D` is invertible between `P_D` and `ℓ²(p_D)`;
2. the polar factor `U_D = T_D (T_D^*T_D)^{-1/2}` is unitary and `U_D J_n = H_n`;
3. `S_N = G_d U_D G_c^{-1}`, i.e. `S_N G_c p = G_d U_D p` for `p ∈ P_D`, where `G_c : P_D → 𝒱_N`
   is an isometry onto `𝒱_N = span{u_L}`;
4. `s_{L-M}² = ∏_{r=M+1}^{L} (N-r)/(N+r)`, `L = M + n`. -/
theorem prop_betabinomialpolar {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) :
    (∀ n : Fin (D + 1), TD α β D (JV α β D n) = sing α β D n • HB α β D n ∧ 0 < sing α β D n) ∧
    Function.Bijective (TD α β D) ∧
    ((∀ x y, ⟪UD α β D x, UD α β D y⟫_ℝ = ⟪x, y⟫_ℝ) ∧ Function.Bijective (UD α β D)) ∧
    (∀ n : Fin (D + 1), UD α β D (JV α β D n) = HB α β D n) ∧
    ((∀ p q, ⟪Gc α β D p, Gc α β D q⟫_ℝ = ⟪p, q⟫_ℝ) ∧
      LinearMap.range (Gc α β D) =
        Submodule.span ℝ (Set.range (uN M σ : Fin (D + 1) → L2m11))) ∧
    (∀ p : PD α β D, SNmap M σ N (uN M σ : Fin (D + 1) → L2m11) (Gc α β D p) =
      Gd N D (D + 1) (UD α β D p)) ∧
    (∀ n : Fin (D + 1), sing α β D n ^ 2 = ∏ k ∈ Finset.range n,
      (((N : ℝ) - ((M : ℝ) + k + 1)) / ((N : ℝ) + ((M : ℝ) + k + 1)))) :=
  ⟨fun n => ⟨TD_JV α β D n, sing_pos α β D n⟩, TD_bijective α β D, UD_unitary α β D,
    UD_JV α β D, ⟨Gc_inner hα hβ hD, Gc_range hα hβ hD⟩, eq_SNpolar hα hβ hD,
    sing_sq_physical hα hβ hD⟩

/-- info: 'FormalResearch.Racah.TdagT_JV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TdagT_JV

/-- info: 'FormalResearch.Racah.polarRoot_JV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarRoot_JV

/-- info: 'FormalResearch.Racah.sing_sq_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sing_sq_gamma

/-- info: 'FormalResearch.Racah.CtildeN_JV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CtildeN_JV

/-- info: 'FormalResearch.Racah.eq_SNwhitening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_SNwhitening

/-- info: 'FormalResearch.Racah.prop_betabinomialpolar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prop_betabinomialpolar

end FormalResearch.Racah
