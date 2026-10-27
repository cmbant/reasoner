import Mathlib
import FormalResearch.FrameFree.Helstrom
import FormalResearch.FrameFree.HelstromTwirlBound

/-!
# `thm:window`: the Chernoff-side lower bound `ξ_inv ≥ ½ C_K`

Namespace `FormalResearch.FrameFree.Helstrom`.

* `kron_mul`, `rotK_mul`: the frames `rotK k u`, `u ∈ SU(2)^n`, are closed under products.
* `symSpace n k`: the subspace of `(ℂ^{2^n})^{⊗k}` of vectors constant on words of the same type;
  every `φ^{⊗k}` lies in it (`copies_mem_symSpace`) and `dim ≤ (k+1)^{2^n}` (`finrank_symSpace_le`).
* `Pe_le_sqrt`: `P_e(k) ≤ ½ √((k+1)^{2^n} F_K(ψ)^k)`, from the twirled Powers-Stormer bound
  (`HelstromTwirlBound.twirl_helstrom`) with `G = {rotK k u}` and `W = symSpace n k`.
* `eventually_half_CK_le`, `half_CK_le_liminf`: `liminf_k -(1/k) log P_e(k) ≥ ½ C_K(ψ)`.
* `window`: both halves of `thm:window` (the upper half is `Helstrom.limsup_neg_log_Pe_le_CK`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexConjugate Matrix BigOperators
open Matrix FormalResearch.FrameFree.NQubit
open scoped ComplexOrder InnerProductSpace

namespace FormalResearch.FrameFree.Helstrom

section kron
variable {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α] [DecidableEq α]

theorem kron_mul (M N : I → Matrix α α ℂ) : kron M * kron N = kron (fun i => M i * N i) := by
  ext x z
  simp only [Matrix.mul_apply, kron]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_prod_pi (fun i b => M i (x i) b * N i b (z i))]

end kron

theorem rotK_mul {n : ℕ} (k : ℕ) (u v : Fin n → Op1) :
    rotK k u * rotK k v = rotK k (fun i => u i * v i) := by
  unfold rotK
  rw [kron_mul]
  congr 1
  funext _
  exact kron_mul u v

/-! ### The symmetric (type-constant) subspace and its dimension -/

/-- The type of a word of `k` copies: how often each local basis state occurs. -/
def cnt {n : ℕ} (k : ℕ) (i : Copies n k) : (Fin n → Fin 2) → Fin (k + 1) := fun q =>
  ⟨(Finset.univ.filter fun t : Fin k => i t = q).card, by
    have := Finset.card_le_univ (Finset.univ.filter fun t : Fin k => i t = q)
    simp at this ⊢; omega⟩

/-- Vectors that depend on a word only through its type. -/
def symSpace (n k : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Copies n k)) where
  carrier := {w | ∀ i j : Copies n k, cnt k i = cnt k j → w i = w j}
  add_mem' := by
    intro a b ha hb i j h
    simp [ha i j h, hb i j h]
  zero_mem' := by intro i j h; simp
  smul_mem' := by
    intro c a ha i j h
    simp [ha i j h]

theorem mem_symSpace {n k : ℕ} (c : Copies n k → ℂ) :
    WithLp.toLp 2 c ∈ symSpace n k ↔ ∀ i j, cnt k i = cnt k j → c i = c j := Iff.rfl

theorem copies_eq_prod_pow {n : ℕ} (k : ℕ) (φ : Ψ n) (i : Copies n k) :
    copies k φ i = ∏ q : Fin n → Fin 2, φ q ^ (Finset.univ.filter fun t : Fin k => i t = q).card := by
  unfold copies
  rw [← Finset.prod_fiberwise Finset.univ i (fun t => φ (i t))]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Finset.prod_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.prod_const]

theorem copies_mem_symSpace {n : ℕ} (k : ℕ) (φ : Ψ n) :
    WithLp.toLp 2 (copies k φ) ∈ symSpace n k := by
  rw [mem_symSpace]
  intro i j h
  rw [copies_eq_prod_pow, copies_eq_prod_pow]
  refine Finset.prod_congr rfl fun q _ => ?_
  have := congrArg Fin.val (congrFun h q)
  simp only [cnt] at this
  rw [this]

/-- Dimension bound for the type-constant subspace: at most `(k+1)^(2^n)`. -/
theorem finrank_symSpace_le (n k : ℕ) : Module.finrank ℂ (symSpace n k) ≤ (k + 1) ^ (2 ^ n) := by
  classical
  let T := (Fin n → Fin 2) → Fin (k + 1)
  let Lg : (T → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Copies n k) :=
    (WithLp.linearEquiv 2 ℂ (Copies n k → ℂ)).symm.toLinearMap ∘ₗ LinearMap.funLeft ℂ ℂ (cnt k)
  have hle : symSpace n k ≤ LinearMap.range Lg := by
    intro w hw
    have hw' : ∀ i j : Copies n k, cnt k i = cnt k j → w i = w j := hw
    refine ⟨fun t => if h : ∃ i, cnt k i = t then w h.choose else 0, ?_⟩
    ext i
    have hex : ∃ i', cnt k i' = cnt k i := ⟨i, rfl⟩
    show (if h : ∃ i', cnt k i' = cnt k i then w h.choose else 0) = w i
    rw [dif_pos hex]
    exact hw' _ _ hex.choose_spec
  calc Module.finrank ℂ (symSpace n k) ≤ Module.finrank ℂ (LinearMap.range Lg) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ (T → ℂ) := LinearMap.finrank_range_le Lg
    _ = (k + 1) ^ (2 ^ n) := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp [T]

/-- **Upper bound on the frame-free error** (the Haar-free Powers-Stormer bound):
`P_e(k) ≤ ½ √((k+1)^{2^n} F_K(ψ)^k)`. -/
theorem Pe_le_sqrt {n : ℕ} (ψ : Ψ n) (k : ℕ) :
    Pe k ψ ≤ Real.sqrt (((k : ℝ) + 1) ^ (2 ^ n) * FKΘ ψ ^ k) / 2 := by
  classical
  let G : Set (Matrix (Copies n k) (Copies n k) ℂ) :=
    {U | ∃ u : Fin n → Op1, (∀ i, SU2 (u i)) ∧ U = rotK k u}
  have hG1 : ∀ U ∈ G, Uᴴ * U = 1 := by
    rintro U ⟨u, hu, rfl⟩; exact rotK_unitary k u hu
  have hmul : ∀ U ∈ G, ∀ V ∈ G, U * V ∈ G := by
    rintro U ⟨u, hu, rfl⟩ V ⟨v, hv, rfl⟩
    exact ⟨fun i => u i * v i, fun i => SU2_mul (hu i) (hv i), rotK_mul k u v⟩
  have hne : G.Nonempty := ⟨rotK k (fun _ => 1), _, fun _ => SU2_one, rfl⟩
  have ha : ∀ U ∈ G, WithLp.toLp 2 (U *ᵥ copies k ψ) ∈ symSpace n k := by
    rintro U ⟨u, hu, rfl⟩
    rw [← copies_rot]; exact copies_mem_symSpace k _
  have hb : ∀ U ∈ G, WithLp.toLp 2 (U *ᵥ copies k (Θ ψ)) ∈ symSpace n k := by
    rintro U ⟨u, hu, rfl⟩
    rw [← copies_rot]; exact copies_mem_symSpace k _
  have hF : ∀ U ∈ G, Complex.normSq (star (copies k ψ) ⬝ᵥ (U *ᵥ copies k (Θ ψ))) ≤ FKΘ ψ ^ k := by
    rintro U ⟨u, hu, rfl⟩
    rw [← copies_rot, star_copies_dot, ← ip_eq_dot, map_pow]
    exact pow_le_pow_left₀ (Complex.normSq_nonneg _) (le_FK ψ (Θ ψ) u hu) k
  obtain ⟨E, hE, hcomm, herr⟩ := twirl_helstrom G hG1 hmul hne (symSpace n k) (copies k ψ)
    (copies k (Θ ψ)) ha hb (FKΘ ψ ^ k) hF
  have hbdd : BddBelow {r | ∃ E, IsInvEffect (n := n) k E ∧ r = err E (copies k ψ) (copies k (Θ ψ))} :=
    ⟨0, by rintro r ⟨E, hE, rfl⟩; exact err_nonneg hE.1 _ _⟩
  refine (csInf_le hbdd ⟨E, ⟨hE, fun u hu => hcomm _ ⟨u, hu, rfl⟩⟩, rfl⟩).trans (herr.trans ?_)
  have hF0 : 0 ≤ FKΘ ψ := (Complex.normSq_nonneg _).trans (le_FKΘ_one ψ)
  have hdim : (Module.finrank ℂ (symSpace n k) : ℝ) ≤ ((k : ℝ) + 1) ^ (2 ^ n) := by
    exact_mod_cast finrank_symSpace_le n k
  gcongr

/-- Eventual form of `liminf_k -(1/k) log P_e(k) ≥ ½ C_K`: for every `c < C_K(ψ)/2`, eventually
`c ≤ -(1/k) log P_e(k)`. -/
theorem eventually_half_CK_le {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) {c : ℝ} (hc : c < CK ψ / 2) :
    ∀ᶠ k : ℕ in Filter.atTop, c ≤ -(1 / (k : ℝ)) * Real.log (Pe k ψ) := by
  have hpos := FKΘ_pos ψ hψ
  set δ := (CK ψ / 2 - c) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hD : (0 : ℝ) < 2 ^ n := by positivity
  have hT : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlittle : ∀ᶠ k : ℕ in Filter.atTop, Real.log ((k : ℝ) + 1) ≤ (δ / 2 ^ n) * ((k : ℝ) + 1) := by
    have h := (Real.isLittleO_log_id_atTop.comp_tendsto hT).bound (c := δ / 2 ^ n) (by positivity)
    filter_upwards [h] with k hk
    have hk' : ‖Real.log ((k : ℝ) + 1)‖ ≤ δ / 2 ^ n * ‖((k : ℝ) + 1)‖ := hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)] at hk'
    exact (le_abs_self _).trans hk'
  filter_upwards [hlittle, Filter.eventually_ge_atTop 1] with k hk hk1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hPe := Pe_le_sqrt ψ k
  have hPpos := Pe_pos ψ hψ k
  have hX : 0 < ((k : ℝ) + 1) ^ (2 ^ n) * FKΘ ψ ^ k := by positivity
  have hlog : Real.log (Pe k ψ) ≤
      (((2 ^ n : ℕ) : ℝ) * Real.log ((k : ℝ) + 1) + k * Real.log (FKΘ ψ)) / 2 - Real.log 2 := by
    have := Real.log_le_log hPpos hPe
    rw [Real.log_div (Real.sqrt_pos.2 hX).ne' two_ne_zero, Real.log_sqrt hX.le,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
    exact this
  have hcast : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by push_cast; ring
  rw [hcast] at hlog
  have ht : 0 < 1 / (k : ℝ) := by positivity
  have htk : 1 / (k : ℝ) * k = 1 := by field_simp
  have h1 : -(1 / (k : ℝ)) * Real.log (Pe k ψ) ≥
      -(1 / (k : ℝ)) * (((2 : ℝ) ^ n * Real.log ((k : ℝ) + 1) + k * Real.log (FKΘ ψ)) / 2 - Real.log 2) :=
    mul_le_mul_of_nonpos_left hlog (by linarith)
  have hDL : (2 : ℝ) ^ n * Real.log ((k : ℝ) + 1) ≤ δ * ((k : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hk hD.le
    calc (2 : ℝ) ^ n * Real.log ((k : ℝ) + 1) ≤ 2 ^ n * (δ / 2 ^ n * ((k : ℝ) + 1)) := this
      _ = δ * ((k : ℝ) + 1) := by field_simp
  have hDL2 : (2 : ℝ) ^ n * Real.log ((k : ℝ) + 1) ≤ 2 * δ * k := by nlinarith
  have h2 : 1 / (k : ℝ) * ((2 : ℝ) ^ n * Real.log ((k : ℝ) + 1)) ≤ 2 * δ := by
    calc 1 / (k : ℝ) * ((2 : ℝ) ^ n * Real.log ((k : ℝ) + 1)) ≤ 1 / (k : ℝ) * (2 * δ * k) :=
          mul_le_mul_of_nonneg_left hDL2 ht.le
      _ = 2 * δ := by rw [mul_comm 2 δ, ← mul_assoc, mul_comm (1 / (k : ℝ)) (δ * 2), mul_assoc, htk, mul_one]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 ≤ 1 / (k : ℝ) * Real.log 2 := by positivity
  have hCK : CK ψ = -Real.log (FKΘ ψ) := rfl
  have e : -(1 / (k : ℝ)) * (((2 : ℝ) ^ n * Real.log ((k : ℝ) + 1) + k * Real.log (FKΘ ψ)) / 2 - Real.log 2)
      = -(1 / (k : ℝ) * ((2 : ℝ) ^ n * Real.log ((k : ℝ) + 1))) / 2
        - (1 / (k : ℝ) * k) * Real.log (FKΘ ψ) / 2 + 1 / (k : ℝ) * Real.log 2 := by ring
  rw [e, htk] at h1
  rw [hCK] at hδ
  linarith

/-- **`thm:window`, lower half: `liminf_k -(1/k) log P_e(k) ≥ ½ C_K(ψ)`** for every unit `ψ`. -/
theorem half_CK_le_liminf {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) :
    CK ψ / 2 ≤ Filter.liminf (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  have hcb : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) :=
    Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (x := CK ψ + 1)
      (eventually_neg_log_Pe_le ψ hψ (by linarith))
  exact Filter.le_liminf_of_le hcb (eventually_half_CK_le ψ hψ hc)

/-- **`thm:window`**: for every unit `ψ`, `½ C_K(ψ) ≤ liminf_k -(1/k) log P_e(k)` and
`limsup_k -(1/k) log P_e(k) ≤ C_K(ψ)`. -/
theorem window {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) :
    CK ψ / 2 ≤ Filter.liminf (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop ∧
    Filter.limsup (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop ≤ CK ψ :=
  ⟨half_CK_le_liminf ψ hψ, limsup_neg_log_Pe_le_CK ψ hψ⟩

end FormalResearch.FrameFree.Helstrom
