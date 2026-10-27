import Mathlib
import FormalResearch.FrameFree.OddWordsArith

/-!
# A real `sl₂`-type structure theory for the odd-word count (Paper P, `prop:oddwords`)

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`Sl2Data n V` is the abstract shadow of the total-spin algebra on `n` spins: a finite-dimensional
real inner product space `V` of dimension `2^n` with a lowering operator `L` whose adjoint is the
raising operator `R`, `H = [R, L]` obeying `[H, L] = -2 L`, and with `H`-eigenspaces
`W_m = ker (H - (n - 2m))` of dimension `C(n, m)` that span `V`.  Everything below is elementary
linear algebra (positivity of `⟨v, R L v⟩` and `⟨v, L R v⟩`): this file proves

* `L`, `R` shift the weight spaces `W_m` (`L_mem_W`, `R_mem_W`), `R W_0 = 0`, `L W_n = 0`;
* `L` is injective on `W_m` for `n - 2m > 0` and `R` is injective for `n - 2m < 0`
  (`L_injOn`, `R_injOn`);
* `W_m ≤ HW_m ⊔ L W_{m-1}` for `m ≥ 1`, where `HW_k = W_k ⊓ ker R` (`W_le_HW_sup`);
* the string formula `R L^{a+1} h = (a+1)(n-2k-a) L^a h` for `h ∈ HW_k` (`R_L_pow_succ`) and
  `L^{n-2k+1} h = 0` (`L_pow_top`);
* `V` is spanned by the strings `L^a h`, `h ∈ HW_k`, `k ≤ n/2`, `a ≤ n-2k` (`strings_top`), and
  `dim HW_k = C(n,k) - C(n,k-1)` for `k ≤ n/2` (`finrank_HW`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Module LinearMap

namespace FormalResearch.FrameFree.OddWords

/-- The abstract total-spin data: see the module docstring. -/
structure Sl2Data (n : ℕ) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] where
  L : V →ₗ[ℝ] V
  hHL : ((adjoint L * L - L * adjoint L) * L - L * (adjoint L * L - L * adjoint L))
    = (-2 : ℝ) • L
  finrank_V : finrank ℝ V = 2 ^ n
  hspec : ∀ μ : ℝ, (∀ m ≤ n, μ ≠ (n : ℝ) - 2 * m) → ∀ v : V,
    (adjoint L * L - L * adjoint L) v = μ • v → v = 0
  decomp : ∀ v : V, ∃ w : ℕ → V,
    (∀ m, (adjoint L * L - L * adjoint L) (w m) = ((n : ℝ) - 2 * m) • w m) ∧
      v = ∑ m ∈ Finset.range (n + 1), w m
  finrank_W : ∀ m : ℕ, finrank ℝ (End.eigenspace (adjoint L * L - L * adjoint L) ((n : ℝ) - 2 * m))
    = n.choose m

theorem adjoint_mul' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : E →ₗ[ℝ] E) : adjoint (A * B) = adjoint B * adjoint A := by
  simp only [← LinearMap.star_eq_adjoint, star_mul]

namespace Sl2Data

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (D : Sl2Data n V)

/-- The raising operator `R = L†`. -/
noncomputable def R : V →ₗ[ℝ] V := adjoint D.L

/-- `H = [R, L]`. -/
noncomputable def H : V →ₗ[ℝ] V := D.R * D.L - D.L * D.R

/-- Weight space `W_m`: `H = n - 2m`. -/
noncomputable def W (m : ℕ) : Submodule ℝ V := End.eigenspace D.H ((n : ℝ) - 2 * m)

/-- Highest-weight vectors of weight `n - 2k`. -/
noncomputable def HW (k : ℕ) : Submodule ℝ V := D.W k ⊓ ker D.R

theorem mem_W {m : ℕ} {v : V} : v ∈ D.W m ↔ D.H v = ((n : ℝ) - 2 * m) • v := by
  rw [W, End.mem_eigenspace_iff]

theorem inner_R (u v : V) : inner ℝ (D.R u) v = inner ℝ u (D.L v) := by
  rw [R, adjoint_inner_left]

theorem inner_L (u v : V) : inner ℝ (D.L u) v = inner ℝ u (D.R v) := by
  rw [R, adjoint_inner_right]

theorem H_selfadjoint : adjoint D.H = D.H := by
  rw [H, map_sub, adjoint_mul', adjoint_mul', R, adjoint_adjoint]

theorem hHR : D.H * D.R - D.R * D.H = (2 : ℝ) • D.R := by
  have h := congrArg adjoint D.hHL
  have e1 : adjoint D.L = D.R := rfl
  have e2 : adjoint (adjoint D.L) = D.L := adjoint_adjoint _
  have hH : adjoint D.H = D.H := D.H_selfadjoint
  have : adjoint (D.H * D.L - D.L * D.H) = - ((2 : ℝ) • D.R) := by
    have h' : adjoint (D.H * D.L - D.L * D.H) = adjoint ((-2 : ℝ) • D.L) := congrArg adjoint D.hHL
    rw [h']
    rw [map_smul]; simp [e1]
  rw [map_sub, adjoint_mul', adjoint_mul', e1, hH] at this
  have h2 : D.R * D.H - D.H * D.R = - ((2 : ℝ) • D.R) := this
  rw [← neg_sub, h2, neg_neg]

theorem hHL' : D.H * D.L - D.L * D.H = (-2 : ℝ) • D.L := D.hHL

theorem H_L (v : V) : D.H (D.L v) = D.L (D.H v) - (2 : ℝ) • D.L v := by
  have := congrArg (fun T : V →ₗ[ℝ] V => T v) D.hHL'
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
  rw [sub_eq_iff_eq_add] at this
  rw [this]; rw [neg_smul, two_smul]; abel

theorem H_R (v : V) : D.H (D.R v) = D.R (D.H v) + (2 : ℝ) • D.R v := by
  have := congrArg (fun T : V →ₗ[ℝ] V => T v) D.hHR
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
  rw [sub_eq_iff_eq_add] at this
  rw [this, add_comm]

theorem L_mem_W {m : ℕ} {v : V} (hv : v ∈ D.W m) : D.L v ∈ D.W (m + 1) := by
  rw [mem_W] at hv ⊢
  rw [H_L, hv, map_smul]
  push_cast
  rw [← sub_smul]; congr 1; ring

theorem R_mem_W {m : ℕ} {v : V} (hv : v ∈ D.W (m + 1)) : D.R v ∈ D.W m := by
  rw [mem_W] at hv ⊢
  have := D.H_R v
  rw [hv, map_smul] at this
  push_cast at this
  have h2 : D.H (D.R v) = ((n : ℝ) - 2 * m) • D.R v := by
    rw [this, ← add_smul]; congr 1; ring
  exact h2

theorem R_zero {v : V} (hv : v ∈ D.W 0) : D.R v = 0 := by
  rw [mem_W] at hv
  refine D.hspec ((n : ℝ) + 2) (fun m hm => ?_) _ ?_
  · have : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
    intro h; linarith
  · show D.H (D.R v) = _
    have := D.H_R v
    rw [hv, map_smul] at this
    rw [this, ← add_smul]; congr 1; push_cast; ring

theorem L_top {v : V} (hv : v ∈ D.W n) : D.L v = 0 := by
  have h1 := D.L_mem_W hv
  rw [mem_W] at h1
  refine D.hspec ((n : ℝ) - 2 * ((n + 1 : ℕ) : ℝ)) (fun m hm => ?_) _ h1
  intro h
  have : (m : ℝ) ≤ n := by exact_mod_cast hm
  push_cast at h
  linarith

theorem inner_LL {m : ℕ} {v : V} (hv : v ∈ D.W m) :
    inner ℝ (D.L v) (D.L v) = inner ℝ (D.R v) (D.R v) + ((n : ℝ) - 2 * m) * inner ℝ v v := by
  have h1 : inner ℝ (D.L v) (D.L v) = inner ℝ v (D.R (D.L v)) := D.inner_L v (D.L v)
  have h2 : D.R (D.L v) = D.L (D.R v) + D.H v := by
    rw [H]; simp
  rw [h1, h2, inner_add_right, D.mem_W.1 hv, inner_smul_right]
  have := D.inner_R v (D.R v)
  rw [← this]

theorem L_injOn {m : ℕ} (hm : (0 : ℝ) < (n : ℝ) - 2 * m) {v : V} (hv : v ∈ D.W m)
    (h : D.L v = 0) : v = 0 := by
  have := D.inner_LL hv
  rw [h, inner_zero_left] at this
  have h0 : 0 ≤ inner ℝ (D.R v) (D.R v) := real_inner_self_nonneg
  have h3 : 0 ≤ inner ℝ v v := real_inner_self_nonneg
  have : inner ℝ v v = 0 := by
    by_contra hne
    have : 0 < inner ℝ v v := lt_of_le_of_ne h3 (Ne.symm hne)
    nlinarith
  exact inner_self_eq_zero.1 this

theorem R_injOn {m : ℕ} (hm : (n : ℝ) - 2 * m < 0) {v : V} (hv : v ∈ D.W m)
    (h : D.R v = 0) : v = 0 := by
  have := D.inner_LL hv
  rw [h, inner_zero_left] at this
  have h0 : 0 ≤ inner ℝ (D.L v) (D.L v) := real_inner_self_nonneg
  have h3 : 0 ≤ inner ℝ v v := real_inner_self_nonneg
  have : inner ℝ v v = 0 := by
    by_contra hne
    have : 0 < inner ℝ v v := lt_of_le_of_ne h3 (Ne.symm hne)
    nlinarith
  exact inner_self_eq_zero.1 this

/-- Every vector of `W_{m+1}` is a highest-weight vector plus `L` of a vector of `W_m`. -/
theorem decomp_step {m : ℕ} {v : V} (hv : v ∈ D.W (m + 1)) :
    ∃ x ∈ D.HW (m + 1), ∃ u ∈ D.W m, v = x + D.L u := by
  rcases lt_or_ge (0 : ℝ) ((n : ℝ) - 2 * m) with hA | hB
  · have hmaps : ∀ u ∈ D.W m, (D.R * D.L) u ∈ D.W m := fun u hu => D.R_mem_W (D.L_mem_W hu)
    let T : D.W m →ₗ[ℝ] D.W m := (D.R * D.L).restrict hmaps
    have hinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have h1 : D.R (D.L (u : V)) = 0 := by
        have := congrArg (fun x : D.W m => (x : V)) hu
        simpa [T] using this
      have h2 : inner ℝ (D.L (u : V)) (D.L (u : V)) = 0 := by
        rw [D.inner_L (u : V) (D.L (u : V)), h1, inner_zero_right]
      have h3 : D.L (u : V) = 0 := inner_self_eq_zero.1 h2
      exact Subtype.ext (D.L_injOn hA u.2 h3)
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    obtain ⟨u, hu⟩ := hsurj ⟨D.R v, D.R_mem_W hv⟩
    have hu' : D.R (D.L (u : V)) = D.R v := by
      have := congrArg (fun x : D.W m => (x : V)) hu
      simpa [T] using this
    refine ⟨v - D.L u, ⟨?_, ?_⟩, u, u.2, by abel⟩
    · exact (D.W (m + 1)).sub_mem hv (D.L_mem_W u.2)
    · exact LinearMap.mem_ker.2 (by rw [map_sub, hu', sub_self])
  · have hneg : (n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ) < 0 := by push_cast; linarith
    have hmaps : ∀ u ∈ D.W (m + 1), (D.L * D.R) u ∈ D.W (m + 1) :=
      fun u hu => D.L_mem_W (D.R_mem_W hu)
    let T : D.W (m + 1) →ₗ[ℝ] D.W (m + 1) := (D.L * D.R).restrict hmaps
    have hinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have h1 : D.L (D.R (u : V)) = 0 := by
        have := congrArg (fun x : D.W (m + 1) => (x : V)) hu
        simpa [T] using this
      have h2 : inner ℝ (D.R (u : V)) (D.R (u : V)) = 0 := by
        rw [D.inner_R (u : V) (D.R (u : V)), h1, inner_zero_right]
      have h3 : D.R (u : V) = 0 := inner_self_eq_zero.1 h2
      exact Subtype.ext (D.R_injOn hneg u.2 h3)
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    obtain ⟨u, hu⟩ := hsurj ⟨v, hv⟩
    have hu' : D.L (D.R (u : V)) = v := by
      have := congrArg (fun x : D.W (m + 1) => (x : V)) hu
      simpa [T] using this
    exact ⟨0, zero_mem _, D.R u, D.R_mem_W u.2, by rw [hu', zero_add]⟩

theorem Lpow_mem_W {k : ℕ} {h : V} (hh : h ∈ D.W k) (a : ℕ) : (D.L ^ a) h ∈ D.W (k + a) := by
  induction a with
  | zero => simpa using hh
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact D.L_mem_W ih

theorem RL_apply (v : V) : D.R (D.L v) = D.L (D.R v) + D.H v := by
  rw [H]; simp

/-- String formula: `R L^{a+1} h = (a+1)(n-2k-a) L^a h` for a highest-weight vector `h`. -/
theorem R_L_pow_succ {k : ℕ} {h : V} (hh : h ∈ D.HW k) (a : ℕ) :
    D.R ((D.L ^ (a + 1)) h) = (((a : ℝ) + 1) * ((n : ℝ) - 2 * k - a)) • (D.L ^ a) h := by
  obtain ⟨hW, hR⟩ := hh
  have hR' : D.R h = 0 := hR
  induction a with
  | zero =>
    rw [pow_one, RL_apply, hR', map_zero, zero_add, D.mem_W.1 hW]
    simp
  | succ a ih =>
    rw [pow_succ' D.L (a + 1), Module.End.mul_apply, RL_apply, ih, map_smul]
    have hm := D.mem_W.1 (D.Lpow_mem_W hW (a + 1))
    have e : D.L ((D.L ^ a) h) = (D.L ^ (a + 1)) h := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hm, e, ← add_smul]
    congr 1
    push_cast; ring

theorem HW_zero_of_large {k : ℕ} (hk : n < 2 * k) : D.HW k = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hW, hR⟩
  have : (n : ℝ) - 2 * k < 0 := by
    have : (n : ℝ) < 2 * k := by exact_mod_cast hk
    linarith
  exact D.R_injOn this hW hR

theorem L_pow_top {k : ℕ} (hk : 2 * k ≤ n) {h : V} (hh : h ∈ D.HW k) :
    (D.L ^ (n - 2 * k + 1)) h = 0 := by
  have hW := D.Lpow_mem_W hh.1 (n - 2 * k + 1)
  have hR : D.R ((D.L ^ (n - 2 * k + 1)) h) = 0 := by
    rw [D.R_L_pow_succ hh, Nat.cast_sub hk]
    push_cast
    simp
  have hneg : (n : ℝ) - 2 * ((k + (n - 2 * k + 1) : ℕ) : ℝ) < 0 := by
    have : ((k + (n - 2 * k + 1) : ℕ) : ℝ) = (n : ℝ) - k + 1 := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hk]; push_cast; ring
    rw [this]
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  exact D.R_injOn hneg hW hR

/-- The span of the strings `L^a h`, `h ∈ HW_k`, `k ≤ n/2`, `a ≤ n - 2k`. -/
noncomputable def Str : Submodule ℝ V :=
  Submodule.span ℝ {v | ∃ k a : ℕ, ∃ h ∈ D.HW k, k ≤ n / 2 ∧ a ≤ n - 2 * k ∧ v = (D.L ^ a) h}

theorem gen_mem_Str {k a : ℕ} {h : V} (hh : h ∈ D.HW k) (hk : k ≤ n / 2) (ha : a ≤ n - 2 * k) :
    (D.L ^ a) h ∈ D.Str :=
  Submodule.subset_span ⟨k, a, h, hh, hk, ha, rfl⟩

theorem L_mem_Str {v : V} (hv : v ∈ D.Str) : D.L v ∈ D.Str := by
  have : D.Str ≤ D.Str.comap D.L := by
    rw [Str, Submodule.span_le]
    rintro v ⟨k, a, h, hh, hk, ha, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have e : D.L ((D.L ^ a) h) = (D.L ^ (a + 1)) h := by
      rw [pow_succ', Module.End.mul_apply]
    rw [e]
    by_cases hlt : a + 1 ≤ n - 2 * k
    · exact D.gen_mem_Str hh hk hlt
    · have : a = n - 2 * k := by omega
      have h2 : 2 * k ≤ n := by omega
      rw [this, D.L_pow_top h2 hh]; exact zero_mem _
  exact this hv

theorem W_le_Str (m : ℕ) : D.W m ≤ D.Str := by
  induction m with
  | zero =>
    intro v hv
    have : v ∈ D.HW 0 := ⟨hv, LinearMap.mem_ker.2 (D.R_zero hv)⟩
    simpa using D.gen_mem_Str (a := 0) this (Nat.zero_le _) (Nat.zero_le _)
  | succ m ih =>
    intro v hv
    obtain ⟨x, hx, u, hu, rfl⟩ := D.decomp_step hv
    refine add_mem ?_ (D.L_mem_Str (ih hu))
    by_cases hk : m + 1 ≤ n / 2
    · simpa using D.gen_mem_Str (a := 0) hx hk (Nat.zero_le _)
    · have : n < 2 * (m + 1) := by omega
      rw [D.HW_zero_of_large this] at hx
      rw [(Submodule.mem_bot ℝ).1 hx]; exact zero_mem _

theorem Str_eq_top : D.Str = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨w, hw, rfl⟩ := D.decomp v
  exact Submodule.sum_mem _ fun m _ => D.W_le_Str m ((D.mem_W).2 (hw m))

theorem finrank_W' (m : ℕ) : finrank ℝ (D.W m) = n.choose m := D.finrank_W m

theorem HW_zero_eq : D.HW 0 = D.W 0 := by
  ext v
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, LinearMap.mem_ker.2 (D.R_zero h)⟩

/-- `dim HW_{m+1} = C(n, m+1) - C(n, m)` for `2(m+1) ≤ n`. -/
theorem finrank_HW_succ {m : ℕ} (hm : 2 * (m + 1) ≤ n) :
    finrank ℝ (D.HW (m + 1)) + n.choose m = n.choose (m + 1) := by
  have hpos : (0 : ℝ) < (n : ℝ) - 2 * m := by
    have : (2 * (m + 1) : ℝ) ≤ n := by exact_mod_cast hm
    linarith
  have hinj : Function.Injective ((D.L).domRestrict (D.W m)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have : D.L (u : V) = 0 := by simpa using hu
    exact Subtype.ext (D.L_injOn hpos u.2 this)
  have hmap : finrank ℝ ((D.W m).map D.L) = n.choose m := by
    have h1 := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict] at h1
    rw [h1, D.finrank_W' m]
  have hdisj : Disjoint (D.HW (m + 1)) ((D.W m).map D.L) := by
    rw [Submodule.disjoint_def]
    rintro y ⟨hyW, hyR⟩ ⟨u, hu, rfl⟩
    have h1 : D.R (D.L u) = 0 := hyR
    have h2 : inner ℝ (D.L u) (D.L u) = 0 := by
      rw [D.inner_L u (D.L u), h1, inner_zero_right]
    exact inner_self_eq_zero.1 h2
  have hle : D.HW (m + 1) ⊔ (D.W m).map D.L ≤ D.W (m + 1) := by
    refine sup_le (fun x hx => hx.1) ?_
    rintro y ⟨u, hu, rfl⟩
    exact D.L_mem_W hu
  have hge : D.W (m + 1) ≤ D.HW (m + 1) ⊔ (D.W m).map D.L := by
    intro v hv
    obtain ⟨x, hx, u, hu, rfl⟩ := D.decomp_step hv
    exact Submodule.add_mem_sup hx ⟨u, hu, rfl⟩
  have heq : D.HW (m + 1) ⊔ (D.W m).map D.L = D.W (m + 1) := le_antisymm hle hge
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (D.HW (m + 1)) ((D.W m).map D.L)
  rw [hdisj.eq_bot, finrank_bot, heq, D.finrank_W' (m + 1), hmap] at hsum
  omega

theorem finrank_HW {k : ℕ} (hk : 2 * k ≤ n) : finrank ℝ (D.HW k) = hwDim n k := by
  cases k with
  | zero => rw [D.HW_zero_eq, D.finrank_W' 0]; simp [hwDim]
  | succ m =>
    have := D.finrank_HW_succ hk
    simp only [hwDim, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    omega

end Sl2Data

end FormalResearch.FrameFree.OddWords
