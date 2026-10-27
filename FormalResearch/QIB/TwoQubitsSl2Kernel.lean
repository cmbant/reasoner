import Mathlib

/-!
# Kernels of nonzero `sl₂` elements on irreducible modules are at most one-dimensional

Namespace `FormalResearch.QIB.Sl2Kernel`.  Claim class: **proved** (finite-dimensional linear algebra
over `ℂ`; no analytic or group-theoretic input).

This is the representation-theoretic step of the stabiliser proof of `prop:twoqubits`
(`QI-B/paper/invariant_discrimination_exponents.tex`): "`L_a` acts on the irreducible spin-`j` carrier with
a kernel of dimension at most one".  Here the statement is proved directly for an arbitrary finite-dimensional
irreducible module of an `sl₂` triple, with no semisimple/nilpotent case split:

* `Triple H E F`: the relations `[H,E] = 2E`, `[H,F] = -2F`, `[E,F] = H`, stated pointwise.
* `Irr H E F`: no invariant subspace other than `⊥` and `⊤`.
* `kernel_sl2`: for `(α, β, γ) ≠ 0`, `∃ k, ∀ u, (αH + βE + γF) u = 0 → ∃ c, u = c • k`.

Proof.  (1) a highest-weight vector `v₀` (`E v₀ = 0`, `H v₀ = λ v₀`) exists; (2) the vectors
`v_k = F^k v₀` are `H`-eigenvectors with distinct eigenvalues `λ - 2k`, `E v_{k+1} ∈ ℂ v_k`; some `v_{N+1}`
vanishes and `v₀,…,v_N` are independent and (irreducibility) span; (3) if the `F`-coefficient `γ` of
`K = αH + βE + γF` is nonzero, then `K` raises the filtration `W_t = span{v_k : k < t}` by exactly
`γ v_{t+1}`-leading term, so `ker K ∩ W_N = 0` while `W_N` has codimension one; (4) a nonzero
`(α,β,γ)` can be moved to `γ ≠ 0` by the inner automorphism `exp (t ad F)` of the triple
(`H ↦ H + 2tF`, `E ↦ E - tH - t²F`, `F ↦ F`), which preserves the relations and irreducibility.
The matrix form and the bridge to `QIB.rank_tau_le_one_of_kernel` are in `TwoQubitsSl2Rank.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Module

namespace FormalResearch.QIB
namespace Sl2Kernel

section Core

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The `sl₂` relations, pointwise. -/
structure Triple (H E F : End ℂ V) : Prop where
  HE : ∀ x, H (E x) = E (H x) + (2 : ℂ) • E x
  HF : ∀ x, H (F x) = F (H x) - (2 : ℂ) • F x
  EF : ∀ x, E (F x) = F (E x) + H x

/-- Irreducibility: the only subspaces invariant under `H`, `E`, `F` are `⊥` and `⊤`. -/
def Irr (H E F : End ℂ V) : Prop :=
  ∀ W : Submodule ℂ V, (∀ w ∈ W, H w ∈ W) → (∀ w ∈ W, E w ∈ W) → (∀ w ∈ W, F w ∈ W) →
    W = ⊥ ∨ W = ⊤

variable [FiniteDimensional ℂ V]

/-- A nonterminating orbit of eigenvectors with injective eigenvalues is impossible in finite dimension. -/
theorem exists_last_nonzero (H : End ℂ V) (w : ℕ → V)
    (μ : ℕ → ℂ) (hμ : Function.Injective μ) (hH : ∀ n, H (w n) = μ n • w n) (h0 : w 0 ≠ 0) :
    ∃ N, w N ≠ 0 ∧ w (N + 1) = 0 := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ n, w n ≠ 0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact hcon n ih
  have hli : LinearIndependent ℂ w :=
    Module.End.eigenvectors_linearIndependent' H μ hμ w
      (fun i => ⟨Module.End.mem_eigenspace_iff.2 (hH i), hall i⟩)
  exact Module.Finite.not_linearIndependent_of_infinite w hli

variable {H E F : End ℂ V}

/-- Existence of a highest-weight vector. -/
theorem exists_highest (h : Triple H E F) [Nontrivial V] :
    ∃ v0 : V, v0 ≠ 0 ∧ E v0 = 0 ∧ ∃ lam : ℂ, H v0 = lam • v0 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue H
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hHw : H w = μ • w := Module.End.mem_eigenspace_iff.1 hw.1
  set u : ℕ → V := fun n => (E ^ n) w with hu_def
  have hu : ∀ n, u (n + 1) = E (u n) := fun n => by
    simp [hu_def, pow_succ', Module.End.mul_apply]
  have hH : ∀ n, H (u n) = (μ + 2 * (n : ℂ)) • u n := by
    intro n
    induction n with
    | zero => simp [hu_def, hHw]
    | succ n ih =>
      rw [hu, h.HE, ih, map_smul, ← add_smul]
      congr 1
      push_cast
      ring
  have hinj : Function.Injective (fun n : ℕ => μ + 2 * (n : ℂ)) := by
    intro a b hab
    simpa using hab
  obtain ⟨N, hN, hN1⟩ :=
    exists_last_nonzero H u (fun n : ℕ => μ + 2 * (n : ℂ)) hinj hH (by simpa [hu_def] using hw.2)
  exact ⟨u N, hN, by rw [← hu]; exact hN1, μ + 2 * (N : ℂ), hH N⟩

/-- The standard-module data attached to a highest-weight vector. -/
theorem exists_model (h : Triple H E F) (hirr : Irr H E F) [Nontrivial V] :
    ∃ (v : ℕ → V) (N : ℕ) (μ c : ℕ → ℂ),
      Function.Injective μ ∧ (∀ k, H (v k) = μ k • v k) ∧ (∀ k, F (v k) = v (k + 1)) ∧
      (∀ k, E (v (k + 1)) = c k • v k) ∧ E (v 0) = 0 ∧ v (N + 1) = 0 ∧ (∀ k ≤ N, v k ≠ 0) ∧
      Submodule.span ℂ (v '' Set.Iic N) = ⊤ := by
  obtain ⟨v0, hv0, hE0, lam, hHl⟩ := exists_highest h
  set v : ℕ → V := fun k => (F ^ k) v0 with hv_def
  have hvs : ∀ k, v (k + 1) = F (v k) := fun k => by
    simp [hv_def, pow_succ', Module.End.mul_apply]
  have hv0' : v 0 = v0 := by simp [hv_def]
  have hHv : ∀ k, H (v k) = (lam - 2 * (k : ℂ)) • v k := by
    intro k
    induction k with
    | zero => simp [hv0', hHl]
    | succ k ih =>
      rw [hvs, h.HF, ih, map_smul, ← hvs, ← sub_smul]
      congr 1
      push_cast
      ring
  have hEv : ∀ k, ∃ c : ℂ, E (v (k + 1)) = c • v k := by
    intro k
    induction k with
    | zero =>
      refine ⟨lam, ?_⟩
      rw [hvs, h.EF, hv0', hE0, map_zero, zero_add, hHl]
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + (lam - 2 * ((k + 1 : ℕ) : ℂ)), ?_⟩
      rw [hvs (k + 1), h.EF, hHv, hc, map_smul, ← hvs, ← add_smul]
  choose c hc using hEv
  have hinj : Function.Injective (fun k : ℕ => lam - 2 * (k : ℂ)) := by
    intro a b hab
    have : (2 : ℂ) * (a : ℂ) = 2 * (b : ℂ) := by linear_combination -hab
    have : (a : ℂ) = b := by linear_combination this / 2
    exact_mod_cast this
  obtain ⟨N, hN, hN1⟩ :=
    exists_last_nonzero H v (fun k : ℕ => lam - 2 * (k : ℂ)) hinj hHv (by rw [hv0']; exact hv0)
  have hne : ∀ k ≤ N, v k ≠ 0 := by
    intro k hk hvk
    apply hN
    clear hN hN1
    induction N, hk using Nat.le_induction with
    | base => exact hvk
    | succ n hn ih => rw [hvs, ih]; exact map_zero F
  refine ⟨v, N, fun k => lam - 2 * (k : ℂ), c, hinj, hHv, fun k => (hvs k).symm, hc,
    by rw [hv0']; exact hE0, hN1, hne, ?_⟩
  -- the span is invariant, hence everything
  set W : Submodule ℂ V := Submodule.span ℂ (v '' Set.Iic N) with hW
  have hvW : ∀ k ≤ N, v k ∈ W := fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩
  have hHW : W ≤ W.comap H := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, hHv]
    exact Submodule.smul_mem _ _ (hvW k hk)
  have hFW : W ≤ W.comap F := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk0 : k ≤ N := hk
    simp only [SetLike.mem_coe, Submodule.mem_comap, ← hvs]
    by_cases hk' : k + 1 ≤ N
    · exact hvW _ hk'
    · have : k = N := by omega
      subst this
      rw [hN1]
      exact W.zero_mem
  have hEW : W ≤ W.comap E := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k ≤ N := hk
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    cases k with
    | zero =>
      have : E (v 0) = 0 := by rw [hv0']; exact hE0
      rw [this]
      exact W.zero_mem
    | succ k =>
      rw [hc]
      exact Submodule.smul_mem _ _ (hvW k (by omega))
  rcases hirr W (fun w hw => hHW hw) (fun w hw => hEW hw) (fun w hw => hFW hw) with hbot | htop
  · exfalso
    have : v 0 ∈ W := hvW 0 (Nat.zero_le _)
    rw [hbot] at this
    exact hne 0 (Nat.zero_le _) ((Submodule.mem_bot ℂ).1 this)
  · exact htop

/-- A kernel meeting a hyperplane complement trivially is at most a line. -/
theorem gen_of_codim_one (K : End ℂ V) (S : Submodule ℂ V) (w : V)
    (hS : ∀ u, ∃ a : ℂ, u - a • w ∈ S) (hker : ∀ u ∈ S, K u = 0 → u = 0) :
    ∃ k : V, ∀ u, K u = 0 → ∃ c : ℂ, u = c • k := by
  by_cases hex : ∃ k, K k = 0 ∧ k ≠ 0
  · obtain ⟨k, hk0, hkne⟩ := hex
    refine ⟨k, fun u hu => ?_⟩
    obtain ⟨a, ha⟩ := hS u
    obtain ⟨b, hb⟩ := hS k
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hkne (hker k (by simpa using hb) hk0)
    refine ⟨a / b, ?_⟩
    have hab : a / b * b = a := div_mul_cancel₀ a hb0
    have hz : u - (a / b) • k ∈ S := by
      have : u - (a / b) • k = (u - a • w) - (a / b) • (k - b • w) := by
        rw [smul_sub, smul_smul, hab]; abel
      rw [this]
      exact S.sub_mem ha (S.smul_mem _ hb)
    have := hker _ hz (by rw [map_sub, hu, map_smul, hk0]; simp)
    exact sub_eq_zero.1 this
  · push Not at hex
    exact ⟨0, fun u hu => ⟨0, by simp [hex u hu]⟩⟩

/-- **Core kernel lemma** (the `F`-coefficient `γ` is nonzero). -/
theorem core_kernel (h : Triple H E F) (hirr : Irr H E F) [Nontrivial V] (α β γ : ℂ) (hγ : γ ≠ 0) :
    ∃ k : V, ∀ u, (α • H + β • E + γ • F) u = 0 → ∃ c : ℂ, u = c • k := by
  obtain ⟨v, N, μ, c, hμ, hHv, hFv, hEv, hE0, hN1, hne, hspan⟩ := exists_model h hirr
  set K : End ℂ V := α • H + β • E + γ • F with hK
  set W : ℕ → Submodule ℂ V := fun t => Submodule.span ℂ (v '' Set.Iio t) with hW
  have hmono : ∀ {s t : ℕ}, s ≤ t → W s ≤ W t := fun hst =>
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hst))
  have hvW : ∀ {j t : ℕ}, j < t → v j ∈ W t := fun hj => Submodule.subset_span ⟨_, hj, rfl⟩
  have hli : LinearIndepOn ℂ v (Set.Iic N) :=
    Module.End.eigenvectors_linearIndependent' H (fun k : Set.Iic N => μ k)
      (fun a b hab => Subtype.ext (hμ hab)) (fun k => v k)
      (fun k => ⟨Module.End.mem_eigenspace_iff.2 (hHv k), hne k k.2⟩)
  have hEW : ∀ j, E (v j) ∈ W (j + 1) := by
    intro j
    cases j with
    | zero => rw [hE0]; exact (W 1).zero_mem
    | succ j => rw [hEv]; exact Submodule.smul_mem _ _ (hvW (by omega))
  have hK0 : ∀ j, K (v j) - γ • v (j + 1) ∈ W (j + 1) := by
    intro j
    have : K (v j) - γ • v (j + 1) = (α * μ j) • v j + β • E (v j) := by
      simp only [hK, LinearMap.add_apply, LinearMap.smul_apply, hHv, hFv, smul_smul]
      abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hvW (by omega)))
      (Submodule.smul_mem _ _ (hEW j))
  have hKW : ∀ t, ∀ u ∈ W t, K u ∈ W (t + 1) := by
    intro t
    have : W t ≤ (W (t + 1)).comap K := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j < t := hj
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      have e : K (v j) = (K (v j) - γ • v (j + 1)) + γ • v (j + 1) := by abel
      rw [e]
      exact Submodule.add_mem _ (hmono (by omega) (hK0 j))
        (Submodule.smul_mem _ _ (hvW (by omega)))
    intro u hu
    exact this hu
  have hdec : ∀ t, ∀ u ∈ W (t + 1), ∃ a : ℂ, a • v t + (u - a • v t) = u ∧ u - a • v t ∈ W t := by
    intro t u hu
    have hins : Set.Iio (t + 1) = insert t (Set.Iio t) := by
      ext x; simp only [Set.mem_Iio, Set.mem_insert_iff]; omega
    have hsup : W (t + 1) = Submodule.span ℂ {v t} ⊔ W t := by
      simp only [hW]
      rw [hins, Set.image_insert_eq, Submodule.span_insert]
    rw [hsup] at hu
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hu
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hy
    refine ⟨a, by abel, ?_⟩
    have : u - a • v t = z := by rw [← hyz, ← ha]; abel
    rw [this]
    exact hz
  have hF3 : ∀ t, t + 1 ≤ N → ∀ u ∈ W (t + 1), K u = 0 → u ∈ W t := by
    intro t ht u hu hKu
    obtain ⟨a, hau, haW⟩ := hdec t u hu
    have hK2 : K u - (γ * a) • v (t + 1) ∈ W (t + 1) := by
      have e : K u - (γ * a) • v (t + 1)
          = a • (K (v t) - γ • v (t + 1)) + K (u - a • v t) := by
        conv_lhs => rw [← hau]
        rw [map_add, map_smul]
        module
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hK0 t)) (hKW t _ haW)
    rw [hKu, zero_sub] at hK2
    have hmem : (γ * a) • v (t + 1) ∈ W (t + 1) := (Submodule.neg_mem_iff _).1 hK2
    have hnot : v (t + 1) ∉ W (t + 1) := by
      have hsub : insert (t + 1) (Set.Iio (t + 1)) ⊆ Set.Iic N := by
        intro x hx
        rcases hx with rfl | hx
        · exact ht
        · exact le_trans (le_of_lt hx) ht
      exact (hli.mono hsub).notMem_span_of_insert (by simp)
    by_cases hga : γ * a = 0
    · have ha0 : a = 0 := (mul_eq_zero.1 hga).resolve_left hγ
      subst ha0
      simpa using haW
    · exfalso
      apply hnot
      have := (W (t + 1)).smul_mem (γ * a)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hga, one_smul] at this
  have hF4 : ∀ t, t ≤ N → ∀ u ∈ W t, K u = 0 → u = 0 := by
    intro t
    induction t with
    | zero =>
      intro _ u hu _
      have h0 : W 0 = ⊥ := by
        simp only [hW]
        have : Set.Iio (0 : ℕ) = ∅ := by ext x; simp
        rw [this, Set.image_empty, Submodule.span_empty]
      rw [h0] at hu
      exact (Submodule.mem_bot ℂ).1 hu
    | succ t ih =>
      intro ht u hu hKu
      exact ih (by omega) u (hF3 t ht u hu hKu) hKu
  refine gen_of_codim_one K (W N) (v N) ?_ (hF4 N le_rfl)
  intro u
  have hu : u ∈ W (N + 1) := by
    have : W (N + 1) = ⊤ := by
      simp only [hW]
      have : Set.Iio (N + 1) = Set.Iic N := by ext x; simp
      rw [this]
      exact hspan
    rw [this]
    trivial
  obtain ⟨a, _, ha⟩ := hdec N u hu
  exact ⟨a, ha⟩

/-- The twisted generators `H + 2tF`, `E - tH - t²F` (the inner automorphism `exp (t ad F)`). -/
def Hs (H F : End ℂ V) (t : ℂ) : End ℂ V := H + (2 * t) • F

/-- See `Hs`. -/
def Es (H E F : End ℂ V) (t : ℂ) : End ℂ V := E - t • H - (t ^ 2) • F

/-- The twist preserves the `sl₂` relations. -/
theorem triple_twist (h : Triple H E F) (t : ℂ) : Triple (Hs H F t) (Es H E F t) F where
  HE x := by
    simp only [Hs, Es, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add,
      map_sub, map_smul, h.HE, h.HF, h.EF]
    module
  HF x := by
    simp only [Hs, Es, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add,
      map_sub, map_smul, h.HE, h.HF, h.EF]
    module
  EF x := by
    simp only [Hs, Es, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add,
      map_sub, map_smul, h.HE, h.HF, h.EF]
    module

/-- The twist preserves irreducibility (the generated algebra is unchanged). -/
theorem irr_twist (hirr : Irr H E F) (t : ℂ) : Irr (Hs H F t) (Es H E F t) F := by
  intro W hH hE hF
  apply hirr W
  · intro w hw
    have : H w = Hs H F t w - (2 * t) • F w := by
      simp only [Hs, LinearMap.add_apply, LinearMap.smul_apply]; module
    rw [this]
    exact W.sub_mem (hH w hw) (W.smul_mem _ (hF w hw))
  · intro w hw
    have : E w = Es H E F t w + t • Hs H F t w - (t ^ 2) • F w := by
      simp only [Hs, Es, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]; module
    rw [this]
    exact W.sub_mem (W.add_mem (hE w hw) (W.smul_mem _ (hH w hw))) (W.smul_mem _ (hF w hw))
  · exact hF

/-- **Kernel lemma.**  On a nonzero finite-dimensional irreducible module of an `sl₂` triple, the kernel
of any nonzero element `αH + βE + γF` is at most one-dimensional. -/
theorem kernel_sl2 (h : Triple H E F) (hirr : Irr H E F) [Nontrivial V] (α β γ : ℂ)
    (hne : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) :
    ∃ k : V, ∀ u : V, (α • H + β • E + γ • F) u = 0 → ∃ c : ℂ, u = c • k := by
  obtain ⟨t, ht⟩ : ∃ t : ℂ, γ - 2 * α * t - β * t ^ 2 ≠ 0 := by
    by_cases hγ : γ = 0
    · subst hγ
      by_contra hcon
      push Not at hcon
      have h1 := hcon 1
      have h2 := hcon (-1)
      have hb : β = 0 := by linear_combination (-1 / 2 : ℂ) * (h1 + h2)
      have ha : α = 0 := by linear_combination (1 / 4 : ℂ) * (h2 - h1)
      rcases hne with h | h | h <;> contradiction
    · exact ⟨0, by simpa using hγ⟩
  obtain ⟨k, hk⟩ :=
    core_kernel (triple_twist h t) (irr_twist hirr t) (α + β * t) β (γ - 2 * α * t - β * t ^ 2) ht
  refine ⟨k, fun u hu => hk u ?_⟩
  have e : (α + β * t) • Hs H F t + β • Es H E F t + (γ - 2 * α * t - β * t ^ 2) • F
      = α • H + β • E + γ • F := by
    refine LinearMap.ext fun x => ?_
    simp only [Hs, Es, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    module
  rw [e]
  exact hu

end Core

end Sl2Kernel
end FormalResearch.QIB
