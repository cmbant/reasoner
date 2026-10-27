import Mathlib
import FormalResearch.QIB.BlockStructure
import FormalResearch.QIB.RealCoordsOnb

/-!
# Real isotypic coordinates for a conjugation-closed `*`-algebra with a real minimal vector

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis on any group, no new axiom).

This is `BlockStructure.lean` with every choice made *real*.  Let `C ⊆ M_ι(ℂ)` be a unital subalgebra
closed under conjugate transpose and under entrywise conjugation.  `RealMin C` is the hypothesis that
every nonzero subspace `U` that is conjugation-closed and `C`-, `C'`-invariant contains a *real* unit
vector `f₀` generating a minimal `C`-invariant subspace.  Under it:

* `exists_rsector`: the sector `T = C'·(C f₀)` of `BlockStructure.exists_sector` has a *real*
  orthonormal frame `e_{(α,b)} = y_α f_b` (`y_α ∈ C'` real, `f_b` a real orthonormal basis of `C f₀`);
* `exists_rsectors`: induction on a conjugation-closed bi-invariant `U` (the orthogonal complement of
  a conjugation-closed sector is conjugation-closed);
* `exists_real_isotypic_coordinates`: the gluing, a *real* unitary `W` (`W.map conj = W`) with
  `M ∈ C ↔ ∃ X, Wᴴ M W = blockOp (fun l => Fin (a l)) X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped Kronecker ComplexOrder

namespace FormalResearch.QIB

section RealStructure

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Subalgebra ℂ (Matrix ι ι ℂ)}

/-- An isotypic sector with a real orthonormal frame. -/
structure RSector (C : Subalgebra ℂ (Matrix ι ι ℂ)) extends Sector C where
  e_real : ∀ p, star (e p) = e p

/-- `RealMin C`: every nonzero conjugation-closed `C`- and `C'`-invariant subspace contains a real
unit vector generating a minimal `C`-invariant subspace inside it. -/
def RealMin (C : Subalgebra ℂ (Matrix ι ι ℂ)) : Prop :=
  ∀ U : Submodule ℂ (ι → ℂ), ConjClosed U → Inv (C : Set (Matrix ι ι ℂ)) U →
    Inv (comm C : Set (Matrix ι ι ℂ)) U → U ≠ ⊥ →
    ∃ S ≤ U, IsMinInv C S ∧ ∃ f0 ∈ S, star f0 = f0 ∧ star f0 ⬝ᵥ f0 = 1

theorem map_conj_mul' (A B : Matrix ι ι ℂ) : (A * B).map conj = A.map conj * B.map conj :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_conj_conj' (A : Matrix ι ι ℂ) : (A.map conj).map conj = A := by
  ext i j; simp

theorem comm_map_conj (hCr : ∀ c ∈ C, c.map conj ∈ C) {y : Matrix ι ι ℂ} (hy : y ∈ comm C) :
    y.map conj ∈ comm C := by
  rw [mem_comm] at hy ⊢
  intro c hc
  have h := congrArg (fun M => M.map conj) (hy (c.map conj) (hCr c hc))
  simp only [map_conj_mul', map_conj_conj'] at h
  exact h

theorem exists_rsector (hC : ∀ c ∈ C, cᴴ ∈ C) (hCr : ∀ c ∈ C, c.map conj ∈ C)
    {S : Submodule ℂ (ι → ℂ)} (hS : IsMinInv C S) {f0 : ι → ℂ} (hf0S : f0 ∈ S)
    (hf0r : star f0 = f0) (hf0 : star f0 ⬝ᵥ f0 = 1) :
    ∃ σ : RSector C, S ≤ σ.T ∧ ∀ U : Submodule ℂ (ι → ℂ), Inv (comm C : Set (Matrix ι ι ℂ)) U →
      S ≤ U → σ.T ≤ U := by
  have hS' := hS
  obtain ⟨hS0, hSC, hmin⟩ := hS
  -- `S = C f0`
  let Sc : Submodule ℂ (ι → ℂ) :=
    { carrier := {v | ∃ c ∈ C, v = c *ᵥ f0}
      add_mem' := by
        rintro _ _ ⟨c1, h1, rfl⟩ ⟨c2, h2, rfl⟩
        exact ⟨c1 + c2, add_mem h1 h2, by rw [Matrix.add_mulVec]⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c _ ⟨c', h, rfl⟩
        exact ⟨c • c', Subalgebra.smul_mem _ h c, by rw [Matrix.smul_mulVec]⟩ }
  have hf0Sc : f0 ∈ Sc := ⟨1, one_mem _, by simp⟩
  have hSc : Sc = S := by
    have hle : Sc ≤ S := by
      rintro _ ⟨c, hc, rfl⟩
      exact hSC c hc f0 hf0S
    have hinv : Inv (C : Set _) Sc := by
      rintro c hc _ ⟨c', hc', rfl⟩
      exact ⟨c * c', mul_mem hc hc', by rw [Matrix.mulVec_mulVec]⟩
    rcases hmin Sc hle hinv with h | h
    · exfalso
      rw [h] at hf0Sc
      have h0 : f0 = 0 := by simpa using hf0Sc
      rw [h0] at hf0
      simp at hf0
    · exact h
  have hSconj : ConjClosed S := by
    rw [← hSc]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c.map conj, hCr c hc, by rw [star_mulVec_map, hf0r]⟩
  obtain ⟨m, f, hfmem, hfreal, hfon, hfspan⟩ := exists_real_onb S hSconj
  -- the orbit space `D f0`
  let M : Submodule ℂ (ι → ℂ) :=
    { carrier := {v | ∃ y ∈ comm C, v = y *ᵥ f0}
      add_mem' := by
        rintro _ _ ⟨y1, h1, rfl⟩ ⟨y2, h2, rfl⟩
        exact ⟨y1 + y2, add_mem h1 h2, by rw [Matrix.add_mulVec]⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c _ ⟨y, h, rfl⟩
        exact ⟨c • y, Subalgebra.smul_mem _ h c, by rw [Matrix.smul_mulVec]⟩ }
  have hf0M : f0 ∈ M := ⟨1, one_mem _, by simp⟩
  have hMconj : ConjClosed M := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.map conj, comm_map_conj hCr hy, by rw [star_mulVec_map, hf0r]⟩
  obtain ⟨a, g, hgmem, hgreal, hgon, hgspan⟩ := exists_real_onb M hMconj
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      have := hgspan f0 hf0M
      rw [this] at hf0
      simp at hf0
    · exact h
  have hyex : ∀ α, ∃ y ∈ comm C, y.map conj = y ∧ g α = y *ᵥ f0 := by
    intro α
    obtain ⟨y', hy', hy'g⟩ := hgmem α
    refine ⟨(1 / 2 : ℂ) • (y' + y'.map conj), ?_, ?_, ?_⟩
    · exact Subalgebra.smul_mem _ (add_mem hy' (comm_map_conj hCr hy')) _
    · ext i j; simp [add_comm, map_ofNat]; ring
    · rw [Matrix.smul_mulVec, Matrix.add_mulVec, ← hy'g]
      have : y'.map conj *ᵥ f0 = g α := by
        calc y'.map conj *ᵥ f0 = y'.map conj *ᵥ star f0 := by rw [hf0r]
          _ = star (y' *ᵥ f0) := (star_mulVec_map _ _).symm
          _ = star (g α) := by rw [← hy'g]
          _ = g α := hgreal α
      rw [this, ← two_smul ℂ (g α), smul_smul]
      norm_num
  choose y hyD hyr hyg using hyex
  have hsch : ∀ w ∈ comm C, ∀ s ∈ S, ∀ t ∈ S,
      star s ⬝ᵥ (w *ᵥ t) = (star f0 ⬝ᵥ (w *ᵥ f0)) * (star s ⬝ᵥ t) := by
    intro w hw s hs t ht
    obtain ⟨μ, hμ⟩ := schur hC hS' hw
    rw [hμ s hs t ht, hμ f0 hf0S f0 hf0S, hf0, mul_one]
  have hω : ∀ α β, star f0 ⬝ᵥ (((y α)ᴴ * y β) *ᵥ f0) = if α = β then 1 else 0 := by
    intro α β
    rw [← Matrix.mulVec_mulVec, ← ip_mulVec', ← hyg α, ← hyg β]
    simpa using hgon α β
  have hyy : ∀ (α β : Fin a) (b b' : Fin m),
      star (y α *ᵥ f b) ⬝ᵥ (y β *ᵥ f b') = if (α, b) = (β, b') then 1 else 0 := by
    intro α β b b'
    rw [ip_mulVec', Matrix.mulVec_mulVec,
      hsch _ (mul_mem (comm_star hC (hyD α)) (hyD β)) _ (hfmem b) _ (hfmem b'), hω, hfon]
    by_cases h1 : α = β <;> by_cases h2 : b = b' <;> simp [h1, h2]
  have hfC : ∀ b, ∃ c ∈ C, f b = c *ᵥ f0 := fun b => by
    have : f b ∈ Sc := by rw [hSc]; exact hfmem b
    exact this
  have hkey : ∀ w ∈ comm C, ∀ b,
      w *ᵥ f b ∈ Submodule.span ℂ (Set.range fun p : Fin a × Fin m => y p.1 *ᵥ f p.2) := by
    intro w hw b
    obtain ⟨c, hc, hcb⟩ := hfC b
    have hwf0 : w *ᵥ f0 ∈ M := ⟨w, hw, rfl⟩
    obtain ⟨lam, hlam⟩ : ∃ lam : Fin a → ℂ, w *ᵥ f0 = ∑ α, lam α • g α := ⟨_, hgspan _ hwf0⟩
    have h1 : ∀ α, c *ᵥ g α = y α *ᵥ f b := by
      intro α
      rw [hyg α, hcb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mem_comm.1 (hyD α) c hc]
    have h2 : w *ᵥ f b = c *ᵥ (w *ᵥ f0) := by
      rw [hcb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mem_comm.1 hw c hc]
    rw [h2, hlam, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [Matrix.mulVec_smul, h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(α, b), rfl⟩)
  set T : Submodule ℂ (ι → ℂ) :=
    Submodule.span ℂ {v | ∃ w ∈ comm C, ∃ s ∈ S, v = w *ᵥ s} with hTdef
  have hTle : T ≤ Submodule.span ℂ (Set.range fun p : Fin a × Fin m => y p.1 *ᵥ f p.2) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, s, hs, rfl⟩
    have hs' := hfspan s hs
    rw [hs', Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hkey w hw b)
  refine ⟨⟨⟨a, m, ha, fun p => y p.1 *ᵥ f p.2, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro p
    exact Submodule.subset_span ⟨y p.1, hyD p.1, f p.2, hfmem p.2, rfl⟩
  · intro p q
    exact hyy p.1 q.1 p.2 q.2
  · intro v hv
    exact expand_of_mem_span (fun p : Fin a × Fin m => y p.1 *ᵥ f p.2) (fun p q => hyy p.1 q.1 p.2 q.2)
      (hTle hv)
  · refine Inv_span fun c hc v hv => ?_
    obtain ⟨w, hw, s, hs, rfl⟩ := hv
    refine Submodule.subset_span ⟨w, hw, c *ᵥ s, hSC c hc s hs, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mem_comm.1 hw c hc]
  · refine Inv_span fun w' hw' v hv => ?_
    obtain ⟨w, hw, s, hs, rfl⟩ := hv
    refine Submodule.subset_span ⟨w' * w, mul_mem hw' hw, s, hs, ?_⟩
    rw [Matrix.mulVec_mulVec]
  · intro c hc
    refine ⟨Matrix.of fun b b' => star (f b) ⬝ᵥ (c *ᵥ f b'), fun α β b b' => ?_⟩
    have hc1 : c *ᵥ (y β *ᵥ f b') = y β *ᵥ (c *ᵥ f b') := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mem_comm.1 (hyD β) c hc]
    show star (y α *ᵥ f b) ⬝ᵥ (c *ᵥ (y β *ᵥ f b')) = _
    rw [hc1, ip_mulVec', Matrix.mulVec_mulVec,
      hsch _ (mul_mem (comm_star hC (hyD α)) (hyD β)) _ (hfmem b) _ (hSC c hc _ (hfmem b')), hω]
    by_cases h1 : α = β <;> simp [h1]
  · intro w' hw'
    refine ⟨Matrix.of fun α β => star f0 ⬝ᵥ (((y α)ᴴ * w' * y β) *ᵥ f0), fun α β b b' => ?_⟩
    show star (y α *ᵥ f b) ⬝ᵥ (w' *ᵥ (y β *ᵥ f b')) = _
    rw [ip_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hsch _ (mul_mem (mul_mem (comm_star hC (hyD α)) hw') (hyD β)) _ (hfmem b) _ (hfmem b'), hfon]
    by_cases h1 : b = b' <;> simp [h1, mul_comm]
  · intro p
    show star (y p.1 *ᵥ f p.2) = y p.1 *ᵥ f p.2
    rw [star_mulVec_map, hyr, hfreal]
  · intro s hs
    exact Submodule.subset_span ⟨1, one_mem _, s, hs, by simp⟩
  · intro U hU hSU
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, s, hs, rfl⟩
    exact hU w hw s (hSU hs)
theorem exists_rsectors (hC : ∀ c ∈ C, cᴴ ∈ C) (hCr : ∀ c ∈ C, c.map conj ∈ C) (hRM : RealMin C)
    (U : Submodule ℂ (ι → ℂ)) (hUconj : ConjClosed U)
    (hUC : Inv (C : Set (Matrix ι ι ℂ)) U) (hUD : Inv (comm C : Set (Matrix ι ι ℂ)) U) :
    ∃ (r : ℕ) (σ : Fin r → RSector C),
      (∀ l, (σ l).T ≤ U) ∧
      (∀ l l', l ≠ l' → ∀ u ∈ (σ l).T, ∀ v ∈ (σ l').T, star u ⬝ᵥ v = 0) ∧
      (∀ v ∈ U, v = ∑ l, ∑ p, (star ((σ l).e p) ⬝ᵥ v) • (σ l).e p) := by
  induction U using WellFoundedLT.induction with
  | _ U ih =>
  by_cases hU0 : U = ⊥
  · subst hU0
    refine ⟨0, Fin.elim0, fun l => l.elim0, fun l => l.elim0, ?_⟩
    intro v hv
    have : v = 0 := by simpa using hv
    simp [this]
  · obtain ⟨S, hSU, hS, f0, hf0S, hf0r, hf0⟩ := hRM U hUconj hUC hUD hU0
    obtain ⟨σ, hST, hσ⟩ := exists_rsector hC hCr hS hf0S hf0r hf0
    have hTU : σ.T ≤ U := hσ U hUD hSU
    set R : Submodule ℂ (ι → ℂ) := U ⊓ perp σ.T with hR
    have hRC : Inv (C : Set (Matrix ι ι ℂ)) R := fun c hc v hv =>
      ⟨hUC c hc v hv.1, (σ.invC.perp (fun M hM => hC M hM)) c hc v hv.2⟩
    have hRD : Inv (comm C : Set (Matrix ι ι ℂ)) R := fun c hc v hv =>
      ⟨hUD c hc v hv.1, (σ.invD.perp (fun M hM => comm_star hC hM)) c hc v hv.2⟩
    have hRU : R < U := by
      refine lt_of_le_of_ne inf_le_left fun h => ?_
      obtain ⟨t, htS, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.1
      have htT : t ∈ σ.T := hST htS
      have htR : t ∈ R := by rw [h]; exact hSU htS
      have := ip_zero_of_perp htR.2 htT
      exact ht0 (dotProduct_star_self_eq_zero.1 this)
    have hTconj : ConjClosed σ.T := by
      intro v hv
      rw [σ.cover v hv, star_sum]
      refine Submodule.sum_mem _ fun p _ => ?_
      rw [star_smul_vec, σ.e_real p]
      exact Submodule.smul_mem _ _ (σ.e_mem p)
    have hRconj : ConjClosed R := by
      intro v hv
      refine ⟨hUconj v hv.1, fun u hu => ?_⟩
      have h1 := hv.2 (star u) (hTconj u hu)
      have h2 : star u ⬝ᵥ star v = star (u ⬝ᵥ v) := by
        simp [dotProduct, star_sum]
      rw [h2]
      have h3 : u ⬝ᵥ v = 0 := by simpa using h1
      rw [h3]; simp
    obtain ⟨r, σ', hT', horth', hcover'⟩ := ih R hRU hRconj hRC hRD
    refine ⟨r + 1, Fin.cons σ σ', ?_, ?_, ?_⟩
    · intro l
      refine Fin.cases ?_ (fun l => ?_) l
      · simpa using hTU
      · simpa using (hT' l).trans inf_le_left
    · intro l l'
      refine Fin.cases ?_ (fun l => ?_) l <;> refine Fin.cases ?_ (fun l' => ?_) l'
      · intro hne; exact absurd rfl hne
      · intro _ u hu v hv
        have hu' : u ∈ σ.T := by simpa using hu
        have hv' : v ∈ (σ' l').T := by simpa using hv
        exact (hT' l' hv').2 u hu'
      · intro _ u hu v hv
        have hu' : u ∈ (σ' l).T := by simpa using hu
        have hv' : v ∈ σ.T := by simpa using hv
        exact ip_zero_of_perp (hT' l hu').2 hv'
      · intro hne u hu v hv
        have hu' : u ∈ (σ' l).T := by simpa using hu
        have hv' : v ∈ (σ' l').T := by simpa using hv
        exact horth' l l' (fun h => hne (congrArg Fin.succ h)) u hu' v hv'
    · intro v hv
      set t : ι → ℂ := ∑ p, (star (σ.e p) ⬝ᵥ v) • σ.e p with ht
      have htT : t ∈ σ.T := Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (σ.e_mem p)
      have het : ∀ p, star (σ.e p) ⬝ᵥ t = star (σ.e p) ⬝ᵥ v := by
        intro p
        simp [ht, dotProduct_sum, dotProduct_smul, σ.onb]
      have hexp : ∀ u ∈ σ.T, ∀ w : ι → ℂ,
          star u ⬝ᵥ w = ∑ p, star (star (σ.e p) ⬝ᵥ u) * (star (σ.e p) ⬝ᵥ w) := by
        intro u hu w
        conv_lhs => rw [σ.cover u hu]
        simp [star_sum, sum_dotProduct, star_smul, smul_dotProduct]
      have hr : v - t ∈ R := by
        refine ⟨Submodule.sub_mem _ hv (hTU htT), fun u hu => ?_⟩
        rw [dotProduct_sub, hexp u hu v, hexp u hu t]
        simp [het]
      have h1 := hcover' (v - t) hr
      have h2 : ∀ l p, star ((σ' l).e p) ⬝ᵥ (v - t) = star ((σ' l).e p) ⬝ᵥ v := by
        intro l p
        rw [dotProduct_sub, ip_zero_of_perp (hT' l ((σ' l).e_mem p)).2 htT, sub_zero]
      have h3 : v - t = ∑ l, ∑ p, (star ((σ' l).e p) ⬝ᵥ v) • (σ' l).e p := by
        refine h1.trans (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => ?_)
        rw [h2]
      rw [Fin.sum_univ_succ]
      show v = ∑ p, (star (σ.e p) ⬝ᵥ v) • σ.e p +
        ∑ l : Fin r, ∑ p, (star ((σ' l).e p) ⬝ᵥ v) • (σ' l).e p
      rw [← h3, ← ht]
      abel

theorem exists_real_isotypic_coordinates (hC : ∀ c ∈ C, cᴴ ∈ C) (hCr : ∀ c ∈ C, c.map conj ∈ C)
    (hRM : RealMin C) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix ι (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ W.map conj = W ∧
      ∀ M : Matrix ι ι ℂ, M ∈ C ↔
        ∃ X : ∀ l, Matrix (Fin (b l)) (Fin (b l)) ℂ,
          Wᴴ * M * W = blockOp (fun l : Fin r => Fin (a l)) X := by
  obtain ⟨r, σ, -, horth, hcover⟩ := exists_rsectors hC hCr hRM ⊤ (fun v _ => Submodule.mem_top)
    (fun _ _ _ _ => Submodule.mem_top) (fun _ _ _ _ => Submodule.mem_top)
  let E : (Idx (fun l : Fin r => Fin (σ l).a) (fun l : Fin r => Fin (σ l).m)) → ι → ℂ :=
    fun k => (σ k.1).e k.2
  let W : Matrix ι (Idx (fun l : Fin r => Fin (σ l).a) (fun l : Fin r => Fin (σ l).m)) ℂ :=
    Matrix.of fun i k => E k i
  have hent : ∀ M : Matrix ι ι ℂ, ∀ k k', (Wᴴ * M * W) k k' = star (E k) ⬝ᵥ (M *ᵥ E k') := by
    intro M k k'
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, W,
      Matrix.of_apply, Pi.star_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hon : ∀ k k', star (E k) ⬝ᵥ E k' = if k = k' then 1 else 0 := by
    rintro ⟨l, p⟩ ⟨l', q⟩
    by_cases h : l = l'
    · subst h
      have := (σ l).onb p q
      show star ((σ l).e p) ⬝ᵥ (σ l).e q = _
      rw [this]
      simp
    · have hne : (⟨l, p⟩ : Idx (fun l : Fin r => Fin (σ l).a) (fun l : Fin r => Fin (σ l).m)) ≠
          ⟨l', q⟩ := fun hh => h (congrArg Sigma.fst hh)
      simp only [hne, ite_false]
      exact horth l l' h _ ((σ l).e_mem p) _ ((σ l').e_mem q)
  have W1 : Wᴴ * W = 1 := by
    ext k k'
    have := hent 1 k k'
    rw [Matrix.mul_one, Matrix.one_mulVec, hon] at this
    rw [this, Matrix.one_apply]
  have W2 : W * Wᴴ = 1 := by
    ext i j
    have h := congrFun (hcover (Pi.single j 1) Submodule.mem_top) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply, Matrix.one_apply]
    rw [Pi.single_apply] at h
    simp only [Finset.sum_apply, Pi.smul_apply, dotProduct_single, smul_eq_mul, Pi.star_apply,
      mul_one] at h
    refine Eq.trans ?_ h.symm
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => ?_
    exact mul_comm _ _
  have hcross : ∀ (𝒮 : Set (Matrix ι ι ℂ)), (∀ l, Inv 𝒮 (σ l).T) → ∀ M ∈ 𝒮, ∀ k k' : Idx
      (fun l : Fin r => Fin (σ l).a) (fun l : Fin r => Fin (σ l).m), k.1 ≠ k'.1 →
      star (E k) ⬝ᵥ (M *ᵥ E k') = 0 := by
    intro 𝒮 hinv M hM k k' hne
    exact horth k.1 k'.1 hne _ ((σ k.1).e_mem k.2) _ (hinv k'.1 M hM _ ((σ k'.1).e_mem k'.2))
  have hC3 : ∀ c ∈ C, ∃ X : ∀ l, Matrix (Fin (σ l).m) (Fin (σ l).m) ℂ,
      Wᴴ * c * W = blockOp (fun l : Fin r => Fin (σ l).a) X := by
    intro c hc
    choose X hX using fun l => (σ l).cblock c hc
    refine ⟨X, ?_⟩
    ext ⟨l, α, b⟩ ⟨l', β, b'⟩
    rw [hent]
    by_cases h : l = l'
    · subst h
      rw [blockOp_apply_same]
      exact hX l α β b b'
    · rw [blockOp_apply_ne _ h]
      exact hcross C (fun l => (σ l).invC) c hc ⟨l, α, b⟩ ⟨l', β, b'⟩ h
  have hD4 : ∀ y ∈ comm C, ∃ Y : ∀ l, Matrix (Fin (σ l).a) (Fin (σ l).a) ℂ,
      Wᴴ * y * W = Matrix.blockDiagonal'
        (fun l => Y l ⊗ₖ (1 : Matrix (Fin (σ l).m) (Fin (σ l).m) ℂ)) := by
    intro y hy
    choose Y hY using fun l => (σ l).dblock y hy
    refine ⟨Y, ?_⟩
    ext ⟨l, α, b⟩ ⟨l', β, b'⟩
    rw [hent]
    by_cases h : l = l'
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply]
      refine (hY l α β b b').trans ?_
      by_cases hb : b = b' <;> simp [hb]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact hcross (comm C : Set (Matrix ι ι ℂ)) (fun l => (σ l).invD) y hy ⟨l, α, b⟩ ⟨l', β, b'⟩ h
  have Wr : W.map conj = W := by
    ext i k
    have := congrFun ((σ k.1).e_real k.2) i
    simpa [W, E, Pi.star_apply, Complex.star_def] using this
  refine ⟨r, fun l => (σ l).a, fun l => (σ l).m, W, fun l => (σ l).ha, W1, W2, Wr, fun M => ⟨hC3 M, ?_⟩⟩
  rintro ⟨X, hX⟩
  refine FormalResearch.FrameFree.Twirls.bicommutant_mem C hC M fun Y hY => ?_
  have hYc : Y ∈ comm C := mem_comm.2 fun c hc => (hY c hc).symm
  obtain ⟨Yb, hYb⟩ := hD4 Y hYc
  have key : ∀ P Q : Matrix ι ι ℂ, P * Q = W * ((Wᴴ * P * W) * (Wᴴ * Q * W)) * Wᴴ := by
    intro P Q
    have : W * ((Wᴴ * P * W) * (Wᴴ * Q * W)) * Wᴴ = (W * Wᴴ) * P * (W * Wᴴ) * Q * (W * Wᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [this, W2]
    simp
  have hcomm : Matrix.blockDiagonal'
        (fun l => Yb l ⊗ₖ (1 : Matrix (Fin (σ l).m) (Fin (σ l).m) ℂ)) *
      blockOp (fun l : Fin r => Fin (σ l).a) X =
      blockOp (fun l : Fin r => Fin (σ l).a) X * Matrix.blockDiagonal'
        (fun l => Yb l ⊗ₖ (1 : Matrix (Fin (σ l).m) (Fin (σ l).m) ℂ)) := by
    unfold blockOp
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext l
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_one]
  rw [key Y M, key M Y, hYb, hX, hcomm]


end RealStructure

end FormalResearch.QIB
