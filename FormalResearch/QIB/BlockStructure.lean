import Mathlib
import FormalResearch.FrameFree.TwirlsBicommutant
import FormalResearch.QIB.BlockOps

/-!
# Isotypic coordinates for a `*`-closed algebra of matrices (structure theorem behind `lem:blockdecomp`)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis on any group, no new axiom).

**`exists_isotypic_coordinates`.**  Let `C ⊆ M_ι(ℂ)` be a unital subalgebra closed under the conjugate
transpose (for instance the commutant of any conjugate-transpose-closed set `G` of matrices, in
particular of any group of unitaries).  Then there are a number `r` of sectors, positive sizes
`a_l`, multiplicities `b_l` and a *unitary change of basis* `W : ι ← Σ l, Fin a_l × Fin b_l`
(`Wᴴ W = 1 = W Wᴴ`) such that
`M ∈ C ↔ ∃ X, Wᴴ M W = blockOp (fun l => Fin a_l) X`, i.e. `C = ⊕_l I_{a_l} ⊗ M_{b_l}(ℂ)` in the
coordinates `W`.  This is exactly the shape `IsotypicInvariants` of `BlockDecomp.lean` asks for; the
transport to a group `G` is in `BlockCoordinates.lean`.

Route (von Neumann / Wedderburn style, no characters, no Haar measure, no Wedderburn-Artin from
Mathlib; the double commutant theorem is `FrameFree.Twirls.bicommutant_mem`).  Write `D = C'` for the
commutant (again `*`-closed).

1. `schur`: if `S` is a minimal nonzero `C`-invariant subspace and `y ∈ D`, the compression of `y` to
   `S` is a scalar (an eigenvalue of the compression exists over `ℂ`; its eigenspace is `C`-invariant).
2. `exists_sector`: for such `S`, the subspace `T = D·S` has an orthonormal frame `e_{(α,b)} = y_α f_b`
   (`f_b` an orthonormal basis of `S`, `y_α ∈ D` with `y_α f_0` an orthonormal basis of `D f_0`),
   spanning `T`, in which `C` acts as `I ⊗ X` (`Sector.cblock`) and `D` as `Y ⊗ I` (`Sector.dblock`).
3. `exists_sectors`: strong induction on `U` (bi-invariant): peel `T = D·S`, pass to
   `U ⊓ T^⊥` (again `C`- and `D`-invariant because both algebras are `*`-closed).
4. `exists_isotypic_coordinates`: glue the sectors into one unitary `W`; the inclusion `C ⊆ blockOps`
   is the block form of `Sector.cblock`; the reverse inclusion is the double commutant theorem, since
   `blockOp X` commutes with `Wᴴ y W = ⊕ Y_l ⊗ I` for every `y ∈ D`.

The vector spaces are `ι → ℂ` with the standard Hermitian form `star v ⬝ᵥ w`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped Kronecker ComplexOrder

namespace FormalResearch.QIB

section Basics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ip_mulVec (M : Matrix ι ι ℂ) (v w : ι → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (Mᴴ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem ip_star_comm (v w : ι → ℂ) : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by
  simp [dotProduct, mul_comm, star_sum]

/-- Orthonormal basis of a subspace of `ℂ^ι` for the standard Hermitian form. -/
theorem exists_onb (U : Submodule ℂ (ι → ℂ)) :
    ∃ (m : ℕ) (g : Fin m → ι → ℂ), (∀ i, g i ∈ U) ∧
      (∀ i j, star (g i) ⬝ᵥ g j = if i = j then 1 else 0) ∧
      ∀ v ∈ U, v = ∑ i, (star (g i) ⬝ᵥ v) • g i := by
  let U' : Submodule ℂ (EuclideanSpace ℂ ι) :=
    U.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ) : EuclideanSpace ℂ ι →ₗ[ℂ] (ι → ℂ))
  let b := stdOrthonormalBasis ℂ U'
  have key : ∀ (x y : EuclideanSpace ℂ ι), inner ℂ x y = star x.ofLp ⬝ᵥ y.ofLp := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  refine ⟨_, fun i => ((b i : U') : EuclideanSpace ℂ ι).ofLp, ?_, ?_, ?_⟩
  · intro i
    exact (b i).2
  · intro i j
    have h := (orthonormal_iff_ite.1 b.orthonormal) i j
    rw [Submodule.coe_inner, key] at h
    exact h
  · intro v hv
    have hx : (WithLp.toLp 2 v : EuclideanSpace ℂ ι) ∈ U' := hv
    have h := b.sum_repr' (⟨_, hx⟩ : U')
    have h2 := congrArg (fun z : U' => (z : EuclideanSpace ℂ ι).ofLp) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul] at h2
    refine h2.symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_inner, key]

/-- A finite orthonormal family expands every vector of its span. -/
theorem expand_of_mem_span {P : Type*} [Fintype P] [DecidableEq P] (e : P → ι → ℂ)
    (he : ∀ p q, star (e p) ⬝ᵥ e q = if p = q then 1 else 0) {v : ι → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range e)) : v = ∑ p, (star (e p) ⬝ᵥ v) • e p := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    simp [he]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [dotProduct_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul c x _ hx =>
    simp only [dotProduct_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← hx]

/-- Orthogonal complement. -/
def perp (U : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {w | ∀ u ∈ U, star u ⬝ᵥ w = 0}
  add_mem' := by
    intro a b ha hb u hu
    rw [dotProduct_add, ha u hu, hb u hu, add_zero]
  zero_mem' := by intro u _; simp
  smul_mem' := by
    intro c w hw u hu
    rw [dotProduct_smul, hw u hu, smul_zero]

theorem mem_perp {U : Submodule ℂ (ι → ℂ)} {w : ι → ℂ} :
    w ∈ perp U ↔ ∀ u ∈ U, star u ⬝ᵥ w = 0 := Iff.rfl

/-- Invariance of a subspace under a set of matrices. -/
def Inv (S : Set (Matrix ι ι ℂ)) (U : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ M ∈ S, ∀ v ∈ U, M *ᵥ v ∈ U

theorem Inv.perp {S : Set (Matrix ι ι ℂ)} (hS : ∀ M ∈ S, Mᴴ ∈ S) {U : Submodule ℂ (ι → ℂ)}
    (hU : Inv S U) : Inv S (perp U) := by
  intro M hM w hw u hu
  rw [ip_mulVec]
  exact hw _ (hU _ (hS M hM) u hu)

end Basics


section Schur

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Subalgebra ℂ (Matrix ι ι ℂ))

/-- The commutant of `C`. -/
abbrev comm : Subalgebra ℂ (Matrix ι ι ℂ) := Subalgebra.centralizer ℂ (C : Set (Matrix ι ι ℂ))

variable {C}

theorem mem_comm {y : Matrix ι ι ℂ} : y ∈ comm C ↔ ∀ c ∈ C, c * y = y * c :=
  Subalgebra.mem_centralizer_iff ℂ

theorem comm_star (hC : ∀ c ∈ C, cᴴ ∈ C) {y : Matrix ι ι ℂ} (hy : y ∈ comm C) : yᴴ ∈ comm C := by
  rw [mem_comm] at hy ⊢
  intro c hc
  have h2 := congrArg Matrix.conjTranspose (hy cᴴ (hC c hc))
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose] at h2
  exact h2.symm

/-- A minimal nonzero `C`-invariant subspace. -/
def IsMinInv (C : Subalgebra ℂ (Matrix ι ι ℂ)) (S : Submodule ℂ (ι → ℂ)) : Prop :=
  S ≠ ⊥ ∧ Inv (C : Set _) S ∧ ∀ S', S' ≤ S → Inv (C : Set _) S' → S' = ⊥ ∨ S' = S

/-- **Schur's lemma** (Hermitian-form version): on a minimal invariant subspace `S`, the compression
of every `y` in the commutant is a scalar. -/
theorem schur (hC : ∀ c ∈ C, cᴴ ∈ C) {S : Submodule ℂ (ι → ℂ)} (hS : IsMinInv C S)
    {y : Matrix ι ι ℂ} (hy : y ∈ comm C) :
    ∃ μ : ℂ, ∀ s ∈ S, ∀ t ∈ S, star s ⬝ᵥ (y *ᵥ t) = μ * (star s ⬝ᵥ t) := by
  obtain ⟨hS0, hSC, hmin⟩ := hS
  obtain ⟨m, f, hfmem, hfon, hfspan⟩ := exists_onb S
  have hm : m ≠ 0 := by
    rintro rfl
    apply hS0
    rw [eq_bot_iff]
    intro v hv
    rw [hfspan v hv]
    simp
  have : NeZero m := ⟨hm⟩
  let X : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b => star (f a) ⬝ᵥ (y *ᵥ f b)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' X)
  obtain ⟨u, hu⟩ := hμ.exists_hasEigenvector
  have hXu : X *ᵥ u = μ • u := by
    have := hu.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  have hu0 : u ≠ 0 := hu.2
  refine ⟨μ, ?_⟩
  -- the eigen-subspace of the compression
  let K : Submodule ℂ (ι → ℂ) :=
    { carrier := {s | s ∈ S ∧ ∀ t ∈ S, star t ⬝ᵥ (y *ᵥ s) = μ * (star t ⬝ᵥ s)}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨S.add_mem ha hb, fun t ht => ?_⟩
        rw [Matrix.mulVec_add, dotProduct_add, dotProduct_add, ha' t ht, hb' t ht, mul_add]
      zero_mem' := by
        refine ⟨S.zero_mem, fun t _ => ?_⟩
        simp
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨S.smul_mem c ha, fun t ht => ?_⟩
        rw [Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, ha' t ht]
        simp only [smul_eq_mul]; ring }
  have hKS : K ≤ S := fun s hs => hs.1
  have hKC : Inv (C : Set _) K := by
    rintro c hc s ⟨hs, hs'⟩
    refine ⟨hSC c hc s hs, fun t ht => ?_⟩
    have hcy : y *ᵥ (c *ᵥ s) = c *ᵥ (y *ᵥ s) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (mem_comm.1 hy c hc)]
    rw [hcy, ip_mulVec, hs' _ (hSC _ (hC c hc) t ht), ip_mulVec c t s]
  set v : ι → ℂ := ∑ b, u b • f b with hv
  have hvS : v ∈ S := S.sum_mem fun b _ => S.smul_mem _ (hfmem b)
  have hfv : ∀ a, star (f a) ⬝ᵥ v = u a := by
    intro a
    simp [hv, dotProduct_sum, dotProduct_smul, hfon]
  have hXv : ∀ a, star (f a) ⬝ᵥ (y *ᵥ v) = μ * u a := by
    intro a
    have h1 : μ * u a = ∑ b, X a b * u b := by
      have := congrFun hXu a
      exact this.symm
    rw [h1, hv, Matrix.mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm]
    rfl
  have hexp : ∀ t ∈ S, ∀ w : ι → ℂ,
      star t ⬝ᵥ w = ∑ a, star (star (f a) ⬝ᵥ t) * (star (f a) ⬝ᵥ w) := by
    intro t ht w
    conv_lhs => rw [hfspan t ht]
    simp [star_sum, sum_dotProduct, star_smul, smul_dotProduct]
  have hvK : v ∈ K := by
    refine ⟨hvS, fun t ht => ?_⟩
    rw [hexp t ht, hexp t ht v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hXv, hfv]
    ring
  have hKne : K ≠ ⊥ := by
    intro h
    have : v = 0 := by
      have : v ∈ (⊥ : Submodule ℂ (ι → ℂ)) := h ▸ hvK
      simpa using this
    apply hu0
    funext a
    rw [← hfv a, this]
    simp
  have hKeq : K = S := (hmin K hKS hKC).resolve_left hKne
  intro s hs t ht
  have : t ∈ K := by rw [hKeq]; exact ht
  exact this.2 s hs


theorem ip_mulVec' (M : Matrix ι ι ℂ) (v w : ι → ℂ) :
    star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (Mᴴ *ᵥ w) := by
  rw [ip_mulVec, Matrix.conjTranspose_conjTranspose]

theorem Inv_span {𝒮 : Set (Matrix ι ι ℂ)} {X : Set (ι → ℂ)}
    (h : ∀ M ∈ 𝒮, ∀ v ∈ X, M *ᵥ v ∈ Submodule.span ℂ X) : Inv 𝒮 (Submodule.span ℂ X) := by
  intro M hM v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h M hM x hx
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx

/-- One isotypic sector: a bi-invariant subspace `T ≅ ℂ^a ⊗ ℂ^m` with an orthonormal frame `e`,
on which `C` acts on the second factor and its commutant on the first. -/
structure Sector (C : Subalgebra ℂ (Matrix ι ι ℂ)) where
  a : ℕ
  m : ℕ
  ha : 0 < a
  e : Fin a × Fin m → ι → ℂ
  T : Submodule ℂ (ι → ℂ)
  e_mem : ∀ p, e p ∈ T
  onb : ∀ p q, star (e p) ⬝ᵥ e q = if p = q then 1 else 0
  cover : ∀ v ∈ T, v = ∑ p, (star (e p) ⬝ᵥ v) • e p
  invC : Inv (C : Set (Matrix ι ι ℂ)) T
  invD : Inv (comm C : Set (Matrix ι ι ℂ)) T
  cblock : ∀ c ∈ C, ∃ X : Matrix (Fin m) (Fin m) ℂ, ∀ (α β : Fin a) (b b' : Fin m),
    star (e (α, b)) ⬝ᵥ (c *ᵥ e (β, b')) = if α = β then X b b' else 0
  dblock : ∀ y ∈ comm C, ∃ Y : Matrix (Fin a) (Fin a) ℂ, ∀ (α β : Fin a) (b b' : Fin m),
    star (e (α, b)) ⬝ᵥ (y *ᵥ e (β, b')) = if b = b' then Y α β else 0

theorem exists_sector (hC : ∀ c ∈ C, cᴴ ∈ C) {S : Submodule ℂ (ι → ℂ)} (hS : IsMinInv C S) :
    ∃ σ : Sector C, S ≤ σ.T ∧ ∀ U : Submodule ℂ (ι → ℂ), Inv (comm C : Set (Matrix ι ι ℂ)) U →
      S ≤ U → σ.T ≤ U := by
  have hS' := hS
  obtain ⟨hS0, hSC, hmin⟩ := hS
  obtain ⟨m, f, hfmem, hfon, hfspan⟩ := exists_onb S
  have hm : m ≠ 0 := by
    rintro rfl
    apply hS0
    rw [eq_bot_iff]
    intro v hv
    rw [hfspan v hv]
    simp
  have : NeZero m := ⟨hm⟩
  set f0 : ι → ℂ := f 0 with hf0def
  have hf0S : f0 ∈ S := hfmem 0
  have hf0 : star f0 ⬝ᵥ f0 = 1 := by simpa using hfon 0 0
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
  obtain ⟨a, g, hgmem, hgon, hgspan⟩ := exists_onb M
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      have := hgspan f0 hf0M
      rw [this] at hf0
      simp at hf0
    · exact h
  choose y hyD hyg using fun α => hgmem α
  -- Schur: compression to `S` of `w ∈ D` is the scalar `⟨f0, w f0⟩`
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
  refine ⟨⟨a, m, ha, fun p => y p.1 *ᵥ f p.2, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
  · intro s hs
    exact Submodule.subset_span ⟨1, one_mem _, s, hs, by simp⟩
  · intro U hU hSU
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, s, hs, rfl⟩
    exact hU w hw s (hSU hs)

theorem ip_zero_of_perp {T : Submodule ℂ (ι → ℂ)} {w t : ι → ℂ} (hw : w ∈ perp T) (ht : t ∈ T) :
    star w ⬝ᵥ t = 0 := by
  rw [ip_star_comm, hw t ht]
  simp

theorem exists_sectors (hC : ∀ c ∈ C, cᴴ ∈ C) (U : Submodule ℂ (ι → ℂ))
    (hUC : Inv (C : Set (Matrix ι ι ℂ)) U) (hUD : Inv (comm C : Set (Matrix ι ι ℂ)) U) :
    ∃ (r : ℕ) (σ : Fin r → Sector C),
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
  · obtain ⟨S, hSU, hS⟩ : ∃ S ≤ U, IsMinInv C S := by
      obtain ⟨S, hS, hSmin⟩ := (wellFounded_lt (α := Submodule ℂ (ι → ℂ))).has_min
        {S | S ≤ U ∧ S ≠ ⊥ ∧ Inv (C : Set (Matrix ι ι ℂ)) S} ⟨U, le_rfl, hU0, hUC⟩
      refine ⟨S, hS.1, hS.2.1, hS.2.2, fun S' hS' hinv => ?_⟩
      by_cases h : S' = ⊥
      · exact Or.inl h
      · right
        by_contra hne
        exact hSmin S' ⟨hS'.trans hS.1, h, hinv⟩ (lt_of_le_of_ne hS' hne)
    obtain ⟨σ, hST, hσ⟩ := exists_sector hC hS
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
    obtain ⟨r, σ', hT', horth', hcover'⟩ := ih R hRU hRC hRD
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

end Schur

section Assemble

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Subalgebra ℂ (Matrix ι ι ℂ)}

theorem exists_isotypic_coordinates (hC : ∀ c ∈ C, cᴴ ∈ C) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix ι (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      ∀ M : Matrix ι ι ℂ, M ∈ C ↔
        ∃ X : ∀ l, Matrix (Fin (b l)) (Fin (b l)) ℂ,
          Wᴴ * M * W = blockOp (fun l : Fin r => Fin (a l)) X := by
  obtain ⟨r, σ, -, horth, hcover⟩ := exists_sectors hC ⊤ (fun _ _ _ _ => Submodule.mem_top)
    (fun _ _ _ _ => Submodule.mem_top)
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
  refine ⟨r, fun l => (σ l).a, fun l => (σ l).m, W, fun l => (σ l).ha, W1, W2, fun M => ⟨hC3 M, ?_⟩⟩
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

end Assemble

end FormalResearch.QIB
