import Mathlib
import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.Sharing
import FormalResearch.FrameFree.OneCopy
import FormalResearch.FrameFree.Zariski
import FormalResearch.FrameFree.TwirlsTwirl

/-!
# What one copy sees (Paper P, `thm:onecopy` (a), (b)) via the Haar-free twirl

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved**.

* `thm:onecopy` (a): `FKΘs_eq_zero_iff_twirl_mul_eq_zero` and `..._trace_eq_zero`: `F_K^π(ψ) = 0` iff the
  one-copy twirls `Z, Z'` of `|ψ⟩⟨ψ|`, `|Θψ⟩⟨Θψ|` satisfy `Z Z' = 0` (equivalently `Tr(Z Z') = 0`: orthogonal
  supports).  `F_K^π = 0 ⟹ ZZ' = 0` is a convex-hull argument; the converse is a compactness argument on
  `SU(2)^β` (`ip_eq_zero_of_twirl_pairing_zero`).  Neither uses Schur-Weyl.
* `thm:onecopy` (b): blocks of at most two spins: `onecopy_twirl_eq_of_small_blocks` (twirls coincide, from
  the slot-permutation criterion of `TwirlsTwirl`) and `FKΘs_pos_of_small_blocks` (`F_K^π > 0` for `ψ ≠ 0`).
* `thm:onecopy` (c) is `OneCopy.FKΘs_eq_zero_of_odd` and `FKΘs_eq_zero_of_chiN`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped ComplexOrder
open FormalResearch.FrameFree.NQubit (Op1 Ψ rot Θ nsq)
open FormalResearch.FrameFree.Sharing (FKs FKΘs)

namespace FormalResearch.FrameFree.Twirls

section OneCopy

variable {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (g : Fin n → β)

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
def proj (ψ : Ψ n) : OpS (Fin n) := Matrix.vecMulVec ψ (star ψ)

theorem tensOp_mulVec (v : β → Op1) (ψ : Ψ n) :
    tensOp g v *ᵥ ψ = rot (fun i => v (g i)) ψ := rfl

theorem ip_eq_dotProduct (ψ φ : Ψ n) : NQubit.ip ψ φ = star ψ ⬝ᵥ φ := by
  simp [NQubit.ip, dotProduct]

theorem conj_proj (U : OpS (Fin n)) (ψ : Ψ n) : U * proj ψ * Uᴴ = proj (U *ᵥ ψ) := by
  rw [proj, proj, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem thetaConj_proj (ψ : Ψ n) : thetaConj (proj ψ) = proj (Θ ψ) := by
  have h1 : (proj ψ).map conj = Matrix.vecMulVec (star ψ) (star (star ψ)) := by
    ext x y; simp [proj, Matrix.vecMulVec_apply, mul_comm]
  have h2 : Θ ψ = epsOp (Fin n) *ᵥ star ψ := by
    funext x
    simp [Θ, epsOp, tensOp, Matrix.mulVec, dotProduct]
  rw [thetaConj, h1, h2, proj, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem proj_isHermitian (ψ : Ψ n) : (proj ψ)ᴴ = proj ψ := by
  ext x y; simp [proj, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

theorem trace_mul_proj (Z : OpS (Fin n)) (x : Ψ n) : (Z * proj x).trace = star x ⬝ᵥ Z *ᵥ x := by
  simp only [proj, Matrix.mul_vecMulVec, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- If `⟨ψ|(⊗ v_{g i}) x⟩ = 0` for all `SU(2)` frames, the twirl of `|ψ⟩⟨ψ|` annihilates `x`. -/
theorem IsTwirl.mulVec_eq_zero {ψ x : Ψ n} {Z : OpS (Fin n)} (hZ : IsTwirl g (proj ψ) Z)
    (h : ∀ v : β → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) →
      NQubit.ip ψ (rot (fun i => v (g i)) x) = 0) : Z *ᵥ x = 0 := by
  refine hZ.1 {W | W *ᵥ x = 0} ?_ ?_ ?_
  · exact isClosed_eq (Continuous.matrix_mulVec continuous_id continuous_const) continuous_const
  · intro A hA B hB a b _ _ _
    show (a • A + b • B) *ᵥ x = 0
    have hA' : A *ᵥ x = 0 := hA
    have hB' : B *ᵥ x = 0 := hB
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hA', hB', smul_zero, smul_zero,
      add_zero]
  · rintro U ⟨u, hu, rfl⟩
    show (tensOp g u * proj ψ * (tensOp g u)ᴴ) *ᵥ x = 0
    rw [conj_proj, proj, Matrix.vecMulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      tensOp_conjTranspose, tensOp_mulVec, ← ip_eq_dotProduct,
      h _ fun b => FormalResearch.FrameFree.NQubit.SU2_adjoint (hu b)]
    simp

/-- `F_K^π(ψ) = 0 ⟹` the one-copy twirls of `ψ` and `Θψ` have orthogonal supports (`Z Z' = 0`). -/
theorem twirl_mul_eq_zero_of_forall {ψ x : Ψ n} {Z Z' : OpS (Fin n)} (hZ : IsTwirl g (proj ψ) Z)
    (hZ' : IsTwirl g (proj x) Z')
    (h : ∀ v : β → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) →
      NQubit.ip ψ (rot (fun i => v (g i)) x) = 0) : Z * Z' = 0 := by
  have hx : Z *ᵥ x = 0 := hZ.mulVec_eq_zero g h
  have hZx : Z * proj x = 0 := by
    rw [proj, Matrix.mul_vecMulVec, hx]; simp
  refine hZ'.1 {W | Z * W = 0} ?_ ?_ ?_
  · exact isClosed_eq (continuous_const.matrix_mul continuous_id) continuous_const
  · intro A hA B hB a b _ _ _
    show Z * (a • A + b • B) = 0
    have hA' : Z * A = 0 := hA
    have hB' : Z * B = 0 := hB
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hA', hB', smul_zero, smul_zero, add_zero]
  · rintro U ⟨u, hu, rfl⟩
    show Z * (tensOp g u * proj x * (tensOp g u)ᴴ) = 0
    have := hZ.2 (tensOp g u) ⟨u, hu, rfl⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← this, Matrix.mul_assoc (tensOp g u) Z,
      hZx, Matrix.mul_zero, Matrix.zero_mul]

/-! ### The converse: a vanishing pairing with the twirl forces `⟨x|Uψ⟩ = 0` on all frames -/

theorem SU2_entry_le {u : Op1} (h : FormalResearch.FrameFree.NQubit.SU2 u) (i j : Fin 2) :
    ‖u i j‖ ≤ 1 := by
  have h1 := congrFun (congrFun h.1 j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Fin.sum_univ_two] at h1
  have h2 : ‖u i j‖ ^ 2 ≤ 1 := by
    have e : (‖u 0 j‖ ^ 2 + ‖u 1 j‖ ^ 2 : ℝ) = 1 := by
      have := congrArg Complex.re h1
      simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
        Complex.one_re] at this
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      linarith
    fin_cases i <;> simp <;> nlinarith [sq_nonneg ‖u 0 j‖, sq_nonneg ‖u 1 j‖]
  nlinarith [norm_nonneg (u i j)]

/-- `SU(2)` is compact (closed and bounded in the entries). -/
theorem isCompact_SU2 : IsCompact {u : Op1 | FormalResearch.FrameFree.NQubit.SU2 u} := by
  have hc : IsClosed {u : Op1 | FormalResearch.FrameFree.NQubit.SU2 u} := by
    have h1 : IsClosed {u : Op1 | uᴴ * u = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    have h2 : IsClosed {u : Op1 | u.det = 1} :=
      isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
    exact h1.inter h2
  have hk : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset hk hc ?_
  intro u hu i _ j _
  simpa using SU2_entry_le hu i j

theorem isCompact_frames :
    IsCompact {u : β → Op1 | ∀ b, FormalResearch.FrameFree.NQubit.SU2 (u b)} := by
  have := isCompact_univ_pi (fun _ : β => isCompact_SU2)
  convert this using 1
  ext u; simp

theorem continuous_tensOp : Continuous (fun u : β → Op1 => tensOp g u) := by
  refine continuous_matrix fun x y => ?_
  simp only [tensOp, Matrix.of_apply]
  exact continuous_finset_prod _ fun i _ =>
    (continuous_apply (y i)).comp ((continuous_apply (x i)).comp (continuous_apply (g i)))

theorem continuous_pairing (x ψ : Ψ n) :
    Continuous (fun u : β → Op1 => star x ⬝ᵥ (tensOp g u *ᵥ ψ)) := by
  have := (continuous_tensOp g).matrix_mulVec (continuous_const (y := ψ))
  unfold dotProduct
  exact continuous_finset_sum _ fun i _ => continuous_const.mul ((continuous_apply i).comp this)

theorem trace_proj_mul_proj (x y : Ψ n) :
    (proj x * proj y).trace = (star y ⬝ᵥ x) * (star x ⬝ᵥ y) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, proj, Matrix.vecMulVec_apply, dotProduct,
    Pi.star_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem re_trace_proj_mul_proj (x y : Ψ n) :
    (proj x * proj y).trace.re = Complex.normSq (star x ⬝ᵥ y) := by
  rw [trace_proj_mul_proj]
  have : star y ⬝ᵥ x = conj (star x ⬝ᵥ y) := by
    simp [dotProduct, mul_comm, map_sum]
  rw [this, mul_comm, Complex.mul_conj]
  simp

/-- **Positivity of the twirl on the orbit** (Haar-free).  If the twirl `Z` of `|ψ⟩⟨ψ|` has
`⟨x|Z|x⟩ = 0`, then `⟨x|(⊗ u_{g i}) ψ⟩ = 0` for every `SU(2)` frame `u`.  The proof covers the compact
frame space by finitely many translates of the open set where the overlap is at least half its
value at a putative nonvanishing frame, and applies the half-space `Re Tr(QW) ≥ c/2`. -/
theorem ip_eq_zero_of_twirl_pairing_zero {ψ x : Ψ n} {Z : OpS (Fin n)} (hZ : IsTwirl g (proj ψ) Z)
    (h0 : star x ⬝ᵥ Z *ᵥ x = 0) (u0 : β → Op1) (hu0 : ∀ b, FormalResearch.FrameFree.NQubit.SU2 (u0 b)) :
    NQubit.ip x (rot (fun i => u0 (g i)) ψ) = 0 := by
  by_contra hne
  set F : (β → Op1) → ℂ := fun u => star x ⬝ᵥ (tensOp g u *ᵥ ψ) with hFdef
  have hF : Continuous F := continuous_pairing g x ψ
  have hFu0 : F u0 = NQubit.ip x (rot (fun i => u0 (g i)) ψ) := by
    rw [hFdef]; simp only [tensOp_mulVec]; rw [ip_eq_dotProduct]
  set c : ℝ := Complex.normSq (F u0) with hc
  have hcpos : 0 < c := Complex.normSq_pos.2 (by rw [hFu0]; exact hne)
  set 𝔽 : Set (β → Op1) := {u | ∀ b, FormalResearch.FrameFree.NQubit.SU2 (u b)} with h𝔽
  have hcomp : IsCompact 𝔽 := isCompact_frames
  set O : 𝔽 → Set (β → Op1) := fun w =>
    {u | c / 2 < Complex.normSq (F (fun b => (w : β → Op1) b * u b))} with hO
  have hOopen : ∀ w, IsOpen (O w) := fun w =>
    isOpen_lt continuous_const (Complex.continuous_normSq.comp
      (hF.comp (continuous_pi fun b => continuous_const.matrix_mul (continuous_apply b))))
  have hcover : 𝔽 ⊆ ⋃ w, O w := by
    intro u hu
    have hw : (fun b => u0 b * (u b)ᴴ) ∈ 𝔽 := fun b =>
      FormalResearch.FrameFree.NQubit.SU2_mul (hu0 b) (FormalResearch.FrameFree.NQubit.SU2_adjoint (hu b))
    refine Set.mem_iUnion.2 ⟨⟨_, hw⟩, ?_⟩
    show c / 2 < Complex.normSq (F fun b => (u0 b * (u b)ᴴ) * u b)
    have : (fun b => (u0 b * (u b)ᴴ) * u b) = u0 := by
      funext b; rw [Matrix.mul_assoc, (hu b).1, Matrix.mul_one]
    rw [this]; linarith
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover O hOopen hcover
  set Q : OpS (Fin n) := ∑ w ∈ t, (tensOp g (w : β → Op1))ᴴ * proj x * tensOp g (w : β → Op1) with hQ
  have hQtr : ∀ W : OpS (Fin n), (Q * W).trace =
      ∑ w ∈ t, (proj x * (tensOp g (w : β → Op1) * W * (tensOp g (w : β → Op1))ᴴ)).trace := by
    intro W
    rw [hQ, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have key1 : c / 2 ≤ (Q * Z).trace.re := by
    refine hZ.le_re_trace g Q (c / 2) ?_
    rintro U ⟨u, hu, rfl⟩
    have hterm : ∀ w : 𝔽, (proj x * (tensOp g (w : β → Op1) * (tensOp g u * proj ψ * (tensOp g u)ᴴ) *
        (tensOp g (w : β → Op1))ᴴ)).trace.re =
        Complex.normSq (F fun b => (w : β → Op1) b * u b) := by
      intro w
      rw [conj_proj, conj_proj, re_trace_proj_mul_proj, Matrix.mulVec_mulVec, tensOp_mul]
    rw [hQtr, Complex.re_sum]
    simp only [hterm]
    obtain ⟨w0, hw0, hu0'⟩ : ∃ w0 ∈ t, u ∈ O w0 := by
      have := ht hu
      simpa using this
    calc c / 2 ≤ Complex.normSq (F fun b => (w0 : β → Op1) b * u b) := le_of_lt hu0'
      _ ≤ _ := Finset.single_le_sum (f := fun w : 𝔽 =>
          Complex.normSq (F fun b => (w : β → Op1) b * u b))
          (fun w _ => Complex.normSq_nonneg _) hw0
  have key2 : (Q * Z).trace = 0 := by
    rw [hQtr]
    refine Finset.sum_eq_zero fun w _ => ?_
    have hV : tensOp g (w : β → Op1) ∈ frameGroup g := ⟨w, w.2, rfl⟩
    have hcomm := hZ.2 _ hV
    have hVV : tensOp g (w : β → Op1) * (tensOp g (w : β → Op1))ᴴ = 1 :=
      mul_eq_one_comm.1 (frameGroup_unitary g hV)
    rw [hcomm, Matrix.mul_assoc, hVV, Matrix.mul_one, Matrix.trace_mul_comm, trace_mul_proj, h0]
  rw [key2] at key1
  simp at key1
  linarith

theorem star_dotProduct_comm (v w : Ψ n) : star v ⬝ᵥ w = conj (star w ⬝ᵥ v) := by
  simp [dotProduct, mul_comm, map_sum]

/-- `⟨ψ|U x⟩ = conj ⟨x|U† ψ⟩` for a frame operator `U`. -/
theorem ip_rot_adjoint (v : β → Op1) (ψ x : Ψ n) :
    NQubit.ip ψ (rot (fun i => v (g i)) x) =
      conj (NQubit.ip x (rot (fun i => (v (g i))ᴴ) ψ)) := by
  have e1 : rot (fun i => v (g i)) x = tensOp g v *ᵥ x := rfl
  have e2 : rot (fun i => (v (g i))ᴴ) ψ = (tensOp g v)ᴴ *ᵥ ψ := by
    rw [tensOp_conjTranspose]; rfl
  rw [e1, e2, ip_eq_dotProduct, ip_eq_dotProduct, star_dotProduct_comm ψ, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec]

theorem forall_ip_eq_zero_of_trace_eq_zero (ψ : Ψ n) {Z Z' : OpS (Fin n)}
    (hZ : IsTwirl g (proj ψ) Z) (hZ' : IsTwirl g (proj (Θ ψ)) Z') (h : (Z * Z').trace = 0) :
    ∀ v : β → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) →
      NQubit.ip ψ (rot (fun i => v (g i)) (Θ ψ)) = 0 := by
  intro u hu
  have h1 : (Z * Z').trace = (Z * proj (Θ ψ)).trace :=
    hZ'.trace_eq g Z fun U hU => (hZ.2 U hU).symm
  rw [h, trace_mul_proj] at h1
  have h2 := ip_eq_zero_of_twirl_pairing_zero g hZ h1.symm
  rw [ip_rot_adjoint, h2 _ fun b => FormalResearch.FrameFree.NQubit.SU2_adjoint (hu b)]
  simp

/-- **`thm:onecopy` (a).**  `F_K^π(ψ) = 0` iff the one-copy twirls of `ψ` and `Θψ` have orthogonal
supports (`Z Z' = 0`), for any twirls `Z`, `Z'` over `K_π`. -/
theorem FKΘs_eq_zero_iff_twirl_mul_eq_zero (ψ : Ψ n) {Z Z' : OpS (Fin n)}
    (hZ : IsTwirl g (proj ψ) Z) (hZ' : IsTwirl g (proj (Θ ψ)) Z') :
    FKΘs g ψ = 0 ↔ Z * Z' = 0 := by
  rw [OneCopy.FKΘs_eq_zero_iff]
  refine ⟨twirl_mul_eq_zero_of_forall g hZ hZ', fun hZZ => ?_⟩
  exact forall_ip_eq_zero_of_trace_eq_zero g ψ hZ hZ' (by rw [hZZ, Matrix.trace_zero])

/-- The same with the trace: `F_K^π(ψ) = 0 ⟺ Tr(Z Z') = 0`. -/
theorem FKΘs_eq_zero_iff_twirl_trace_eq_zero (ψ : Ψ n) {Z Z' : OpS (Fin n)}
    (hZ : IsTwirl g (proj ψ) Z) (hZ' : IsTwirl g (proj (Θ ψ)) Z') :
    FKΘs g ψ = 0 ↔ (Z * Z').trace = 0 := by
  rw [OneCopy.FKΘs_eq_zero_iff]
  refine ⟨fun h => ?_, forall_ip_eq_zero_of_trace_eq_zero g ψ hZ hZ'⟩
  rw [(FKΘs_eq_zero_iff_twirl_mul_eq_zero g ψ hZ hZ').1 ((OneCopy.FKΘs_eq_zero_iff g ψ).2 h),
    Matrix.trace_zero]

theorem FKΘs_nonneg (ψ : Ψ n) : 0 ≤ FKΘs g ψ :=
  Real.sSup_nonneg (by rintro r ⟨v, hv, rfl⟩; exact Complex.normSq_nonneg _)

/-- **`thm:onecopy` (b), twirls.**  If every block has at most two spins, the one-copy twirls of
`ψ` and `Θψ` coincide. -/
theorem onecopy_twirl_eq_of_small_blocks
    (hg : ∀ i j l, g i = g j → g j = g l → i = j ∨ j = l ∨ i = l) (ψ : Ψ n)
    {Z Z' : OpS (Fin n)} (hZ : IsTwirl g (proj ψ) Z) (hZ' : IsTwirl g (proj (Θ ψ)) Z') : Z = Z' := by
  rw [← thetaConj_proj] at hZ'
  exact twirl_thetaConj_eq_of_small_blocks g hg (proj_isHermitian ψ) hZ hZ'

theorem trace_twirl_eq_nsq {ψ : Ψ n} {Z : OpS (Fin n)} (hZ : IsTwirl g (proj ψ) Z) :
    Z.trace = (nsq ψ : ℂ) := by
  have h := hZ.trace_eq g 1 fun U _ => by simp
  rw [Matrix.one_mul, Matrix.one_mul, proj] at h
  have : (Matrix.vecMulVec ψ (star ψ)).trace = star ψ ⬝ᵥ ψ := by
    simp [Matrix.trace, dotProduct, Matrix.vecMulVec_apply, mul_comm]
  rw [h, this, ← ip_eq_dotProduct, FormalResearch.FrameFree.NQubit.ip_self]

/-- **`thm:onecopy` (b), positivity.**  If every block has at most two spins, `F_K^π(ψ) > 0` for every
nonzero `ψ`. -/
theorem FKΘs_pos_of_small_blocks (hg : ∀ i j l, g i = g j → g j = g l → i = j ∨ j = l ∨ i = l)
    (ψ : Ψ n) (hψ : 0 < nsq ψ) : 0 < FKΘs g ψ := by
  obtain ⟨Z, hZ⟩ := exists_twirl g (proj ψ)
  obtain ⟨Z', hZ'⟩ := exists_twirl g (proj (Θ ψ))
  have hEq := onecopy_twirl_eq_of_small_blocks g hg ψ hZ hZ'
  subst hEq
  refine lt_of_le_of_ne (FKΘs_nonneg g ψ) fun h0 => ?_
  have h1 := (FKΘs_eq_zero_iff_twirl_trace_eq_zero g ψ hZ hZ').1 h0.symm
  have hH := hZ.isHermitian g (proj_isHermitian ψ)
  have h2 : (Zᴴ * Z).trace = 0 := by rw [hH]; exact h1
  have h3 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h2
  have h4 := trace_twirl_eq_nsq g hZ
  rw [h3, Matrix.trace_zero] at h4
  have : (0 : ℝ) = nsq ψ := by exact_mod_cast h4
  linarith

end OneCopy







end FormalResearch.FrameFree.Twirls
