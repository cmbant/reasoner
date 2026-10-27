import FormalResearch.FrameFree.ZClosure
import FormalResearch.FrameFree.SupportRateHelstrom

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate InnerProductSpace BigOperators
open FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

/-!
# `ZClosureSup`, reduced to the Euclidean density of polynomial images

Namespace `FormalResearch.FrameFree.SupportRate`.

`ZClosureSup ψ` (`SupportRateHelstrom`) says that the supremum of `|⟨ψ|z⟩|²/‖z‖²` over the Zariski-closure cone of
the `SL(2,ℂ)^n`-orbit of `Θψ` is at most `F_C(ψ)`, the supremum over the orbit.  This is **equivalent** to
`lim R_k^{1/k} ≤ F_C` (the character space of the compressed-shift algebra contains the whole Zariski-closure
cone in the unit ball), so it is a genuine algebraic-geometry input: the Euclidean closure of a constructible
set equals its Zariski closure (Mumford, *Complex projective varieties*, 4.16).  The hypothesis
`PolyImageClosure` below is exactly that statement for images of polynomial maps `ℂ^κ → ℂ^ι`, with no reference to
`ψ`.

Proved here, **given `PolyImageClosure`** (no `sorry`, no other hypothesis):

* `fid_le_FCΘ`: `|⟨ψ|rot A Θψ⟩|² ≤ F_C(ψ) ‖rot A Θψ‖²` for *every* `A ∈ M₂(ℂ)^n`, singular or not (density of
  invertible matrices and continuity);
* `zClosureSup_of_polyImageClosure`: the tensor-power cone is the zero locus of the ideal of the polynomial image
  `{s · (A₁ ⊗ ⋯ ⊗ Aₙ) Θψ}` (`eval_eq_zero_of_pw_mem`), which `PolyImageClosure` places in the Euclidean closure of
  the image, on which the closed inequality `|⟨ψ|z⟩|² ≤ F_C ‖z‖²` holds;
* `supportRateUpper_of_polyImageClosure`, `tendsto_of_calibrated_of_polyImageClosure`: the corresponding forms of
  `SupportRateUpper` and `cor:calibrated`.
-/

namespace FormalResearch.FrameFree.SupportRate

open MvPolynomial

/-- **Euclidean density of a polynomial image in its Zariski closure** (Chevalley + Mumford 4.16, not proved
here): if every polynomial vanishing on the image of the polynomial map `Φ : ℂ^κ → ℂ^ι` vanishes at `z`, then
`z` is a limit of points of the image. -/
def PolyImageClosure : Prop :=
  ∀ (ι κ : Type) (Φ : ι → MvPolynomial κ ℂ) (z : ι → ℂ),
    (∀ p : MvPolynomial ι ℂ, (∀ t : κ → ℂ, eval (fun i => eval t (Φ i)) p = 0) → eval z p = 0) →
    z ∈ closure (Set.range fun (t : κ → ℂ) (i : ι) => eval t (Φ i))

/-! ### The inequality for every `A ∈ M₂(ℂ)^n` -/

theorem finite_det_eq_zero (M : Op1) : {ε : ℂ | (M + ε • (1 : Op1)).det = 0}.Finite := by
  have hq : (Polynomial.X ^ 2 + Polynomial.C (M 0 0 + M 1 1) * Polynomial.X + Polynomial.C M.det
      : Polynomial ℂ) ≠ 0 := by
    intro h
    have := congrArg (fun q : Polynomial ℂ => q.coeff 2) h
    simp at this
  refine (Polynomial.finite_setOfPred_isRoot hq).subset fun ε hε => ?_
  simp only [Set.mem_ofPred_eq] at hε ⊢
  rw [Matrix.det_fin_two] at hε
  rw [Matrix.det_fin_two]
  simp [Matrix.add_apply, Matrix.smul_apply] at hε ⊢
  linear_combination hε

theorem dense_det_ne_zero {n : ℕ} (A : Fin n → Op1) :
    Dense {ε : ℂ | ∀ i, (A i + ε • (1 : Op1)).det ≠ 0} := by
  have hfin : (⋃ i, {ε : ℂ | (A i + ε • (1 : Op1)).det = 0}).Finite :=
    Set.finite_iUnion fun i => finite_det_eq_zero (A i)
  refine (dense_univ.sdiff_finite hfin).mono fun ε hε => ?_
  simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, true_and] at hε
  exact hε

/-- `|⟨ψ|(A₁ ⊗ ⋯ ⊗ Aₙ) Θψ⟩|² ≤ F_C(ψ) ‖(A₁ ⊗ ⋯ ⊗ Aₙ) Θψ‖²` for every (possibly singular) `A`. -/
theorem fid_le_FCΘ {n : ℕ} (ψ : Ψ n) (A : Fin n → Op1) :
    Complex.normSq (ip ψ (rot A (Θ ψ))) ≤ Ceilings.FCΘ ψ * nsq (rot A (Θ ψ)) := by
  set H : (Fin n → Op1) → ℝ := fun B =>
    Ceilings.FCΘ ψ * nsq (rot B (Θ ψ)) - Complex.normSq (ip ψ (rot B (Θ ψ))) with hH
  have hHc : Continuous H :=
    (continuous_const.mul (Ceilings.continuous_nsq_rot _)).sub
      (Complex.continuous_normSq.comp (Ceilings.continuous_ip_rot ψ _))
  have hU : ∀ B : Fin n → Op1, (∀ i, (B i).det ≠ 0) → 0 ≤ H B := by
    intro B hB
    simp only [hH, sub_nonneg]
    by_cases hne : nsq (rot B (Θ ψ)) = 0
    · have := normSq_ip_le ψ (rot B (Θ ψ))
      rw [hne] at this ⊢
      simpa using this
    · have hpos : 0 < nsq (rot B (Θ ψ)) := lt_of_le_of_ne (Ceilings.nsq_nonneg' _) (Ne.symm hne)
      have := Ceilings.le_FC_det ψ (Θ ψ) B hB hne
      rw [div_le_iff₀ hpos] at this
      exact this
  set f : ℂ → ℝ := fun ε => H (fun i => A i + ε • (1 : Op1)) with hf
  have hfc : Continuous f := hHc.comp (by fun_prop)
  have hcl : IsClosed {ε : ℂ | 0 ≤ f ε} := isClosed_le continuous_const hfc
  have hsub : {ε : ℂ | ∀ i, (A i + ε • (1 : Op1)).det ≠ 0} ⊆ {ε : ℂ | 0 ≤ f ε} :=
    fun ε hε => hU _ hε
  have hall : ∀ ε, 0 ≤ f ε := by
    intro ε
    have := closure_minimal hsub hcl
    rw [(dense_det_ne_zero A).closure_eq] at this
    exact this (Set.mem_univ ε)
  have h0 := hall 0
  simpa [hf, hH] using h0

/-! ### The polynomial parametrisation of the cone `ℂ · M₂(ℂ)^n · Θψ` -/

/-- Parameters: a scalar (`none`) and the entries of `n` one-qubit matrices. -/
abbrev Par (n : ℕ) := Option (Fin n × Fin 2 × Fin 2)

/-- The matrices `A₁, …, Aₙ` read off from parameters. -/
def parMat {n : ℕ} (t : Par n → ℂ) : Fin n → Op1 := fun i => Matrix.of fun a b => t (some (i, a, b))

/-- Coordinate `x` of `s · (A₁ ⊗ ⋯ ⊗ Aₙ) Θψ`, as a polynomial in `(s, A)`. -/
noncomputable def orbitPoly {n : ℕ} (ψ : Ψ n) (x : Fin n → Fin 2) : MvPolynomial (Par n) ℂ :=
  X none * ∑ y, (∏ i, X (some (i, x i, y i))) * C (Θ ψ y)

theorem eval_orbitPoly {n : ℕ} (ψ : Ψ n) (t : Par n → ℂ) (x : Fin n → Fin 2) :
    eval t (orbitPoly ψ x) = t none * rot (parMat t) (Θ ψ) x := by
  simp [orbitPoly, rot, parMat, map_sum, map_prod]

theorem ip_smul {n : ℕ} (ψ u : Ψ n) (c : ℂ) : ip ψ (c • u) = c * ip ψ u := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem nsq_smul {n : ℕ} (u : Ψ n) (c : ℂ) : nsq (c • u) = Complex.normSq c * nsq u := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem isClosed_fid {n : ℕ} (ψ : Ψ n) (F : ℝ) :
    IsClosed {u : Ψ n | Complex.normSq (ip ψ u) ≤ F * nsq u} := by
  refine isClosed_le ?_ ?_
  · refine Complex.continuous_normSq.comp ?_
    unfold ip
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_apply x)
  · unfold nsq
    exact continuous_const.mul
      (continuous_finsetSum _ fun x _ => Complex.continuous_normSq.comp (continuous_apply x))

/-- **`ZClosureSup`, given the Euclidean density of polynomial images.** -/
theorem zClosureSup_of_polyImageClosure (h : PolyImageClosure) {n : ℕ} (ψ : Ψ n) :
    ZClosureSup ψ := by
  intro z hz
  have hmem : z ∈ closure (Set.range fun (t : Par n → ℂ) (x : Fin n → Fin 2) =>
      eval t (orbitPoly ψ x)) := by
    refine h _ _ (orbitPoly ψ) z fun p hp => ?_
    have hz' : ∀ k : ℕ, pw (WithLp.toLp 2 z : V (Fin n → Fin 2)) k ∈ W (orbitSet ψ) k := fun k => by
      rw [W_orbitSet]; exact hz k
    refine eval_eq_zero_of_pw_mem (orbitSet ψ) (WithLp.toLp 2 z) hz' p ?_
    rintro w ⟨g, hg, rfl⟩ c
    set t : Par n → ℂ := fun o => match o with | none => c | some (i, a, b) => g i a b with ht
    have hpm : parMat t = g := by
      funext i; ext a b; rfl
    have hfun : c • WithLp.ofLp (WithLp.toLp 2 (rot g (Θ ψ))) = fun x => eval t (orbitPoly ψ x) := by
      funext x
      rw [eval_orbitPoly, hpm]
      simp [ht]
    rw [hfun]
    exact hp t
  refine closure_minimal ?_ (isClosed_fid ψ (Ceilings.FCΘ ψ)) hmem
  rintro u ⟨t, rfl⟩
  have hu : (fun x => eval t (orbitPoly ψ x)) = t none • rot (parMat t) (Θ ψ) := by
    funext x; rw [eval_orbitPoly]; rfl
  show Complex.normSq (ip ψ (fun x => eval t (orbitPoly ψ x))) ≤
    Ceilings.FCΘ ψ * nsq (fun x => eval t (orbitPoly ψ x))
  rw [hu, ip_smul, nsq_smul, Complex.normSq_mul, ← mul_assoc, mul_comm _ (Complex.normSq (t none)),
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (fid_le_FCΘ ψ (parMat t)) (Complex.normSq_nonneg _)

/-- **`SupportRateUpper`** (hard half of `thm:supportrate`), given `PolyImageClosure`. -/
theorem supportRateUpper_of_polyImageClosure (h : PolyImageClosure) {n : ℕ} (ψ : Ψ n) :
    Helstrom.SupportRateUpper ψ :=
  supportRateUpper_of_zClosureSup ψ (zClosureSup_of_polyImageClosure h ψ)

/-- **`cor:calibrated`**, given `PolyImageClosure`: if `F_C(ψ) = F_K(ψ)` then
`-(1/k) log P_e(k) → C_K(ψ)`. -/
theorem tendsto_of_calibrated_of_polyImageClosure (h : PolyImageClosure) {n : ℕ} (ψ : Ψ n)
    (hψ : nsq ψ = 1) (hcal : Ceilings.FCΘ ψ = FKΘ ψ) :
    Filter.Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop (nhds (CK ψ)) :=
  tendsto_of_calibrated_of_zClosureSup ψ hψ (zClosureSup_of_polyImageClosure h ψ) hcal

end FormalResearch.FrameFree.SupportRate
