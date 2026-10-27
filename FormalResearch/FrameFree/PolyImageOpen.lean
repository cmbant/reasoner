import Mathlib
import FormalResearch.FrameFree.PolyImageBasic
import FormalResearch.FrameFree.PolyImageLift
import FormalResearch.FrameFree.PolyImagePoints
import FormalResearch.FrameFree.PolyImagePointSet

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Polynomial images: local openness of a finite map to `ℂ^d`

Namespace `FormalResearch.FrameFree.PolyImage`.

`exists_point_near_of_normalization`: let `P = ℂ[x₁..x_d]`, `B ⊇ P` a finitely generated domain integral over `P`
with generators `yᵢ`, `c ≠ 0` in `P`.  Then every `ℂ`-point `ζ` of `B` is a limit of `ℂ`-points `ζ'` of `B` with
`ζ'(c) ≠ 0`.  (Local openness of `Spec B → ℂ^d` at `ζ`, plus Euclidean density of `{c ≠ 0}`.)  The proof uses a
generic linear form `θ = Σ κᵢ yᵢ` separating `ζ` from the rest of its fibre, the minimal polynomial `F` of `θ`
(roots of `F^x` near `ζ θ` exist for `x` near the base point of `ζ`), `exists_point_over`, and compactness of the
bounded part of the point set.
-/

namespace FormalResearch.FrameFree.PolyImage

open Polynomial Filter Topology

section

variable {d : ℕ} {B : Type*} [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
  [Algebra (MvPolynomial (Fin d) ℂ) B] [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B]
  [Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) B] [Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) B]
  {ι : Type*} [Fintype ι]

theorem exists_point_near_of_normalization (y : ι → B)
    (hy : Function.Surjective (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] B))
    {c : MvPolynomial (Fin d) ℂ} (hc : c ≠ 0) (ζ : B →ₐ[ℂ] ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ζ' : B →ₐ[ℂ] ℂ, ζ' (algebraMap (MvPolynomial (Fin d) ℂ) B c) ≠ 0 ∧
      ∀ i, ‖ζ' (y i) - ζ (y i)‖ < ε := by
  classical
  let P := MvPolynomial (Fin d) ℂ
  let w0 : Fin d → ℂ := fun j => ζ (algebraMap P B (MvPolynomial.X j))
  let z : ι → ℂ := fun i => ζ (y i)
  have hzmem : z ∈ pointSet y := ⟨ζ, fun i => rfl⟩
  -- the relations of the generators and their bounds
  have hint : ∀ u : B, IsIntegral P u := fun u => Algebra.IsIntegral.isIntegral u
  choose R hR using fun i => eventually_roots_bounded (minpoly P (y i)) (minpoly.monic (hint (y i))) w0
  have hRev : ∀ᶠ x in 𝓝 w0, ∀ i t, ((minpoly P (y i)).map (MvPolynomial.eval x)).IsRoot t → ‖t‖ ≤ R i :=
    eventually_all.2 fun i => (hR i).mono fun x hx t ht => hx t ht
  -- coordinates of the base `P` as polynomials in the generators
  choose q hq using fun j : Fin d => hy (algebraMap P B (MvPolynomial.X j))
  have hqj : ∀ (ζ' : B →ₐ[ℂ] ℂ) (j : Fin d),
      ζ' (algebraMap P B (MvPolynomial.X j)) = MvPolynomial.eval (fun i => ζ' (y i)) (q j) := by
    intro ζ' j
    rw [← hq j]
    have : ζ' (MvPolynomial.aeval y (q j)) = MvPolynomial.aeval (fun i => ζ' (y i)) (q j) := by
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    rw [this]
    rfl
  -- the fibre of `z` is finite
  have hfib : {p : ι → ℂ | p ∈ pointSet y ∧ (fun j => MvPolynomial.eval p (q j)) = w0}.Finite := by
    refine (Set.Finite.pi (t := fun i => {t : ℂ | ((minpoly P (y i)).map (MvPolynomial.eval w0)).IsRoot t})
      (fun i => ?_)).subset ?_
    · exact Polynomial.finite_setOfPred_isRoot
        ((minpoly.monic (hint (y i))).map _).ne_zero
    · rintro p ⟨⟨ζ1, hζ1⟩, hp⟩ i -
      have h1 : (fun j => ζ1 (algebraMap P B (MvPolynomial.X j))) = w0 := by
        funext j
        rw [hqj ζ1 j, show (fun i => ζ1 (y i)) = p from funext hζ1]
        exact congrFun hp j
      have := isRoot_map_of_point ζ1 (y i) (minpoly P (y i)) (minpoly.aeval P (y i))
      rw [h1, hζ1 i] at this
      exact this
  -- a linear form separating `z` from the other points of its fibre
  obtain ⟨κ, hκ⟩ : ∃ κ : ι → ℂ, ∀ p ∈ {p : ι → ℂ | p ∈ pointSet y ∧
      (fun j => MvPolynomial.eval p (q j)) = w0}, p ≠ z → ∑ i, κ i * (p i - z i) ≠ 0 := by
    obtain ⟨κ, hκ⟩ := exists_forall_sum_ne_zero (hfib.toFinset.filter (· ≠ z) |>.image fun p => p - z)
      (by
        intro s hs
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hp
        exact sub_ne_zero.2 hp.2)
    refine ⟨κ, fun p hp hpz => ?_⟩
    have := hκ (p - z) (Finset.mem_image.2 ⟨p, by simp [Set.Finite.mem_toFinset, hp, hpz], rfl⟩)
    simpa using this
  -- the separating element and its minimal polynomial
  let θ : B := ∑ i, κ i • y i
  have hθ : ∀ ζ' : B →ₐ[ℂ] ℂ, ζ' θ = ∑ i, κ i * ζ' (y i) := by
    intro ζ'; simp [θ, map_sum]
  let F : P[X] := minpoly P θ
  have hFm : F.Monic := minpoly.monic (hint θ)
  have hn : 0 < F.natDegree := minpoly.natDegree_pos (hint θ)
  let b : ℂ := ζ θ
  have hFb : (F.map (MvPolynomial.eval w0)).eval b = 0 :=
    isRoot_map_of_point ζ θ F (minpoly.aeval P θ)
  have hroot : ∀ x : Fin d → ℂ, ∃ r : ℂ, (F.map (MvPolynomial.eval x)).IsRoot r ∧
      ‖r - b‖ ^ F.natDegree ≤ ‖(F.map (MvPolynomial.eval x)).eval b‖ := by
    intro x
    have h := exists_root_near (F.map (MvPolynomial.eval x)) (hFm.map _) (by
      rw [hFm.natDegree_map]; exact hn) b
    rwa [hFm.natDegree_map] at h
  choose r hr1 hr2 using hroot
  have hrt : Tendsto r (𝓝 w0) (𝓝 b) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    have hcont := (continuous_eval_map F b).continuousAt (x := w0)
    have h0 : ‖(F.map (MvPolynomial.eval w0)).eval b‖ = 0 := by rw [hFb]; simp
    have hev : ∀ᶠ x in 𝓝 w0, ‖(F.map (MvPolynomial.eval x)).eval b‖ < η ^ F.natDegree := by
      have : Tendsto (fun x => ‖(F.map (MvPolynomial.eval x)).eval b‖) (𝓝 w0) (𝓝 0) := by
        rw [← h0]; exact hcont.norm
      exact this.eventually (gt_mem_nhds (pow_pos hη _))
    filter_upwards [hev] with x hx
    rw [dist_eq_norm]
    by_contra hcon
    push Not at hcon
    have := pow_le_pow_left₀ hη.le hcon F.natDegree
    exact absurd (this.trans_lt ((hr2 x).trans_lt hx)) (lt_irrefl _)
  -- compactness of the bounded part of the point set away from `z`
  let proj : (ι → ℂ) → (Fin d → ℂ) × ℂ :=
    fun p => (fun j => MvPolynomial.eval p (q j), ∑ i, κ i * p i)
  have hproj : Continuous proj := by
    refine Continuous.prodMk (continuous_pi fun j => MvPolynomial.continuous_eval _) ?_
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  let S : Set (ι → ℂ) := {p | p ∈ pointSet y ∧ (∀ i, ‖p i‖ ≤ R i) ∧ ¬ ∀ i, ‖p i - z i‖ < ε}
  have hScl : IsClosed S := by
    have h1 : IsClosed {p : ι → ℂ | ∀ i, ‖p i‖ ≤ R i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le (continuous_apply i).norm continuous_const
    have h2 : IsOpen {p : ι → ℂ | ∀ i, ‖p i - z i‖ < ε} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_lt ((continuous_apply i).sub continuous_const).norm continuous_const
    exact ((isClosed_pointSet y hy).inter (h1.inter h2.isClosed_compl))
  have hScpt : IsCompact S :=
    (isCompact_univ_pi fun i => isCompact_closedBall (0 : ℂ) (R i)).of_isClosed_subset hScl
      (fun p hp i _ => by simpa using hp.2.1 i)
  have hbz : b = ∑ i, κ i * z i := hθ ζ
  have hnot : (w0, b) ∉ proj '' S := by
    rintro ⟨p, ⟨hpZ, hpb, hpne⟩, hprojp⟩
    have h1 : (fun j => MvPolynomial.eval p (q j)) = w0 := congrArg Prod.fst hprojp
    have h2 : ∑ i, κ i * p i = b := congrArg Prod.snd hprojp
    by_cases hpz : p = z
    · exact hpne fun i => by simp [hpz, hε]
    · have := hκ p ⟨hpZ, h1⟩ hpz
      apply this
      simp only [mul_sub, Finset.sum_sub_distrib, h2, ← hbz, sub_self]
  have hU : (proj '' S)ᶜ ∈ 𝓝 (w0, b) := (hScpt.image hproj).isClosed.isOpen_compl.mem_nhds hnot
  have hev1 : ∀ᶠ x in 𝓝 w0, (x, r x) ∈ (proj '' S)ᶜ :=
    (Tendsto.prodMk_nhds tendsto_id hrt).eventually hU
  have hD : Dense {x : Fin d → ℂ | MvPolynomial.eval x c ≠ 0} := dense_eval_ne_zero hc
  obtain ⟨x, hxc, hxU, hxR⟩ := ((mem_closure_iff_frequently.1 (hD w0)).and_eventually
    (hev1.and hRev)).exists
  -- the point over `x` with `θ = r x`
  have hrx : Polynomial.eval₂ ((MvPolynomial.aeval x : P →ₐ[ℂ] ℂ) : P →+* ℂ) (r x) (minpoly P θ) = 0 := by
    have := hr1 x
    rw [Polynomial.IsRoot, Polynomial.eval_map] at this
    rw [MvPolynomial.coe_aeval_eq_eval]
    exact this
  obtain ⟨ζ', hζ'1, hζ'2⟩ := exists_point_over θ (MvPolynomial.aeval x) (r x) hrx
  have hbase : ∀ j, ζ' (algebraMap P B (MvPolynomial.X j)) = x j := by
    intro j
    have : ζ' (algebraMap P B (MvPolynomial.X j)) = MvPolynomial.aeval x (MvPolynomial.X j) :=
      congrArg (fun φ : P →ₐ[ℂ] ℂ => φ (MvPolynomial.X j)) hζ'1
    simpa using this
  refine ⟨ζ', ?_, ?_⟩
  · have : ζ' (algebraMap P B c) = MvPolynomial.aeval x c :=
      congrArg (fun φ : P →ₐ[ℂ] ℂ => φ c) hζ'1
    rw [this]
    simpa [MvPolynomial.coe_aeval_eq_eval] using hxc
  · by_contra hcon
    have hmem : (fun i => ζ' (y i)) ∈ S := by
      refine ⟨⟨ζ', fun i => rfl⟩, fun i => ?_, hcon⟩
      have := isRoot_map_of_point ζ' (y i) (minpoly P (y i)) (minpoly.aeval P (y i))
      have hx' : (fun j => ζ' (algebraMap P B (MvPolynomial.X j))) = x := funext hbase
      rw [hx'] at this
      exact hxR i _ this
    apply hxU
    refine ⟨_, hmem, ?_⟩
    refine Prod.ext (funext fun j => ?_) ?_
    · show MvPolynomial.eval (fun i => ζ' (y i)) (q j) = x j
      rw [← hqj ζ' j, hbase]
    · show ∑ i, κ i * ζ' (y i) = r x
      rw [← hθ ζ', hζ'2]

end

end FormalResearch.FrameFree.PolyImage
