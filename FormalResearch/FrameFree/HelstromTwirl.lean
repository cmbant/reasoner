import Mathlib

/-!
# Haar-free twirl (generic finite-dimensional statement)

Namespace `FormalResearch.FrameFree.Helstrom`.

For a set `G` of unitary matrices closed under products and a matrix `ρ`, `twirl_exists` gives a matrix
`Z` that commutes with all of `G` and lies in every closed convex set containing the orbit
`{U ρ U†}`.  `Z` is the minimum-Frobenius-norm point of the closed convex hull of the orbit; no Haar
measure or compactness of the group is used.  Invariance of `Z` follows from uniqueness of the
minimum-norm point (`exists_fixed_point_hull`, parallelogram law) and the fact that conjugation by a
unitary is a linear isometry of the flattened matrix space (`conjLI`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix

namespace FormalResearch.FrameFree.Helstrom

theorem exists_fixed_point_hull {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (O : Set V) (hO : O.Nonempty) (Φ : Set (V →ₗᵢ[ℝ] V))
    (hinv : ∀ φ ∈ Φ, ∀ x ∈ O, φ x ∈ O) :
    ∃ Z : V, (∀ C : Set V, IsClosed C → Convex ℝ C → O ⊆ C → Z ∈ C) ∧ ∀ φ ∈ Φ, φ Z = Z := by
  set K := closure (convexHull ℝ O) with hK
  have hKc : Convex ℝ K := (convex_convexHull ℝ O).closure
  have hKcl : IsClosed K := isClosed_closure
  have hKne : K.Nonempty := (hO.convexHull).closure
  have hsub : ∀ C : Set V, IsClosed C → Convex ℝ C → O ⊆ C → K ⊆ C := fun C hC hCc hOC =>
    closure_minimal (convexHull_min hOC hCc) hC
  obtain ⟨Z, hZK, hZ⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcl.isComplete hKc (0 : V)
  have hmin : ∀ w ∈ K, ‖Z‖ ≤ ‖w‖ := by
    intro w hw
    have hb : BddBelow (Set.range fun w : K => ‖(0 : V) - (w : V)‖) :=
      ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
    have := ciInf_le hb ⟨w, hw⟩
    simp only [zero_sub, norm_neg] at hZ this
    rw [hZ]; exact this
  have huniq : ∀ Z' ∈ K, ‖Z'‖ ≤ ‖Z‖ → Z' = Z := by
    intro Z' hZ' hle
    have hm : (1/2 : ℝ) • (Z + Z') ∈ K := by
      have := hKc hZK hZ' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      simpa [smul_add] using this
    have h1 := hmin _ hm
    have h2 := hmin _ hZ'
    have hpar := parallelogram_law_with_norm ℝ Z Z'
    have hn : ‖(1/2 : ℝ) • (Z + Z')‖ = ‖Z + Z'‖ / 2 := by
      rw [norm_smul]; simp; ring
    rw [hn] at h1
    have heq : ‖Z'‖ = ‖Z‖ := le_antisymm hle h2
    have : ‖Z - Z'‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg Z, norm_nonneg (Z + Z'), norm_nonneg (Z - Z')]
    have h0 : ‖Z - Z'‖ = 0 := by nlinarith [norm_nonneg (Z - Z')]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm
  refine ⟨Z, fun C hC hCc hOC => hsub C hC hCc hOC hZK, ?_⟩
  intro φ hφ
  have hpre : K ⊆ (φ ⁻¹' K) := by
    apply hsub
    · exact hKcl.preimage φ.continuous
    · exact hKc.linear_preimage φ.toLinearMap
    · intro x hx
      exact subset_closure (subset_convexHull ℝ O (hinv φ hφ x hx))
  exact huniq _ (hpre hZK) (by rw [φ.norm_map])


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev MV (ι : Type*) [Fintype ι] := EuclideanSpace ℂ (ι × ι)

def ofV (x : MV ι) : Matrix ι ι ℂ := Matrix.of fun i j => x (i, j)
def toV (M : Matrix ι ι ℂ) : MV ι := WithLp.toLp 2 (fun p : ι × ι => M p.1 p.2)

@[simp] theorem ofV_toV (M : Matrix ι ι ℂ) : ofV (toV M) = M := by ext i j; rfl
@[simp] theorem toV_ofV (x : MV ι) : toV (ofV x) = x := by ext p; rfl

theorem sum_norm_sq_eq (A : Matrix ι ι ℂ) :
    ‖toV A‖ ^ 2 = (A * Aᴴ).trace.re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [toV, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]


theorem ofV_add (x y : MV ι) : ofV (x + y) = ofV x + ofV y := by ext i j; rfl
theorem ofV_smul (r : ℝ) (x : MV ι) : ofV (r • x) = r • ofV x := by ext i j; rfl
theorem toV_add (x y : Matrix ι ι ℂ) : toV (x + y) = toV x + toV y := by ext p; rfl
theorem toV_smul (r : ℝ) (x : Matrix ι ι ℂ) : toV (r • x) = r • toV x := by ext p; rfl

/-- Conjugation by a unitary, as a real-linear isometry of the flattened matrix space. -/
noncomputable def conjLI (U : Matrix ι ι ℂ) (h1 : Uᴴ * U = 1) : MV ι →ₗᵢ[ℝ] MV ι where
  toFun x := toV (U * ofV x * Uᴴ)
  map_add' x y := by
    rw [ofV_add, Matrix.mul_add, Matrix.add_mul, toV_add]
  map_smul' r x := by
    rw [ofV_smul, Matrix.mul_smul, Matrix.smul_mul, toV_smul]; rfl
  norm_map' x := by
    have h : ‖toV (U * ofV x * Uᴴ)‖ ^ 2 = ‖x‖ ^ 2 := by
      have e1 := sum_norm_sq_eq (U * ofV x * Uᴴ)
      have e2 := sum_norm_sq_eq (ofV x)
      rw [toV_ofV] at e2
      have : (U * ofV x * Uᴴ * (U * ofV x * Uᴴ)ᴴ).trace = (ofV x * (ofV x)ᴴ).trace := by
        calc (U * ofV x * Uᴴ * (U * ofV x * Uᴴ)ᴴ).trace
            = (U * (ofV x * (Uᴴ * U) * (ofV x)ᴴ) * Uᴴ).trace := by
              simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
          _ = (ofV x * (ofV x)ᴴ).trace := by
            rw [h1, Matrix.mul_one, Matrix.trace_mul_cycle, h1, Matrix.one_mul]
      rw [e1, e2, this]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem continuous_ofV : Continuous (ofV : MV ι → Matrix ι ι ℂ) :=
  continuous_matrix fun i j => (EuclideanSpace.proj (i, j) : MV ι →L[ℂ] ℂ).continuous

theorem twirl_exists (G : Set (Matrix ι ι ℂ)) (hG1 : ∀ U ∈ G, Uᴴ * U = 1)
    (hmul : ∀ U ∈ G, ∀ V ∈ G, U * V ∈ G) (hne : G.Nonempty)
    (ρ : Matrix ι ι ℂ) :
    ∃ Z : Matrix ι ι ℂ, (∀ C : Set (Matrix ι ι ℂ), IsClosed C → Convex ℝ C →
        (∀ U ∈ G, U * ρ * Uᴴ ∈ C) → Z ∈ C) ∧ ∀ U ∈ G, U * Z = Z * U := by
  classical
  obtain ⟨U0, hU0⟩ := hne
  let O : Set (MV ι) := {x | ∃ U ∈ G, x = toV (U * ρ * Uᴴ)}
  let Φ : Set (MV ι →ₗᵢ[ℝ] MV ι) := {φ | ∃ U, ∃ hU : U ∈ G, φ = conjLI U (hG1 U hU)}
  have hO : O.Nonempty := ⟨_, U0, hU0, rfl⟩
  have hinv : ∀ φ ∈ Φ, ∀ x ∈ O, φ x ∈ O := by
    rintro φ ⟨U, hU, rfl⟩ x ⟨V, hV, rfl⟩
    refine ⟨U * V, hmul U hU V hV, ?_⟩
    show toV (U * ofV (toV (V * ρ * Vᴴ)) * Uᴴ) = _
    rw [ofV_toV, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Zv, hZ1, hZ2⟩ := exists_fixed_point_hull O hO Φ hinv
  refine ⟨ofV Zv, ?_, ?_⟩
  · intro C hC hCc hOC
    have := hZ1 (ofV ⁻¹' C) (hC.preimage continuous_ofV) ?_ ?_
    · exact this
    · intro x hx y hy a b ha hb hab
      show ofV (a • x + b • y) ∈ C
      rw [ofV_add, ofV_smul, ofV_smul]
      exact hCc hx hy ha hb hab
    · rintro _ ⟨U, hU, rfl⟩
      show ofV (toV _) ∈ C
      rw [ofV_toV]; exact hOC U hU
  · intro U hU
    have h := hZ2 _ ⟨U, hU, rfl⟩
    have h' : toV (U * ofV Zv * Uᴴ) = Zv := h
    have h'' : U * ofV Zv * Uᴴ = ofV Zv := by
      have := congrArg ofV h'
      rwa [ofV_toV] at this
    calc U * ofV Zv = U * ofV Zv * (Uᴴ * U) := by rw [hG1 U hU, Matrix.mul_one]
      _ = (U * ofV Zv * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = ofV Zv * U := by rw [h'']

end FormalResearch.FrameFree.Helstrom
