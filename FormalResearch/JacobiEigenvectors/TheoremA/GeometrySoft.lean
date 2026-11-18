module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryAll
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftInt
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftMorse
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftUnif
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftSymbol

/-!
# Paper J, Layer 2 (L2.G4 (d)): the soft edge, lem:tha-geom (d); `TheGeometry`

Source: Paper J `thmA.tex` Section 4.2 `lem:tha-geom` (d), `lem:hyp-morse`, `app_smooth` (Morse coordinate).

Proves `GeomSoft` and `GeomSoftLower` of `TheoremA/GeometryStatements.lean` (frozen; not edited), hence
`theGeometry : TheGeometry F K r` (with `theGeometry_of_soft`, `GeometryAll.lean`).  Proof chain (all `proved`):

1. `SoftSymbol` (`GeometrySoftSymbol.lean`): `f_+` is `C^r` on `(0, L)`; `f_+'' = f2 L G B` on `(0, L)` with `f2` an explicit
   expression in the jets, jointly continuous on `K x [a, b]`.
2. `SoftUnif` (`GeometrySoftUnif.lean`): from joint continuity and uniqueness of the maximiser, `uc` is continuous on `K` (closed graph
   into a compact interval), stays `rho_0` away from `0, L`, has a uniform gap `f + gamma <= X_s` off a neighbourhood of `uc`, and a
   tube of radius `rho_1` on which `m <= -f'' <= M` (`uData_exists`, compactness of `K x [0, L]`).
3. `SoftInt`, `SoftMorse`: `t(x) = x sqrt(h(x))`, `h(x) = int_0^1 (1 - s)(-f''(uc + s x)) ds`, satisfies `f(uc + x) = X_s - t^2`,
   `t(0) = 0`, `t' >= c_t = m/(2 sqrt(M/2))` and is `C^{r-2}` (`C^{r-2}` of the integral: induction on the order through dominated
   differentiation under the integral).
4. `Single.body`: for one `mu`: normal form (HI3), `-1 < ...` on the collar, the endpoint bounds `1 + eta_1 <= ...` (with
   `eta_1 = (2 eta c_t)^2 / 2 / (2 L sqrt(C_G))`), localisation `{T >= 0} subset (u_c - eta/4, u_c + eta/4)` and `T < 0`, `Q_0 > 0` off it.
5. `softConcl`: uniform constants over `K` (`eta_0 = min(rho_0/6, rho_1/4)`; for `eta <= eta_0`: `delta_* = min(gamma/2, 2 a_min, (2 eta c_t)^2/8)`).
6. `geomSoft` (from (H1), (H3p)), `geomSoftLower` (the same for `negFamily F`: only (H1) and (H3m) enter; `f_+(-B_0) = -f_-(B_0)`).

Differences from the paper / the frozen statement: none.  Only (H1) and (H3) are used (not (H2)); `PrincipalReg F K r` is used through the
jets `G_0, G_0', G_0'', B_0', B_0''` (jointly continuous) and `C^r` of the symbols.  `t` is `x sqrt(h(x))`, which equals the paper's
`sign(x) sqrt(f(u_c) - f(u_c + x))`.  The constants (`eta_0`, `delta_*`, `c_t`, `a_min`, `eta_1`) are explicit in terms of the compactness data.
Not formalised: nothing in `lem:tha-geom` (d).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge

open Set Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA.HypMorse
  FormalResearch.JacobiEigenvectors.TheoremA.SoftMorse FormalResearch.JacobiEigenvectors.TheoremA.SoftMorse.MorseData
  FormalResearch.JacobiEigenvectors.TheoremA.SoftUnif
  FormalResearch.JacobiEigenvectors.TheoremA.SoftSymbol

variable {Par : Type*} [TopologicalSpace Par]

/-- What the soft-edge analysis uses of `(H1)`--`(H3)`: `G_0 >= g > 0` and the upper fold (the unique maximiser of `f_+`, interior,
with `f_+'' < 0`).  `Hyp` gives it for `F` (H3p) and, through `negFamily`, for the lower edge (H3m). -/
structure SoftHyp (F : SymbolFamily Par) (K : Set Par) (g : ℝ) : Prop where
  hg : 0 < g
  lb : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L, g ≤ F.G 0 μ u
  h3 : ∀ μ ∈ K, ∃ uc : ℝ, 0 < uc ∧ uc < F.L ∧
    (∀ u ∈ Icc 0 F.L, fPlus F.L (F.G 0 μ) (F.B 0 μ) u = Xsp F.L (F.G 0 μ) (F.B 0 μ) ↔ u = uc) ∧
    deriv (deriv (fPlus F.L (F.G 0 μ) (F.B 0 μ))) uc < 0

/-- The uniform data over `K`: the fold `uc`, its distance `rho0` to the ends, curvature bounds `m <= -f'' <= M` on a tube of radius `rho1`
around the fold, and `G_0 <= Cg`. -/
structure UData (F : SymbolFamily Par) (K : Set Par) (uc : Par → ℝ) (ρ0 m M ρ1 Cg : ℝ) : Prop where
  ρ0_pos : 0 < ρ0
  m_pos : 0 < m
  mM : m ≤ M
  ρ1_pos : 0 < ρ1
  Cg_pos : 0 < Cg
  uc_mem : ∀ μ ∈ K, ρ0 ≤ uc μ ∧ uc μ ≤ F.L - ρ0
  uc_char : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L, fPlus F.L (F.G 0 μ) (F.B 0 μ) u = F.bandHi μ ↔ u = uc μ
  curv : ∀ μ ∈ K, ∀ u ∈ Icc (ρ0 / 2) (F.L - ρ0 / 2), |u - uc μ| < ρ1 →
    m ≤ -deriv (deriv (fPlus F.L (F.G 0 μ) (F.B 0 μ))) u ∧ -deriv (deriv (fPlus F.L (F.G 0 μ) (F.B 0 μ))) u ≤ M
  gap : ∀ ε : ℝ, 0 < ε → ∃ γ : ℝ, 0 < γ ∧ ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L, ε ≤ |u - uc μ| →
    fPlus F.L (F.G 0 μ) (F.B 0 μ) u + γ ≤ F.bandHi μ
  Gub : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L, F.G 0 μ u ≤ Cg

/-- The jets used, jointly continuous on `K x [0, L]` (from `PrincipalReg`). -/
structure Jets (F : SymbolFamily Par) (K : Set Par) : Prop where
  j0G : ContinuousOn (fun p : Par × ℝ => F.G 0 p.1 p.2) (K ×ˢ Icc 0 F.L)
  j0B : ContinuousOn (fun p : Par × ℝ => F.B 0 p.1 p.2) (K ×ˢ Icc 0 F.L)
  j1G : ContinuousOn (fun p : Par × ℝ => d1 F.L (F.G 0 p.1) p.2) (K ×ˢ Icc 0 F.L)
  j2G : ContinuousOn (fun p : Par × ℝ => d2 F.L (F.G 0 p.1) p.2) (K ×ˢ Icc 0 F.L)
  j1B : ContinuousOn (fun p : Par × ℝ => d1 F.L (F.B 0 p.1) p.2) (K ×ˢ Icc 0 F.L)
  j2B : ContinuousOn (fun p : Par × ℝ => d2 F.L (F.B 0 p.1) p.2) (K ×ˢ Icc 0 F.L)

lemma jets_of_reg {F : SymbolFamily Par} {K : Set Par} {r : ℕ} (hr : 2 ≤ r) (hreg : PrincipalReg F K r) :
    Jets F K where
  j0G := by simpa [iteratedDerivWithin_zero] using hreg.1.2 0 (by omega)
  j0B := by simpa [iteratedDerivWithin_zero] using hreg.2.2 0 (by omega)
  j1G := hreg.1.2 1 (by omega)
  j2G := hreg.1.2 2 hr
  j1B := hreg.2.2 1 (by omega)
  j2B := hreg.2.2 2 hr

lemma jets_contf {F : SymbolFamily Par} {K : Set Par} (hj : Jets F K) :
    ContinuousOn (fun p : Par × ℝ => fPlus F.L (F.G 0 p.1) (F.B 0 p.1) p.2) (K ×ˢ Icc 0 F.L) := by
  have hc : ContinuousOn (fun p : Par × ℝ => p.2 * (F.L - p.2) * F.G 0 p.1 p.2) (K ×ˢ Icc 0 F.L) :=
    (continuous_snd.continuousOn.mul (continuousOn_const.sub continuous_snd.continuousOn)).mul hj.j0G
  exact hj.j0B.add (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hc))

/-- The fold and its basic properties, for `mu in K`. -/
structure FoldData (F : SymbolFamily Par) (K : Set Par) (uc : Par → ℝ) : Prop where
  int : ∀ μ ∈ K, 0 < uc μ ∧ uc μ < F.L
  char : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L, fPlus F.L (F.G 0 μ) (F.B 0 μ) u = F.bandHi μ ↔ u = uc μ
  dd : ∀ μ ∈ K, deriv (deriv (fPlus F.L (F.G 0 μ) (F.B 0 μ))) (uc μ) < 0
  le : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L, fPlus F.L (F.G 0 μ) (F.B 0 μ) u ≤ F.bandHi μ
  cont : ContinuousOn uc K

lemma fold_exists {F : SymbolFamily Par} {K : Set Par} {r : ℕ} (hr : 2 ≤ r) {g : ℝ} (h : SoftHyp F K g)
    (hreg : PrincipalReg F K r) : ∃ uc : Par → ℝ, FoldData F K uc := by
  choose! uc huc0 hucL hchar hucdd using h.h3
  have hr2 : (2 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
  have hcontμ : ∀ μ ∈ K, ContinuousOn (fPlus F.L (F.G 0 μ) (F.B 0 μ)) (Icc 0 F.L) :=
    fun μ hμ => fPlus_continuousOn ((hreg.1.1 μ hμ).of_le hr2) ((hreg.2.1 μ hμ).of_le hr2)
  have hmem : ∀ μ ∈ K, uc μ ∈ Icc 0 F.L := fun μ hμ => ⟨(huc0 μ hμ).le, (hucL μ hμ).le⟩
  have hle : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L, fPlus F.L (F.G 0 μ) (F.B 0 μ) u ≤ F.bandHi μ :=
    fun μ hμ u hu => fPlus_le_Xsp (hcontμ μ hμ) hu
  have hfuc : ∀ μ ∈ K, fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) = F.bandHi μ :=
    fun μ hμ => (hchar μ hμ (uc μ) (hmem μ hμ)).2 rfl
  have hmax : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L,
      fPlus F.L (F.G 0 μ) (F.B 0 μ) u ≤ fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) := by
    intro μ hμ u hu
    rw [hfuc μ hμ]; exact hle μ hμ u hu
  have huniq : ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L,
      fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) ≤ fPlus F.L (F.G 0 μ) (F.B 0 μ) u → u = uc μ := by
    intro μ hμ u hu hge
    rw [hfuc μ hμ] at hge
    exact (hchar μ hμ u hu).1 (le_antisymm (hle μ hμ u hu) hge)
  exact ⟨uc, fun μ hμ => ⟨huc0 μ hμ, hucL μ hμ⟩, hchar, hucdd, hle,
    uc_continuousOn (f := fun μ u => fPlus F.L (F.G 0 μ) (F.B 0 μ) u) (jets_contf (jets_of_reg hr hreg))
      hmem hmax huniq⟩

lemma fold_huniq {F : SymbolFamily Par} {K : Set Par} {uc : Par → ℝ} (hf : FoldData F K uc) :
    ∀ μ ∈ K, ∀ u ∈ Icc 0 F.L,
      fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) ≤ fPlus F.L (F.G 0 μ) (F.B 0 μ) u → u = uc μ := by
  intro μ hμ u hu hge
  have hmem : uc μ ∈ Icc 0 F.L := ⟨(hf.int μ hμ).1.le, (hf.int μ hμ).2.le⟩
  have hfuc : fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) = F.bandHi μ := (hf.char μ hμ _ hmem).2 rfl
  rw [hfuc] at hge
  exact (hf.char μ hμ u hu).1 (le_antisymm (hf.le μ hμ u hu) hge)

lemma fold_hfuc {F : SymbolFamily Par} {K : Set Par} {uc : Par → ℝ} (hf : FoldData F K uc) {μ : Par} (hμ : μ ∈ K) :
    fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) = F.bandHi μ :=
  (hf.char μ hμ _ ⟨(hf.int μ hμ).1.le, (hf.int μ hμ).2.le⟩).2 rfl

lemma uData_exists {F : SymbolFamily Par} {K : Set Par} {r : ℕ} (hr : 2 ≤ r) (hK : IsCompact K) {g : ℝ}
    (h : SoftHyp F K g) (hreg : PrincipalReg F K r) {uc : Par → ℝ} (hf : FoldData F K uc) :
    ∃ ρ0 m M ρ1 Cg : ℝ, UData F K uc ρ0 m M ρ1 Cg := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, 1, 1, 1, ⟨one_pos, one_pos, le_rfl, one_pos, one_pos,
      fun μ hμ => by simp at hμ, fun μ hμ => by simp at hμ, fun μ hμ => by simp at hμ,
      fun ε _ => ⟨1, one_pos, fun μ hμ => by simp at hμ⟩, fun μ hμ => by simp at hμ⟩⟩
  have hj := jets_of_reg hr hreg
  have hL := F.L_pos
  have hr2 : (2 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
  have hmem : ∀ μ ∈ K, uc μ ∈ Icc 0 F.L := fun μ hμ => ⟨(hf.int μ hμ).1.le, (hf.int μ hμ).2.le⟩
  obtain ⟨ρ0, hρ0, hmargin⟩ := uc_margin hK hf.cont hf.int
  obtain ⟨μ1, hμ1⟩ := hne
  have h2ρ : 2 * ρ0 ≤ F.L := by
    have := hmargin μ1 hμ1
    linarith [this.1, this.2]
  have ha0 : 0 < ρ0 / 2 := by linarith
  have hbL : F.L - ρ0 / 2 < F.L := by linarith
  have hGpos : ∀ μ ∈ K, ∀ v ∈ Ioo 0 F.L, 0 < F.G 0 μ v :=
    fun μ hμ v hv => lt_of_lt_of_le h.hg (h.lb μ hμ v (Ioo_subset_Icc_self hv))
  have hΦ : ContinuousOn (fun p : Par × ℝ => -f2 F.L (F.G 0 p.1) (F.B 0 p.1) p.2) (K ×ˢ Icc (ρ0 / 2) (F.L - ρ0 / 2)) :=
    (continuousOn_f2 (Gp := F.G 0) (Bp := F.B 0) ha0 hbL h.hg h.lb hj.j0G hj.j1G hj.j2G hj.j1B hj.j2B).neg
  have hΦeq : ∀ μ ∈ K, ∀ u ∈ Icc (ρ0 / 2) (F.L - ρ0 / 2),
      (fun p : Par × ℝ => -f2 F.L (F.G 0 p.1) (F.B 0 p.1) p.2) (μ, u) =
        -deriv (deriv (fPlus F.L (F.G 0 μ) (F.B 0 μ))) u := by
    intro μ hμ u hu
    show -f2 F.L (F.G 0 μ) (F.B 0 μ) u = _
    rw [deriv_deriv_fPlus_eq ((hreg.1.1 μ hμ).of_le hr2) ((hreg.2.1 μ hμ).of_le hr2) (hGpos μ hμ)
      ⟨by linarith [hu.1], by linarith [hu.2]⟩]
  generalize (fun p : Par × ℝ => -f2 F.L (F.G 0 p.1) (F.B 0 p.1) p.2) = Φ at hΦ hΦeq
  have hucab : ∀ μ ∈ K, uc μ ∈ Icc (ρ0 / 2) (F.L - ρ0 / 2) := by
    intro μ hμ
    have := hmargin μ hμ
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hgraph : ContinuousOn (fun μ : Par => (μ, uc μ)) K := continuousOn_id.prodMk hf.cont
  have hmapsg : Set.MapsTo (fun μ : Par => (μ, uc μ)) K (K ×ˢ Icc (ρ0 / 2) (F.L - ρ0 / 2)) :=
    fun μ hμ => ⟨hμ, hucab μ hμ⟩
  have hψ : ContinuousOn (fun μ : Par => Φ (μ, uc μ)) K := hΦ.comp hgraph hmapsg
  have hψpos : ∀ μ ∈ K, 0 < Φ (μ, uc μ) := by
    intro μ hμ
    rw [hΦeq μ hμ _ (hucab μ hμ)]
    linarith [hf.dd μ hμ]
  obtain ⟨μ0, hμ0, hmin⟩ := hK.exists_isMinOn ⟨μ1, hμ1⟩ hψ
  have hm0pos : 0 < Φ (μ0, uc μ0) := hψpos μ0 hμ0
  obtain ⟨ρ1, hρ1, htube⟩ := tube_pos (K := K) (uc := uc) (Φ := Φ) (c := Φ (μ0, uc μ0) / 2) hK hf.cont hΦ
    (fun μ hμ => ⟨hucab μ hμ, by
      have := isMinOn_iff.1 hmin μ hμ
      linarith⟩)
  obtain ⟨Mb, hMb⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hΦ
  obtain ⟨C0, hC0⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hj.j0G
  refine ⟨ρ0, Φ (μ0, uc μ0) / 2, max Mb (Φ (μ0, uc μ0) / 2), ρ1, max C0 1,
    ⟨hρ0, by linarith, le_max_right _ _, hρ1, lt_of_lt_of_le one_pos (le_max_right _ _), hmargin, hf.char, ?_, ?_, ?_⟩⟩
  · intro μ hμ u hu hdist
    have h1 := htube μ hμ u hu hdist
    have h2 := (le_abs_self _).trans (hMb (μ, u) ⟨hμ, hu⟩)
    rw [← hΦeq μ hμ u hu]
    exact ⟨h1.le, h2.trans (le_max_left _ _)⟩
  · intro ε hε
    obtain ⟨γ, hγ, hgap⟩ := gap_unif (f := fun μ u => fPlus F.L (F.G 0 μ) (F.B 0 μ) u) hK (jets_contf hj) hf.cont hmem
      (fold_huniq hf) hε
    refine ⟨γ, hγ, fun μ hμ u hu hεu => ?_⟩
    have := hgap μ hμ u hu hεu
    rw [fold_hfuc hf hμ] at this
    exact this
  · intro μ hμ u hu
    have := (le_abs_self _).trans (hC0 (μ, u) ⟨hμ, hu⟩)
    exact this.trans (le_max_left _ _)

/-- A function with `t 0 = 0` and `t' >= ct` on `(-3 eta, 3 eta)` is `>= 2 eta ct` at `2 eta` and `<= -2 eta ct` at `-2 eta`. -/
lemma tf_ends {t : ℝ → ℝ} {ct η : ℝ} (hη : 0 < η) (h0 : t 0 = 0)
    (hd : ∀ x ∈ Ioo (-(3 * η)) (3 * η), DifferentiableAt ℝ t x ∧ ct ≤ deriv t x) :
    2 * η * ct ≤ t (2 * η) ∧ t (-(2 * η)) ≤ -(2 * η * ct) := by
  have hsub1 : Icc 0 (2 * η) ⊆ Ioo (-(3 * η)) (3 * η) := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsub2 : Icc (-(2 * η)) 0 ⊆ Ioo (-(3 * η)) (3 * η) := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have c1 : ContinuousOn t (Icc 0 (2 * η)) := fun y hy => (hd y (hsub1 hy)).1.continuousAt.continuousWithinAt
  have c2 : ContinuousOn t (Icc (-(2 * η)) 0) := fun y hy => (hd y (hsub2 hy)).1.continuousAt.continuousWithinAt
  have d1 : DifferentiableOn ℝ t (interior (Icc 0 (2 * η))) := by
    rw [interior_Icc]; exact fun y hy => (hd y (hsub1 (Ioo_subset_Icc_self hy))).1.differentiableWithinAt
  have d2 : DifferentiableOn ℝ t (interior (Icc (-(2 * η)) 0)) := by
    rw [interior_Icc]; exact fun y hy => (hd y (hsub2 (Ioo_subset_Icc_self hy))).1.differentiableWithinAt
  have e1 := (convex_Icc 0 (2 * η)).mul_sub_le_image_sub_of_le_deriv c1 d1
    (fun y hy => by rw [interior_Icc] at hy; exact (hd y (hsub1 (Ioo_subset_Icc_self hy))).2) 0
    ⟨le_rfl, by linarith⟩ (2 * η) ⟨by linarith, le_rfl⟩ (by linarith)
  have e2 := (convex_Icc (-(2 * η)) 0).mul_sub_le_image_sub_of_le_deriv c2 d2
    (fun y hy => by rw [interior_Icc] at hy; exact (hd y (hsub2 (Ioo_subset_Icc_self hy))).2) (-(2 * η))
    ⟨le_rfl, by linarith⟩ 0 ⟨by linarith, le_rfl⟩ (by linarith)
  rw [h0] at e1 e2
  constructor <;> nlinarith

/-- The per-parameter content of `GeomSoftConcl` at the upper soft edge of the principal pair `(G0, B0)`, written without `F`. -/
def SoftBody (L : ℝ) (G0 B0 : ℝ → ℝ) (r : ℕ) (η δs uc ct aMin η1 : ℝ) (tf : ℝ → ℝ) : Prop :=
  (0 < uc - 2 * η ∧ uc + 2 * η < L ∧ fPlus L G0 B0 uc = Xsp L G0 B0) ∧
  ContDiffOn ℝ ((r - 2 : ℕ) : WithTop ℕ∞) tf (Icc (-2 * η) (2 * η)) ∧ tf 0 = 0 ∧
  (∀ x ∈ Icc (-2 * η) (2 * η), ct ≤ deriv tf x ∧ fPlus L G0 B0 (uc + x) = Xsp L G0 B0 - tf x ^ 2) ∧
  (∀ x ∈ Icc (-2 * η) (2 * η), aMin ≤ Real.sqrt (E0 L G0 (uc + x))) ∧
  (0 < Xsp L G0 B0 - B0 0 ∧ 0 < Xsp L G0 B0 - B0 L) ∧
  Real.sqrt δs < min |tf (-2 * η)| (tf (2 * η)) / 2 ∧
  ∀ δ0 : ℝ, 0 < δ0 → δ0 ≤ δs → ∀ X : ℝ, |X - Xsp L G0 B0| ≤ δ0 →
    (∀ u ∈ Icc 0 L, 0 ≤ Tfun L G0 B0 X u → uc - η / 4 < u ∧ u < uc + η / 4) ∧
    (∀ u ∈ Icc 0 L, η / 4 ≤ |u - uc| → Tfun L G0 B0 X u < 0 ∧ 0 < X - B0 u) ∧
    (∀ x ∈ Icc (-2 * η) (2 * η),
      (X - B0 (uc + x)) / (2 * Real.sqrt (E0 L G0 (uc + x)))
        = 1 + (tf x ^ 2 - (Xsp L G0 B0 - X)) / (2 * Real.sqrt (E0 L G0 (uc + x)))) ∧
    (∀ x ∈ Icc (-2 * η) (2 * η), -1 < (X - B0 (uc + x)) / (2 * Real.sqrt (E0 L G0 (uc + x)))) ∧
    (1 + η1 ≤ (X - B0 (uc - 2 * η)) / (2 * Real.sqrt (E0 L G0 (uc - 2 * η))) ∧
      1 + η1 ≤ (X - B0 (uc + 2 * η)) / (2 * Real.sqrt (E0 L G0 (uc + 2 * η))))

/-- `a_min`. -/
def aMinOf (L g ρ0 : ℝ) : ℝ := Real.sqrt ((ρ0 / 2) * (L - ρ0 / 2) * g)

/-- `eta_1`. -/
def eta1Of (L Cg ct η : ℝ) : ℝ := ((2 * η * ct) ^ 2 / 2) / (2 * L * Real.sqrt Cg)

/-! ### One parameter value -/

/-- The data of a single principal pair `(G0, B0)` with its fold `uc`: `G0 >= g > 0`, `C^r` symbols, the fold is interior and the unique
maximiser of `f_+`, curvature bounds on a tube, `G0 <= Cg`. -/
structure Single (L : ℝ) (G0 B0 : ℝ → ℝ) (n : ℕ) (g Cg ρ0 m M ρ1 uc : ℝ) : Prop where
  hL : 0 < L
  hg : 0 < g
  hGg : ∀ u ∈ Icc 0 L, g ≤ G0 u
  hGr : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) G0 (Icc 0 L)
  hBr : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) B0 (Icc 0 L)
  ρ0_pos : 0 < ρ0
  m_pos : 0 < m
  mM : m ≤ M
  uc_mem : ρ0 ≤ uc ∧ uc ≤ L - ρ0
  char : ∀ u ∈ Icc 0 L, fPlus L G0 B0 u = Xsp L G0 B0 ↔ u = uc
  curv : ∀ u ∈ Icc (ρ0 / 2) (L - ρ0 / 2), |u - uc| < ρ1 →
    m ≤ -deriv (deriv (fPlus L G0 B0)) u ∧ -deriv (deriv (fPlus L G0 B0)) u ≤ M
  Gub : ∀ u ∈ Icc 0 L, G0 u ≤ Cg

namespace Single

variable {L : ℝ} {G0 B0 : ℝ → ℝ} {n : ℕ} {g Cg ρ0 m M ρ1 uc : ℝ} (sd : Single L G0 B0 n g Cg ρ0 m M ρ1 uc)

include sd

lemma ten : (2 : ℝ) * ρ0 ≤ L := by
  have := sd.uc_mem
  linarith [this.1, this.2]

lemma cont2 : ContDiffOn ℝ 2 G0 (Icc 0 L) ∧ ContDiffOn ℝ 2 B0 (Icc 0 L) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ((n + 2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_add_left 2 n
  exact ⟨sd.hGr.of_le h2, sd.hBr.of_le h2⟩

lemma fcont : ContinuousOn (fPlus L G0 B0) (Icc 0 L) :=
  fPlus_continuousOn sd.cont2.1 sd.cont2.2

lemma f_le : ∀ u ∈ Icc 0 L, fPlus L G0 B0 u ≤ Xsp L G0 B0 := fun u hu => fPlus_le_Xsp sd.fcont hu

lemma uc_Icc : uc ∈ Icc 0 L := ⟨by linarith [sd.uc_mem.1, sd.ρ0_pos], by linarith [sd.uc_mem.2, sd.ρ0_pos]⟩

lemma f_uc : fPlus L G0 B0 uc = Xsp L G0 B0 := (sd.char uc sd.uc_Icc).2 rfl

lemma deriv_uc : deriv (fPlus L G0 B0) uc = 0 := by
  apply IsLocalMax.deriv_eq_zero
  have hmem : Icc 0 L ∈ 𝓝 uc :=
    Icc_mem_nhds (by linarith [sd.uc_mem.1, sd.ρ0_pos]) (by linarith [sd.uc_mem.2, sd.ρ0_pos])
  filter_upwards [hmem] with y hy
  rw [sd.f_uc]
  exact sd.f_le y hy

/-- The Morse data at the fold, for the window radius `3 eta`. -/
lemma morseData {η : ℝ} (hη : 0 < η) (h3 : 3 * η ≤ ρ0 / 2) (h3' : 3 * η < ρ1) :
    MorseData (fPlus L G0 B0) uc (3 * η) (Ioo 0 L) n m M where
  hρ := by linarith
  hU := isOpen_Ioo
  hUρ := by
    intro u hu
    have := sd.uc_mem
    constructor <;> nlinarith [hu.1, hu.2, sd.ρ0_pos]
  hf := fPlus_contDiffOn_r sd.hGg sd.hg sd.hGr sd.hBr
  hf0 := sd.deriv_uc
  hm := sd.m_pos
  hmM := sd.mM
  hb := by
    intro u hu
    have hu1 := sd.uc_mem
    have habs : |u - uc| < ρ1 := by
      rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]
    exact sd.curv u ⟨by linarith [hu.1], by linarith [hu.2]⟩ habs

lemma E_lower {u : ℝ} (hu : u ∈ Icc (ρ0 / 2) (L - ρ0 / 2)) : (ρ0 / 2) * (L - ρ0 / 2) * g ≤ E0 L G0 u := by
  have hu0 : u ∈ Icc 0 L := ⟨by linarith [hu.1, sd.ρ0_pos], by linarith [hu.2, sd.ρ0_pos]⟩
  have h1 : (ρ0 / 2) * (L - ρ0 / 2) ≤ u * (L - u) := by nlinarith [hu.1, hu.2]
  have h2 : g ≤ G0 u := sd.hGg u hu0
  have h3 : 0 ≤ (ρ0 / 2) * (L - ρ0 / 2) := by nlinarith [sd.ρ0_pos, sd.ten]
  unfold E0
  exact mul_le_mul h1 h2 sd.hg.le (le_trans h3 h1)

lemma E_upper {u : ℝ} (hu : u ∈ Icc 0 L) : E0 L G0 u ≤ L ^ 2 * Cg := by
  have h1 : u * (L - u) ≤ L ^ 2 := by nlinarith [hu.1, hu.2]
  have h2 : G0 u ≤ Cg := sd.Gub u hu
  have h3 : 0 ≤ G0 u := le_trans sd.hg.le (sd.hGg u hu)
  have h4 : 0 ≤ u * (L - u) := mul_nonneg hu.1 (by linarith [hu.2])
  have hC : 0 ≤ Cg := le_trans h3 h2
  unfold E0
  calc u * (L - u) * G0 u ≤ L ^ 2 * G0 u := mul_le_mul_of_nonneg_right h1 h3
    _ ≤ L ^ 2 * Cg := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)

/-- Away from the fold (`|u - uc| >= eta/4`): `T < 0` and `X - B_0 > 0`, for `X >= X_s - gamma/2`. -/
lemma far {η γ X : ℝ} (hgap : ∀ u ∈ Icc 0 L, η / 4 ≤ |u - uc| → fPlus L G0 B0 u + γ ≤ Xsp L G0 B0)
    (hγ : 0 < γ) (hX : Xsp L G0 B0 - γ / 2 ≤ X) :
    ∀ u ∈ Icc 0 L, η / 4 ≤ |u - uc| → Tfun L G0 B0 X u < 0 ∧ 0 < X - B0 u := by
  intro u hu hfar
  have hf : fPlus L G0 B0 u < X := by
    have := hgap u hu hfar
    linarith
  have hE : 0 ≤ Real.sqrt (E0 L G0 u) := Real.sqrt_nonneg _
  have hfp : fPlus L G0 B0 u = B0 u + 2 * Real.sqrt (E0 L G0 u) := rfl
  have hB : 0 < X - B0 u := by linarith
  refine ⟨?_, hB⟩
  rw [Tfun_eq sd.hGg sd.hg hu]
  have : fMinus L G0 B0 u = B0 u - 2 * Real.sqrt (E0 L G0 u) := rfl
  exact mul_neg_of_neg_of_pos (by linarith) (by rw [this]; linarith)

lemma Cg_pos : 0 < Cg := lt_of_lt_of_le sd.hg (le_trans (sd.hGg uc sd.uc_Icc) (sd.Gub uc sd.uc_Icc))

lemma aMin_pos : 0 < aMinOf L g ρ0 := by
  unfold aMinOf
  apply Real.sqrt_pos.2
  have := sd.ten
  have := sd.ρ0_pos
  have := sd.hg
  have h1 : 0 < L - ρ0 / 2 := by linarith
  positivity

lemma eta1_pos {η ct : ℝ} (hη : 0 < η) (hct : 0 < ct) : 0 < eta1Of L Cg ct η := by
  unfold eta1Of
  have := sd.hL
  have := sd.Cg_pos
  positivity

lemma body {η δs γ : ℝ} (hη : 0 < η) (h3 : 3 * η ≤ ρ0 / 2) (h3' : 3 * η < ρ1) (hγ : 0 < γ)
    (hgap : ∀ u ∈ Icc 0 L, η / 4 ≤ |u - uc| → fPlus L G0 B0 u + γ ≤ Xsp L G0 B0)
    (hδ0 : 0 < δs) (hδ1 : δs ≤ γ / 2) (hδ2 : δs ≤ 2 * aMinOf L g ρ0)
    (hδ3 : δs ≤ (2 * η * ctOf m M) ^ 2 / 8) :
    SoftBody L G0 B0 (n + 2) η δs uc (ctOf m M) (aMinOf L g ρ0) (eta1Of L Cg (ctOf m M) η)
      (morseT (fPlus L G0 B0) uc) := by
  obtain ⟨hcd, h0, hmain⟩ := (sd.morseData hη h3 h3').main
  have hρ0 := sd.ρ0_pos
  have hten := sd.ten
  have hL := sd.hL
  have hct : 0 < ctOf m M := (sd.morseData hη h3 h3').ctOf_pos
  have hxI : ∀ x ∈ Icc (-2 * η) (2 * η), x ∈ Ioo (-(3 * η)) (3 * η) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxU : ∀ x ∈ Icc (-2 * η) (2 * η), uc + x ∈ Icc (ρ0 / 2) (L - ρ0 / 2) := by
    intro x hx
    have := sd.uc_mem
    exact ⟨by linarith [hx.1, this.1], by linarith [hx.2, this.2]⟩
  have hxI0 : ∀ x ∈ Icc (-2 * η) (2 * η), uc + x ∈ Icc 0 L :=
    fun x hx => ⟨by linarith [(hxU x hx).1], by linarith [(hxU x hx).2]⟩
  have hEs : ∀ x ∈ Icc (-2 * η) (2 * η), aMinOf L g ρ0 ≤ Real.sqrt (E0 L G0 (uc + x)) :=
    fun x hx => Real.sqrt_le_sqrt (sd.E_lower (hxU x hx))
  have hEpos : ∀ x ∈ Icc (-2 * η) (2 * η), 0 < Real.sqrt (E0 L G0 (uc + x)) :=
    fun x hx => lt_of_lt_of_le sd.aMin_pos (hEs x hx)
  have hEup : ∀ x ∈ Icc (-2 * η) (2 * η), Real.sqrt (E0 L G0 (uc + x)) ≤ L * Real.sqrt Cg := by
    intro x hx
    calc Real.sqrt (E0 L G0 (uc + x)) ≤ Real.sqrt (L ^ 2 * Cg) := Real.sqrt_le_sqrt (sd.E_upper (hxI0 x hx))
      _ = L * Real.sqrt Cg := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]
  have hends := tf_ends hη h0 (fun x hx => ⟨(hmain x hx).2.1, (hmain x hx).1⟩)
  set t := morseT (fPlus L G0 B0) uc with ht
  set ct := ctOf m M with hctdef
  have hτ : 0 < 2 * η * ct := by positivity
  have e2 : -2 * η = -(2 * η) := by ring
  have hid : ∀ x ∈ Icc (-2 * η) (2 * η), fPlus L G0 B0 (uc + x) = Xsp L G0 B0 - t x ^ 2 := by
    intro x hx
    rw [(hmain x (hxI x hx)).2.2, sd.f_uc]
  have hlow : (2 * η * ct) ^ 2 ≤ t (-2 * η) ^ 2 ∧ (2 * η * ct) ^ 2 ≤ t (2 * η) ^ 2 := by
    rw [e2]
    constructor <;> nlinarith [hends.1, hends.2]
  refine ⟨⟨by linarith [sd.uc_mem.1], by linarith [sd.uc_mem.2], sd.f_uc⟩, ?_, h0,
    fun x hx => ⟨(hmain x (hxI x hx)).1, hid x hx⟩, hEs, ?_, ?_, ?_⟩
  · have : (n + 2 - 2 : ℕ) = n := by omega
    rw [this]
    exact hcd.mono (fun x hx => hxI x hx)
  · have h0L : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
    have hLL : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
    have a1 : fPlus L G0 B0 0 = B0 0 := fPlus_zero
    have a2 : fPlus L G0 B0 L = B0 L := fPlus_L
    have n1 : fPlus L G0 B0 0 ≠ Xsp L G0 B0 := fun h => by
      have := (sd.char 0 h0L).1 h
      linarith [sd.uc_mem.1]
    have n2 : fPlus L G0 B0 L ≠ Xsp L G0 B0 := fun h => by
      have := (sd.char L hLL).1 h
      linarith [sd.uc_mem.2]
    constructor
    · have := lt_of_le_of_ne (sd.f_le 0 h0L) n1
      linarith
    · have := lt_of_le_of_ne (sd.f_le L hLL) n2
      linarith
  · have hmin : 2 * η * ct ≤ min |t (-2 * η)| (t (2 * η)) :=
      le_min (le_abs.2 (Or.inr (by rw [e2]; linarith [hends.2]))) hends.1
    have hsq : Real.sqrt δs < 2 * η * ct / 2 :=
      (Real.sqrt_lt' (by positivity)).2 (by nlinarith [hτ, hδ3])
    linarith
  · intro δ0 hδ0' hδ0s X hX
    have hXs := abs_le.1 hX
    have hXlo : Xsp L G0 B0 - γ / 2 ≤ X := by linarith [hXs.1]
    have hfar := sd.far hgap hγ hXlo
    have hkey : ∀ x ∈ Icc (-2 * η) (2 * η),
        B0 (uc + x) = Xsp L G0 B0 - t x ^ 2 - 2 * Real.sqrt (E0 L G0 (uc + x)) := by
      intro x hx
      have := hid x hx
      unfold fPlus at this
      linarith
    have hnf : ∀ x ∈ Icc (-2 * η) (2 * η),
        (X - B0 (uc + x)) / (2 * Real.sqrt (E0 L G0 (uc + x)))
          = 1 + (t x ^ 2 - (Xsp L G0 B0 - X)) / (2 * Real.sqrt (E0 L G0 (uc + x))) := by
      intro x hx
      have hE := (hEpos x hx).ne'
      rw [hkey x hx]
      field_simp
      ring
    refine ⟨?_, hfar, hnf, ?_, ?_⟩
    · intro u hu hT
      by_contra hn
      have hfarr : η / 4 ≤ |u - uc| := by
        by_contra h'
        push_neg at h'
        rw [abs_lt] at h'
        exact hn ⟨by linarith [h'.1], by linarith [h'.2]⟩
      linarith [(hfar u hu hfarr).1]
    · intro x hx
      have hE := hEpos x hx
      have hEa := hEs x hx
      rw [lt_div_iff₀ (by positivity), hkey x hx]
      nlinarith [sq_nonneg (t x), sd.aMin_pos]
    · have hend : ∀ x ∈ Icc (-2 * η) (2 * η), (2 * η * ct) ^ 2 ≤ t x ^ 2 →
          1 + eta1Of L Cg ct η ≤ (X - B0 (uc + x)) / (2 * Real.sqrt (E0 L G0 (uc + x))) := by
        intro x hx htx
        rw [hnf x hx]
        have hE := hEpos x hx
        have hnum : (2 * η * ct) ^ 2 / 2 ≤ t x ^ 2 - (Xsp L G0 B0 - X) := by
          have : Xsp L G0 B0 - X ≤ (2 * η * ct) ^ 2 / 8 := by linarith [hXs.2]
          nlinarith [hτ]
        have hden : 2 * Real.sqrt (E0 L G0 (uc + x)) ≤ 2 * L * Real.sqrt Cg := by
          have := hEup x hx
          nlinarith
        have hCg := sd.Cg_pos
        have h1 : eta1Of L Cg ct η ≤ (t x ^ 2 - (Xsp L G0 B0 - X)) / (2 * Real.sqrt (E0 L G0 (uc + x))) := by
          unfold eta1Of
          apply div_le_div₀ (by nlinarith [hτ]) hnum (by positivity) hden
        linarith
      have ea : uc - 2 * η = uc + (-2 * η) := by ring
      refine ⟨?_, ?_⟩
      · rw [ea]
        exact hend _ ⟨le_rfl, by linarith⟩ hlow.1
      · exact hend _ ⟨by linarith, le_rfl⟩ hlow.2

end Single

/-! ### The conclusion for a family -/

lemma single_of {F : SymbolFamily Par} {K : Set Par} {n : ℕ} {g : ℝ} (h : SoftHyp F K g)
    (hreg : PrincipalReg F K (n + 2)) {uc : Par → ℝ} {ρ0 m M ρ1 Cg : ℝ} (ud : UData F K uc ρ0 m M ρ1 Cg)
    {μ : Par} (hμ : μ ∈ K) : Single F.L (F.G 0 μ) (F.B 0 μ) n g Cg ρ0 m M ρ1 (uc μ) where
  hL := F.L_pos
  hg := h.hg
  hGg := h.lb μ hμ
  hGr := hreg.1.1 μ hμ
  hBr := hreg.2.1 μ hμ
  ρ0_pos := ud.ρ0_pos
  m_pos := ud.m_pos
  mM := ud.mM
  uc_mem := ud.uc_mem μ hμ
  char := ud.uc_char μ hμ
  curv := ud.curv μ hμ
  Gub := ud.Gub μ hμ

/-- **lem:tha-geom (d)** at the upper soft edge, from the soft hypotheses. -/
theorem softConcl (F : SymbolFamily Par) (K : Set Par) (r : ℕ) (hr : 2 ≤ r) (hK : IsCompact K) {g : ℝ}
    (h : SoftHyp F K g) (hreg : PrincipalReg F K r) : GeomSoftConcl F K r := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨μ1, hμ1⟩
  · exact ⟨1, one_pos, fun η _ _ => ⟨1, one_pos, fun _ => 0, fun _ _ => 0, 1, 1, 1, one_pos, one_pos, one_pos,
      fun μ hμ => absurd hμ (notMem_empty μ)⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  obtain ⟨uc, hf⟩ := fold_exists hr h hreg
  obtain ⟨ρ0, m, M, ρ1, Cg, ud⟩ := uData_exists hr hK h hreg hf
  have hs1 := single_of h hreg ud hμ1
  have hmd : 0 < ctOf m M := by
    unfold ctOf
    have h1 : 0 < M := lt_of_lt_of_le ud.m_pos ud.mM
    have h2 : 0 < Real.sqrt (M / 2) := Real.sqrt_pos.2 (by linarith)
    exact div_pos ud.m_pos (by linarith)
  refine ⟨min (ρ0 / 6) (ρ1 / 4), lt_min (by linarith [ud.ρ0_pos]) (by linarith [ud.ρ1_pos]), fun η hη hηle => ?_⟩
  have hη1 : η ≤ ρ0 / 6 := le_trans hηle (min_le_left _ _)
  have hη2 : η ≤ ρ1 / 4 := le_trans hηle (min_le_right _ _)
  have h3 : 3 * η ≤ ρ0 / 2 := by linarith
  have h3' : 3 * η < ρ1 := by linarith [ud.ρ1_pos]
  obtain ⟨γ, hγ, hgap⟩ := ud.gap (η / 4) (by positivity)
  have hτ : 0 < (2 * η * ctOf m M) ^ 2 / 8 := by positivity
  refine ⟨min (min (γ / 2) (2 * aMinOf F.L g ρ0)) ((2 * η * ctOf m M) ^ 2 / 8),
    lt_min (lt_min (by linarith) (by linarith [hs1.aMin_pos])) hτ, uc,
    fun μ => morseT (fPlus F.L (F.G 0 μ) (F.B 0 μ)) (uc μ), ctOf m M, aMinOf F.L g ρ0,
    eta1Of F.L Cg (ctOf m M) η, hmd, hs1.aMin_pos, hs1.eta1_pos hη hmd, fun μ hμ => ?_⟩
  exact (single_of h hreg ud hμ).body hη h3 h3' hγ (fun u hu hε => hgap μ hμ u hu hε)
    (lt_min (lt_min (by linarith) (by linarith [hs1.aMin_pos])) hτ)
    ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)

/-! ### `GeomSoft`, `GeomSoftLower`, `TheGeometry` -/

lemma softHyp_of_hypOn {F : SymbolFamily Par} {K : Set Par} (hyp : HypOn F K) : ∃ g : ℝ, SoftHyp F K g := by
  obtain ⟨g, hg⟩ := hyp
  rcases K.eq_empty_or_nonempty with rfl | ⟨μ1, hμ1⟩
  · exact ⟨1, ⟨one_pos, fun μ hμ => absurd hμ (notMem_empty μ), fun μ hμ => absurd hμ (notMem_empty μ)⟩⟩
  · exact ⟨g, ⟨(hg μ1 hμ1).gstar_pos, fun μ hμ => (hg μ hμ).G0_lb, fun μ hμ => (hg μ hμ).H3p⟩⟩

/-- **lem:tha-geom (d)**, upper soft edge. -/
theorem geomSoft (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : GeomSoft F K r := by
  intro hr hK hyp hreg
  obtain ⟨g, h⟩ := softHyp_of_hypOn hyp
  exact softConcl F K r hr hK h hreg

lemma jetReg_neg {K : Set Par} {L : ℝ} {r : ℕ} {f : Par → ℝ → ℝ} (hf : JetReg f K L r) :
    JetReg (fun μ s => -f μ s) K L r := by
  refine ⟨fun μ hμ => (hf.1 μ hμ).neg, fun i hi => ?_⟩
  have := (hf.2 i hi).neg
  refine this.congr (fun p hp => ?_)
  exact iteratedDerivWithin_fun_neg (f p.1)

lemma softHyp_neg {F : SymbolFamily Par} {K : Set Par} {r : ℕ} (hr : 2 ≤ r) (hyp : HypOn F K)
    (hreg : PrincipalReg F K r) : ∃ g : ℝ, SoftHyp (negFamily F) K g := by
  obtain ⟨g, hg⟩ := hyp
  have hr2 : (2 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
  rcases K.eq_empty_or_nonempty with rfl | ⟨μ1, hμ1⟩
  · exact ⟨1, ⟨one_pos, fun μ hμ => absurd hμ (notMem_empty μ), fun μ hμ => absurd hμ (notMem_empty μ)⟩⟩
  refine ⟨g, ⟨(hg μ1 hμ1).gstar_pos, fun μ hμ => (hg μ hμ).G0_lb, fun μ hμ => ?_⟩⟩
  obtain ⟨uc, h0, hL, hchar, hdd⟩ := (hg μ hμ).H3m
  have hG2 : ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) := (hreg.1.1 μ hμ).of_le hr2
  have hB2 : ContDiffOn ℝ 2 (F.B 0 μ) (Icc 0 F.L) := (hreg.2.1 μ hμ).of_le hr2
  have hucI : uc ∈ Icc 0 F.L := ⟨h0.le, hL.le⟩
  have hqe : fMinus F.L (F.G 0 μ) (F.B 0 μ) uc = Xsm F.L (F.G 0 μ) (F.B 0 μ) := (hchar uc hucI).2 rfl
  have hX : Xsp F.L (F.G 0 μ) (fun u => -F.B 0 μ u) = -Xsm F.L (F.G 0 μ) (F.B 0 μ) :=
    Xsp_neg_B (fMinus_continuousOn hG2 hB2) hucI hqe
  refine ⟨uc, h0, hL, ?_, ?_⟩
  · intro u hu
    show fPlus F.L (F.G 0 μ) (fun u => -F.B 0 μ u) u = Xsp F.L (F.G 0 μ) (fun u => -F.B 0 μ u) ↔ u = uc
    rw [hX, congrFun fPlus_neg_B u]
    rw [← hchar u hu]
    constructor <;> intro h <;> linarith
  · show deriv (deriv (fPlus F.L (F.G 0 μ) (fun u => -F.B 0 μ u))) uc < 0
    rw [congrFun deriv_deriv_fPlus_neg uc]
    linarith

/-- **lem:tha-geom (d)**, lower soft edge (through `negFamily`). -/
theorem geomSoftLower (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : GeomSoftLower F K r := by
  intro hr hK hyp hreg
  obtain ⟨g, h⟩ := softHyp_neg hr hyp hreg
  have hreg' : PrincipalReg (negFamily F) K r := ⟨hreg.1, jetReg_neg hreg.2⟩
  exact softConcl (negFamily F) K r hr hK h hreg'

/-- **lem:tha-geom** for every family (all of (a)--(d)). -/
theorem theGeometry (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : TheGeometry F K r :=
  theGeometry_of_soft F K r (geomSoft F K r) (geomSoftLower F K r)

end FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge.geomSoft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge.geomSoft

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge.geomSoftLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge.geomSoftLower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge.theGeometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.SoftEdge.theGeometry
