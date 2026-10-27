import Mathlib
import FormalResearch.FrameFree.HelstromSupport

/-!
# QI-B `thm:finite`: one finite projective orbit suffices

Formalises `thm:finite` of `QI-B/paper/invariant_discrimination_exponents.tex` (label `thm:finite`):
if at least one of the two projective `K`-orbits (`K = SU(2)^n`, acting by `rot u`) is finite, then
`F_K(x,y)^d / 4 ≤ P_e^K(d) ≤ s F_K(x,y)^d` (the upper bound for all large `d`, with `s` the number of
rays of the finite orbit), hence `-(1/d) log P_e^K(d) → -log F_K(x,y) = C_K(x,y)` whenever `F_K(x,y) > 0`.

**Setting.**  The existing `FrameFree.Helstrom.Pe k ψ` is the invariant-test error for the pair
`(ψ, Θψ)` only.  Nothing in its proof uses `Θ`, so here `PeP k x y` is the same definition for an
arbitrary pair `(x, y)` (`Pe_eq_PeP : Pe k ψ = PeP k ψ (Θ ψ)` is `rfl`), and the theorem is proved for
an arbitrary unit pair; `thm_finite_Theta` is the specialisation to `(ψ, Θψ)` stated with `Pe`, `FKΘ`, `CK`.

**Finite-orbit hypothesis** (`FiniteOrbit y s b`): the rays of the orbit `{rot u y : u ∈ SU(2)^n}` are exactly
the `s` pairwise non-proportional rays `b 0, …, b (s-1)`, each of which is an orbit point.

**Proof, as in the paper.**  Lower bound: `Pe_ge_of_rot` (the closest-pair converse `F^d/4 ≤ P_e`), which
needs `F_K` to be attained; for a finite orbit it is (`FK_attained`).  Upper bound: the test that accepts
`x` on the orthogonal complement of the support space `span{b_j^{⊗d}}` is `K`-invariant
(`suppB_isInv`), never errs on `y`, and `‖Π x^{⊗d}‖² ≤ 2 Σ_j |⟨b_j,x⟩|^{2d} ≤ 2 s F^d` once the Gram
matrix of the `b_j^{⊗d}` is `⪰ I/2` (`proj_sq_le`: this is the paper's `‖G_d - I‖ ≤ (s-1) α^d`
estimate, done here with the cruder constant `s α^d ≤ 1/2`, which also holds for large `d`).

**Cross-references (not re-proved).**  `prop:supportstruct`'s elementary parts `R_d ≥ F_C^d` is
`FrameFree/HelstromSupport.lean: FCΘ_pow_le_Rk`; its spectral-radius half is
`FrameFree/SupportRate*.lean`.  `prop:orbitideal` (`W_{y,d} = I_d(X_y)^⊥`) is Zariski/Bombieri-pairing
algebra and is not formalised there; `thm:finite` does not use it (only the elementary support space
`span{(ky)^{⊗d}}`, which here is `suppB`).

**Notes on the paper's statement.**  `F < 1` is not used by the proof (for `F = 1` both bounds are
trivial and the limit is `0 = -log 1`); `0 < F` is automatic for unit `ψ` in the `Θ`-setting
(`FKΘ_pos`) and is a hypothesis for a general pair.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexConjugate Matrix BigOperators InnerProductSpace
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom
open Filter

namespace FormalResearch.QIB

/-! ### An abstract projection estimate -/

/-- Projection of `x` onto the span of `s` unit vectors with pairwise overlaps `≤ ε`, `s ε ≤ 1/2`:
`‖Π x‖² ≤ 2 Σ_j |⟨v_j, x⟩|²`. -/
theorem proj_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} (v : Fin s → EuclideanSpace ℂ ι)
    (hv : ∀ j, ‖v j‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ i j, i ≠ j → ‖⟪v i, v j⟫_ℂ‖ ≤ ε) (hs : (s : ℝ) * ε ≤ 1 / 2)
    (x : EuclideanSpace ℂ ι) :
    ‖(Submodule.span ℂ (Set.range v)).starProjection x‖ ^ 2 ≤ 2 * ∑ j, ‖⟪v j, x⟫_ℂ‖ ^ 2 := by
  set W := Submodule.span ℂ (Set.range v) with hW
  set w := W.starProjection x with hw
  have hwW : w ∈ W := Submodule.starProjection_apply_mem W x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hwW
  set a : Fin s → ℝ := fun j => ‖c j‖ with ha
  set A : ℝ := ∑ j, a j ^ 2 with hA
  set S : ℝ := ∑ j, ‖⟪v j, x⟫_ℂ‖ ^ 2 with hS
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h0 : ⟪x - w, w⟫_ℂ = 0 := Submodule.starProjection_inner_eq_zero x w hwW
  have hxw : ⟪x, w⟫_ℂ = ⟪w, w⟫_ℂ := by
    have := inner_sub_left x w w (𝕜 := ℂ)
    rw [h0] at this
    exact sub_eq_zero.1 this.symm
  have hww : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hwx : ⟪w, x⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hxw, hww]; simp
  set t : ℝ := ‖w‖ ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  -- upper bound on t
  have hup : t ^ 2 ≤ A * S := by
    have h1 : t = ‖⟪w, x⟫_ℂ‖ := by rw [hwx]; simp [abs_of_nonneg ht0]
    have h2 : ⟪w, x⟫_ℂ = ∑ j, conj (c j) * ⟪v j, x⟫_ℂ := by
      rw [← hc, sum_inner]
      exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_left]
    have h3 : t ≤ ∑ j, a j * ‖⟪v j, x⟫_ℂ‖ := by
      rw [h1, h2]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, RCLike.norm_conj]
    have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j => ‖⟪v j, x⟫_ℂ‖)
    calc t ^ 2 ≤ (∑ j, a j * ‖⟪v j, x⟫_ℂ‖) ^ 2 := pow_le_pow_left₀ ht0 h3 2
      _ ≤ A * S := h4
  -- lower bound on t
  have hlow : A - ε * (s * A) ≤ t := by
    have h1 : ⟪w, w⟫_ℂ = ∑ i, ∑ j, conj (c i) * (c j * ⟪v i, v j⟫_ℂ) := by
      conv_lhs => rw [← hc]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_left, inner_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right]
    have h2 : t = ∑ i, ∑ j, (conj (c i) * (c j * ⟪v i, v j⟫_ℂ)).re := by
      have := congrArg Complex.re (hww.symm.trans h1)
      rw [Complex.ofReal_re, Complex.re_sum] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.re_sum]
    have h3 : ∀ i j, (if i = j then a i ^ 2 else 0) - ε * (a i * a j)
        ≤ (conj (c i) * (c j * ⟪v i, v j⟫_ℂ)).re := by
      intro i j
      by_cases hij : i = j
      · subst hij
        have hone : ⟪v i, v i⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K, hv i]; simp
        have hi : (if i = i then a i ^ 2 else 0) = a i ^ 2 := by simp
        rw [hone, hi]
        have : (conj (c i) * (c i * 1)).re = a i ^ 2 := by
          rw [mul_one, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
        rw [this]
        have : 0 ≤ ε * (a i * a i) := by positivity
        linarith
      · have hi : (if i = j then a i ^ 2 else 0) = 0 := by simp [hij]
        rw [hi, zero_sub]
        have hb := hε i j hij
        have h5 : ‖conj (c i) * (c j * ⟪v i, v j⟫_ℂ)‖ ≤ a i * a j * ε := by
          rw [norm_mul, RCLike.norm_conj, norm_mul]
          have : 0 ≤ a i * a j := by positivity
          calc ‖c i‖ * (‖c j‖ * ‖⟪v i, v j⟫_ℂ‖) = a i * a j * ‖⟪v i, v j⟫_ℂ‖ := by
                simp [ha]; ring
            _ ≤ a i * a j * ε := mul_le_mul_of_nonneg_left hb this
        have h6 := (abs_le.1 (Complex.abs_re_le_norm (conj (c i) * (c j * ⟪v i, v j⟫_ℂ)))).1
        linarith
    have h4 : ∑ i, ∑ j, ((if i = j then a i ^ 2 else 0) - ε * (a i * a j))
        = A - ε * (∑ i, a i) ^ 2 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      simp only [Finset.mul_sum]
      rfl
    have h5 : (∑ i, a i) ^ 2 ≤ s * A := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
      simpa using this
    have h6 : t ≥ ∑ i, ∑ j, ((if i = j then a i ^ 2 else 0) - ε * (a i * a j)) := by
      rw [h2]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h3 i j
    rw [h4] at h6
    have := mul_le_mul_of_nonneg_left h5 hε0
    linarith
  have hA2 : A / 2 ≤ t := by
    have : ε * (s * A) ≤ A / 2 := by
      have := mul_le_mul_of_nonneg_right hs hA0
      nlinarith
    linarith
  by_cases ht' : t = 0
  · rw [ht']; linarith
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht')
    have : t * t ≤ t * (2 * S) := by nlinarith
    exact le_of_mul_le_mul_left this htpos

/-! ### Small algebra of `ip`, `nsq`, `copies` -/

theorem ip_conj_symm' {n : ℕ} (φ ψ : Ψ n) : ip φ ψ = conj (ip ψ φ) := by
  unfold ip
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_comm]

theorem ip_smul_right {n : ℕ} (c : ℂ) (φ ψ : Ψ n) : ip φ (c • ψ) = c * ip φ ψ := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_left_comm]

theorem ip_smul_left {n : ℕ} (c : ℂ) (φ ψ : Ψ n) : ip (c • φ) ψ = conj c * ip φ ψ := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_assoc]

theorem ip_sub_left {n : ℕ} (φ φ' ψ : Ψ n) : ip (φ - φ') ψ = ip φ ψ - ip φ' ψ := by
  simp [ip, sub_mul, Finset.sum_sub_distrib]

theorem ip_sub_right {n : ℕ} (φ ψ ψ' : Ψ n) : ip φ (ψ - ψ') = ip φ ψ - ip φ ψ' := by
  simp [ip, mul_sub, Finset.sum_sub_distrib]

theorem nsq_smul {n : ℕ} (c : ℂ) (φ : Ψ n) : nsq (c • φ) = Complex.normSq c * nsq φ := by
  unfold nsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Complex.normSq_mul]

theorem copies_smul {n : ℕ} (k : ℕ) (c : ℂ) (φ : Ψ n) : copies k (c • φ) = c ^ k • copies k φ := by
  funext i
  simp [copies, Finset.prod_mul_distrib]

/-- Two unit vectors that are not proportional have `|⟨φ,ψ⟩|² < 1` (strict Cauchy-Schwarz). -/
theorem normSq_ip_lt_one {n : ℕ} {φ ψ : Ψ n} (hφ : nsq φ = 1) (hψ : nsq ψ = 1)
    (h : ¬ ∃ c : ℂ, φ = c • ψ) : Complex.normSq (ip φ ψ) < 1 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ip ψ φ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Ψ n, r = φ - c • ψ := ⟨_, rfl⟩
  have key : ip r r = 1 - (Complex.normSq c : ℂ) := by
    have e1 : ip φ φ = 1 := by rw [ip_self, hφ]; simp
    have e2 : ip ψ ψ = 1 := by rw [ip_self, hψ]; simp
    have e3 : ip φ ψ = conj c := by rw [hc]; exact ip_conj_symm' φ ψ
    rw [hr]
    simp only [ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, e1, e2, e3, ← hc]
    rw [← Complex.mul_conj]
    ring
  have hrr : ip r r = (nsq r : ℂ) := ip_self r
  have hnr : nsq r = 1 - Complex.normSq c := by
    have := hrr.symm.trans key
    exact_mod_cast this
  have hr0 : nsq r ≠ 0 := by
    intro h0
    apply h
    refine ⟨c, ?_⟩
    have hz : ∀ x, r x = 0 := by
      intro x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (r x))).1 h0 x
        (Finset.mem_univ x)
      exact Complex.normSq_eq_zero.1 this
    funext x
    have := hz x
    rw [hr, Pi.sub_apply, sub_eq_zero] at this
    exact this
  have hpos : 0 < nsq r :=
    lt_of_le_of_ne (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg (r x)) (Ne.symm hr0)
  have : Complex.normSq (ip φ ψ) = Complex.normSq c := by
    rw [ip_conj_symm' φ ψ, Complex.normSq_conj, hc]
  rw [this]
  linarith

/-! ### The pair error `PeP` -/

/-- The frame-free error for an arbitrary pair `(x, y)`: the best equal-prior error of a
`K`-invariant test between `x^{⊗k}` and `y^{⊗k}`.  `PeP k ψ (Θ ψ) = Pe k ψ`. -/
noncomputable def PeP {n : ℕ} (k : ℕ) (x y : Ψ n) : ℝ :=
  sInf {r | ∃ E, IsInvEffect (n := n) k E ∧ r = err E (copies k x) (copies k y)}

theorem Pe_eq_PeP {n : ℕ} (k : ℕ) (ψ : Ψ n) : Pe k ψ = PeP k ψ (Θ ψ) := rfl

theorem PeP_bdd {n : ℕ} (k : ℕ) (x y : Ψ n) :
    BddBelow {r | ∃ E, IsInvEffect (n := n) k E ∧ r = err E (copies k x) (copies k y)} :=
  ⟨0, by rintro r ⟨E, hE, rfl⟩; exact err_nonneg hE.1 _ _⟩

theorem PeP_le_err {n : ℕ} {k : ℕ} {E : Matrix (Copies n k) (Copies n k) ℂ} (hE : IsInvEffect k E)
    (x y : Ψ n) : PeP k x y ≤ err E (copies k x) (copies k y) :=
  csInf_le (PeP_bdd k x y) ⟨E, hE, rfl⟩

/-- The closest-pair converse for any unit pair: `|⟨x|u y⟩|^{2k}/4 ≤ P_e(k)`. -/
theorem PeP_ge_of_rot {n : ℕ} {x y : Ψ n} (hx : nsq x = 1) (hy : nsq y = 1) (u : Fin n → Op1)
    (hu : ∀ i, SU2 (u i)) (k : ℕ) : Complex.normSq (ip x (rot u y)) ^ k / 4 ≤ PeP k x y := by
  refine le_csInf ⟨_, 0, isInvEffect_zero k, rfl⟩ ?_
  rintro r ⟨E, hE, rfl⟩
  rw [← err_rot_right hE u hu, ← copies_rot]
  have hrot : nsq (rot u y) = 1 := by rw [nsq_rot u hu, hy]
  have h := quarter_le_err hE.1 (star_copies_self k x hx) (star_copies_self k (rot u y) hrot)
  rw [star_copies_dot, ← ip_eq_dot, map_pow] at h
  exact h

theorem isInvEffect_one_sub {n : ℕ} {k : ℕ} {E : Matrix (Copies n k) (Copies n k) ℂ}
    (hE : IsInvEffect k E) : IsInvEffect k (1 - E) :=
  ⟨⟨hE.1.2, by simpa using hE.1.1⟩, fun u hu => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hE.2 u hu]⟩

theorem err_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Matrix ι ι ℂ) (a b : ι → ℂ) :
    err (1 - E) b a = err E a b := by
  unfold err
  rw [sub_sub_cancel]
  ring

theorem PeP_le_swap {n : ℕ} (k : ℕ) (x y : Ψ n) : PeP k x y ≤ PeP k y x := by
  refine le_csInf ⟨_, 0, isInvEffect_zero k, rfl⟩ ?_
  rintro r ⟨E, hE, rfl⟩
  have := PeP_le_err (isInvEffect_one_sub hE) x y
  rwa [err_one_sub] at this

/-- Swapping the two hypotheses does not change the invariant error (replace `E` by `1 - E`). -/
theorem PeP_comm {n : ℕ} (k : ℕ) (x y : Ψ n) : PeP k x y = PeP k y x :=
  le_antisymm (PeP_le_swap k x y) (PeP_le_swap k y x)

theorem rotSet_subset_swap {n : ℕ} (x y : Ψ n) : rotSet x y ⊆ rotSet y x := by
  rintro r ⟨u, hu, rfl⟩
  refine ⟨fun i => (u i)ᴴ, fun i => SU2_adjoint (hu i), ?_⟩
  have h1 : rot (fun i => (u i)ᴴ) (rot u y) = y := by
    rw [rot_comp]
    have : (fun i => (u i)ᴴ * u i) = fun _ => (1 : Op1) := funext fun i => (hu i).1
    rw [this, rot_one]
  have h2 := ip_rot (fun i => (u i)ᴴ) (fun i => (SU2_adjoint (hu i)).1) x (rot u y)
  rw [h1] at h2
  rw [← h2, ip_conj_symm' (rot _ x) y, Complex.normSq_conj]

theorem FK_comm {n : ℕ} (x y : Ψ n) : FK x y = FK y x := by
  unfold FK
  rw [Set.Subset.antisymm (rotSet_subset_swap x y) (rotSet_subset_swap y x)]

/-! ### Finite projective orbits -/

/-- `b 0, …, b (s-1)` are the `s` distinct rays of the orbit `{rot u y : u ∈ SU(2)^n}`: each is an
orbit point, every orbit point is proportional to one of them, and they are pairwise non-proportional. -/
structure FiniteOrbit {n : ℕ} (y : Ψ n) (s : ℕ) (b : Fin s → Ψ n) : Prop where
  mem : ∀ j, ∃ u : Fin n → Op1, (∀ i, SU2 (u i)) ∧ b j = rot u y
  cover : ∀ u : Fin n → Op1, (∀ i, SU2 (u i)) → ∃ j, ∃ c : ℂ, rot u y = c • b j
  sep : ∀ i j, i ≠ j → ¬ ∃ c : ℂ, b i = c • b j

namespace FiniteOrbit

variable {n : ℕ} {y : Ψ n} {s : ℕ} {b : Fin s → Ψ n}

theorem pos (hb : FiniteOrbit y s b) : 0 < s := by
  obtain ⟨j, _⟩ := hb.cover (fun _ => 1) (fun _ => SU2_one)
  exact Fin.pos j

theorem nsq_b (hb : FiniteOrbit y s b) (hy : nsq y = 1) (j : Fin s) : nsq (b j) = 1 := by
  obtain ⟨v, hv, h⟩ := hb.mem j
  rw [h, nsq_rot v hv, hy]

theorem sep_lt (hb : FiniteOrbit y s b) (hy : nsq y = 1) (i j : Fin s) (hij : i ≠ j) :
    Complex.normSq (ip (b i) (b j)) < 1 :=
  normSq_ip_lt_one (hb.nsq_b hy i) (hb.nsq_b hy j) (hb.sep i j hij)

/-- The set of `s` rays is closed under the group action. -/
theorem closed (hb : FiniteOrbit y s b) (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) (j : Fin s) :
    ∃ i, ∃ c : ℂ, rot u (b j) = c • b i := by
  obtain ⟨v, hv, hbj⟩ := hb.mem j
  obtain ⟨i, c, hc⟩ := hb.cover (fun l => u l * v l) (fun l => SU2_mul (hu l) (hv l))
  exact ⟨i, c, by rw [hbj, rot_comp, hc]⟩

end FiniteOrbit

/-- If the orbit of `y` is finite, `F_K(x,y)` is attained (at an orbit point). -/
theorem FK_attained {n : ℕ} {x y : Ψ n} {s : ℕ} {b : Fin s → Ψ n} (hy : nsq y = 1)
    (hb : FiniteOrbit y s b) :
    ∃ u : Fin n → Op1, (∀ i, SU2 (u i)) ∧ FK x y = Complex.normSq (ip x (rot u y)) := by
  have : Nonempty (Fin s) := ⟨⟨0, hb.pos⟩⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : Fin s => Complex.normSq (ip x (b j)))
  obtain ⟨u0, hu0, hb0⟩ := hb.mem j0
  refine ⟨u0, hu0, le_antisymm ?_ (le_FK x y u0 hu0)⟩
  show sSup (rotSet x y) ≤ _
  apply csSup_le (rotSet_nonempty x y)
  rintro r ⟨u, hu, rfl⟩
  obtain ⟨j, c, hc⟩ := hb.cover u hu
  have hc1 : Complex.normSq c = 1 := by
    have h1 : nsq (rot u y) = 1 := by rw [nsq_rot u hu, hy]
    rw [hc, nsq_smul, hb.nsq_b hy j, mul_one] at h1
    exact h1
  rw [hc, ip_smul_right, Complex.normSq_mul, hc1, one_mul, ← hb0]
  exact hj0 j

/-- **Lower bound** (all `k`): `F_K(x,y)^k / 4 ≤ P_e(k)` for a finite orbit. -/
theorem PeP_ge_of_finiteOrbit {n : ℕ} {x y : Ψ n} {s : ℕ} {b : Fin s → Ψ n} (hx : nsq x = 1)
    (hy : nsq y = 1) (hb : FiniteOrbit y s b) (k : ℕ) : FK x y ^ k / 4 ≤ PeP k x y := by
  obtain ⟨u, hu, hF⟩ := FK_attained (x := x) hy hb
  rw [hF]
  exact PeP_ge_of_rot hx hy u hu k

/-! ### The support test -/

/-- The `k`-th tensor powers of the rays `b j`, as vectors. -/
def vecs {n s : ℕ} (k : ℕ) (b : Fin s → Ψ n) : Fin s → EuclideanSpace ℂ (Copies n k) :=
  fun j => WithLp.toLp 2 (copies k (b j))

/-- The support space `span{b_j^{⊗k}}` of the finite orbit. -/
def suppB {n s : ℕ} (k : ℕ) (b : Fin s → Ψ n) : Submodule ℂ (EuclideanSpace ℂ (Copies n k)) :=
  Submodule.span ℂ (Set.range (vecs k b))

theorem suppB_invariant {n : ℕ} {y : Ψ n} {s : ℕ} {b : Fin s → Ψ n} (hb : FiniteOrbit y s b) (k : ℕ)
    (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) :
    ∀ v : Copies n k → ℂ, WithLp.toLp 2 v ∈ suppB k b →
      WithLp.toLp 2 (rotK k u *ᵥ v) ∈ suppB k b := by
  have key : ∀ x ∈ suppB k b, WithLp.toLp 2 (rotK k u *ᵥ WithLp.ofLp x) ∈ suppB k b := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨i, c, hc⟩ := hb.closed u hu j
      have h : rotK k u *ᵥ copies k (b j) = c ^ k • copies k (b i) := by
        rw [← copies_rot, hc, copies_smul]
      have e : WithLp.ofLp (vecs k b j) = copies k (b j) := rfl
      have hm : c ^ k • vecs k b i ∈ suppB k b :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      rw [e, h]
      exact hm
    | zero => simp
    | add x y _ _ hx hy =>
      have := Submodule.add_mem _ hx hy
      simpa [Matrix.mulVec_add] using this
    | smul a x _ hx =>
      have := Submodule.smul_mem _ a hx
      simpa [Matrix.mulVec_smul] using this
  intro v hv
  simpa using key _ hv

/-- The orthogonal projector onto the support space is a `K`-invariant test. -/
theorem suppB_isInv {n : ℕ} {y : Ψ n} {s : ℕ} {b : Fin s → Ψ n} (hb : FiniteOrbit y s b) (k : ℕ) :
    IsInvEffect (n := n) k (projMat (suppB k b)) := by
  refine ⟨projMat_isEffect _, fun u hu => ?_⟩
  refine projMat_commute _ (fun v hv => ?_) (fun v hv => ?_)
  · exact suppB_invariant hb k u hu v hv
  · rw [rotK_conjTranspose]
    exact suppB_invariant hb k _ (fun i => SU2_adjoint (hu i)) v hv

/-- The support test never errs on `y`, so `P_e(k) ≤ ½ ‖Π x^{⊗k}‖²`. -/
theorem PeP_le_half_proj {n : ℕ} {x y : Ψ n} {s : ℕ} {b : Fin s → Ψ n} (hb : FiniteOrbit y s b)
    (k : ℕ) :
    PeP k x y ≤ ‖(suppB k b).starProjection (WithLp.toLp 2 (copies k x))‖ ^ 2 / 2 := by
  refine (PeP_le_err (suppB_isInv hb k) x y).trans (le_of_eq ?_)
  have hy : WithLp.toLp 2 (copies k y) ∈ suppB k b := by
    obtain ⟨j, c, hc⟩ := hb.cover (fun _ => 1) (fun _ => SU2_one)
    rw [rot_one] at hc
    rw [hc, copies_smul]
    have hm : c ^ k • vecs k b j ∈ suppB k b :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    exact hm
  unfold err
  rw [qf_one_sub_projMat_of_mem _ hy, qf_projMat_self]
  simp

/-- **Upper bound** (all large `k`): `P_e(k) ≤ s F_K(x,y)^k` when the orbit of `y` has `s` rays. -/
theorem PeP_eventually_le {n : ℕ} {x y : Ψ n} {s : ℕ} {b : Fin s → Ψ n} (hy : nsq y = 1)
    (hb : FiniteOrbit y s b) :
    ∀ᶠ k : ℕ in atTop, PeP k x y ≤ s * FK x y ^ k := by
  classical
  -- a uniform separation constant α < 1
  obtain ⟨α, hα0, hα1, hα⟩ : ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ i j, i ≠ j → ‖ip (b i) (b j)‖ ≤ α := by
    have hne : Nonempty (Fin s × Fin s) := ⟨(⟨0, hb.pos⟩, ⟨0, hb.pos⟩)⟩
    let f : Fin s × Fin s → ℝ := fun p => if p.1 = p.2 then 0 else ‖ip (b p.1) (b p.2)‖
    have hf0 : ∀ p, 0 ≤ f p := fun p => by
      by_cases h : p.1 = p.2
      · simp [f, h]
      · simp [f, h]
    have hf1 : ∀ p, f p < 1 := by
      intro p
      by_cases h : p.1 = p.2
      · simp [f, h]
      · have h1 := hb.sep_lt hy p.1 p.2 h
        rw [Complex.normSq_eq_norm_sq] at h1
        have e : f p = ‖ip (b p.1) (b p.2)‖ := by simp [f, h]
        rw [e]
        rcases lt_or_ge ‖ip (b p.1) (b p.2)‖ 1 with h2 | h2
        · exact h2
        · nlinarith [norm_nonneg (ip (b p.1) (b p.2))]
    obtain ⟨p0, hp0⟩ := Finite.exists_max f
    refine ⟨f p0, hf0 p0, hf1 p0, fun i j hij => ?_⟩
    have e : f (i, j) = ‖ip (b i) (b j)‖ := by simp [f, hij]
    rw [← e]
    exact hp0 (i, j)
  have hlim : Tendsto (fun k : ℕ => (s : ℝ) * α ^ k) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).const_mul (s : ℝ)
  filter_upwards [hlim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  have hk' : (s : ℝ) * α ^ k ≤ 1 / 2 := hk
  have hvip : ∀ i j, ⟪vecs k b i, vecs k b j⟫_ℂ = (ip (b i) (b j)) ^ k := by
    intro i j
    simp only [vecs]
    rw [inner_toLp, star_copies_dot, ← ip_eq_dot]
  have hv1 : ∀ j, ‖vecs k b j‖ = 1 := by
    intro j
    have h : ⟪vecs k b j, vecs k b j⟫_ℂ = 1 := by
      rw [hvip, ip_self, hb.nsq_b hy j]; simp
    rw [inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖vecs k b j‖ ^ 2 = 1 := by
      have h3 : ((‖vecs k b j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_one, Complex.ofReal_pow]; exact h
      exact Complex.ofReal_injective h3
    nlinarith [norm_nonneg (vecs k b j)]
  have hε : ∀ i j, i ≠ j → ‖⟪vecs k b i, vecs k b j⟫_ℂ‖ ≤ α ^ k := by
    intro i j hij
    rw [hvip, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hα i j hij) k
  have hproj := proj_sq_le (vecs k b) hv1 (pow_nonneg hα0 k) hε hk'
    (WithLp.toLp 2 (copies k x))
  have hterm : ∀ j, ‖⟪vecs k b j, (WithLp.toLp 2 (copies k x) : EuclideanSpace ℂ (Copies n k))⟫_ℂ‖ ^ 2
      ≤ FK x y ^ k := by
    intro j
    have e : ⟪vecs k b j, (WithLp.toLp 2 (copies k x) : EuclideanSpace ℂ (Copies n k))⟫_ℂ
        = (ip (b j) x) ^ k := by
      simp only [vecs]
      rw [inner_toLp, star_copies_dot, ← ip_eq_dot]
    rw [e, norm_pow, ← pow_mul, mul_comm, pow_mul, ← Complex.normSq_eq_norm_sq, ip_conj_symm' (b j) x,
      Complex.normSq_conj]
    obtain ⟨u, hu, hbj⟩ := hb.mem j
    refine pow_le_pow_left₀ (Complex.normSq_nonneg _) ?_ k
    rw [hbj]
    exact le_FK x y u hu
  calc PeP k x y
      ≤ ‖(suppB k b).starProjection (WithLp.toLp 2 (copies k x))‖ ^ 2 / 2 := PeP_le_half_proj hb k
    _ ≤ (2 * ∑ j, ‖⟪vecs k b j, (WithLp.toLp 2 (copies k x) : EuclideanSpace ℂ (Copies n k))⟫_ℂ‖ ^ 2) / 2 := by
        have : ‖(suppB k b).starProjection (WithLp.toLp 2 (copies k x))‖ ^ 2 ≤
            2 * ∑ j, ‖⟪vecs k b j, (WithLp.toLp 2 (copies k x) : EuclideanSpace ℂ (Copies n k))⟫_ℂ‖ ^ 2 :=
          hproj
        linarith
    _ = ∑ j, ‖⟪vecs k b j, (WithLp.toLp 2 (copies k x) : EuclideanSpace ℂ (Copies n k))⟫_ℂ‖ ^ 2 := by ring
    _ ≤ ∑ j : Fin s, FK x y ^ k := Finset.sum_le_sum fun j _ => hterm j
    _ = s * FK x y ^ k := by simp

/-! ### The exponent -/

/-- From `F^k/4 ≤ P_k` and eventually `P_k ≤ s F^k` (with `F, s > 0`) to
`-(1/k) log P_k → -log F`. -/
theorem tendsto_of_bounds {F : ℝ} {s : ℕ} {P : ℕ → ℝ} (hF : 0 < F) (hs : 0 < s)
    (hlow : ∀ k, F ^ k / 4 ≤ P k) (hup : ∀ᶠ k : ℕ in atTop, P k ≤ s * F ^ k) :
    Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (P k)) atTop (nhds (-Real.log F)) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hlim1 : Tendsto (fun k : ℕ => -Real.log F + Real.log 4 / k) atTop (nhds (-Real.log F)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 4))
  have hlim2 : Tendsto (fun k : ℕ => -Real.log F - Real.log s / k) atTop (nhds (-Real.log F)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log s))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim2 hlim1 ?_ ?_
  · filter_upwards [hup, eventually_ge_atTop 1] with k hk hk1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hPpos : 0 < P k := lt_of_lt_of_le (by positivity) (hlow k)
    have h := Real.log_le_log hPpos hk
    rw [Real.log_mul hs'.ne' (by positivity), Real.log_pow] at h
    have h2 : -(1 / (k : ℝ)) * (Real.log s + k * Real.log F) ≤ -(1 / (k : ℝ)) * Real.log (P k) :=
      mul_le_mul_of_nonpos_left h (by have : 0 < 1 / (k : ℝ) := by positivity
                                      linarith)
    refine le_trans (le_of_eq ?_) h2
    field_simp
    ring
  · filter_upwards [eventually_ge_atTop 1] with k hk1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hPpos : 0 < P k := lt_of_lt_of_le (by positivity) (hlow k)
    have h := Real.log_le_log (by positivity) (hlow k)
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
    have h2 : -(1 / (k : ℝ)) * Real.log (P k) ≤ -(1 / (k : ℝ)) * (k * Real.log F - Real.log 4) :=
      mul_le_mul_of_nonpos_left h (by have : 0 < 1 / (k : ℝ) := by positivity
                                      linarith)
    refine h2.trans (le_of_eq ?_)
    field_simp
    ring

/-- **`thm:finite`, quantitative form.**  If the `K`-orbit of `y` or of `x` has `s` rays `b`, then for
unit `x, y`: `F^k/4 ≤ P_e^K(k)` for every `k` and `P_e^K(k) ≤ s F^k` for all large `k`
(`F = F_K(x,y)`). -/
theorem thm_finite_bounds {n : ℕ} {x y : Ψ n} (hx : nsq x = 1) (hy : nsq y = 1) {s : ℕ}
    {b : Fin s → Ψ n} (hb : FiniteOrbit y s b ∨ FiniteOrbit x s b) :
    (∀ k : ℕ, FK x y ^ k / 4 ≤ PeP k x y) ∧
      ∀ᶠ k : ℕ in atTop, PeP k x y ≤ s * FK x y ^ k := by
  rcases hb with hb | hb
  · exact ⟨PeP_ge_of_finiteOrbit hx hy hb, PeP_eventually_le hy hb⟩
  · refine ⟨fun k => ?_, ?_⟩
    · rw [PeP_comm, FK_comm]
      exact PeP_ge_of_finiteOrbit hy hx hb k
    · filter_upwards [PeP_eventually_le (x := y) hx hb] with k hk
      rwa [PeP_comm, FK_comm]

/-- **`thm:finite`** (QI-B).  For unit `x, y`, if the projective `K`-orbit of `y` or of `x` is finite
(`s` rays) and `0 < F_K(x,y)`, then `ξ_inv(x,y) = lim_k -(1/k) log P_e^K(k) = -log F_K(x,y) = C_K(x,y)`;
the hypothesis `F_K < 1` of the paper is not needed. -/
theorem thm_finite {n : ℕ} {x y : Ψ n} (hx : nsq x = 1) (hy : nsq y = 1) (hF : 0 < FK x y) {s : ℕ}
    {b : Fin s → Ψ n} (hb : FiniteOrbit y s b ∨ FiniteOrbit x s b) :
    Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (PeP k x y)) atTop (nhds (-Real.log (FK x y))) := by
  have hs : 0 < s := by rcases hb with hb | hb <;> exact hb.pos
  obtain ⟨hlow, hup⟩ := thm_finite_bounds hx hy hb
  exact tendsto_of_bounds hF hs hlow hup

/-- `thm:finite` in the existing `(ψ, Θψ)` setting: `P_e = Pe`, `F_K = FKΘ`, `C_K = CK`.  Here `0 < F_K`
is automatic (`FKΘ_pos`).  The finite orbit may be that of `Θψ` or of `ψ`. -/
theorem thm_finite_Theta {n : ℕ} {ψ : Ψ n} (hψ : nsq ψ = 1) {s : ℕ} {b : Fin s → Ψ n}
    (hb : FiniteOrbit (Θ ψ) s b ∨ FiniteOrbit ψ s b) :
    (∀ k : ℕ, FKΘ ψ ^ k / 4 ≤ Pe k ψ) ∧
      (∀ᶠ k : ℕ in atTop, Pe k ψ ≤ s * FKΘ ψ ^ k) ∧
      Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) atTop (nhds (CK ψ)) := by
  have hΘ : nsq (Θ ψ) = 1 := by rw [nsq_Θ, hψ]
  obtain ⟨hlow, hup⟩ := thm_finite_bounds hψ hΘ hb
  have hs : 0 < s := by rcases hb with hb | hb <;> exact hb.pos
  exact ⟨hlow, hup, tendsto_of_bounds (FKΘ_pos ψ hψ) hs hlow hup⟩

end FormalResearch.QIB
