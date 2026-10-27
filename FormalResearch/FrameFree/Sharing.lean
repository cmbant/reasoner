import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.GateOverlap
import FormalResearch.FourQubitEntropy.Attainment

open scoped ComplexConjugate Matrix BigOperators Kronecker

/-!
# Frame sharing (Paper P, `sec2_frames.tex`)

A *sharing pattern* of `n` spins is a function `g : Fin n → β`: spins `i, j` share one `SU(2)` frame
iff `g i = g j`.  `FKs g ψ φ` is the rotation overlap `F_K^π` (one frame per block), `FCs` the filter
overlap `F_C^π` (one `SL(2,ℂ)` element per block, normalised by `‖gφ‖²`), `CKs = -log F_K^π`.
`g = id` is the independent-frame case (`FKs_id : FKs id = FK`), `g = fun _ => ()` the common frame.

## Proved here (no hypothesis beyond those named)

* `prop:refine` (any `n`): `FKs_mono`, `FKΘs_mono`, `FCs_mono`, `CKs_mono` (finer pattern, larger value).
* `prop:invariantstates` (any `n`): `FKΘs_of_invariant`, `CKs_of_invariant`; the filter version
  `FCΘs_of_invariant(_unit)` takes invariance under the *complexified* group as hypothesis (the paper
  derives it from `K_π`-invariance by Zariski density, proved in `Zariski.lean`:
  `Zariski.FCΘs_of_SU2_invariant(_unit)` needs only `K_π`-invariance).
* `thm:exchangesharing` for the Choi probe `ψ_{U_θ}` (`psiEx θ`), `U_θ = cos θ − i sin θ SWAP`
  (`pattern_trichotomy`: every pattern is in exactly one of the cases (i), (ii), (iii)):
  - (i) (`g 0 = g 1 ∨ g 2 = g 3`), unconditional, all `θ`: `FKΘs_exchange_i`, `FCΘs_exchange_i`
    (both `= κ θ`), `CKs_exchange_i` (`= log (4/(1+3cos²2θ))`);
  - (ii), (iii): the lower bounds `cos² θ ≤ F_K^π` (inside `{13|24}`), `sin² θ ≤ F_K^π`
    (inside `{14|23}`), `κ ≤ F_K^π` (all patterns) are unconditional (explicit rotations); the upper
    bounds use the independent-frame exchange law as an **explicit hypothesis**
    (`ExchangeIndepBound θ : FKΘ ψ_{U_θ} ≤ cos² θ`, `ExchangeIndepBoundC θ` for the filters).  The
    paper obtains it from the Weyl-vertex formula (R7) / filtered-gate law (R8), neither of which is
    formalised for the Choi probe (`exchange_closed_form` is the closed form on the Weyl side only;
    `PhysicalBridge.FKmag_le_rotOverlap` goes in the wrong direction to discharge it).  The hypothesis is
    meant for `0 ≤ θ ≤ π/4` (it is false for `θ = π/2`, where `κ = 1`).
    `FKΘs_exchange_ii/iii`, `FCΘs_exchange_ii/iii`, `CKs_exchange_ii/iii`, `CKs_sqrtSwap`.
* `thm:m4sharing` for `M₄` (`M4n`, the vector `M4` of `FourQubitEntropy/Attainment.lean`):
  (a) three spins in a block: `FKΘs_M4_triple`, `FCΘs_M4_triple` (`= 0`);
  (b) pairs and singletons with at least one pair (`PairNoTriple`): `FKΘs_M4_pair`, `FCΘs_M4_pair`
  (`= 4/9`) and `CKs_M4_pair` (`= log (9/4)`), unconditionally.  The filter inequality is `key_FC`
  (`|2tr(AD) − trA trD|² ≤ (8/3)(‖AD‖² + ‖A‖²‖D‖²)` for all `2×2` matrices, the paper's Cauchy--Schwarz
  argument in the Pauli decomposition) with the exact overlap and norm formulas `ov_M4_kl`,
  `nsq_M4_kl` (proved with `linear_combination` certificates found by Groebner reduction).

## NOT proved here

* Everything about `ξ_inv` (the Helstrom exponent of the frame-averaged hypotheses), including the
  sentence "`ξ_inv^π = …` exactly": that needs the calibration corollary and the window theorem; only the
  `F_K^π`, `F_C^π`, `C_K^π` values are stated.
* `C_K^π = ∞` for `M₄` with a triple (`F_K^π = 0`): Lean's `log 0 = 0`, so only `F_K^π = F_C^π = 0` is stated.
* The independent-frame exchange law (the hypotheses above); hence the exact values in cases (ii), (iii) of
  `thm:exchangesharing` and the `√SWAP` row are conditional.  Case (iii) is open in the paper and only
  the bounds are stated.
* The pattern counts (eight, four, three; five, nine) are not formalised as cardinalities; the
  classification is by the predicates `g 0 = g 1 ∨ g 2 = g 3`, `Refines g pat1324`, `Refines g pat1423`,
  `HasTriple`, `PairNoTriple`.
* `thm:copythreshold` (a) (twirls, Schur--Weyl duality, slot permutations) is not formalised.
* `thm:m4sharing` (c) (independent frames, `ξ_inv = log 2`) is not part of this file.
-/

namespace FormalResearch.FrameFree.Sharing

open FormalResearch.FrameFree.NQubit

/-! ## Part 1. Sharing patterns, refinement (Proposition `prop:refine`) -/

section Generic

variable {n : ℕ} {β β' : Type*}

/-- Overlaps `|⟨ψ|(⊗_i v_{g i}) φ⟩|²` over frames `v : β → SU(2)`: one rotation per block of the
sharing pattern `g : Fin n → β` (spins `i, j` share a frame iff `g i = g j`). -/
def shSet (g : Fin n → β) (ψ φ : Ψ n) : Set ℝ :=
  {r | ∃ v : β → Op1, (∀ b, SU2 (v b)) ∧ r = Complex.normSq (ip ψ (rot (fun i => v (g i)) φ))}

/-- `F_K^π(ψ, φ)`: the rotation overlap restricted to `K_π`. -/
noncomputable def FKs (g : Fin n → β) (ψ φ : Ψ n) : ℝ := sSup (shSet g ψ φ)

/-- `F_K^π(ψ) = F_K^π(ψ, Θψ)`. -/
noncomputable def FKΘs (g : Fin n → β) (ψ : Ψ n) : ℝ := FKs g ψ (Θ ψ)

/-- `C_K^π(ψ) = -log F_K^π(ψ)`. -/
noncomputable def CKs (g : Fin n → β) (ψ : Ψ n) : ℝ := - Real.log (FKΘs g ψ)

theorem shSet_subset (g : Fin n → β) (ψ φ : Ψ n) : shSet g ψ φ ⊆ rotSet ψ φ := by
  rintro r ⟨v, hv, rfl⟩
  exact ⟨fun i => v (g i), fun i => hv _, rfl⟩

theorem shSet_nonempty (g : Fin n → β) (ψ φ : Ψ n) : (shSet g ψ φ).Nonempty :=
  ⟨_, fun _ => 1, fun _ => SU2_one, rfl⟩

theorem shSet_bddAbove (g : Fin n → β) (ψ φ : Ψ n) : BddAbove (shSet g ψ φ) :=
  (rotSet_bddAbove ψ φ).mono (shSet_subset g ψ φ)

/-- Every frame `v` gives a lower bound on `F_K^π`. -/
theorem le_FKs (g : Fin n → β) (ψ φ : Ψ n) (v : β → Op1) (hv : ∀ b, SU2 (v b)) :
    Complex.normSq (ip ψ (rot (fun i => v (g i)) φ)) ≤ FKs g ψ φ :=
  le_csSup (shSet_bddAbove g ψ φ) ⟨v, hv, rfl⟩

/-- `F_K^π ≤ F_K` for every pattern (independent frames are the finest pattern). -/
theorem FKs_le_FK (g : Fin n → β) (ψ φ : Ψ n) : FKs g ψ φ ≤ FK ψ φ :=
  csSup_le_csSup (rotSet_bddAbove ψ φ) (shSet_nonempty g ψ φ) (shSet_subset g ψ φ)

/-- Independent frames: the pattern `id` into singletons gives the plain `F_K`. -/
theorem FKs_id (ψ φ : Ψ n) : FKs (id : Fin n → Fin n) ψ φ = FK ψ φ := by
  rfl

/-- The pattern `π` refines `π'` (every block of `π` lies in a block of `π'`). -/
def Refines (g : Fin n → β) (g' : Fin n → β') : Prop := ∀ i j, g i = g j → g' i = g' j

/-- A frame assignment for the coarser pattern `π'` gives one for the finer pattern `π`
with the same rotation on every spin (`K_{π'} ⊆ K_π`), for any one-qubit constraint `P ∋ 1`. -/
theorem exists_fine_frame {g : Fin n → β} {g' : Fin n → β'} (h : Refines g g') (P : Op1 → Prop)
    (hP : P 1) (v' : β' → Op1) (hv' : ∀ b, P (v' b)) :
    ∃ v : β → Op1, (∀ b, P (v b)) ∧ ∀ i, v (g i) = v' (g' i) := by
  classical
  refine ⟨fun b => if hb : ∃ i, g i = b then v' (g' hb.choose) else 1, ?_, ?_⟩
  · intro b
    by_cases hb : ∃ i, g i = b
    · simp only [hb, ↓reduceDIte]; exact hv' _
    · simp only [hb, ↓reduceDIte]; exact hP
  · intro i
    have hex : ∃ j, g j = g i := ⟨i, rfl⟩
    simp only [hex, ↓reduceDIte]
    rw [h _ _ hex.choose_spec]

theorem shSet_mono {g : Fin n → β} {g' : Fin n → β'} (h : Refines g g') (ψ φ : Ψ n) :
    shSet g' ψ φ ⊆ shSet g ψ φ := by
  rintro r ⟨v', hv', rfl⟩
  obtain ⟨v, hv, hvv⟩ := exists_fine_frame h SU2 SU2_one v' hv'
  exact ⟨v, hv, by simp only [hvv]⟩

/-- **Proposition `prop:refine`** (rotation part).  If `π` refines `π'` then
`F_K^{π'} ≤ F_K^{π}`: sharing frames never hurts. -/
theorem FKs_mono {g : Fin n → β} {g' : Fin n → β'} (h : Refines g g') (ψ φ : Ψ n) :
    FKs g' ψ φ ≤ FKs g ψ φ :=
  csSup_le_csSup (shSet_bddAbove g ψ φ) (shSet_nonempty g' ψ φ) (shSet_mono h ψ φ)

theorem FKΘs_mono {g : Fin n → β} {g' : Fin n → β'} (h : Refines g g') (ψ : Ψ n) :
    FKΘs g' ψ ≤ FKΘs g ψ := FKs_mono h ψ (Θ ψ)

/-- **Proposition `prop:refine`** (chiral distance): `C_K^π ≤ C_K^{π'}` when `π` refines `π'`
(assuming `F_K^{π'}(ψ) > 0`, as `log 0 = 0` in Lean). -/
theorem CKs_mono {g : Fin n → β} {g' : Fin n → β'} (h : Refines g g') (ψ : Ψ n)
    (hpos : 0 < FKΘs g' ψ) : CKs g ψ ≤ CKs g' ψ := by
  unfold CKs
  have := Real.log_le_log hpos (FKΘs_mono h ψ)
  linarith

theorem Refines.refl (g : Fin n → β) : Refines g g := fun _ _ h => h

theorem Refines.trans {β'' : Type*} {g : Fin n → β} {g' : Fin n → β'} {g'' : Fin n → β''}
    (h : Refines g g') (h' : Refines g' g'') : Refines g g'' :=
  fun i j hij => h' i j (h i j hij)

/-- Every pattern refines the common frame. -/
theorem refines_const (g : Fin n → β) : Refines g (fun _ => ()) := fun _ _ _ => rfl

/-- Independent frames refine every pattern. -/
theorem id_refines (g' : Fin n → β') : Refines (id : Fin n → Fin n) g' :=
  fun i j h => by rw [show i = j from h]

/-! ### Filters: `F_C^π` and invariant states (Proposition `prop:invariantstates`) -/

theorem nsq_nonneg (ψ : Ψ n) : 0 ≤ nsq ψ := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The filter ratios `|⟨ψ|gφ⟩|²/‖gφ‖²`, `g` in the complexification `𝒢_π` of `K_π`
(one `SL(2,ℂ)` element per block). -/
def fiSet (g : Fin n → β) (ψ φ : Ψ n) : Set ℝ :=
  {r | ∃ v : β → Op1, (∀ b, (v b).det = 1) ∧
    r = Complex.normSq (ip ψ (rot (fun i => v (g i)) φ)) / nsq (rot (fun i => v (g i)) φ)}

/-- `F_C^π(ψ, φ) = sup_{g ∈ 𝒢_π} |⟨ψ|gφ⟩|²/‖gφ‖²`. -/
noncomputable def FCs (g : Fin n → β) (ψ φ : Ψ n) : ℝ := sSup (fiSet g ψ φ)

/-- `F_C^π(ψ) = F_C^π(ψ, Θψ)`. -/
noncomputable def FCΘs (g : Fin n → β) (ψ : Ψ n) : ℝ := FCs g ψ (Θ ψ)

theorem ratio_le (ψ χ : Ψ n) : Complex.normSq (ip ψ χ) / nsq χ ≤ nsq ψ := by
  rcases (nsq_nonneg χ).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact nsq_nonneg ψ
  · rw [div_le_iff₀ hpos]; exact normSq_ip_le ψ χ

theorem fiSet_nonempty (g : Fin n → β) (ψ φ : Ψ n) : (fiSet g ψ φ).Nonempty :=
  ⟨_, fun _ => 1, fun _ => Matrix.det_one, rfl⟩

theorem fiSet_bddAbove (g : Fin n → β) (ψ φ : Ψ n) : BddAbove (fiSet g ψ φ) := by
  refine ⟨nsq ψ, ?_⟩
  rintro r ⟨v, -, rfl⟩
  exact ratio_le _ _

/-- **Proposition `prop:refine`** (filter part): `F_C^{π'} ≤ F_C^{π}` when `π` refines `π'`. -/
theorem FCs_mono {g : Fin n → β} {g' : Fin n → β'} (h : Refines g g') (ψ φ : Ψ n) :
    FCs g' ψ φ ≤ FCs g ψ φ := by
  refine csSup_le_csSup (fiSet_bddAbove g ψ φ) (fiSet_nonempty g' ψ φ) ?_
  rintro r ⟨v', hv', rfl⟩
  obtain ⟨v, hv, hvv⟩ := exists_fine_frame h (fun a : Op1 => a.det = 1) Matrix.det_one v' hv'
  exact ⟨v, hv, by simp only [hvv]⟩

/-- `F_K^π ≤ F_C^π` for a unit vector `φ` (rotations are filters). -/
theorem FKs_le_FCs (g : Fin n → β) (ψ φ : Ψ n) (hφ : nsq φ = 1) : FKs g ψ φ ≤ FCs g ψ φ := by
  refine csSup_le_csSup (fiSet_bddAbove g ψ φ) (shSet_nonempty g ψ φ) ?_
  rintro r ⟨v, hv, rfl⟩
  refine ⟨v, fun b => (hv b).2, ?_⟩
  rw [nsq_rot _ (fun i => hv _), hφ, div_one]

/-- The complex-linear `ε v̄ ε⁻¹ = (v†)⁻¹` of an `SL(2,ℂ)` element; equal to `v` on `SU(2)`. -/
def wd (v : Op1) : Op1 := !![conj (v 1 1), -conj (v 1 0); -conj (v 0 1), conj (v 0 0)]

theorem eps_mul_conj (v : Op1) : eps * v.map conj = wd v * eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, wd, Matrix.mul_apply, Fin.sum_univ_two]

theorem wd_wd (v : Op1) : wd (wd v) = v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wd]

theorem det_wd {v : Op1} (h : v.det = 1) : (wd v).det = 1 := by
  have h' : conj (v.det) = 1 := by rw [h]; simp
  simp only [Matrix.det_fin_two, wd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h' ⊢
  simp only [map_sub, map_mul] at h'
  rw [← h']; ring

/-- `Θ` conjugates a filter `g` into `ε ḡ ε⁻¹`. -/
theorem Θ_rot_filter {m : ℕ} (u : Fin m → Op1) (ψ : Ψ m) :
    Θ (rot u ψ) = rot (fun i => wd (u i)) (Θ ψ) := by
  rw [Θ_eq_rot, Θ_eq_rot, conj_rot, rot_comp, rot_comp]
  congr 1
  funext i
  exact eps_mul_conj (u i)

/-- **Proposition `prop:invariantstates`** (rotation part).  If `ψ` is invariant under `K_π`
(`rot (v∘g) ψ = ψ` for all `SU(2)` frames, e.g. every block has total spin `0`), then
`F_K^π(ψ) = |⟨ψ|Θψ⟩|²`.  Hence also `C_K^π = -log |⟨ψ|Θψ⟩|² = ξ_cal`. -/
theorem FKΘs_of_invariant (g : Fin n → β) (ψ : Ψ n)
    (hψ : ∀ v : β → Op1, (∀ b, SU2 (v b)) → rot (fun i => v (g i)) ψ = ψ) :
    FKΘs g ψ = Complex.normSq (ip ψ (Θ ψ)) := by
  have hset : shSet g ψ (Θ ψ) = {Complex.normSq (ip ψ (Θ ψ))} := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [← Θ_rot _ (fun i => hv _), hψ v hv]
      rfl
    · rintro rfl
      exact ⟨fun _ => 1, fun _ => SU2_one, by rw [rot_one]⟩
  unfold FKΘs FKs
  rw [hset, csSup_singleton]

theorem CKs_of_invariant (g : Fin n → β) (ψ : Ψ n)
    (hψ : ∀ v : β → Op1, (∀ b, SU2 (v b)) → rot (fun i => v (g i)) ψ = ψ) :
    CKs g ψ = - Real.log (Complex.normSq (ip ψ (Θ ψ))) := by
  unfold CKs; rw [FKΘs_of_invariant g ψ hψ]

/-- **Proposition `prop:invariantstates`** (filter part).  If `ψ` is invariant under the
complexification of `K_π` (the paper obtains this from `K_π`-invariance by Zariski density; see
`Zariski.FCΘs_of_SU2_invariant`), then `F_C^π(ψ) = |⟨ψ|Θψ⟩|²/‖Θψ‖²`, which is `|⟨ψ|Θψ⟩|²` for a unit vector. -/
theorem FCΘs_of_invariant (g : Fin n → β) (ψ : Ψ n)
    (hψ : ∀ v : β → Op1, (∀ b, (v b).det = 1) → rot (fun i => v (g i)) ψ = ψ) :
    FCΘs g ψ = Complex.normSq (ip ψ (Θ ψ)) / nsq (Θ ψ) := by
  have hset : fiSet g ψ (Θ ψ) = {Complex.normSq (ip ψ (Θ ψ)) / nsq (Θ ψ)} := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h1 : rot (fun i => v (g i)) (Θ ψ) = Θ ψ := by
        have h2 := hψ (fun b => wd (v b)) (fun b => det_wd (hv b))
        have h3 := congrArg Θ h2
        rw [Θ_rot_filter] at h3
        simpa only [wd_wd] using h3
      rw [h1]; rfl
    · rintro rfl
      exact ⟨fun _ => 1, fun _ => Matrix.det_one, by rw [rot_one]⟩
  unfold FCΘs FCs
  rw [hset, csSup_singleton]

theorem FCΘs_of_invariant_unit (g : Fin n → β) (ψ : Ψ n) (hψ1 : nsq ψ = 1)
    (hψ : ∀ v : β → Op1, (∀ b, (v b).det = 1) → rot (fun i => v (g i)) ψ = ψ) :
    FCΘs g ψ = Complex.normSq (ip ψ (Θ ψ)) := by
  rw [FCΘs_of_invariant g ψ hψ, nsq_Θ, hψ1, div_one]


end Generic

/-! ## Part 2. Four spins as `4 × 4` matrices; Choi states -/

section FourSpins

theorem sum_pi_succ {n : ℕ} (F : (Fin (n+1) → Fin 2) → ℂ) :
    ∑ f, F f = ∑ a : Fin 2, ∑ g : Fin n → Fin 2, F (Fin.cons a g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type]; rfl

/-- Sums over `Fin 4 → Fin 2` as four nested sums. -/
theorem sum4 (F : (Fin 4 → Fin 2) → ℂ) :
    ∑ f, F f = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2, F ![a, b, c, d] := by
  rw [sum_pi_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_pi_succ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_pi_succ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_pi_succ]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp
  congr 1

theorem eq_four (x : Fin 4 → Fin 2) : x = ![x 0, x 1, x 2, x 3] := by
  ext i; fin_cases i <;> rfl

/-- `4 × 4` matrices, rows = spins `(1,2)`, columns = spins `(3,4)`. -/
abbrev Mat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The four-spin vector with cut matrix `Z`: `ψ(x₁x₂x₃x₄) = Z_{(x₁x₂),(x₃x₄)}`. -/
def ofMat (Z : Mat4) : Ψ 4 := fun x => Z (x 0, x 1) (x 2, x 3)

/-- Local rotations act on the cut matrix by `Z ↦ (u₁⊗u₂) Z (u₃⊗u₄)ᵀ`. -/
theorem rot_ofMat (u : Fin 4 → Op1) (Z : Mat4) :
    rot u (ofMat Z) = ofMat ((u 0 ⊗ₖ u 1) * Z * (u 2 ⊗ₖ u 3)ᵀ) := by
  funext x
  rw [eq_four x]
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  generalize x 3 = d
  simp only [rot, ofMat, sum4]
  simp [Fin.prod_univ_four, Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.kroneckerMap_apply]
  ring

theorem ip_ofMat (A B : Mat4) : ip (ofMat A) (ofMat B) = Matrix.trace (Aᴴ * B) := by
  simp only [ip, ofMat, sum4]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  ring

theorem cj_ofMat (A : Mat4) : cj (ofMat A) = ofMat (A.map conj) := rfl

/-- `E = ε ⊗ ε`, the cut matrix of the singlet pair `s₁₃ s₂₄` up to the factor `1/2`. -/
def EE : Mat4 := eps ⊗ₖ eps

theorem EE_conjT : EEᴴ = EEᵀ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [EE, eps, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]

theorem EE_mul_EEt : EE * EEᵀ = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [EE, eps, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply]

theorem EEt_mul_EE : EEᵀ * EE = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [EE, eps, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply]

theorem EE_map_conj : EE.map conj = EE := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [EE, eps, Matrix.kroneckerMap_apply]

/-- The Choi state `ψ_V = (V ⊗ I₃₄) s₁₃ s₂₄` of a two-qubit operator `V` (acting on spins `1,2`;
spins `3,4` are their singlet partners). -/
noncomputable def choi (V : Mat4) : Ψ 4 := ofMat ((1 / 2 : ℂ) • (V * EE))

theorem eps_mul_transpose (u : Op1) : eps * uᵀ = u.adjugate * eps := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eps, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

theorem EE_mul_kron_transpose (a b : Op1) : EE * (a ⊗ₖ b)ᵀ = (a.adjugate ⊗ₖ b.adjugate) * EE := by
  unfold EE
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    eps_mul_transpose, eps_mul_transpose]

/-- Local rotations of a Choi state: `rot u ψ_V = ψ_{(u₁⊗u₂) V (adj u₃ ⊗ adj u₄)}`
(for `SU(2)` elements `adj u = u⁻¹ = u†`). -/
theorem rot_choi (u : Fin 4 → Op1) (V : Mat4) :
    rot u (choi V) = choi ((u 0 ⊗ₖ u 1) * V * ((u 2).adjugate ⊗ₖ (u 3).adjugate)) := by
  unfold choi
  rw [rot_ofMat]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have h : (u 0 ⊗ₖ u 1) * (V * EE) * (u 2 ⊗ₖ u 3)ᵀ = (u 0 ⊗ₖ u 1) * V * (EE * (u 2 ⊗ₖ u 3)ᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [h, EE_mul_kron_transpose, ← Matrix.mul_assoc]

theorem ip_choi (U M : Mat4) : ip (choi U) (choi M) = (1 / 4 : ℂ) * Matrix.trace (Uᴴ * M) := by
  unfold choi
  rw [ip_ofMat]
  have h : ((1 / 2 : ℂ) • (U * EE))ᴴ * ((1 / 2 : ℂ) • (M * EE)) =
      (1 / 4 : ℂ) • (EEᵀ * ((Uᴴ * M) * EE)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, EE_conjT, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    have : star (1 / 2 : ℂ) * (1 / 2) = 1 / 4 := by simp; norm_num
    rw [this]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_smul, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
    EE_mul_EEt, Matrix.mul_one]
  simp

/-- `Θ` acts on the cut matrix by `Z ↦ (ε⊗ε) Z̄ (ε⊗ε)ᵀ`. -/
theorem Θ_ofMat (A : Mat4) : Θ (ofMat A) = ofMat (EE * A.map conj * EEᵀ) := by
  rw [Θ_eq_rot, cj_ofMat, rot_ofMat]
  rfl

/-- `Θ ψ_V = ψ_{(ε⊗ε) V̄ (ε⊗ε)ᵀ}`. -/
theorem Θ_choi (V : Mat4) : Θ (choi V) = choi (EE * V.map conj * EEᵀ) := by
  unfold choi
  rw [Θ_ofMat]
  congr 1
  have hE : ∀ k j, conj (EE k j) = EE k j := fun k j => congrFun (congrFun EE_map_conj k) j
  have h1 : ((1 / 2 : ℂ) • (V * EE)).map conj = (1 / 2 : ℂ) • (V.map conj * EE) := by
    ext i j
    simp [Matrix.mul_apply, map_sum, hE]
    left; exact map_ofNat _ 2
  rw [h1, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [EE_mul_EEt, EEt_mul_EE]

/-- The swap of two qubits. -/
def Sw : Mat4 := Matrix.of fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

/-- `C·I + S·SWAP`. -/
def Ug (C S : ℂ) : Mat4 := C • (1 : Mat4) + S • Sw

theorem Ug_conjT (C S : ℂ) : (Ug C S)ᴴ = Ug (conj C) (conj S) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Ug, Sw, Matrix.conjTranspose_apply, Matrix.one_apply]

/-- **Master formula.**  `tr[(C₁+S₁ SWAP)(a⊗b)(C₂+S₂ SWAP)(c⊗e)]`, for arbitrary `2×2` matrices. -/
theorem trace_gate (C₁ S₁ C₂ S₂ : ℂ) (a b c e : Op1) :
    Matrix.trace (Ug C₁ S₁ * ((a ⊗ₖ b) * Ug C₂ S₂ * (c ⊗ₖ e))) =
      C₁ * C₂ * (Matrix.trace (a * c) * Matrix.trace (b * e)) +
      C₁ * S₂ * Matrix.trace (c * a * e * b) + S₁ * C₂ * Matrix.trace (a * c * b * e) +
      S₁ * S₂ * (Matrix.trace (b * c) * Matrix.trace (a * e)) := by
  simp [Ug, Sw, Matrix.trace, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  ring

/-! ### The exchange gates `U_θ = cos θ − i sin θ SWAP` and their Choi probes -/

/-- `U_θ = cos θ · I − i sin θ · SWAP`. -/
noncomputable def Uex (θ : ℝ) : Mat4 := Ug (Real.cos θ) (-(Complex.I * Real.sin θ))

/-- The Choi probe `ψ_{U_θ} = (U_θ ⊗ I₃₄) s₁₃ s₂₄`. -/
noncomputable def psiEx (θ : ℝ) : Ψ 4 := choi (Uex θ)

theorem Ug_map_conj (C S : ℂ) : (Ug C S).map conj = Ug (conj C) (conj S) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Ug, Sw, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]

theorem trace_Ug_mul (C₁ S₁ C₂ S₂ : ℂ) :
    Matrix.trace (Ug C₁ S₁ * Ug C₂ S₂) = 4 * C₁ * C₂ + 2 * C₁ * S₂ + 2 * S₁ * C₂ + 4 * S₁ * S₂ := by
  simp [Ug, Sw, Matrix.trace, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem Uex_conjT (θ : ℝ) : (Uex θ)ᴴ = Ug (Real.cos θ) (Complex.I * Real.sin θ) := by
  rw [Uex, Ug_conjT, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    neg_mul, neg_neg]

theorem Uex_neg (θ : ℝ) : Uex (-θ) = Ug (Real.cos θ) (Complex.I * Real.sin θ) := by
  rw [Uex, Real.cos_neg, Real.sin_neg]
  push_cast
  rw [mul_neg, neg_neg]

theorem EE_mul_Ug (C S : ℂ) : EE * Ug C S = Ug C S * EE := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Ug, Sw, EE, eps, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- `ψ_{U_θ}` is mapped by `Θ` to `ψ_{U_{-θ}} = ψ_{U_θ^{-1}}`. -/
theorem Θ_psiEx (θ : ℝ) : Θ (psiEx θ) = psiEx (-θ) := by
  unfold psiEx
  rw [Θ_choi, Uex_neg]
  congr 1
  have h : (Uex θ).map conj = Ug (Real.cos θ) (Complex.I * Real.sin θ) := by
    rw [Uex, Ug_map_conj, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_I,
      Complex.conj_ofReal, neg_mul, neg_neg]
  rw [h, EE_mul_Ug, Matrix.mul_assoc, EE_mul_EEt, Matrix.mul_one]

/-- `ψ_{U_θ}` is a unit vector. -/
theorem nsq_psiEx (θ : ℝ) : nsq (psiEx θ) = 1 := by
  have h : ip (psiEx θ) (psiEx θ) = 1 := by
    unfold psiEx
    rw [ip_choi, Uex_conjT, Uex, trace_Ug_mul]
    have hc := Real.cos_sq_add_sin_sq θ
    have hc' : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast hc
    linear_combination hc' - ((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have h2 := ip_self (psiEx θ)
  rw [h] at h2
  exact_mod_cast h2.symm

/-- The overlap `⟨ψ_{U_θ}| u ψ_{U_{-θ}}⟩` of the Choi probe of `U_θ` with a local rotation of
that of `U_θ⁻¹ = Θ`-image, in terms of the one-qubit traces (`c' = adj u₃`, `e' = adj u₄`). -/
theorem ov_gate (θ : ℝ) (u : Fin 4 → Op1) :
    ip (psiEx θ) (rot u (psiEx (-θ))) =
      (1 / 4 : ℂ) * (
        (Real.cos θ : ℂ) * Real.cos θ *
          (Matrix.trace (u 0 * (u 2).adjugate) * Matrix.trace (u 1 * (u 3).adjugate)) +
        (Real.cos θ : ℂ) * (Complex.I * Real.sin θ) *
          Matrix.trace ((u 2).adjugate * u 0 * (u 3).adjugate * u 1) +
        (Complex.I * Real.sin θ) * Real.cos θ *
          Matrix.trace (u 0 * (u 2).adjugate * u 1 * (u 3).adjugate) +
        (Complex.I * Real.sin θ) * (Complex.I * Real.sin θ) *
          (Matrix.trace (u 1 * (u 2).adjugate) * Matrix.trace (u 0 * (u 3).adjugate))) := by
  unfold psiEx
  rw [rot_choi, ip_choi, Uex_conjT, Uex_neg, trace_gate]

/-! ### `SU(2)` traces and the three exchange-gate bounds -/

theorem SU2_adj {u : Op1} (h : SU2 u) : u.adjugate = uᴴ := by
  have h1 : u * u.adjugate = 1 := by rw [Matrix.mul_adjugate, h.2]; simp
  calc u.adjugate = (uᴴ * u) * u.adjugate := by rw [h.1, Matrix.one_mul]
    _ = uᴴ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem SU2_adj_su2 {u : Op1} (h : SU2 u) : SU2 u.adjugate := by
  rw [SU2_adj h]; exact SU2_adjoint h

theorem SU2_entry11 {u : Op1} (h : SU2 u) : u 1 1 = conj (u 0 0) := by
  have e := congrFun (congrFun (SU2_adj h) 0) 0
  simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using e

theorem SU2_normSq_le {u : Op1} (h : SU2 u) : Complex.normSq (u 0 0) ≤ 1 := by
  have e := congrFun (congrFun h.1 0) 0
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply] at e
  have e' : Complex.normSq (u 0 0) + Complex.normSq (u 1 0) = 1 := by
    have := congrArg Complex.re e
    simp [Complex.normSq_apply] at this ⊢
    nlinarith
  nlinarith [Complex.normSq_nonneg (u 1 0)]

/-- The trace of an `SU(2)` element is real, of modulus at most `2`. -/
theorem SU2_trace {u : Op1} (h : SU2 u) :
    ∃ r : ℝ, Matrix.trace u = r ∧ r ^ 2 ≤ 4 := by
  refine ⟨2 * (u 0 0).re, ?_, ?_⟩
  · rw [Matrix.trace_fin_two, SU2_entry11 h]
    apply Complex.ext <;> simp <;> ring
  · have h1 := SU2_normSq_le h
    have h2 : (u 0 0).re ^ 2 ≤ Complex.normSq (u 0 0) := by
      rw [Complex.normSq_apply]; nlinarith [sq_nonneg (u 0 0).im]
    nlinarith

theorem SU2_trace_pair {P Q : Op1} (hP : SU2 P) (hQ : SU2 Q) :
    ∃ x y z : ℝ, Matrix.trace P = x ∧ Matrix.trace Q = y ∧ Matrix.trace (P * Q) = z ∧
      x ^ 2 ≤ 4 ∧ y ^ 2 ≤ 4 ∧ z ^ 2 ≤ 4 := by
  obtain ⟨x, hx, hx2⟩ := SU2_trace hP
  obtain ⟨y, hy, hy2⟩ := SU2_trace hQ
  obtain ⟨z, hz, hz2⟩ := SU2_trace (SU2_mul hP hQ)
  exact ⟨x, y, z, hx, hy, hz, hx2, hy2, hz2⟩

/-- `κ(θ) = (1 + 3 cos² 2θ)/4`. -/
noncomputable def kappa (θ : ℝ) : ℝ := (1 + 3 * Real.cos (2 * θ) ^ 2) / 4

theorem normSq_re_im (a b : ℝ) : Complex.normSq ((a : ℂ) + Complex.I * (b : ℂ)) = a ^ 2 + b ^ 2 := by
  simp [Complex.normSq_apply]; ring

/-- The elementary estimate behind case (i): the coefficient of `⟨ψ|uΘψ⟩` is
`¼[cos 2θ · xy + i sin 2θ · z]` with real `x, y, z ∈ [-2, 2]`. -/
theorem core_bound (θ : ℝ) (x y z : ℝ) (hx : x ^ 2 ≤ 4) (hy : y ^ 2 ≤ 4) (hz : z ^ 2 ≤ 4) :
    Complex.normSq ((1 / 4 : ℂ) * ((Real.cos θ : ℂ) * Real.cos θ * ((x : ℂ) * y) +
      (Real.cos θ : ℂ) * (Complex.I * Real.sin θ) * z + (Complex.I * Real.sin θ) * Real.cos θ * z +
      (Complex.I * Real.sin θ) * (Complex.I * Real.sin θ) * ((x : ℂ) * y))) ≤ kappa θ := by
  have e : (1 / 4 : ℂ) * ((Real.cos θ : ℂ) * Real.cos θ * ((x : ℂ) * y) +
      (Real.cos θ : ℂ) * (Complex.I * Real.sin θ) * z + (Complex.I * Real.sin θ) * Real.cos θ * z +
      (Complex.I * Real.sin θ) * (Complex.I * Real.sin θ) * ((x : ℂ) * y)) =
      ((Real.cos (2 * θ) * (x * y) / 4 : ℝ) : ℂ) + Complex.I * ((Real.sin (2 * θ) * z / 4 : ℝ) : ℂ) := by
    rw [Real.cos_two_mul', Real.sin_two_mul]
    generalize Real.cos θ = c
    generalize Real.sin θ = s
    push_cast
    linear_combination ((1 / 4 : ℂ) * (s : ℂ) ^ 2 * (x * y)) * Complex.I_sq
  rw [e, normSq_re_im]
  have hxy : (x * y) ^ 2 ≤ 16 := by
    rw [mul_pow]; nlinarith [sq_nonneg x, sq_nonneg y]
  have hc := Real.cos_sq_add_sin_sq (2 * θ)
  unfold kappa
  have h1 : (Real.cos (2 * θ) * (x * y) / 4) ^ 2 ≤ Real.cos (2 * θ) ^ 2 := by
    have : (Real.cos (2 * θ) * (x * y) / 4) ^ 2 = Real.cos (2 * θ) ^ 2 * (x * y) ^ 2 / 16 := by ring
    rw [this]; nlinarith [sq_nonneg (Real.cos (2 * θ))]
  have h2 : (Real.sin (2 * θ) * z / 4) ^ 2 ≤ Real.sin (2 * θ) ^ 2 / 4 := by
    have : (Real.sin (2 * θ) * z / 4) ^ 2 = Real.sin (2 * θ) ^ 2 * z ^ 2 / 16 := by ring
    rw [this]; nlinarith [sq_nonneg (Real.sin (2 * θ))]
  nlinarith

/-- Case (i), spins `1,2` share a frame: `|⟨ψ_{U_θ}|uΘψ_{U_θ}⟩|² ≤ κ`. -/
theorem ov_le_kappa_of_01 (θ : ℝ) (u : Fin 4 → Op1) (hu : ∀ i, SU2 (u i)) (h01 : u 0 = u 1) :
    Complex.normSq (ip (psiEx θ) (rot u (psiEx (-θ)))) ≤ kappa θ := by
  have hc2 := SU2_adj_su2 (hu 2)
  have hc3 := SU2_adj_su2 (hu 3)
  obtain ⟨x, y, z, hx, hy, hz, hx2, hy2, hz2⟩ :=
    SU2_trace_pair (SU2_mul (hu 0) hc2) (SU2_mul (hu 0) hc3)
  have e1 : Matrix.trace (u 0 * (u 2).adjugate) = x := hx
  have e2 : Matrix.trace (u 1 * (u 3).adjugate) = y := by rw [← h01]; exact hy
  have e5 : Matrix.trace (u 1 * (u 2).adjugate) = x := by rw [← h01]; exact hx
  have e6 : Matrix.trace (u 0 * (u 3).adjugate) = y := hy
  have e4 : Matrix.trace (u 0 * (u 2).adjugate * u 1 * (u 3).adjugate) = z := by
    rw [← h01, ← hz]; simp only [Matrix.mul_assoc]
  have e3 : Matrix.trace ((u 2).adjugate * u 0 * (u 3).adjugate * u 1) = z := by
    rw [← h01, Matrix.trace_mul_comm, ← hz]; simp only [Matrix.mul_assoc]
  rw [ov_gate, e1, e2, e3, e4, e5, e6]
  exact core_bound θ x y z hx2 hy2 hz2

/-- Case (i), spins `3,4` share a frame: `|⟨ψ_{U_θ}|uΘψ_{U_θ}⟩|² ≤ κ`. -/
theorem ov_le_kappa_of_23 (θ : ℝ) (u : Fin 4 → Op1) (hu : ∀ i, SU2 (u i)) (h23 : u 2 = u 3) :
    Complex.normSq (ip (psiEx θ) (rot u (psiEx (-θ)))) ≤ kappa θ := by
  have hc2 := SU2_adj_su2 (hu 2)
  obtain ⟨x, y, z, hx, hy, hz, hx2, hy2, hz2⟩ :=
    SU2_trace_pair (SU2_mul (hu 0) hc2) (SU2_mul (hu 1) hc2)
  have e1 : Matrix.trace (u 0 * (u 2).adjugate) = x := hx
  have e2 : Matrix.trace (u 1 * (u 3).adjugate) = y := by rw [← h23]; exact hy
  have e5 : Matrix.trace (u 1 * (u 2).adjugate) = y := hy
  have e6 : Matrix.trace (u 0 * (u 3).adjugate) = x := by rw [← h23]; exact hx
  have e4 : Matrix.trace (u 0 * (u 2).adjugate * u 1 * (u 3).adjugate) = z := by
    rw [← h23, ← hz]; simp only [Matrix.mul_assoc]
  have e3 : Matrix.trace ((u 2).adjugate * u 0 * (u 3).adjugate * u 1) = z := by
    rw [← h23, show (u 2).adjugate * u 0 * (u 2).adjugate * u 1 =
      (u 2).adjugate * (u 0 * (u 2).adjugate * u 1) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, ← hz]
    simp only [Matrix.mul_assoc]
  rw [ov_gate, e1, e2, e3, e4, e5, e6, mul_comm (y : ℂ) (x : ℂ)]
  exact core_bound θ x y z hx2 hy2 hz2

/-- `iσ_z`. -/
def pz : Op1 := !![Complex.I, 0; 0, -Complex.I]

theorem SU2_pz : SU2 pz := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [pz, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [pz, Matrix.det_fin_two]

/-- `iσ_x`. -/
def px : Op1 := !![0, Complex.I; Complex.I, 0]

theorem SU2_px : SU2 px := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [px, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [px, Matrix.det_fin_two]

/-- The explicit rotation `(iσ_z, iσ_y, iσ_z, iσ_y) ∈ K_{13|24}`: overlap `cos θ · e^{iθ}`. -/
theorem ov_13_24_eq (θ : ℝ) :
    ip (psiEx θ) (rot ![pz, eps, pz, eps] (psiEx (-θ))) =
      (Real.cos θ : ℂ) * ((Real.cos θ : ℂ) + Complex.I * Real.sin θ) := by
  rw [ov_gate]
  simp [pz, eps, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

/-- The explicit rotation `(iσ_z, iσ_y, iσ_y, iσ_z) ∈ K_{14|23}`: overlap `i sin θ · e^{iθ}`. -/
theorem ov_14_23_eq (θ : ℝ) :
    ip (psiEx θ) (rot ![pz, eps, eps, pz] (psiEx (-θ))) =
      Complex.I * (Real.sin θ : ℂ) * ((Real.cos θ : ℂ) + Complex.I * Real.sin θ) := by
  rw [ov_gate]
  simp [pz, eps, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

/-- The identity rotation: overlap `cos 2θ + (i/2) sin 2θ`. -/
theorem ov_id_eq (θ : ℝ) :
    ip (psiEx θ) (psiEx (-θ)) =
      ((Real.cos (2 * θ) : ℝ) : ℂ) + Complex.I * ((Real.sin (2 * θ) / 2 : ℝ) : ℂ) := by
  have h := ov_gate θ (fun _ => (1 : Op1))
  rw [rot_one] at h
  rw [h]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.adjugate_one]
  rw [Complex.cos_two_mul', Complex.sin_two_mul]
  linear_combination (Complex.sin (θ : ℂ)) ^ 2 * Complex.I_sq

theorem normSq_ov_id (θ : ℝ) : Complex.normSq (ip (psiEx θ) (psiEx (-θ))) = kappa θ := by
  rw [ov_id_eq, normSq_re_im]
  have hc := Real.cos_sq_add_sin_sq (2 * θ)
  unfold kappa
  nlinarith

theorem normSq_ov_13_24 (θ : ℝ) :
    Complex.normSq (ip (psiEx θ) (rot ![pz, eps, pz, eps] (psiEx (-θ)))) = Real.cos θ ^ 2 := by
  rw [ov_13_24_eq, Complex.normSq_mul, Complex.normSq_ofReal, normSq_re_im]
  have hc := Real.cos_sq_add_sin_sq θ
  nlinarith

theorem normSq_ov_14_23 (θ : ℝ) :
    Complex.normSq (ip (psiEx θ) (rot ![pz, eps, eps, pz] (psiEx (-θ)))) = Real.sin θ ^ 2 := by
  rw [ov_14_23_eq, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal,
    normSq_re_im]
  have hc := Real.cos_sq_add_sin_sq θ
  nlinarith

end FourSpins

/-! ## Part 3. Theorem `thm:exchangesharing` -/

section ExchangeSharing

variable {β : Type*}

/-- The pattern `{13|24}` (spins `1,3` and `2,4` share). -/
def pat1324 : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The pattern `{14|23}`. -/
def pat1423 : Fin 4 → Fin 2 := ![0, 1, 1, 0]

/-- Lower bound for every pattern: the identity rotation, `F_K^π ≥ κ`. -/
theorem kappa_le_FKΘs (g : Fin 4 → β) (θ : ℝ) : kappa θ ≤ FKΘs g (psiEx θ) := by
  unfold FKΘs
  rw [Θ_psiEx]
  have h := le_FKs g (psiEx θ) (psiEx (-θ)) (fun _ => 1) (fun _ => SU2_one)
  have e : (fun i => (fun _ : β => (1 : Op1)) (g i)) = fun _ => (1 : Op1) := rfl
  rw [e, rot_one, normSq_ov_id] at h
  exact h

/-- Lower bound for patterns inside `{13|24}`: `F_K^π ≥ cos² θ`. -/
theorem cos_sq_le_FKΘs (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ) :
    Real.cos θ ^ 2 ≤ FKΘs g (psiEx θ) := by
  unfold FKΘs
  rw [Θ_psiEx]
  obtain ⟨v, hv, hvv⟩ := exists_fine_frame h SU2 SU2_one ![pz, eps] (by
    intro b; fin_cases b
    · exact SU2_pz
    · exact SU2_eps)
  have h1 := le_FKs g (psiEx θ) (psiEx (-θ)) v hv
  have e : (fun i => v (g i)) = ![pz, eps, pz, eps] := by
    funext i; rw [hvv i]; fin_cases i <;> rfl
  rw [e, normSq_ov_13_24] at h1
  exact h1

/-- Lower bound for patterns inside `{14|23}`: `F_K^π ≥ sin² θ`. -/
theorem sin_sq_le_FKΘs (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ) :
    Real.sin θ ^ 2 ≤ FKΘs g (psiEx θ) := by
  unfold FKΘs
  rw [Θ_psiEx]
  obtain ⟨v, hv, hvv⟩ := exists_fine_frame h SU2 SU2_one ![pz, eps] (by
    intro b; fin_cases b
    · exact SU2_pz
    · exact SU2_eps)
  have h1 := le_FKs g (psiEx θ) (psiEx (-θ)) v hv
  have e : (fun i => v (g i)) = ![pz, eps, eps, pz] := by
    funext i; rw [hvv i]; fin_cases i <;> rfl
  rw [e, normSq_ov_14_23] at h1
  exact h1

/-- Upper bound `κ` when spins `1,2` or spins `3,4` share a frame (unconditional). -/
theorem FKΘs_le_kappa (g : Fin 4 → β) (h : g 0 = g 1 ∨ g 2 = g 3) (θ : ℝ) :
    FKΘs g (psiEx θ) ≤ kappa θ := by
  unfold FKΘs FKs
  rw [Θ_psiEx]
  refine csSup_le (shSet_nonempty g _ _) ?_
  rintro r ⟨v, hv, rfl⟩
  rcases h with h | h
  · exact ov_le_kappa_of_01 θ _ (fun i => hv _) (by simp [h])
  · exact ov_le_kappa_of_23 θ _ (fun i => hv _) (by simp [h])

/-- **Theorem `thm:exchangesharing` (i)**, rotation overlap.  If spins `1,2` share a frame, or spins `3,4`
do (eight patterns, the common frame among them), `F_K^π(ψ_{U_θ}) = κ(θ)` exactly.  Unconditional. -/
theorem FKΘs_exchange_i (g : Fin 4 → β) (h : g 0 = g 1 ∨ g 2 = g 3) (θ : ℝ) :
    FKΘs g (psiEx θ) = kappa θ :=
  le_antisymm (FKΘs_le_kappa g h θ) (kappa_le_FKΘs g θ)

theorem kappa_pos (θ : ℝ) : 0 < kappa θ := by unfold kappa; positivity

/-- **Theorem `thm:exchangesharing` (i)**, chiral distance: `C_K^π = log (4/(1+3cos²2θ))`. -/
theorem CKs_exchange_i (g : Fin 4 → β) (h : g 0 = g 1 ∨ g 2 = g 3) (θ : ℝ) :
    CKs g (psiEx θ) = Real.log (4 / (1 + 3 * Real.cos (2 * θ) ^ 2)) := by
  unfold CKs
  rw [FKΘs_exchange_i g h θ, ← Real.log_inv, kappa]
  congr 1
  rw [inv_div]

/-- Every one of the fifteen sharing patterns of four spins is in exactly one of the three cases of
`thm:exchangesharing`: `1~2` or `3~4` (case (i)); else only `{13},{24}` may share (case (ii));
else only `{14},{23}` may share (case (iii), which also contains the unshared pattern). -/
theorem pattern_trichotomy (g : Fin 4 → β) :
    (g 0 = g 1 ∨ g 2 = g 3) ∨ Refines g pat1324 ∨ Refines g pat1423 := by
  by_cases h01 : g 0 = g 1
  · exact Or.inl (Or.inl h01)
  by_cases h23 : g 2 = g 3
  · exact Or.inl (Or.inr h23)
  right
  by_cases h02 : g 0 = g 2
  · left
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pat1324]
  by_cases h13 : g 1 = g 3
  · left
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pat1324]
  · right
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pat1423]

/-- Independent-frame exchange law (rotation part), recalled: `F_K(ψ_{U_θ}, ψ_{U_θ^{-1}}) ≤ cos² θ`
for `0 ≤ θ ≤ π/4`.  The paper obtains it from the Weyl-vertex formula (R7) for the magic-diagonal
form of `ψ_{U_θ}`, or from the filtered-gate law (R8).  Neither is formalised, so it is an explicit
hypothesis below.  Its closed form is `exchange_closed_form`. -/
def ExchangeIndepBound (θ : ℝ) : Prop := FKΘ (psiEx θ) ≤ Real.cos θ ^ 2

/-- **Theorem `thm:exchangesharing` (ii)**, rotation overlap, assuming the independent-frame bound.
If only the pairs `{1,3},{2,4}` share (four patterns, independent frames among them),
`F_K^π = cos² θ`. -/
theorem FKΘs_exchange_ii (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ)
    (hR : ExchangeIndepBound θ) : FKΘs g (psiEx θ) = Real.cos θ ^ 2 := by
  refine le_antisymm ?_ (cos_sq_le_FKΘs g h θ)
  exact (FKs_le_FK g _ _).trans hR

/-- **Theorem `thm:exchangesharing` (iii)**, rotation overlap, assuming the independent-frame bound.
If only the cross pairs `{1,4},{2,3}` share (three patterns),
`max(sin²θ, κ) ≤ F_K^π ≤ cos²θ`. -/
theorem FKΘs_exchange_iii (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ)
    (hR : ExchangeIndepBound θ) :
    max (Real.sin θ ^ 2) (kappa θ) ≤ FKΘs g (psiEx θ) ∧ FKΘs g (psiEx θ) ≤ Real.cos θ ^ 2 :=
  ⟨max_le (sin_sq_le_FKΘs g h θ) (kappa_le_FKΘs g θ), (FKs_le_FK g _ _).trans hR⟩

/-- **Theorem `thm:exchangesharing` (ii)**, chiral distance: `C_K^π = -log cos² θ
= log (2/(1+cos 2θ))`. -/
theorem CKs_exchange_ii (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ)
    (hR : ExchangeIndepBound θ) : CKs g (psiEx θ) = Real.log (2 / (1 + Real.cos (2 * θ))) := by
  unfold CKs
  rw [FKΘs_exchange_ii g h θ hR, ← Real.log_inv, Real.cos_two_mul]
  congr 1
  by_cases hc : Real.cos θ = 0
  · simp [hc]
  · field_simp
    ring

/-- **Theorem `thm:exchangesharing` (iii)**, chiral distance:
`log (2/(1+cos 2θ)) ≤ C_K^π ≤ -log max(sin²θ, κ)`. -/
theorem CKs_exchange_iii (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ)
    (hR : ExchangeIndepBound θ) :
    Real.log (2 / (1 + Real.cos (2 * θ))) ≤ CKs g (psiEx θ) ∧
      CKs g (psiEx θ) ≤ -Real.log (max (Real.sin θ ^ 2) (kappa θ)) := by
  obtain ⟨h1, h2⟩ := FKΘs_exchange_iii g h θ hR
  have hk := kappa_pos θ
  have hpos : 0 < max (Real.sin θ ^ 2) (kappa θ) := lt_of_lt_of_le hk (le_max_right _ _)
  have hF : 0 < FKΘs g (psiEx θ) := lt_of_lt_of_le hpos h1
  have hcos : 0 < Real.cos θ ^ 2 := lt_of_lt_of_le hF h2
  have hc : Real.cos θ ≠ 0 := by
    intro h0; rw [h0] at hcos; simp at hcos
  constructor
  · have e : Real.log (2 / (1 + Real.cos (2 * θ))) = -Real.log (Real.cos θ ^ 2) := by
      rw [← Real.log_inv, Real.cos_two_mul]
      congr 1
      field_simp
      ring
    rw [e]
    unfold CKs
    have := Real.log_le_log hF h2
    linarith
  · unfold CKs
    have := Real.log_le_log hpos h1
    linarith

/-- The independent-frame bound has the closed form already proved in `GateOverlap.lean`: for
`0 ≤ θ ≤ π/4`, `(1 + |cos 2θ|)/2 = cos² θ`, i.e. `FKmag (dgate (θ/2,θ/2,θ/2)) = cos² θ`. -/
theorem exchange_closed_form (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    FKmag (dgate (fun _ => θ / 2)) = Real.cos θ ^ 2 := by
  rw [FKmag_gate_exchange]
  have hc : 0 ≤ Real.cos (2 * θ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [abs_of_nonneg hc, Real.cos_two_mul]
  ring

/-- At `√SWAP` (`θ = π/4`): `κ = 1/4`. -/
theorem kappa_quarter : kappa (Real.pi / 4) = 1 / 4 := by
  unfold kappa
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
  norm_num

/-- **`√SWAP`, every pattern** (`thm:exchangesharing`, last sentence), rotation form, assuming the
independent-frame bound at `π/4`: `C_K^π = log 4` if spins `1,2` or `3,4` share a frame and
`log 2` for every other pattern. -/
theorem CKs_sqrtSwap (g : Fin 4 → β) (hR : ExchangeIndepBound (Real.pi / 4)) :
    ((g 0 = g 1 ∨ g 2 = g 3) → CKs g (psiEx (Real.pi / 4)) = Real.log 4) ∧
    (¬ (g 0 = g 1 ∨ g 2 = g 3) → CKs g (psiEx (Real.pi / 4)) = Real.log 2) := by
  have hcos : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsin : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  constructor
  · intro h
    unfold CKs
    rw [FKΘs_exchange_i g h, kappa_quarter, show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      Real.log_inv, neg_neg]
  · intro h
    have hF : FKΘs g (psiEx (Real.pi / 4)) = 1 / 2 := by
      rcases pattern_trichotomy g with h' | h' | h'
      · exact absurd h' h
      · rw [FKΘs_exchange_ii g h' _ hR, hcos]
      · obtain ⟨h1, h2⟩ := FKΘs_exchange_iii g h' _ hR
        rw [hcos] at h2
        have : (1 / 2 : ℝ) ≤ max (Real.sin (Real.pi / 4) ^ 2) (kappa (Real.pi / 4)) := by
          rw [hsin]; exact le_max_left _ _
        linarith
    unfold CKs
    rw [hF, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]

end ExchangeSharing


/-! ## Part 4. The Higuchi--Sudbery state `M₄` (Theorem `thm:m4sharing`) -/

section M4

open FormalResearch.FourQubitEntropy in
/-- `M₄` as a vector of `Ψ 4`: the vector `M4` of `FormalResearch/FourQubitEntropy/Attainment.lean`. -/
noncomputable def M4n : Ψ 4 := fun x => FormalResearch.FourQubitEntropy.M4 (x 0) (x 1) (x 2) (x 3)

/-- `ω = e^{2πi/3}`. -/
noncomputable abbrev ω3 : ℂ := FormalResearch.FourQubitEntropy.omega

/-- `1/√6` as a complex number. -/
noncomputable def r6 : ℂ := ((1 / Real.sqrt 6 : ℝ) : ℂ)

theorem r6_sq : r6 ^ 2 = 1 / 6 := by
  unfold r6
  rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]
  push_cast; norm_num

theorem conj_r6 : conj r6 = r6 := Complex.conj_ofReal _

theorem ω3_rel : ω3 ^ 2 + ω3 + 1 = 0 := FormalResearch.FourQubitEntropy.omega_sq_add

theorem conjω3_rel : (conj ω3) ^ 2 + conj ω3 + 1 = 0 := by
  have := congrArg conj ω3_rel
  simpa using this

theorem conjω3_eq : conj ω3 = -ω3 - 1 := by
  have h := FormalResearch.FourQubitEntropy.conj_omega
  rw [h]; linear_combination ω3_rel

/-- The cut matrix of `ε(x₁,x₂)ε(x₃,x₄)` (the pairing `{12|34}`). -/
def Y1 : Mat4 := Matrix.of fun i j => eps i.1 i.2 * eps j.1 j.2

/-- `M₄ = (ω·T_{12|34} + T_{13|24})/√6` as a cut matrix. -/
noncomputable def Z4 : Mat4 := r6 • (ω3 • Y1 + EE)

theorem M4n_eq : M4n = ofMat Z4 := by
  funext x
  rw [eq_four x]
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  generalize x 3 = d
  have hc := conjω3_eq
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [M4n, ofMat, Z4, Y1, EE, eps, Matrix.kroneckerMap_apply, FormalResearch.FourQubitEntropy.M4,
      r6, hc] <;> ring

theorem kron_sandwich_Y1 (W : Op1) : (W ⊗ₖ W) * Y1 * (W ⊗ₖ W)ᵀ = (W.det) ^ 2 • Y1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Y1, eps, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.det_fin_two] <;> ring

theorem kron_sandwich_EE (W : Op1) : (W ⊗ₖ W) * EE * (W ⊗ₖ W)ᵀ = (W.det) ^ 2 • EE := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [EE, eps, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.det_fin_two] <;> ring

/-- `M₄` is a singlet: invariant under `W^{⊗4}` for `det W = 1`. -/
theorem rot_const_M4n (W : Op1) (hW : W.det = 1) : rot (fun _ => W) M4n = M4n := by
  rw [M4n_eq, rot_ofMat]
  congr 1
  simp only [Z4, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    kron_sandwich_Y1, kron_sandwich_EE, hW]
  simp

/-- `Θ M₄ = \overline{M₄}` (componentwise conjugate). -/
theorem Θ_M4n : Θ M4n = ofMat (Z4.map conj) := by
  rw [M4n_eq, Θ_ofMat]
  congr 1
  have hE : ∀ k j, conj (EE k j) = EE k j := fun k j => congrFun (congrFun EE_map_conj k) j
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Z4, Y1, EE, eps, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6]

theorem ov_M4_01 (A B : Op1) :
    ip M4n (rot ![A, B, (1 : Op1), (1 : Op1)] (Θ M4n)) =
      -(1 / 6 : ℂ) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*(2*(A 0 0)*(B 1 1) - 2*(A 0 1)*(B 1 0) - 2*(A 1 0)*(B 0 1) + 2*(A 1 1)*(B 0 0))) * conjω3_rel + (1*(A 0 0)*(B 0 0) - 1*(A 0 0)*(B 1 1) + 2*(A 0 1)*(B 1 0) + 2*(A 1 0)*(B 0 1) - 1*(A 1 1)*(B 0 0) + 1*(A 1 1)*(B 1 1)) * r6_sq

theorem ov_M4_02 (A B : Op1) :
    ip M4n (rot ![A, (1 : Op1), B, (1 : Op1)] (Θ M4n)) =
      -(conj ω3 ^ 2 / 6 : ℂ) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (-(A 0 0)*(B 0 0)/6 + (A 0 0)*(B 1 1)/6 - (A 0 1)*(B 1 0)/3 - (A 1 0)*(B 0 1)/3 + (A 1 1)*(B 0 0)/6 - (A 1 1)*(B 1 1)/6 + r6^2*((A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) + (A 1 1)*(B 0 0) + (A 1 1)*(B 1 1))) * conjω3_rel + (-(A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) - 2*(A 0 1)*(B 1 0) - 2*(A 1 0)*(B 0 1) + (A 1 1)*(B 0 0) - (A 1 1)*(B 1 1) + (conj ω3)*(-(A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) - 2*(A 0 1)*(B 1 0) - 2*(A 1 0)*(B 0 1) + (A 1 1)*(B 0 0) - (A 1 1)*(B 1 1))) * r6_sq

theorem ov_M4_03 (A B : Op1) :
    ip M4n (rot ![A, (1 : Op1), (1 : Op1), B] (Θ M4n)) =
      -(conj ω3 / 6 : ℂ) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) + (A 1 1)*(B 0 0) + (A 1 1)*(B 1 1))) * conjω3_rel + ((conj ω3)*((A 0 0)*(B 0 0) - (A 0 0)*(B 1 1) + 2*(A 0 1)*(B 1 0) + 2*(A 1 0)*(B 0 1) - (A 1 1)*(B 0 0) + (A 1 1)*(B 1 1))) * r6_sq

theorem ov_M4_12 (A B : Op1) :
    ip M4n (rot ![(1 : Op1), A, B, (1 : Op1)] (Θ M4n)) =
      -(conj ω3 / 6 : ℂ) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) + (A 1 1)*(B 0 0) + (A 1 1)*(B 1 1))) * conjω3_rel + ((conj ω3)*((A 0 0)*(B 0 0) - (A 0 0)*(B 1 1) + 2*(A 0 1)*(B 1 0) + 2*(A 1 0)*(B 0 1) - (A 1 1)*(B 0 0) + (A 1 1)*(B 1 1))) * r6_sq

theorem ov_M4_13 (A B : Op1) :
    ip M4n (rot ![(1 : Op1), A, (1 : Op1), B] (Θ M4n)) =
      -(conj ω3 ^ 2 / 6 : ℂ) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (-(A 0 0)*(B 0 0)/6 + (A 0 0)*(B 1 1)/6 - (A 0 1)*(B 1 0)/3 - (A 1 0)*(B 0 1)/3 + (A 1 1)*(B 0 0)/6 - (A 1 1)*(B 1 1)/6 + r6^2*((A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) + (A 1 1)*(B 0 0) + (A 1 1)*(B 1 1))) * conjω3_rel + (-(A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) - 2*(A 0 1)*(B 1 0) - 2*(A 1 0)*(B 0 1) + (A 1 1)*(B 0 0) - (A 1 1)*(B 1 1) + (conj ω3)*(-(A 0 0)*(B 0 0) + (A 0 0)*(B 1 1) - 2*(A 0 1)*(B 1 0) - 2*(A 1 0)*(B 0 1) + (A 1 1)*(B 0 0) - (A 1 1)*(B 1 1))) * r6_sq

theorem ov_M4_23 (A B : Op1) :
    ip M4n (rot ![(1 : Op1), (1 : Op1), A, B] (Θ M4n)) =
      -(1 / 6 : ℂ) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*(2*(A 0 0)*(B 1 1) - 2*(A 0 1)*(B 1 0) - 2*(A 1 0)*(B 0 1) + 2*(A 1 1)*(B 0 0))) * conjω3_rel + (1*(A 0 0)*(B 0 0) - 1*(A 0 0)*(B 1 1) + 2*(A 0 1)*(B 1 0) + 2*(A 1 0)*(B 0 1) - 1*(A 1 1)*(B 0 0) + 1*(A 1 1)*(B 1 1)) * r6_sq

theorem ov_M4_zero0 (A : Op1) : ip M4n (rot ![A, (1 : Op1), (1 : Op1), (1 : Op1)] (Θ M4n)) = 0 := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply]
  linear_combination (r6^2*(2*(A 0 0) + 2*(A 1 1))) * conjω3_rel + (0) * r6_sq

theorem ov_M4_zero1 (A : Op1) : ip M4n (rot ![(1 : Op1), A, (1 : Op1), (1 : Op1)] (Θ M4n)) = 0 := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply]
  linear_combination (r6^2*(2*(A 0 0) + 2*(A 1 1))) * conjω3_rel + (0) * r6_sq

theorem ov_M4_zero2 (A : Op1) : ip M4n (rot ![(1 : Op1), (1 : Op1), A, (1 : Op1)] (Θ M4n)) = 0 := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply]
  linear_combination (r6^2*(2*(A 0 0) + 2*(A 1 1))) * conjω3_rel + (0) * r6_sq

theorem ov_M4_zero3 (A : Op1) : ip M4n (rot ![(1 : Op1), (1 : Op1), (1 : Op1), A] (Θ M4n)) = 0 := by
  rw [Θ_M4n, M4n_eq, rot_ofMat, ip_ofMat]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply]
  linear_combination (r6^2*(2*(A 0 0) + 2*(A 1 1))) * conjω3_rel + (0) * r6_sq



/-- Frobenius norm squared of a `2×2` matrix. -/
def fro (M : Op1) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

theorem fro_cast (M : Op1) : ((fro M : ℝ) : ℂ) = ∑ i, ∑ j, conj (M i j) * M i j := by
  simp [fro, Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]

/-! Norms of the rotated state: `‖(A⊗B)ΘM₄‖² = (‖A B⁻¹‖² + ‖A‖²‖B‖²)/6` at every position. -/

theorem nsq_M4_01 (A B : Op1) :
    nsq (rot ![A, B, (1 : Op1), (1 : Op1)] (Θ M4n)) = (fro (A * B.adjugate) + fro A * fro B) / 6 := by
  apply Complex.ofReal_injective
  rw [← ip_self, Θ_M4n, rot_ofMat, ip_ofMat]
  push_cast
  simp only [fro_cast]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((starRingEnd ℂ) ω3)*(2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0))) + r6^2*((A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)))) * conjω3_eq + (r6^2*(-2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)))) * conjω3_rel + ((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) * r6_sq

theorem nsq_M4_02 (A B : Op1) :
    nsq (rot ![A, (1 : Op1), B, (1 : Op1)] (Θ M4n)) = (fro (A * B.adjugate) + fro A * fro B) / 6 := by
  apply Complex.ofReal_injective
  rw [← ip_self, Θ_M4n, rot_ofMat, ip_ofMat]
  push_cast
  simp only [fro_cast]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((starRingEnd ℂ) ω3)*((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) + r6^2*((A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)))) * conjω3_eq + (r6^2*(-(A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1)))) * conjω3_rel + ((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) * r6_sq

theorem nsq_M4_03 (A B : Op1) :
    nsq (rot ![A, (1 : Op1), (1 : Op1), B] (Θ M4n)) = (fro (A * B.adjugate) + fro A * fro B) / 6 := by
  apply Complex.ofReal_injective
  rw [← ip_self, Θ_M4n, rot_ofMat, ip_ofMat]
  push_cast
  simp only [fro_cast]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((starRingEnd ℂ) ω3)*((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) + r6^2*((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1)))) * conjω3_eq + (r6^2*(-(A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1)))) * conjω3_rel + ((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) * r6_sq

theorem nsq_M4_12 (A B : Op1) :
    nsq (rot ![(1 : Op1), A, B, (1 : Op1)] (Θ M4n)) = (fro (A * B.adjugate) + fro A * fro B) / 6 := by
  apply Complex.ofReal_injective
  rw [← ip_self, Θ_M4n, rot_ofMat, ip_ofMat]
  push_cast
  simp only [fro_cast]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((starRingEnd ℂ) ω3)*((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) + r6^2*((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1)))) * conjω3_eq + (r6^2*(-(A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1)))) * conjω3_rel + ((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) * r6_sq

theorem nsq_M4_13 (A B : Op1) :
    nsq (rot ![(1 : Op1), A, (1 : Op1), B] (Θ M4n)) = (fro (A * B.adjugate) + fro A * fro B) / 6 := by
  apply Complex.ofReal_injective
  rw [← ip_self, Θ_M4n, rot_ofMat, ip_ofMat]
  push_cast
  simp only [fro_cast]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((starRingEnd ℂ) ω3)*((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) + r6^2*((A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)))) * conjω3_eq + (r6^2*(-(A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1)))) * conjω3_rel + ((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) * r6_sq

theorem nsq_M4_23 (A B : Op1) :
    nsq (rot ![(1 : Op1), (1 : Op1), A, B] (Θ M4n)) = (fro (A * B.adjugate) + fro A * fro B) / 6 := by
  apply Complex.ofReal_injective
  rw [← ip_self, Θ_M4n, rot_ofMat, ip_ofMat]
  push_cast
  simp only [fro_cast]
  simp [Z4, Y1, EE, eps, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, conj_r6, Matrix.conjTranspose_apply,
      Matrix.adjugate_fin_two]
  linear_combination (r6^2*((starRingEnd ℂ) ω3)*(2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0))) + r6^2*((A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)))) * conjω3_eq + (r6^2*(-2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) - 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)))) * conjω3_rel + ((A 0 0)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) - (A 0 0)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 0)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) - (A 0 0)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) - (A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 0 1)*(B 0 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 0)) + (A 0 1)*(B 0 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 0 1)) - (A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 0 1)*(B 1 0)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 0)) + (A 0 1)*(B 1 1)*((starRingEnd ℂ) (A 0 1))*((starRingEnd ℂ) (B 1 1)) + (A 1 0)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 0)) + 2*(A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) - (A 1 0)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 0)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 0)) + 2*(A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) - (A 1 0)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) - (A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 0 1)) + 2*(A 1 1)*(B 0 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 0)) + (A 1 1)*(B 0 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 0 1)) - (A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 0))*((starRingEnd ℂ) (B 1 1)) + 2*(A 1 1)*(B 1 0)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 0)) + (A 1 1)*(B 1 1)*((starRingEnd ℂ) (A 1 1))*((starRingEnd ℂ) (B 1 1))) * r6_sq

/-! ### The filter inequality for a pair of free frames

`|2 tr(AD) − tr A tr D|² ≤ (8/3)(‖AD‖² + ‖A‖²‖D‖²)` for all `2×2` complex matrices (the paper's
Cauchy--Schwarz argument, in the Pauli decomposition `A = a₀ + a·σ`). -/

theorem core_real (p q S T u v W : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hu : 0 ≤ u) (hv : v = p * q) (hu2 : u ^ 2 ≤ S * T) (hW : (u - v) ^ 2 ≤ W) :
    3 * u ^ 2 ≤ W + 2 * ((p ^ 2 + S) * (q ^ 2 + T)) := by
  have h0 : 0 ≤ p ^ 2 * T + S * q ^ 2 := by positivity
  have h1 : 2 * p * q * u ≤ p ^ 2 * T + S * q ^ 2 := by
    have hsq : (2 * p * q * u) ^ 2 ≤ (p ^ 2 * T + S * q ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (p ^ 2 * T - S * q ^ 2),
        mul_le_mul_of_nonneg_left hu2 (mul_nonneg (sq_nonneg p) (sq_nonneg q))]
    by_contra hc
    push Not at hc
    nlinarith
  subst hv
  nlinarith [sq_nonneg (p * q), mul_nonneg hp hq]

theorem fro_two_coeff (A : Op1) :
    fro A = 2 * (Complex.normSq ((A 0 0 + A 1 1) / 2) + Complex.normSq ((A 0 1 + A 1 0) / 2) +
      Complex.normSq (Complex.I * (A 0 1 - A 1 0) / 2) + Complex.normSq ((A 0 0 - A 1 1) / 2)) := by
  simp [fro, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem tr_two_coeff (A D : Op1) :
    Matrix.trace (A * D) = 2 * (((A 0 0 + A 1 1) / 2) * ((D 0 0 + D 1 1) / 2) +
      ((A 0 1 + A 1 0) / 2) * ((D 0 1 + D 1 0) / 2) +
      (Complex.I * (A 0 1 - A 1 0) / 2) * (Complex.I * (D 0 1 - D 1 0) / 2) +
      ((A 0 0 - A 1 1) / 2) * ((D 0 0 - D 1 1) / 2)) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem fro_ge_tr (M : Op1) : Complex.normSq (Matrix.trace M) ≤ 2 * fro M := by
  simp only [fro, Matrix.trace_fin_two, Fin.sum_univ_two, Complex.normSq_apply, Complex.add_re,
    Complex.add_im]
  nlinarith [sq_nonneg ((M 0 0).re - (M 1 1).re), sq_nonneg ((M 0 0).im - (M 1 1).im),
    mul_self_nonneg (M 0 1).re, mul_self_nonneg (M 0 1).im, mul_self_nonneg (M 1 0).re,
    mul_self_nonneg (M 1 0).im]

theorem normSq_two : Complex.normSq (2 : ℂ) = 4 := by
  simp [Complex.normSq_apply]; norm_num

theorem normSq_four : Complex.normSq (4 : ℂ) = 16 := by
  simp [Complex.normSq_apply]; norm_num

theorem key_FC (A D : Op1) :
    Complex.normSq (2 * Matrix.trace (A * D) - Matrix.trace A * Matrix.trace D) ≤
      (8 / 3) * (fro (A * D) + fro A * fro D) := by
  have hAD := fro_ge_tr (A * D)
  have hA : Matrix.trace A = 2 * ((A 0 0 + A 1 1) / 2) := by simp [Matrix.trace_fin_two]; ring
  have hD : Matrix.trace D = 2 * ((D 0 0 + D 1 1) / 2) := by simp [Matrix.trace_fin_two]; ring
  rw [tr_two_coeff] at hAD ⊢
  rw [hA, hD]
  rw [fro_two_coeff A, fro_two_coeff D]
  generalize (A 0 0 + A 1 1) / 2 = a0 at *
  generalize (A 0 1 + A 1 0) / 2 = a1 at *
  generalize Complex.I * (A 0 1 - A 1 0) / 2 = a2 at *
  generalize (A 0 0 - A 1 1) / 2 = a3 at *
  generalize (D 0 0 + D 1 1) / 2 = d0 at *
  generalize (D 0 1 + D 1 0) / 2 = d1 at *
  generalize Complex.I * (D 0 1 - D 1 0) / 2 = d2 at *
  generalize (D 0 0 - D 1 1) / 2 = d3 at *
  obtain ⟨x, hx⟩ : ∃ x, x = a1 * d1 + a2 * d2 + a3 * d3 := ⟨_, rfl⟩
  have hs : a0 * d0 + a1 * d1 + a2 * d2 + a3 * d3 = a0 * d0 + x := by rw [hx]; ring
  have e : 2 * (2 * (a0 * d0 + a1 * d1 + a2 * d2 + a3 * d3)) - 2 * a0 * (2 * d0) = 4 * x := by
    rw [hx]; ring
  rw [e]
  rw [hs, Complex.normSq_mul, normSq_two] at hAD
  rw [Complex.normSq_mul, normSq_four]
  -- Cauchy-Schwarz for the vector parts
  have hx2 : Complex.normSq x ≤
      (Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3) *
        (Complex.normSq d1 + Complex.normSq d2 + Complex.normSq d3) := by
    have h1 : ‖x‖ ≤ ‖a1‖ * ‖d1‖ + ‖a2‖ * ‖d2‖ + ‖a3‖ * ‖d3‖ := by
      rw [hx]
      calc ‖a1 * d1 + a2 * d2 + a3 * d3‖ ≤ ‖a1 * d1 + a2 * d2‖ + ‖a3 * d3‖ := norm_add_le _ _
        _ ≤ ‖a1 * d1‖ + ‖a2 * d2‖ + ‖a3 * d3‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by simp only [norm_mul]
    have h2 : ‖x‖ ^ 2 ≤ (‖a1‖ * ‖d1‖ + ‖a2‖ * ‖d2‖ + ‖a3‖ * ‖d3‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm,
      ← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm]
    nlinarith [sq_nonneg (‖a1‖ * ‖d2‖ - ‖a2‖ * ‖d1‖), sq_nonneg (‖a1‖ * ‖d3‖ - ‖a3‖ * ‖d1‖),
      sq_nonneg (‖a2‖ * ‖d3‖ - ‖a3‖ * ‖d2‖)]
  have hW : (‖x‖ - ‖a0 * d0‖) ^ 2 ≤ Complex.normSq (a0 * d0 + x) := by
    have h := abs_norm_sub_norm_le x (-(a0 * d0))
    rw [norm_neg, sub_neg_eq_add, add_comm] at h
    rw [← Complex.sq_norm]
    have := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at this
    exact this
  have core := core_real ‖a0‖ ‖d0‖
    (Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3)
    (Complex.normSq d1 + Complex.normSq d2 + Complex.normSq d3) ‖x‖ ‖a0 * d0‖
    (Complex.normSq (a0 * d0 + x)) (norm_nonneg _) (norm_nonneg _)
    (by linarith [Complex.normSq_nonneg a1, Complex.normSq_nonneg a2, Complex.normSq_nonneg a3])
    (by linarith [Complex.normSq_nonneg d1, Complex.normSq_nonneg d2, Complex.normSq_nonneg d3])
    (norm_nonneg _) (norm_mul _ _) (by rw [Complex.sq_norm]; exact hx2) hW
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm] at core
  nlinarith [core, hAD]


/-- The Cauchy--Schwarz bound behind case (i) (`thm:exchangesharing`): for all `2×2` matrices,
`|cos 2θ · tr A tr B + i sin 2θ · tr(AB)|² ≤ (1 + 3 cos² 2θ) ‖A‖²‖B‖²`. -/
theorem exch_ineq (C2 S2 : ℝ) (hcs : C2 ^ 2 + S2 ^ 2 = 1) (A B : Op1) :
    Complex.normSq ((C2 : ℂ) * (Matrix.trace A * Matrix.trace B) + Complex.I * S2 * Matrix.trace (A * B)) ≤
      (1 + 3 * C2 ^ 2) * (fro A * fro B) := by
  have hA : Matrix.trace A = 2 * ((A 0 0 + A 1 1) / 2) := by simp [Matrix.trace_fin_two]; ring
  have hB : Matrix.trace B = 2 * ((B 0 0 + B 1 1) / 2) := by simp [Matrix.trace_fin_two]; ring
  rw [tr_two_coeff, hA, hB, fro_two_coeff A, fro_two_coeff B]
  generalize (A 0 0 + A 1 1) / 2 = a0 at *
  generalize (A 0 1 + A 1 0) / 2 = a1 at *
  generalize Complex.I * (A 0 1 - A 1 0) / 2 = a2 at *
  generalize (A 0 0 - A 1 1) / 2 = a3 at *
  generalize (B 0 0 + B 1 1) / 2 = b0 at *
  generalize (B 0 1 + B 1 0) / 2 = b1 at *
  generalize Complex.I * (B 0 1 - B 1 0) / 2 = b2 at *
  generalize (B 0 0 - B 1 1) / 2 = b3 at *
  obtain ⟨x, hx⟩ : ∃ x, x = a1 * b1 + a2 * b2 + a3 * b3 := ⟨_, rfl⟩
  set z : ℂ := 2 * (C2 : ℂ) + Complex.I * S2 with hz
  have hE : (C2 : ℂ) * (2 * a0 * (2 * b0)) + Complex.I * S2 * (2 * (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3)) =
      (2 * z) * (a0 * b0) + (2 * Complex.I * S2) * x := by
    rw [hx, hz]; ring
  rw [hE]
  have hm2 : ‖z‖ ^ 2 = 1 + 3 * C2 ^ 2 := by
    rw [Complex.sq_norm, hz, Complex.normSq_apply]
    simp
    nlinarith
  have hSm : |S2| ≤ ‖z‖ := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg z, abs_nonneg S2, sq_abs S2]
  have hxn : ‖x‖ ≤ ‖a1‖ * ‖b1‖ + ‖a2‖ * ‖b2‖ + ‖a3‖ * ‖b3‖ := by
    rw [hx]
    calc ‖a1 * b1 + a2 * b2 + a3 * b3‖ ≤ ‖a1 * b1 + a2 * b2‖ + ‖a3 * b3‖ := norm_add_le _ _
      _ ≤ ‖a1 * b1‖ + ‖a2 * b2‖ + ‖a3 * b3‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by simp only [norm_mul]
  have hEn : ‖(2 * z) * (a0 * b0) + (2 * Complex.I * S2) * x‖ ≤
      2 * ‖z‖ * (‖a0‖ * ‖b0‖ + (‖a1‖ * ‖b1‖ + ‖a2‖ * ‖b2‖ + ‖a3‖ * ‖b3‖)) := by
    calc ‖(2 * z) * (a0 * b0) + (2 * Complex.I * S2) * x‖
        ≤ ‖(2 * z) * (a0 * b0)‖ + ‖(2 * Complex.I * S2) * x‖ := norm_add_le _ _
      _ = 2 * ‖z‖ * (‖a0‖ * ‖b0‖) + 2 * |S2| * ‖x‖ := by
        simp [norm_mul]
      _ ≤ _ := by nlinarith [norm_nonneg z, norm_nonneg a0, norm_nonneg b0, norm_nonneg x, abs_nonneg S2]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hEn 2
  rw [Complex.sq_norm] at hsq
  have hcs4 : (‖a0‖ * ‖b0‖ + (‖a1‖ * ‖b1‖ + ‖a2‖ * ‖b2‖ + ‖a3‖ * ‖b3‖)) ^ 2 ≤
      (‖a0‖ ^ 2 + ‖a1‖ ^ 2 + ‖a2‖ ^ 2 + ‖a3‖ ^ 2) * (‖b0‖ ^ 2 + ‖b1‖ ^ 2 + ‖b2‖ ^ 2 + ‖b3‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a0‖ * ‖b1‖ - ‖a1‖ * ‖b0‖), sq_nonneg (‖a0‖ * ‖b2‖ - ‖a2‖ * ‖b0‖),
      sq_nonneg (‖a0‖ * ‖b3‖ - ‖a3‖ * ‖b0‖), sq_nonneg (‖a1‖ * ‖b2‖ - ‖a2‖ * ‖b1‖),
      sq_nonneg (‖a1‖ * ‖b3‖ - ‖a3‖ * ‖b1‖), sq_nonneg (‖a2‖ * ‖b3‖ - ‖a3‖ * ‖b2‖)]
  simp only [Complex.sq_norm] at hcs4
  rw [mul_pow, mul_pow, hm2] at hsq
  have hm0 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  rw [hm2] at hm0
  nlinarith [mul_le_mul_of_nonneg_left hcs4 (show (0:ℝ) ≤ 1 + 3 * C2 ^ 2 by positivity)]

/-! ### Frame-sharing reductions and the bounds -/

theorem SU2_param {u : Op1} (h : SU2 u) :
    u 1 1 = conj (u 0 0) ∧ u 1 0 = -conj (u 0 1) ∧
      (u 0 0).re ^ 2 + (u 0 0).im ^ 2 + ((u 0 1).re ^ 2 + (u 0 1).im ^ 2) = 1 := by
  have a := SU2_adj h
  have h10 : u 1 0 = -conj (u 0 1) := by
    have e := congrFun (congrFun a 0) 1
    simp [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] at e
    have := congrArg conj e
    simp at this
    exact this.symm
  refine ⟨SU2_entry11 h, h10, ?_⟩
  have hd := h.2
  rw [Matrix.det_fin_two, SU2_entry11 h, h10] at hd
  have := congrArg Complex.re hd
  simp at this
  nlinarith

/-- The `SU(2)` bound `|2 tr(A B⁻¹) − tr A tr B⁻¹| ≤ 4` (Cauchy--Schwarz for the vector parts of
`A, B` viewed as unit quaternions). -/
theorem X_bound {A B : Op1} (hA : SU2 A) (hB : SU2 B) :
    Complex.normSq (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) ≤ 16 := by
  obtain ⟨hA11, hA10, hAn⟩ := SU2_param hA
  obtain ⟨hB11, hB10, hBn⟩ := SU2_param hB
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, hA11, hA10, hB11, hB10]
  rw [Complex.normSq_apply]
  simp
  generalize (A 0 0).re = a at *
  generalize (A 0 0).im = b at *
  generalize (A 0 1).re = c at *
  generalize (A 0 1).im = d at *
  generalize (B 0 0).re = e at *
  generalize (B 0 0).im = f at *
  generalize (B 0 1).re = g at *
  generalize (B 0 1).im = h at *
  have hcs : (b * f + c * g + d * h) ^ 2 ≤ (b ^ 2 + c ^ 2 + d ^ 2) * (f ^ 2 + g ^ 2 + h ^ 2) := by
    nlinarith [sq_nonneg (b * g - c * f), sq_nonneg (b * h - d * f), sq_nonneg (c * h - d * g)]
  have h1 : b ^ 2 + c ^ 2 + d ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have h2 : f ^ 2 + g ^ 2 + h ^ 2 ≤ 1 := by nlinarith [sq_nonneg e]
  have h3 : (b ^ 2 + c ^ 2 + d ^ 2) * (f ^ 2 + g ^ 2 + h ^ 2) ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg f, sq_nonneg g, sq_nonneg h]
  nlinarith

theorem normSq_ω3 : Complex.normSq ω3 = 1 := by
  have h := FormalResearch.FourQubitEntropy.omega_mul_conj
  rw [Complex.mul_conj] at h
  exact_mod_cast h

theorem det_mul_adj {u : Op1} (h : u.det = 1) : u * u.adjugate = 1 := by
  rw [Matrix.mul_adjugate, h]; simp

theorem det_adj_one {u : Op1} (h : u.det = 1) : u.adjugate.det = 1 := by
  rw [Matrix.det_adjugate]; simp [h]

theorem Z4_conj : Z4.map conj = r6 • (conj ω3 • Y1 + EE) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Z4, Y1, EE, eps, Matrix.kroneckerMap_apply, conj_r6] <;> ring

/-- `Θ M₄` is a singlet for the complexified group: `W^{⊗4} Θ M₄ = Θ M₄` for `det W = 1`. -/
theorem rot_const_ΘM4n (W : Op1) (hW : W.det = 1) : rot (fun _ => W) (Θ M4n) = Θ M4n := by
  rw [Θ_M4n, rot_ofMat]
  congr 1
  rw [Z4_conj]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    kron_sandwich_Y1, kron_sandwich_EE, hW]
  simp

/-- Right-multiplying all four frames by one `W ∈ SL(2,ℂ)` does not change the rotated state. -/
theorem rot_reduce (u : Fin 4 → Op1) (W : Op1) (hW : W.det = 1) :
    rot (fun i => u i * W) (Θ M4n) = rot u (Θ M4n) := by
  have h := rot_comp u (fun _ : Fin 4 => W) (Θ M4n)
  rw [rot_const_ΘM4n W hW] at h
  exact h.symm

theorem ov_reduce (u : Fin 4 → Op1) (W : Op1) (hW : W.det = 1) :
    ip M4n (rot (fun i => u i * W) (Θ M4n)) = ip M4n (rot u (Θ M4n)) := by
  rw [rot_reduce u W hW]

/-- Three spins in a block: the overlap vanishes, for any frames of determinant one. -/
theorem ov_M4_triple (u : Fin 4 → Op1) (hu : ∀ i, (u i).det = 1)
    (h : (u 0 = u 1 ∧ u 1 = u 2) ∨ (u 0 = u 1 ∧ u 1 = u 3) ∨ (u 0 = u 2 ∧ u 2 = u 3) ∨
      (u 1 = u 2 ∧ u 2 = u 3)) :
    ip M4n (rot u (Θ M4n)) = 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← ov_reduce u (u 0).adjugate (det_adj_one (hu 0))]
    have e : (fun i => u i * (u 0).adjugate) =
        ![(1 : Op1), (1 : Op1), (1 : Op1), u 3 * (u 0).adjugate] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hu 0), ← h2, ← h1]
    rw [e]; exact ov_M4_zero3 _
  · rw [← ov_reduce u (u 0).adjugate (det_adj_one (hu 0))]
    have e : (fun i => u i * (u 0).adjugate) =
        ![(1 : Op1), (1 : Op1), u 2 * (u 0).adjugate, (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hu 0), ← h2, ← h1]
    rw [e]; exact ov_M4_zero2 _
  · rw [← ov_reduce u (u 0).adjugate (det_adj_one (hu 0))]
    have e : (fun i => u i * (u 0).adjugate) =
        ![(1 : Op1), u 1 * (u 0).adjugate, (1 : Op1), (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hu 0), ← h2, ← h1]
    rw [e]; exact ov_M4_zero1 _
  · rw [← ov_reduce u (u 1).adjugate (det_adj_one (hu 1))]
    have e : (fun i => u i * (u 1).adjugate) =
        ![u 0 * (u 1).adjugate, (1 : Op1), (1 : Op1), (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hu 1), ← h2, ← h1]
    rw [e]; exact ov_M4_zero0 _

/-- Two spins in a block (`det = 1` frames): the overlap is a unit phase times `-(1/6)·X(A,B)`, and the
norm of the rotated state is `(‖A B⁻¹‖² + ‖A‖²‖B‖²)/6`, where `A, B` are the other two frames
right-multiplied by the inverse of the shared one (`SU(2)` if all frames are). -/
theorem M4_pair_data (u : Fin 4 → Op1) (hd : ∀ i, (u i).det = 1)
    (h : u 0 = u 1 ∨ u 0 = u 2 ∨ u 0 = u 3 ∨ u 1 = u 2 ∨ u 1 = u 3 ∨ u 2 = u 3) :
    ∃ (c : ℂ) (A B : Op1), Complex.normSq c = 1 ∧ ((∀ i, SU2 (u i)) → SU2 A ∧ SU2 B) ∧
      ip M4n (rot u (Θ M4n)) =
        c * (-(1 / 6 : ℂ)) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) ∧
      nsq (rot u (Θ M4n)) = (fro (A * B.adjugate) + fro A * fro B) / 6 := by
  have hc1 : Complex.normSq (conj ω3) = 1 := by rw [Complex.normSq_conj]; exact normSq_ω3
  have hc2 : Complex.normSq (conj ω3 ^ 2) = 1 := by rw [map_pow, hc1]; simp
  rcases h with h | h | h | h | h | h
  · refine ⟨1, u 2 * (u 0).adjugate, u 3 * (u 0).adjugate, (by simp),
      fun hu => ⟨SU2_mul (hu 2) (SU2_adj_su2 (hu 0)), SU2_mul (hu 3) (SU2_adj_su2 (hu 0))⟩, ?_⟩
    rw [← rot_reduce u (u 0).adjugate (det_adj_one (hd 0))]
    have e : (fun i => u i * (u 0).adjugate) =
        ![(1 : Op1), (1 : Op1), u 2 * (u 0).adjugate, u 3 * (u 0).adjugate] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hd 0), ← h]
    rw [e]
    exact ⟨by rw [ov_M4_23]; ring, nsq_M4_23 _ _⟩
  · refine ⟨conj ω3 ^ 2, u 1 * (u 0).adjugate, u 3 * (u 0).adjugate, hc2,
      fun hu => ⟨SU2_mul (hu 1) (SU2_adj_su2 (hu 0)), SU2_mul (hu 3) (SU2_adj_su2 (hu 0))⟩, ?_⟩
    rw [← rot_reduce u (u 0).adjugate (det_adj_one (hd 0))]
    have e : (fun i => u i * (u 0).adjugate) =
        ![(1 : Op1), u 1 * (u 0).adjugate, (1 : Op1), u 3 * (u 0).adjugate] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hd 0), ← h]
    rw [e]
    exact ⟨by rw [ov_M4_13]; ring, nsq_M4_13 _ _⟩
  · refine ⟨conj ω3, u 1 * (u 0).adjugate, u 2 * (u 0).adjugate, hc1,
      fun hu => ⟨SU2_mul (hu 1) (SU2_adj_su2 (hu 0)), SU2_mul (hu 2) (SU2_adj_su2 (hu 0))⟩, ?_⟩
    rw [← rot_reduce u (u 0).adjugate (det_adj_one (hd 0))]
    have e : (fun i => u i * (u 0).adjugate) =
        ![(1 : Op1), u 1 * (u 0).adjugate, u 2 * (u 0).adjugate, (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hd 0), ← h]
    rw [e]
    exact ⟨by rw [ov_M4_12]; ring, nsq_M4_12 _ _⟩
  · refine ⟨conj ω3, u 0 * (u 1).adjugate, u 3 * (u 1).adjugate, hc1,
      fun hu => ⟨SU2_mul (hu 0) (SU2_adj_su2 (hu 1)), SU2_mul (hu 3) (SU2_adj_su2 (hu 1))⟩, ?_⟩
    rw [← rot_reduce u (u 1).adjugate (det_adj_one (hd 1))]
    have e : (fun i => u i * (u 1).adjugate) =
        ![u 0 * (u 1).adjugate, (1 : Op1), (1 : Op1), u 3 * (u 1).adjugate] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hd 1), ← h]
    rw [e]
    exact ⟨by rw [ov_M4_03]; ring, nsq_M4_03 _ _⟩
  · refine ⟨conj ω3 ^ 2, u 0 * (u 1).adjugate, u 2 * (u 1).adjugate, hc2,
      fun hu => ⟨SU2_mul (hu 0) (SU2_adj_su2 (hu 1)), SU2_mul (hu 2) (SU2_adj_su2 (hu 1))⟩, ?_⟩
    rw [← rot_reduce u (u 1).adjugate (det_adj_one (hd 1))]
    have e : (fun i => u i * (u 1).adjugate) =
        ![u 0 * (u 1).adjugate, (1 : Op1), u 2 * (u 1).adjugate, (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hd 1), ← h]
    rw [e]
    exact ⟨by rw [ov_M4_02]; ring, nsq_M4_02 _ _⟩
  · refine ⟨1, u 0 * (u 2).adjugate, u 1 * (u 2).adjugate, (by simp),
      fun hu => ⟨SU2_mul (hu 0) (SU2_adj_su2 (hu 2)), SU2_mul (hu 1) (SU2_adj_su2 (hu 2))⟩, ?_⟩
    rw [← rot_reduce u (u 2).adjugate (det_adj_one (hd 2))]
    have e : (fun i => u i * (u 2).adjugate) =
        ![u 0 * (u 2).adjugate, u 1 * (u 2).adjugate, (1 : Op1), (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [det_mul_adj (hd 2), ← h]
    rw [e]
    exact ⟨by rw [ov_M4_01]; ring, nsq_M4_01 _ _⟩

/-- Two spins in a block: the overlap is a unit phase times `-(1/6)·X(A,B)` (`SU(2)` frames). -/
theorem ov_M4_pair (u : Fin 4 → Op1) (hu : ∀ i, SU2 (u i))
    (h : u 0 = u 1 ∨ u 0 = u 2 ∨ u 0 = u 3 ∨ u 1 = u 2 ∨ u 1 = u 3 ∨ u 2 = u 3) :
    ∃ (c : ℂ) (A B : Op1), SU2 A ∧ SU2 B ∧ Complex.normSq c = 1 ∧
      ip M4n (rot u (Θ M4n)) =
        c * (-(1 / 6 : ℂ)) * (2 * Matrix.trace (A * B.adjugate) - Matrix.trace A * Matrix.trace B.adjugate) := by
  obtain ⟨c, A, B, hc, hS, e, -⟩ := M4_pair_data u (fun i => (hu i).2) h
  exact ⟨c, A, B, (hS hu).1, (hS hu).2, hc, e⟩

theorem normSq_neg_sixth : Complex.normSq (-(1 / 6 : ℂ)) = 1 / 36 := by
  simp [Complex.normSq_apply]; norm_num

/-- One frame assignment in which two spins share a frame has overlap `|⟨M₄|uΘM₄⟩|² ≤ 4/9`. -/
theorem normSq_ov_M4_le (u : Fin 4 → Op1) (hu : ∀ i, SU2 (u i))
    (h : u 0 = u 1 ∨ u 0 = u 2 ∨ u 0 = u 3 ∨ u 1 = u 2 ∨ u 1 = u 3 ∨ u 2 = u 3) :
    Complex.normSq (ip M4n (rot u (Θ M4n))) ≤ 4 / 9 := by
  obtain ⟨c, A, B, hA, hB, hc, e⟩ := ov_M4_pair u hu h
  rw [e, Complex.normSq_mul, Complex.normSq_mul, hc, normSq_neg_sixth]
  have := X_bound hA hB
  nlinarith

/-- Some block contains at least three spins (the four triples; the common frame is among them). -/
def HasTriple {β : Type*} (g : Fin 4 → β) : Prop :=
  (g 0 = g 1 ∧ g 1 = g 2) ∨ (g 0 = g 1 ∧ g 1 = g 3) ∨ (g 0 = g 2 ∧ g 2 = g 3) ∨
    (g 1 = g 2 ∧ g 2 = g 3)

/-- The blocks are pairs and singletons with at least one pair: one pair is a whole block (nine
patterns). -/
def PairNoTriple {β : Type*} (g : Fin 4 → β) : Prop :=
  (g 0 = g 1 ∧ g 2 ≠ g 0 ∧ g 3 ≠ g 0) ∨ (g 0 = g 2 ∧ g 1 ≠ g 0 ∧ g 3 ≠ g 0) ∨
  (g 0 = g 3 ∧ g 1 ≠ g 0 ∧ g 2 ≠ g 0) ∨ (g 1 = g 2 ∧ g 0 ≠ g 1 ∧ g 3 ≠ g 1) ∨
  (g 1 = g 3 ∧ g 0 ≠ g 1 ∧ g 2 ≠ g 1) ∨ (g 2 = g 3 ∧ g 0 ≠ g 2 ∧ g 1 ≠ g 2)

variable {β : Type*}

theorem FKΘs_M4_le (g : Fin 4 → β)
    (h : g 0 = g 1 ∨ g 0 = g 2 ∨ g 0 = g 3 ∨ g 1 = g 2 ∨ g 1 = g 3 ∨ g 2 = g 3) :
    FKΘs g M4n ≤ 4 / 9 := by
  unfold FKΘs FKs
  refine csSup_le (shSet_nonempty g _ _) ?_
  rintro r ⟨v, hv, rfl⟩
  refine normSq_ov_M4_le _ (fun i => hv _) ?_
  rcases h with h | h | h | h | h | h <;> simp [h]

theorem X_px : 2 * Matrix.trace (px * px.adjugate) - Matrix.trace px * Matrix.trace px.adjugate = 4 := by
  simp [px, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.adjugate_fin_two]
  norm_num

theorem normSq_phase4 (c : ℂ) (hc : Complex.normSq c = 1) :
    Complex.normSq (-(c / 6 : ℂ) * 4) = 4 / 9 := by
  have e : -(c / 6 : ℂ) * 4 = c * (-(2 / 3 : ℂ)) := by ring
  rw [e, Complex.normSq_mul, hc]
  simp [Complex.normSq_apply]; norm_num

theorem le_FKΘs_M4 (g : Fin 4 → β) (h : PairNoTriple g) : 4 / 9 ≤ FKΘs g M4n := by
  classical
  have hc1 : Complex.normSq (conj ω3) = 1 := by rw [Complex.normSq_conj]; exact normSq_ω3
  have hc2 : Complex.normSq (conj ω3 ^ 2) = 1 := by rw [map_pow, hc1]; simp
  unfold FKΘs
  rcases h with ⟨h, h2, h3⟩ | ⟨h, h2, h3⟩ | ⟨h, h2, h3⟩ | ⟨h, h2, h3⟩ | ⟨h, h2, h3⟩ | ⟨h, h2, h3⟩
  · obtain ⟨v, hv, hvd⟩ : ∃ v : β → Op1, (∀ b, SU2 (v b)) ∧
        ∀ b, v b = if b = g 0 then 1 else px := by
      refine ⟨fun b => if b = g 0 then 1 else px, fun b => ?_, fun _ => rfl⟩
      beta_reduce
      split_ifs
      exacts [SU2_one, SU2_px]
    have e : (fun i => v (g i)) = ![(1 : Op1), (1 : Op1), px, px] := by
      funext i
      fin_cases i <;> simp [hvd, ← h, h2, h3]
    have h1 := le_FKs g M4n (Θ M4n) v hv
    rw [e, ov_M4_23, X_px, normSq_phase4 _ (by simp)] at h1
    exact h1
  · obtain ⟨v, hv, hvd⟩ : ∃ v : β → Op1, (∀ b, SU2 (v b)) ∧
        ∀ b, v b = if b = g 0 then 1 else px := by
      refine ⟨fun b => if b = g 0 then 1 else px, fun b => ?_, fun _ => rfl⟩
      beta_reduce
      split_ifs
      exacts [SU2_one, SU2_px]
    have e : (fun i => v (g i)) = ![(1 : Op1), px, (1 : Op1), px] := by
      funext i
      fin_cases i <;> simp [hvd, ← h, h2, h3]
    have h1 := le_FKs g M4n (Θ M4n) v hv
    rw [e, ov_M4_13, X_px, normSq_phase4 _ hc2] at h1
    exact h1
  · obtain ⟨v, hv, hvd⟩ : ∃ v : β → Op1, (∀ b, SU2 (v b)) ∧
        ∀ b, v b = if b = g 0 then 1 else px := by
      refine ⟨fun b => if b = g 0 then 1 else px, fun b => ?_, fun _ => rfl⟩
      beta_reduce
      split_ifs
      exacts [SU2_one, SU2_px]
    have e : (fun i => v (g i)) = ![(1 : Op1), px, px, (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [hvd, ← h, h2, h3]
    have h1 := le_FKs g M4n (Θ M4n) v hv
    rw [e, ov_M4_12, X_px, normSq_phase4 _ hc1] at h1
    exact h1
  · obtain ⟨v, hv, hvd⟩ : ∃ v : β → Op1, (∀ b, SU2 (v b)) ∧
        ∀ b, v b = if b = g 1 then 1 else px := by
      refine ⟨fun b => if b = g 1 then 1 else px, fun b => ?_, fun _ => rfl⟩
      beta_reduce
      split_ifs
      exacts [SU2_one, SU2_px]
    have e : (fun i => v (g i)) = ![px, (1 : Op1), (1 : Op1), px] := by
      funext i
      fin_cases i <;> simp [hvd, ← h, h2, h3]
    have h1 := le_FKs g M4n (Θ M4n) v hv
    rw [e, ov_M4_03, X_px, normSq_phase4 _ hc1] at h1
    exact h1
  · obtain ⟨v, hv, hvd⟩ : ∃ v : β → Op1, (∀ b, SU2 (v b)) ∧
        ∀ b, v b = if b = g 1 then 1 else px := by
      refine ⟨fun b => if b = g 1 then 1 else px, fun b => ?_, fun _ => rfl⟩
      beta_reduce
      split_ifs
      exacts [SU2_one, SU2_px]
    have e : (fun i => v (g i)) = ![px, (1 : Op1), px, (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [hvd, ← h, h2, h3]
    have h1 := le_FKs g M4n (Θ M4n) v hv
    rw [e, ov_M4_02, X_px, normSq_phase4 _ hc2] at h1
    exact h1
  · obtain ⟨v, hv, hvd⟩ : ∃ v : β → Op1, (∀ b, SU2 (v b)) ∧
        ∀ b, v b = if b = g 2 then 1 else px := by
      refine ⟨fun b => if b = g 2 then 1 else px, fun b => ?_, fun _ => rfl⟩
      beta_reduce
      split_ifs
      exacts [SU2_one, SU2_px]
    have e : (fun i => v (g i)) = ![px, px, (1 : Op1), (1 : Op1)] := by
      funext i
      fin_cases i <;> simp [hvd, ← h, h2, h3]
    have h1 := le_FKs g M4n (Θ M4n) v hv
    rw [e, ov_M4_01, X_px, normSq_phase4 _ (by simp)] at h1
    exact h1

/-- **Theorem `thm:m4sharing` (b)**, rotation overlap: pairs and singletons with at least one pair
(nine patterns): `F_K^π(M₄) = 4/9`.  Unconditional. -/
theorem FKΘs_M4_pair (g : Fin 4 → β) (h : PairNoTriple g) : FKΘs g M4n = 4 / 9 := by
  refine le_antisymm (FKΘs_M4_le g ?_) (le_FKΘs_M4 g h)
  rcases h with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> simp [h]

/-- **Theorem `thm:m4sharing` (b)**, chiral distance: `C_K^π(M₄) = log (9/4)`. -/
theorem CKs_M4_pair (g : Fin 4 → β) (h : PairNoTriple g) : CKs g M4n = Real.log (9 / 4) := by
  unfold CKs
  rw [FKΘs_M4_pair g h, ← Real.log_inv]
  norm_num

/-- **Theorem `thm:m4sharing` (a)**, rotation overlap: some block contains three spins (five patterns):
`F_K^π(M₄) = 0`. -/
theorem FKΘs_M4_triple (g : Fin 4 → β) (h : HasTriple g) : FKΘs g M4n = 0 := by
  unfold FKΘs FKs
  apply le_antisymm
  · refine csSup_le (shSet_nonempty g _ _) ?_
    rintro r ⟨v, hv, rfl⟩
    rw [ov_M4_triple _ (fun i => (hv _).2) (by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2])]
    simp
  · refine Real.sSup_nonneg ?_
    rintro r ⟨v, hv, rfl⟩
    exact Complex.normSq_nonneg _

/-- **Theorem `thm:m4sharing` (a)**, filters: `F_C^π(M₄) = 0` when some block contains three spins. -/
theorem FCΘs_M4_triple (g : Fin 4 → β) (h : HasTriple g) : FCΘs g M4n = 0 := by
  unfold FCΘs FCs
  apply le_antisymm
  · refine csSup_le (fiSet_nonempty g _ _) ?_
    rintro r ⟨v, hv, rfl⟩
    rw [ov_M4_triple _ (fun i => hv _) (by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2])]
    simp
  · refine Real.sSup_nonneg ?_
    rintro r ⟨v, hv, rfl⟩
    exact div_nonneg (Complex.normSq_nonneg _) (nsq_nonneg _)


/-! ### Filters: `F_C^π(M₄)` -/

theorem fro_nonneg (M : Op1) : 0 ≤ fro M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem fro_adj (B : Op1) : fro B.adjugate = fro B := by
  simp only [fro, Fin.sum_univ_two, Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Complex.normSq_neg]
  ring

theorem fro_one : fro (1 : Op1) = 2 := by
  simp [fro, Matrix.one_apply]

/-- `M₄` is a unit vector. -/
theorem nsq_M4n : nsq M4n = 1 := by
  have h := nsq_M4_23 (1 : Op1) 1
  have e : (![(1 : Op1), (1 : Op1), (1 : Op1), (1 : Op1)] : Fin 4 → Op1) = fun _ => 1 := by
    funext i; fin_cases i <;> rfl
  rw [e, rot_one, nsq_Θ] at h
  rw [h, Matrix.adjugate_one, Matrix.one_mul, fro_one]; norm_num

/-- The filter ratio of one frame assignment in which two spins share a frame is at most `4/9`. -/
theorem ratio_M4_le (u : Fin 4 → Op1) (hd : ∀ i, (u i).det = 1)
    (h : u 0 = u 1 ∨ u 0 = u 2 ∨ u 0 = u 3 ∨ u 1 = u 2 ∨ u 1 = u 3 ∨ u 2 = u 3) :
    Complex.normSq (ip M4n (rot u (Θ M4n))) / nsq (rot u (Θ M4n)) ≤ 4 / 9 := by
  obtain ⟨c, A, B, hc, -, e, hn⟩ := M4_pair_data u hd h
  have hN : 0 ≤ (fro (A * B.adjugate) + fro A * fro B) / 6 := by
    have := fro_nonneg (A * B.adjugate); have := fro_nonneg A; have := fro_nonneg B; positivity
  rw [e, hn]
  rcases hN.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; norm_num
  · rw [div_le_iff₀ hpos, Complex.normSq_mul, Complex.normSq_mul, hc, normSq_neg_sixth]
    have := key_FC A B.adjugate
    rw [fro_adj] at this
    nlinarith

theorem FCΘs_M4_le (g : Fin 4 → β)
    (h : g 0 = g 1 ∨ g 0 = g 2 ∨ g 0 = g 3 ∨ g 1 = g 2 ∨ g 1 = g 3 ∨ g 2 = g 3) :
    FCΘs g M4n ≤ 4 / 9 := by
  unfold FCΘs FCs
  refine csSup_le (fiSet_nonempty g _ _) ?_
  rintro r ⟨v, hv, rfl⟩
  refine ratio_M4_le _ (fun i => hv _) ?_
  rcases h with h | h | h | h | h | h <;> simp [h]

/-- **Theorem `thm:m4sharing` (b)**, filters: `F_C^π(M₄) = 4/9` for pairs and singletons with at
least one pair. -/
theorem FCΘs_M4_pair (g : Fin 4 → β) (h : PairNoTriple g) : FCΘs g M4n = 4 / 9 := by
  have hpair : g 0 = g 1 ∨ g 0 = g 2 ∨ g 0 = g 3 ∨ g 1 = g 2 ∨ g 1 = g 3 ∨ g 2 = g 3 := by
    rcases h with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> simp [h]
  refine le_antisymm (FCΘs_M4_le g hpair) ?_
  rw [← FKΘs_M4_pair g h]
  exact FKs_le_FCs g M4n (Θ M4n) (by rw [nsq_Θ, nsq_M4n])

end M4

/-! ## Part 5. Filters for the exchange gates (`thm:exchangesharing`, filter part) -/

section ExchangeFilters

variable {β : Type*}

theorem fro_eq_trace (M : Op1) : ((fro M : ℝ) : ℂ) = Matrix.trace (Mᴴ * M) := by
  simp [fro, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]
  ring

theorem trace_cyc4 (p q r s : Op1) : Matrix.trace (p * q * r * s) = Matrix.trace (s * p * q * r) := by
  rw [Matrix.trace_mul_comm (p * q * r) s]
  simp only [Matrix.mul_assoc]

theorem trace_GK (w c : Op1) :
    Matrix.trace (wᴴ * w * (c * cᴴ)) = Matrix.trace ((w * c)ᴴ * (w * c)) := by
  rw [Matrix.conjTranspose_mul, Matrix.trace_mul_comm (cᴴ * wᴴ) (w * c)]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm wᴴ]
  simp only [Matrix.mul_assoc]

/-- The squared norm of a rotated gate probe, as a trace. -/
theorem nsq_rot_psiEx_cast (θ : ℝ) (u : Fin 4 → Op1) :
    ((nsq (rot u (psiEx (-θ))) : ℝ) : ℂ) =
      (1 / 4 : ℂ) * Matrix.trace (Ug (Real.cos θ) (-(Complex.I * Real.sin θ)) *
        (((((u 0)ᴴ * u 0) ⊗ₖ ((u 1)ᴴ * u 1))) * Ug (Real.cos θ) (Complex.I * Real.sin θ) *
          ((((u 2).adjugate * (u 2).adjugateᴴ) ⊗ₖ ((u 3).adjugate * (u 3).adjugateᴴ))))) := by
  rw [← ip_self]
  unfold psiEx
  rw [rot_choi, ip_choi]
  congr 1
  have hV : (Ug (Real.cos θ) (Complex.I * Real.sin θ))ᴴ =
      Ug (Real.cos θ) (-(Complex.I * Real.sin θ)) := by
    rw [Ug_conjT, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rw [Uex_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hV,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker]
  have e1 : ((u 0)ᴴ ⊗ₖ (u 1)ᴴ) * ((u 0 ⊗ₖ u 1)) = ((u 0)ᴴ * u 0) ⊗ₖ ((u 1)ᴴ * u 1) := by
    rw [← Matrix.mul_kronecker_mul]
  have e2 : ((u 2).adjugate ⊗ₖ (u 3).adjugate) * ((u 2).adjugateᴴ ⊗ₖ (u 3).adjugateᴴ) =
      ((u 2).adjugate * (u 2).adjugateᴴ) ⊗ₖ ((u 3).adjugate * (u 3).adjugateᴴ) := by
    rw [← Matrix.mul_kronecker_mul]
  rw [← e1, ← e2]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm ((u 2).adjugateᴴ ⊗ₖ (u 3).adjugateᴴ)]
  simp only [Matrix.mul_assoc]

/-- Case `u₀ = u₁`: the norm of the rotated probe is `‖A'‖²‖B'‖²/4`,
`A' = u₀ u₂⁻¹`, `B' = u₀ u₃⁻¹`. -/
theorem nsq_case1 (θ : ℝ) (u : Fin 4 → Op1) (h : u 0 = u 1) :
    nsq (rot u (psiEx (-θ))) = fro (u 0 * (u 2).adjugate) * fro (u 0 * (u 3).adjugate) / 4 := by
  apply Complex.ofReal_injective
  rw [nsq_rot_psiEx_cast, ← h, trace_gate, trace_cyc4 ((u 2).adjugate * (u 2).adjugateᴴ)]
  rw [Complex.ofReal_div, Complex.ofReal_mul, fro_eq_trace, fro_eq_trace,
    ← trace_GK (u 0) (u 2).adjugate, ← trace_GK (u 0) (u 3).adjugate]
  have hcs := Real.cos_sq_add_sin_sq θ
  generalize Real.cos θ = c at *
  generalize Real.sin θ = s at *
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  generalize Matrix.trace ((u 0)ᴴ * u 0 * ((u 2).adjugate * (u 2).adjugateᴴ)) = T1
  generalize Matrix.trace ((u 0)ᴴ * u 0 * ((u 3).adjugate * (u 3).adjugateᴴ)) = T2
  generalize Matrix.trace ((u 0)ᴴ * u 0 * ((u 2).adjugate * (u 2).adjugateᴴ) * ((u 0)ᴴ * u 0) *
    ((u 3).adjugate * (u 3).adjugateᴴ)) = X
  push_cast
  linear_combination (T1 * T2 / 4) * hcs' - (T1 * T2 / 4) * (s : ℂ) ^ 2 * Complex.I_sq

/-- Case `u₂ = u₃`: the norm of the rotated probe is `‖A'‖²‖B'‖²/4`,
`A' = u₀ u₂⁻¹`, `B' = u₁ u₂⁻¹`. -/
theorem nsq_case2 (θ : ℝ) (u : Fin 4 → Op1) (h : u 2 = u 3) :
    nsq (rot u (psiEx (-θ))) = fro (u 0 * (u 2).adjugate) * fro (u 1 * (u 2).adjugate) / 4 := by
  apply Complex.ofReal_injective
  rw [nsq_rot_psiEx_cast, ← h, trace_gate,
    trace_cyc4 ((u 0)ᴴ * u 0) ((u 2).adjugate * (u 2).adjugateᴴ) ((u 1)ᴴ * u 1)]
  rw [Complex.ofReal_div, Complex.ofReal_mul, fro_eq_trace, fro_eq_trace,
    ← trace_GK (u 0) (u 2).adjugate, ← trace_GK (u 1) (u 2).adjugate]
  have hcs := Real.cos_sq_add_sin_sq θ
  generalize Real.cos θ = c at *
  generalize Real.sin θ = s at *
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  generalize Matrix.trace ((u 0)ᴴ * u 0 * ((u 2).adjugate * (u 2).adjugateᴴ)) = T1
  generalize Matrix.trace ((u 1)ᴴ * u 1 * ((u 2).adjugate * (u 2).adjugateᴴ)) = T2
  generalize Matrix.trace ((u 2).adjugate * (u 2).adjugateᴴ * ((u 0)ᴴ * u 0) *
    ((u 2).adjugate * (u 2).adjugateᴴ) * ((u 1)ᴴ * u 1)) = X
  push_cast
  linear_combination (T1 * T2 / 4) * hcs' - (T1 * T2 / 4) * (s : ℂ) ^ 2 * Complex.I_sq

/-- Case `u₀ = u₁`: the overlap is `¼[cos 2θ tr A' tr B' + i sin 2θ tr(A'B')]`. -/
theorem ov_case1 (θ : ℝ) (u : Fin 4 → Op1) (h : u 0 = u 1) :
    ip (psiEx θ) (rot u (psiEx (-θ))) =
      (1 / 4 : ℂ) * ((Real.cos (2 * θ) : ℂ) *
        (Matrix.trace (u 0 * (u 2).adjugate) * Matrix.trace (u 0 * (u 3).adjugate)) +
        Complex.I * (Real.sin (2 * θ) : ℂ) *
          Matrix.trace (u 0 * (u 2).adjugate * (u 0 * (u 3).adjugate))) := by
  have t1 : Matrix.trace ((u 2).adjugate * u 0 * (u 3).adjugate * u 0) =
      Matrix.trace (u 0 * (u 2).adjugate * u 0 * (u 3).adjugate) :=
    trace_cyc4 ((u 2).adjugate) (u 0) ((u 3).adjugate) (u 0)
  rw [ov_gate, ← h, t1]
  simp only [Matrix.mul_assoc]
  rw [Real.cos_two_mul', Real.sin_two_mul]
  generalize Real.cos θ = c
  generalize Real.sin θ = s
  push_cast
  linear_combination ((1 / 4 : ℂ) * (s : ℂ) ^ 2 *
    (Matrix.trace (u 0 * (u 2).adjugate) * Matrix.trace (u 0 * (u 3).adjugate))) * Complex.I_sq

/-- Case `u₂ = u₃`: the overlap is `¼[cos 2θ tr A' tr B' + i sin 2θ tr(A'B')]`. -/
theorem ov_case2 (θ : ℝ) (u : Fin 4 → Op1) (h : u 2 = u 3) :
    ip (psiEx θ) (rot u (psiEx (-θ))) =
      (1 / 4 : ℂ) * ((Real.cos (2 * θ) : ℂ) *
        (Matrix.trace (u 0 * (u 2).adjugate) * Matrix.trace (u 1 * (u 2).adjugate)) +
        Complex.I * (Real.sin (2 * θ) : ℂ) *
          Matrix.trace (u 0 * (u 2).adjugate * (u 1 * (u 2).adjugate))) := by
  have t2 : Matrix.trace ((u 2).adjugate * u 0 * (u 2).adjugate * u 1) =
      Matrix.trace (u 0 * (u 2).adjugate * u 1 * (u 2).adjugate) :=
    (trace_cyc4 (u 0) ((u 2).adjugate) (u 1) ((u 2).adjugate)).symm
  rw [ov_gate, ← h, t2]
  simp only [Matrix.mul_assoc]
  rw [Real.cos_two_mul', Real.sin_two_mul]
  generalize Real.cos θ = c
  generalize Real.sin θ = s
  push_cast
  linear_combination ((1 / 4 : ℂ) * (s : ℂ) ^ 2 *
    (Matrix.trace (u 0 * (u 2).adjugate) * Matrix.trace (u 1 * (u 2).adjugate))) * Complex.I_sq

/-- The filter ratio of one frame assignment with `u₀ = u₁` or `u₂ = u₃` is at most `κ`. -/
theorem ratio_exch_le (θ : ℝ) (u : Fin 4 → Op1) (h : u 0 = u 1 ∨ u 2 = u 3) :
    Complex.normSq (ip (psiEx θ) (rot u (psiEx (-θ)))) / nsq (rot u (psiEx (-θ))) ≤ kappa θ := by
  have hcs := Real.cos_sq_add_sin_sq (2 * θ)
  obtain ⟨A, B, hov, hn⟩ : ∃ A B : Op1,
      ip (psiEx θ) (rot u (psiEx (-θ))) = (1 / 4 : ℂ) * ((Real.cos (2 * θ) : ℂ) *
        (Matrix.trace A * Matrix.trace B) + Complex.I * (Real.sin (2 * θ) : ℂ) * Matrix.trace (A * B)) ∧
      nsq (rot u (psiEx (-θ))) = fro A * fro B / 4 := by
    rcases h with h | h
    · exact ⟨_, _, ov_case1 θ u h, nsq_case1 θ u h⟩
    · exact ⟨_, _, ov_case2 θ u h, nsq_case2 θ u h⟩
  have hN : 0 ≤ fro A * fro B / 4 := by
    have := fro_nonneg A; have := fro_nonneg B; positivity
  have hE := exch_ineq (Real.cos (2 * θ)) (Real.sin (2 * θ)) hcs A B
  rw [hov, hn]
  rcases hN.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact (kappa_pos θ).le
  · rw [div_le_iff₀ hpos, Complex.normSq_mul]
    have h16 : Complex.normSq (1 / 4 : ℂ) = 1 / 16 := by
      simp [Complex.normSq_apply]; norm_num
    rw [h16]
    have hk : kappa θ = (1 + 3 * Real.cos (2 * θ) ^ 2) / 4 := rfl
    rw [hk]
    nlinarith

/-- **Theorem `thm:exchangesharing` (i)**, filter upper bound: `F_C^π ≤ κ` if spins `1,2` or spins
`3,4` share a frame. -/
theorem FCΘs_le_kappa (g : Fin 4 → β) (h : g 0 = g 1 ∨ g 2 = g 3) (θ : ℝ) :
    FCΘs g (psiEx θ) ≤ kappa θ := by
  unfold FCΘs FCs
  rw [Θ_psiEx]
  refine csSup_le (fiSet_nonempty g _ _) ?_
  rintro r ⟨v, hv, rfl⟩
  refine ratio_exch_le θ _ ?_
  rcases h with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h])

/-- **Theorem `thm:exchangesharing` (i)**, filters: `F_C^π(ψ_{U_θ}) = κ(θ)`. -/
theorem FCΘs_exchange_i (g : Fin 4 → β) (h : g 0 = g 1 ∨ g 2 = g 3) (θ : ℝ) :
    FCΘs g (psiEx θ) = kappa θ := by
  refine le_antisymm (FCΘs_le_kappa g h θ) ?_
  rw [← FKΘs_exchange_i g h θ]
  exact FKs_le_FCs g (psiEx θ) (Θ (psiEx θ)) (by rw [nsq_Θ, nsq_psiEx])

/-- Independent-frame exchange law (filter part), recalled (R8): `F_C^{1|2|3|4}(ψ_{U_θ}) ≤ cos² θ`.
An explicit hypothesis, as `ExchangeIndepBound`. -/
def ExchangeIndepBoundC (θ : ℝ) : Prop := FCΘs (id : Fin 4 → Fin 4) (psiEx θ) ≤ Real.cos θ ^ 2

/-- **Theorem `thm:exchangesharing` (ii)**, filters, assuming the independent-frame filter bound:
`F_C^π = cos² θ` for the four patterns inside `{13|24}`. -/
theorem FCΘs_exchange_ii (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ)
    (hR : ExchangeIndepBoundC θ) : FCΘs g (psiEx θ) = Real.cos θ ^ 2 := by
  refine le_antisymm ?_ ?_
  · exact (FCs_mono (id_refines g) _ _).trans hR
  · exact (cos_sq_le_FKΘs g h θ).trans
      (FKs_le_FCs g (psiEx θ) (Θ (psiEx θ)) (by rw [nsq_Θ, nsq_psiEx]))

/-- **Theorem `thm:exchangesharing` (iii)**, filters, assuming the independent-frame filter bound:
`max(sin²θ, κ) ≤ F_C^π ≤ cos²θ` for the three cross patterns. -/
theorem FCΘs_exchange_iii (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ)
    (hR : ExchangeIndepBoundC θ) :
    max (Real.sin θ ^ 2) (kappa θ) ≤ FCΘs g (psiEx θ) ∧ FCΘs g (psiEx θ) ≤ Real.cos θ ^ 2 := by
  have hle : FKΘs g (psiEx θ) ≤ FCΘs g (psiEx θ) :=
    FKs_le_FCs g (psiEx θ) (Θ (psiEx θ)) (by rw [nsq_Θ, nsq_psiEx])
  exact ⟨((max_le (sin_sq_le_FKΘs g h θ) (kappa_le_FKΘs g θ)).trans hle),
    (FCs_mono (id_refines g) _ _).trans hR⟩

end ExchangeFilters


end FormalResearch.FrameFree.Sharing
