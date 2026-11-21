module

public import FormalResearch.JacobiEigenvectors.Engine.Defect
public import FormalResearch.JacobiEigenvectors.Engine.CorrectorOrder

/-!
# Paper J engine, L1.2 (part 2): the ansatz, its defect pieces and the three structural facts (i)--(iii)

Source: Paper J, `engine.tex` Section 2, `thm:eng-corr` and its proof in `app_engine.tex` ("Proof of Theorem
`thm:eng-corr`": the facts (i) "`L_A` is even and kills the leading order", (ii) "odd bracket", (iii) "even flux").
Namespace `FormalResearch.JacobiEigenvectors.Engine`.  Builds on `Defect` (`defectRow`, `Fcas`, `defectRow_parity`, `Fcas_even`,
`green_identity`) and `CorrectorOrder` (uniform orders, `PApprox`, the parity lift).

## Statements formalised
* The ansatz of the paper: `Aans g k = Σ_{i<k} h^{2i} g_i` (with `g_i = g_{2i}`), `Bans b l = Σ_{i<l} h^{2i} b_{i+1}`
  (with `b_i = B_{2i-1}`); `vrow (Aans g k) (Bans b l)` is `(A^{[m]}, h B^{[m]})` for `m = 2k - 1` (`l = k - 1`) and `m = 2k` (`l = k`).
* `SymbolExp N pp qq Π₊ Π₋`: **the analytic input of `thm:eng-corr`** (see below), the uniform order-`N` Taylor expansions in
  `h` of the finitely many composite symbol functions that occur in the defect and in `F_cas`.
* `lA g` and `lB b`: the `𝔄`-components of the defect of the single-term vectors `(g, 0)` and `(0, h b)`; `lA` is the operator `L_A`
  of the proof (`h`-even, vanishing at `h = 0` by (eq:eng-langer)), `lB` the operator `h^{-1} L_B[h·]`.
* (i) `lA_UO2`: `L_A[g] = O(h²)` for `g ∈ BSmooth 2` (Langer condition (eq:eng-langer) + parity).
* (ii) `lB_UO3`: `lB b - h 𝒯[b] = O(h³)` for `b ∈ BSmooth 3`, with the transport operator
  `𝒯[b] = -(2 M₀ b' + M₀' b)`, `M₀ = P₀ Π₋(·,0)₂₁ = Ω₀² V₀` (eq:eng-T, eq:eng-omega).
* (iii) `dFA_UO1`, `dFB_UO`: the change of `F_cas` when `h^{2k} g` is added to `A` (resp. `h^{2k} b` to `B`): `ΔF_A = h^{2k}·2V₀ g₀ g + O(h^{2k+2})` and
  `ΔF_B = O(h^{2k+1})` (before the parity upgrade, done in `Corrector`).
* `defectRow_add_A/B`: exact additivity of the defect in the ansatz; `defect_remainder`: the `h^{2K+2}` remainders of
  (eq:eng-factor) enter as `O(h^{2K+2})`.

## What `SymbolExp` assumes, and why it is a fair hypothesis
The paper assumes `P_{2i}, Q_{2i} ∈ C^r(I_u)` and `Π_± ∈ C^r(I_u × (-h₀,h₀))` with `r` large.  The proof of `thm:eng-corr` uses only the
*Taylor expansions in `h`, with bounded coefficients and uniform `O(h^N)` remainder, of the finitely many composite functions*
`(u,h) ↦ P_h(u ± h/2) Π_±(u,h)_{ij}`, `Q_h(u)` and `(s,h) ↦ P_h(s) Π_-(s + h/2, h)_{ij}`.  `SymbolExp N` states exactly that
these have `PApprox N` expansions (together with the boundedness of `Π_±`).  It does **not** prescribe any coefficient, and
the conclusions that matter (Langer, parity, the transport operator) are derived from the exact identities of
`SymplecticLadder` plus these expansions.  Deriving `SymbolExp` from `C^r` regularity of the primitive data is bookkeeping
(multivariate Taylor on a joint domain) and is not done here.

## Differences from the paper
* Uniformity over all `u ∈ ℝ` (see `CorrectorOrder`).
* Bond nondegeneracy: the exact identities `Π₊(u,h) = adj Π₋(u+h,h)` (used by `lB_UO3`, `Fcas_even`, `green_identity`) need
  `𝒟²(s,h) = d2 s h ≠ 0` (the paper's hypothesis, with the real function `d2 = 𝒟²`); the paper's proof uses them silently at every bond.  Here: `∃ δ_D > 0, ∀ s, 0 < |h| < δ_D → d2 s h ≠ 0`.
  (At a hard-edge bond `𝒟² = 0` this fails; the all-order bound is then formalised for interior bonds only.)
* The parity of `M(s,h) = P_h(s) Π₋(s+h/2,h)₂₁` (paper: "`M` is even in `h`") is derived from `Π₊ = adj Π₋(·+h)` and (SM3).
-/

@[expose] public section

noncomputable section

open Finset

namespace FormalResearch.JacobiEigenvectors.Engine

/-! ### The ansatz -/

/-- `A(u,h²) = Σ_{i<k} h^{2i} g_{2i}(u)`. -/
def Aans (g : ℕ → ℝ → ℝ) (k : ℕ) (u h : ℝ) : ℝ := ∑ i ∈ range k, h ^ (2 * i) * g i u

/-- `B(u,h²) = Σ_{i=1}^{l} h^{2i-2} B_{2i-1}(u)`, stored as `b (i+1) = B_{2i+1}`. -/
def Bans (b : ℕ → ℝ → ℝ) (l : ℕ) (u h : ℝ) : ℝ := ∑ i ∈ range l, h ^ (2 * i) * b (i + 1) u

lemma Aans_succ (g : ℕ → ℝ → ℝ) (k : ℕ) (u h : ℝ) : Aans g (k + 1) u h = Aans g k u h + h ^ (2 * k) * g k u := by
  simp [Aans, Finset.sum_range_succ]

lemma Bans_succ (b : ℕ → ℝ → ℝ) (l : ℕ) (u h : ℝ) :
    Bans b (l + 1) u h = Bans b l u h + h ^ (2 * l) * b (l + 1) u := by
  simp [Bans, Finset.sum_range_succ]

lemma Aans_even (g : ℕ → ℝ → ℝ) (k : ℕ) (u h : ℝ) : Aans g k u (-h) = Aans g k u h := by
  simp [Aans, pow_mul]

lemma Bans_even (b : ℕ → ℝ → ℝ) (l : ℕ) (u h : ℝ) : Bans b l u (-h) = Bans b l u h := by
  simp [Bans, pow_mul]

lemma Aans_zero_h (g : ℕ → ℝ → ℝ) {k : ℕ} (hk : 1 ≤ k) (u : ℝ) : Aans g k u 0 = g 0 u := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [Aans, Finset.sum_range_succ', zero_pow]

lemma Bans_zero_h (b : ℕ → ℝ → ℝ) (l : ℕ) (u : ℝ) : Bans b l u 0 = if l = 0 then 0 else b 1 u := by
  rcases l with _ | l
  · simp [Bans]
  · simp [Bans, Finset.sum_range_succ', zero_pow]

lemma Aans_papprox {N k : ℕ} {g : ℕ → ℝ → ℝ} (hg : ∀ i < k, BSmooth N (g i)) (c : ℝ) :
    PApprox N (fun u h => Aans g k (u + c * h) h) := by
  refine PApprox.sum (range k) fun i hi => ?_
  exact PApprox.hpow_mul _ (BSmooth.papprox_shift (hg i (Finset.mem_range.mp hi)) c)

lemma Bans_papprox {N l : ℕ} {b : ℕ → ℝ → ℝ} (hb : ∀ i, 1 ≤ i → i ≤ l → BSmooth N (b i)) (c : ℝ) :
    PApprox N (fun u h => Bans b l (u + c * h) h) := by
  refine PApprox.sum (range l) fun i hi => ?_
  exact PApprox.hpow_mul _ (BSmooth.papprox_shift (hb (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)) c)

/-! ### Additivity and explicit components of the defect -/

section Defect

variable (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2)

lemma defectRow_add_B (AA BB BB' : ℝ → ℝ → ℝ) (u h : ℝ) (k : Fin 2) :
    defectRow pp qq AA (fun u h => BB u h + BB' u h) PiP PiM u h k =
      defectRow pp qq AA BB PiP PiM u h k + defectRow pp qq (fun _ _ => 0) BB' PiP PiM u h k := by
  fin_cases k <;> simp [defectRow, vrow, rowMul] <;> ring

lemma defectRow_add_A (AA AA' BB : ℝ → ℝ → ℝ) (u h : ℝ) (k : Fin 2) :
    defectRow pp qq (fun u h => AA u h + AA' u h) BB PiP PiM u h k =
      defectRow pp qq AA BB PiP PiM u h k + defectRow pp qq AA' (fun _ _ => 0) PiP PiM u h k := by
  fin_cases k <;> simp [defectRow, vrow, rowMul] <;> ring

lemma defectRow_zero_eq (AA BB : ℝ → ℝ → ℝ) (u h : ℝ) :
    defectRow pp qq AA BB PiP PiM u h 0 =
      pp (u + h / 2) h * (AA (u + h) h * PiP u h 0 0 + h * BB (u + h) h * PiP u h 1 0)
      + pp (u - h / 2) h * (AA (u - h) h * PiM u h 0 0 + h * BB (u - h) h * PiM u h 1 0)
      - qq u h * AA u h := by
  simp [defectRow, vrow, rowMul]

lemma defectRow_one_eq (AA BB : ℝ → ℝ → ℝ) (u h : ℝ) :
    defectRow pp qq AA BB PiP PiM u h 1 =
      pp (u + h / 2) h * (AA (u + h) h * PiP u h 0 1 + h * BB (u + h) h * PiP u h 1 1)
      + pp (u - h / 2) h * (AA (u - h) h * PiM u h 0 1 + h * BB (u - h) h * PiM u h 1 1)
      - qq u h * (h * BB u h) := by
  simp [defectRow, vrow, rowMul]

/-- The `𝔄`-component of the defect of `(h^j g, 0)`, with `h^j` removed: the operator `L_A[g]`. -/
def lA (g : ℝ → ℝ) (u h : ℝ) : ℝ :=
  pp (u + h / 2) h * PiP u h 0 0 * g (u + h) + pp (u - h / 2) h * PiM u h 0 0 * g (u - h) - qq u h * g u

/-- The `𝔄`-component of the defect of `(0, h^{j+1} b)`, with `h^{j+1}` removed: `L_B[h b] = h · lB b`. -/
def lB (b : ℝ → ℝ) (u h : ℝ) : ℝ :=
  pp (u + h / 2) h * PiP u h 1 0 * b (u + h) + pp (u - h / 2) h * PiM u h 1 0 * b (u - h)

lemma defect_zero_A (j : ℕ) (g : ℝ → ℝ) (u h : ℝ) :
    defectRow pp qq (fun u h => h ^ j * g u) (fun _ _ => 0) PiP PiM u h 0 = h ^ j * lA pp qq PiP PiM g u h := by
  rw [defectRow_zero_eq]; simp only [lA]; ring

lemma defect_zero_B (j : ℕ) (b : ℝ → ℝ) (u h : ℝ) :
    defectRow pp qq (fun _ _ => 0) (fun u h => h ^ j * b u) PiP PiM u h 0 = h ^ (j + 1) * lB pp PiP PiM b u h := by
  rw [defectRow_zero_eq]; simp only [lB]; ring

end Defect

/-! ### The analytic input -/

/-- **The analytic input of `thm:eng-corr`** (see the module docstring): uniform order-`N` Taylor expansions in `h` of the
composite symbol functions, and boundedness of the propagators. -/
structure SymbolExp (N : ℕ) (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) : Prop where
  /-- `(u,h) ↦ P_h(u + h/2) Π₊(u,h)_{ij}`. -/
  sP : ∀ i j, PApprox N (fun u h => pp (u + h / 2) h * PiP u h i j)
  /-- `(u,h) ↦ P_h(u - h/2) Π₋(u,h)_{ij}`. -/
  sM : ∀ i j, PApprox N (fun u h => pp (u - h / 2) h * PiM u h i j)
  /-- `(u,h) ↦ 𝒬_h(u)`. -/
  qe : PApprox N qq
  /-- `(s,h) ↦ P_h(s) Π₋(s + h/2, h)_{ij}` (the coefficients of `F_cas`). -/
  cM : ∀ i j, PApprox N (fun s h => pp s h * PiM (s + h / 2) h i j)
  bddP : ∀ i j, UO 0 (fun u h => PiP u h i j)
  bddM : ∀ i j, UO 0 (fun u h => PiM u h i j)

/-- The coefficient `M(s,h) = P_h(s) Π₋(s+h/2,h)₂₁` of the finite-difference form of `L_B` (eq:app-LB). -/
def Mfun (pp : ℝ → ℝ → ℝ) (PiM : ℝ → ℝ → M2) (s h : ℝ) : ℝ := pp s h * PiM (s + h / 2) h 1 0

/-- `M₀(s) = P₀(s) Π₋(s,0)₂₁ = Ω₀² V₀` (eq:eng-omega). -/
def M0fun (pp : ℝ → ℝ → ℝ) (PiM : ℝ → ℝ → M2) (s : ℝ) : ℝ := pp s 0 * PiM s 0 1 0

/-- The transport operator `𝒯[b] = -(2 Ω₀²V₀ b' + (Ω₀²V₀)' b)` of (eq:eng-T), with `M₀ = Ω₀²V₀`. -/
def transportOp (M0 b : ℝ → ℝ) (u : ℝ) : ℝ := -(2 * M0 u * deriv b u + deriv M0 u * b u)

/-- The signed `V₀(s) = P₀(s) Π₋(s,0)₁₂` of the paper (`Fcas_zero`). -/
def V0fun (pp : ℝ → ℝ → ℝ) (PiM : ℝ → ℝ → M2) (s : ℝ) : ℝ := pp s 0 * PiM s 0 0 1

lemma UO.shift_half {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) : UO n (fun u h => f (u + h / 2) h) :=
  (hf.shift (1 / 2)).congr fun u h => by simp only [one_div]; ring_nf

lemma UO.shift_neg_half {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) : UO n (fun u h => f (u - h / 2) h) :=
  (hf.shift (-1 / 2)).congr fun u h => by ring_nf

lemma UO.shift_one {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) : UO n (fun u h => f (u + h) h) :=
  (hf.shift 1).congr fun u h => by ring_nf

lemma UO.shift_neg_one {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) : UO n (fun u h => f (u - h) h) :=
  (hf.shift (-1)).congr fun u h => by ring_nf

/-! ### (i) `L_A` kills the leading order -/

section Claims

variable {γ : ℝ} {dd d2 pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}

lemma lA_even_of_par {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg) (hP : ∀ s h, pp s (-h) = pp s h)
    (hQ : ∀ u h, qq u (-h) = qq u h) (g : ℝ → ℝ) (u h : ℝ) :
    lA pp qq PiP PiM g u (-h) = lA pp qq PiP PiM g u h := by
  obtain ⟨p00, p01, p10, p11, m00, m01, m10, m11⟩ := par_Pi_entries_of_par hpar u h
  have e1 : u + -h / 2 = u - h / 2 := by ring
  have e2 : u - -h / 2 = u + h / 2 := by ring
  have e3 : u + -h = u - h := by ring
  have e4 : u - -h = u + h := by ring
  simp only [lA, e1, e2, e3, e4, hP, hQ, p00, m00]
  ring

lemma lA_even (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (hP : ∀ s h, pp s (-h) = pp s h)
    (hQ : ∀ u h, qq u (-h) = qq u h) (g : ℝ → ℝ) (u h : ℝ) :
    lA pp qq PiP PiM g u (-h) = lA pp qq PiP PiM g u h :=
  lA_even_of_par L.par_Pi hP hQ g u h

lemma lB_odd_of_par {pp : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg) (hP : ∀ s h, pp s (-h) = pp s h)
    (b : ℝ → ℝ) (u h : ℝ) :
    lB pp PiP PiM b u (-h) = -lB pp PiP PiM b u h := by
  obtain ⟨p00, p01, p10, p11, m00, m01, m10, m11⟩ := par_Pi_entries_of_par hpar u h
  have e1 : u + -h / 2 = u - h / 2 := by ring
  have e2 : u - -h / 2 = u + h / 2 := by ring
  have e3 : u + -h = u - h := by ring
  have e4 : u - -h = u + h := by ring
  simp only [lB, e1, e2, e3, e4, hP, p10, m10]
  ring

lemma lB_odd (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (hP : ∀ s h, pp s (-h) = pp s h)
    (b : ℝ → ℝ) (u h : ℝ) :
    lB pp PiP PiM b u (-h) = -lB pp PiP PiM b u h :=
  lB_odd_of_par L.par_Pi hP b u h

/-- A `PApprox 1` function vanishing at `h = 0` is `O(h)`. -/
lemma uo1_of_zero {f : ℝ → ℝ → ℝ} (hf : PApprox 1 f) (h0 : ∀ u, f u 0 = 0) : UO 1 f := by
  have := hf.order1
  simpa [h0] using this

/-- **(i)** `L_A[g] = O(h²)` for `g ∈ BSmooth 2`: parity of `lA` and the Langer condition (eq:eng-langer). -/
theorem lA_UO2 {N : ℕ} (hN : 2 ≤ N) (hS : SymbolExp N pp qq PiP PiM)
    (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (hP : ∀ s h, pp s (-h) = pp s h)
    (hQ : ∀ u h, qq u (-h) = qq u h)
    (hlang : ∀ u, pp u 0 * (PiP u 0 0 0 + PiM u 0 0 0) = qq u 0) {g : ℝ → ℝ} (hg : BSmooth 2 g) :
    UO 2 (lA pp qq PiP PiM g) := by
  have s1 := hg.papprox_shift' (c := 1) (σ := fun u h => u + h) (fun u h => by ring)
  have s2 := hg.papprox_shift' (c := -1) (σ := fun u h => u - h) (fun u h => by ring)
  have s0 : PApprox 2 (fun u _ => g u) := PApprox.of_bdd_fun hg.bdd
  have hpa : PApprox 2 (lA pp qq PiP PiM g) := by
    unfold lA
    exact ((((hS.sP 0 0).mono hN).mul s1).add (((hS.sM 0 0).mono hN).mul s2)).sub
      ((hS.qe.mono hN).mul s0)
  have h0 : ∀ u, lA pp qq PiP PiM g u 0 = 0 := by
    intro u
    have := hlang u
    simp only [lA, zero_div, add_zero, sub_zero]
    linear_combination (g u) * this
  have h1 : UO 1 (lA pp qq PiP PiM g) := uo1_of_zero (hpa.mono (by norm_num)) h0
  exact PApprox.lift (n := 1) (σ := 1) (δ0 := 1) (by norm_num) hpa h1 one_pos
    (fun u h _ => by rw [one_mul]; exact lA_even L hP hQ g u h)

/-! ### (ii) the odd bracket and the transport operator -/

lemma Mfun_even_of_adj {pp : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg) (hP : ∀ s h, pp s (-h) = pp s h)
    (s h : ℝ) (hadj : PiP (s - h / 2) h = Matrix.adjugate (PiM (s + h / 2) h)) :
    Mfun pp PiM s (-h) = Mfun pp PiM s h := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + h / 2 := ⟨s - h / 2, by ring⟩
  have e0 : u + h / 2 - h / 2 = u := by ring
  have e0' : u + h / 2 + h / 2 = u + h := by ring
  rw [e0, e0'] at hadj
  obtain ⟨_, _, p10, _⟩ := adj_entries (PiM (u + h) h) (PiP u h) hadj
  obtain ⟨_, _, _, _, _, _, m10, _⟩ := par_Pi_entries_of_par hpar u h
  have e1 : u + h / 2 + -h / 2 = u := by ring
  have e2 : u + h / 2 + h / 2 = u + h := by ring
  simp only [Mfun, e1, e2, hP, m10, p10]
  ring

lemma Mfun_even (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (hP : ∀ s h, pp s (-h) = pp s h) {δD : ℝ}
    (hD : ∀ s h, 0 < |h| → |h| < δD → d2 s h ≠ 0) (s h : ℝ) (hh : |h| < δD) :
    Mfun pp PiM s (-h) = Mfun pp PiM s h := by
  by_cases h0 : h = 0
  · subst h0; simp
  · obtain ⟨u, rfl⟩ : ∃ u, s = u + h / 2 := ⟨s - h / 2, by ring⟩
    have hadj := Pp_eq_adj_of_prod L u h (hD (u + h / 2) h (abs_pos.mpr h0) hh)
    exact Mfun_even_of_adj L.par_Pi hP (u + h / 2) h (by ring_nf at hadj ⊢; simpa using hadj)

private lemma Mdev_of_even {N : ℕ} (hN : 2 ≤ N) (hS : SymbolExp N pp qq PiP PiM) {δ0 : ℝ} (hδ0 : 0 < δ0)
    (heven : ∀ s h, |h| < δ0 → Mfun pp PiM s (-h) = Mfun pp PiM s h) :
    UO 2 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) := by
  have hf : PApprox 2 (Mfun pp PiM) := (hS.cM 1 0).mono hN
  have hval : ∀ s, Mfun pp PiM s 0 = M0fun pp PiM s := by intro s; simp [Mfun, M0fun]
  obtain ⟨C, δ, hδ, hb⟩ := hf.bdd'
  have hg : PApprox 2 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) :=
    hf.sub (PApprox.of_fun (M0fun pp PiM) (C := C) (fun s => by
      have := hb s 0 (by simpa using hδ)
      rwa [hval] at this))
  have h1 : UO 1 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) := by
    have := (hf.mono (by norm_num : 1 ≤ 2)).order1
    simpa [hval] using this
  exact PApprox.lift (n := 1) (σ := 1) (δ0 := δ0) (by norm_num) hg h1 hδ0
    (fun s h hh => by simp [heven s h hh])

/-- `M(s,h) = M₀(s) + O(h²)` uniformly in `s` from `Π₊ = adj Π₋(·+h)` (no `𝒟² ≠ 0` hypothesis). -/
lemma Mdev_of_adj {N : ℕ} (hN : 2 ≤ N) (hS : SymbolExp N pp qq PiP PiM)
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg)
    (hadj : ∀ u h, PiP u h = Matrix.adjugate (PiM (u + h) h))
    (hP : ∀ s h, pp s (-h) = pp s h) :
    UO 2 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) :=
  Mdev_of_even hN hS one_pos (fun s h _ => Mfun_even_of_adj hpar hP s h
    (by have := hadj (s - h / 2) h; rwa [show s - h / 2 + h = s + h / 2 by ring] at this))

/-- `M(s,h) = M₀(s) + O(h²)` uniformly in `s` (the paper: "`M` is even in `h`", `M(s,0) = Ω₀²V₀`). -/
lemma Mdev {N : ℕ} (hN : 2 ≤ N) (hS : SymbolExp N pp qq PiP PiM)
    (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (hP : ∀ s h, pp s (-h) = pp s h) {δD : ℝ} (hδD : 0 < δD)
    (hD : ∀ s h, 0 < |h| → |h| < δD → d2 s h ≠ 0) :
    UO 2 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) :=
  Mdev_of_even hN hS hδD (fun s h hh => Mfun_even L hP hD s h hh)

lemma lB_eq_of_adj {pp : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} (b : ℝ → ℝ) (u h : ℝ)
    (hadj : PiP u h = Matrix.adjugate (PiM (u + h) h)) :
    lB pp PiP PiM b u h =
      -(Mfun pp PiM (u + h / 2) h) * b (u + h) + Mfun pp PiM (u - h / 2) h * b (u - h) := by
  obtain ⟨_, _, p10, _⟩ := adj_entries (PiM (u + h) h) (PiP u h) hadj
  have e1 : u + h / 2 + h / 2 = u + h := by ring
  have e2 : u - h / 2 + h / 2 = u := by ring
  simp only [lB, Mfun, e1, e2, p10]
  ring

lemma lB_eq (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) {δD : ℝ}
    (hD : ∀ s h, 0 < |h| → |h| < δD → d2 s h ≠ 0) (b : ℝ → ℝ) (u h : ℝ) (hh : |h| < δD) :
    lB pp PiP PiM b u h =
      -(Mfun pp PiM (u + h / 2) h) * b (u + h) + Mfun pp PiM (u - h / 2) h * b (u - h) := by
  by_cases h0 : h = 0
  · subst h0
    obtain ⟨_, _, p10, _⟩ := par_Pi_entries L u 0
    rw [neg_zero] at p10
    simp only [lB, Mfun, zero_div, add_zero, sub_zero, p10]
    ring
  · exact lB_eq_of_adj b u h (Pp_eq_adj_of_prod L u h (hD (u + h / 2) h (abs_pos.mpr h0) hh))

lemma UO.h_mul {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) : UO (n + 1) (fun u h => h * f u h) := by
  have := UO.hpow_mul 1 hf
  rw [add_comm] at this
  simpa using this

lemma transportOp_bdd {M0 b : ℝ → ℝ} (hM0 : BSmooth 1 M0) (hb : BSmooth 1 b) :
    ∃ C, ∀ x, |transportOp M0 b x| ≤ C := by
  obtain ⟨Cm, hCm⟩ := hM0.bdd
  obtain ⟨Cm', hCm'⟩ := hM0.d.bdd
  obtain ⟨Cb, hCb⟩ := hb.bdd
  obtain ⟨Cb', hCb'⟩ := hb.d.bdd
  refine ⟨2 * |Cm| * |Cb'| + |Cm'| * |Cb|, fun x => ?_⟩
  unfold transportOp
  rw [abs_neg]
  have a1 : |M0 x| ≤ |Cm| := (hCm x).trans (le_abs_self Cm)
  have a2 : |deriv b x| ≤ |Cb'| := (hCb' x).trans (le_abs_self Cb')
  have a3 : |deriv M0 x| ≤ |Cm'| := (hCm' x).trans (le_abs_self Cm')
  have a4 : |b x| ≤ |Cb| := (hCb x).trans (le_abs_self Cb)
  have t1 : |2 * M0 x * deriv b x| ≤ 2 * |Cm| * |Cb'| := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left a1 (by norm_num)) a2 (abs_nonneg _) (by positivity)
  have t2 : |deriv M0 x * b x| ≤ |Cm'| * |Cb| := by
    rw [abs_mul]
    exact mul_le_mul a3 a4 (abs_nonneg _) (abs_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

private lemma lB_UO3_aux {N : ℕ} (hN : 3 ≤ N) (hS : SymbolExp N pp qq PiP PiM)
    (hM0 : BSmooth 2 (M0fun pp PiM)) {b : ℝ → ℝ} (hb : BSmooth 3 b)
    (hMd : UO 2 (fun s h => Mfun pp PiM s h - M0fun pp PiM s))
    {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hlB_eq : ∀ u h, |h| < δ0 → lB pp PiP PiM b u h =
      -(Mfun pp PiM (u + h / 2) h) * b (u + h) + Mfun pp PiM (u - h / 2) h * b (u - h))
    (hlB_odd : ∀ u h, lB pp PiP PiM b u (-h) = -lB pp PiP PiM b u h) :
    UO 3 (fun u h => lB pp PiP PiM b u h - h * transportOp (M0fun pp PiM) b u) := by
  have hb2 : BSmooth 2 b := hb.mono (by norm_num)
  have εp : UO 2 (fun u h => Mfun pp PiM (u + h / 2) h - M0fun pp PiM (u + h / 2)) := hMd.shift_half
  have εm : UO 2 (fun u h => Mfun pp PiM (u - h / 2) h - M0fun pp PiM (u - h / 2)) := hMd.shift_neg_half
  have emp : UO 2 (fun u h => M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u) :=
    hM0.uo_shift_order1 (1 / 2) (σ := fun u h => u + h / 2) (fun u h => by ring)
  have emm : UO 2 (fun u h => M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u) :=
    hM0.uo_shift_order1 (-1 / 2) (σ := fun u h => u - h / 2) (fun u h => by ring)
  have ebp : UO 2 (fun u h => b (u + h) - b u - (1 * h) * deriv b u) :=
    hb2.uo_shift_order1 1 (σ := fun u h => u + h) (fun u h => by ring)
  have ebm : UO 2 (fun u h => b (u - h) - b u - (-1 * h) * deriv b u) :=
    hb2.uo_shift_order1 (-1) (σ := fun u h => u - h) (fun u h => by ring)
  obtain ⟨Cb, hCb⟩ := hb.bdd
  obtain ⟨Cb', hCb'⟩ := hb.d.bdd
  obtain ⟨Cm, hCm⟩ := hM0.bdd
  obtain ⟨Cm', hCm'⟩ := hM0.d.bdd
  have βp : UO 0 (fun u h => b (u + h)) := UO.of_bdd (fun u h => hCb _)
  have βm : UO 0 (fun u h => b (u - h)) := UO.of_bdd (fun u h => hCb _)
  have b0 : UO 0 (fun u (_ : ℝ) => b u) := UO0_of_fun ⟨Cb, hCb⟩
  have b1 : UO 0 (fun u (_ : ℝ) => deriv b u) := UO0_of_fun ⟨Cb', hCb'⟩
  have μ0 : UO 0 (fun u (_ : ℝ) => M0fun pp PiM u) := UO0_of_fun ⟨Cm, hCm⟩
  have μ1 : UO 0 (fun u (_ : ℝ) => deriv (M0fun pp PiM) u / 2) :=
    UO0_of_fun ⟨|Cm'|, fun x => by
      rw [abs_div, abs_two]
      have := (hCm' x).trans (le_abs_self Cm')
      linarith [abs_nonneg (deriv (M0fun pp PiM) x)]⟩
  have T1 := εp.mul_right βp
  have T2 := εm.mul_right βm
  have T3 := μ0.mul_left (ebm.sub ebp)
  have T4 := (μ1.mul_left (ebp.add ebm)).h_mul
  have T5 := b0.mul_left (emm.sub emp)
  have T6 := (b1.mul_left (emp.add emm)).h_mul
  have T7 := emm.mul ebm
  have T8 := emp.mul ebp
  have key : UO 2 (fun u h =>
      -((Mfun pp PiM (u + h / 2) h - M0fun pp PiM (u + h / 2)) * b (u + h))
      + (Mfun pp PiM (u - h / 2) h - M0fun pp PiM (u - h / 2)) * b (u - h)
      + M0fun pp PiM u * ((b (u - h) - b u - (-1 * h) * deriv b u) - (b (u + h) - b u - (1 * h) * deriv b u))
      - h * (deriv (M0fun pp PiM) u / 2 * ((b (u + h) - b u - (1 * h) * deriv b u)
          + (b (u - h) - b u - (-1 * h) * deriv b u)))
      + b u * ((M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u)
          - (M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u))
      - h * (deriv b u * ((M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u)
          + (M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u)))
      + (M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u)
          * (b (u - h) - b u - (-1 * h) * deriv b u)
      - (M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u)
          * (b (u + h) - b u - (1 * h) * deriv b u)) := by
    have T4' := T4.mono (by norm_num : 2 ≤ 2 + 1)
    have T6' := T6.mono (by norm_num : 2 ≤ 2 + 1)
    have T7' := T7.mono (by norm_num : 2 ≤ 2 + 2)
    have T8' := T8.mono (by norm_num : 2 ≤ 2 + 2)
    exact ((((((T1.neg.add T2).add T3).sub T4').add T5).sub T6').add T7').sub T8'
  have h2 : UO 2 (fun u h => lB pp PiP PiM b u h - h * transportOp (M0fun pp PiM) b u) := by
    refine UO.congr_loc key hδ0 (fun u h hh => ?_)
    rw [hlB_eq u h hh]
    simp only [transportOp]
    ring
  have hpa : PApprox 3 (fun u h => lB pp PiP PiM b u h - h * transportOp (M0fun pp PiM) b u) := by
    have s1 := hb.papprox_shift' (c := 1) (σ := fun u h => u + h) (fun u h => by ring)
    have s2 := hb.papprox_shift' (c := -1) (σ := fun u h => u - h) (fun u h => by ring)
    have hT : PApprox 3 (fun u _ => transportOp (M0fun pp PiM) b u) :=
      PApprox.of_bdd_fun (transportOp_bdd (hM0.mono (by norm_num)) (hb.mono (by norm_num)))
    unfold lB
    exact ((((hS.sP 1 0).mono hN).mul s1).add (((hS.sM 1 0).mono hN).mul s2)).sub
      ((PApprox.hpow 1).mul hT |>.congr fun u h => by simp)
  exact PApprox.lift (n := 2) (σ := -1) (δ0 := 1) (by norm_num) hpa h2 one_pos
    (fun u h _ => by rw [hlB_odd]; ring)

/-- **(ii)** `lB b - h 𝒯[b] = O(h³)` from `Π₊ = adj Π₋(·+h)` (no `𝒟² ≠ 0` hypothesis). -/
theorem lB_UO3_of_adj {N : ℕ} (hN : 3 ≤ N) (hS : SymbolExp N pp qq PiP PiM)
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg)
    (hadj : ∀ u h, PiP u h = Matrix.adjugate (PiM (u + h) h))
    (hP : ∀ s h, pp s (-h) = pp s h)
    (hM0 : BSmooth 2 (M0fun pp PiM)) {b : ℝ → ℝ} (hb : BSmooth 3 b) :
    UO 3 (fun u h => lB pp PiP PiM b u h - h * transportOp (M0fun pp PiM) b u) :=
  lB_UO3_aux hN hS hM0 hb (Mdev_of_adj (by omega : 2 ≤ N) hS hpar hadj hP) one_pos
    (fun u h _ => lB_eq_of_adj b u h (hadj u h)) (lB_odd_of_par hpar hP b)

/-- **(ii)** `lB b - h 𝒯[b] = O(h³)`: the odd bracket gives the transport operator `𝒯[b] = -(2 M₀ b' + M₀' b)` at
leading order, and parity removes the `h²` term. -/
theorem lB_UO3 {N : ℕ} (hN : 3 ≤ N) (hS : SymbolExp N pp qq PiP PiM)
    (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (hP : ∀ s h, pp s (-h) = pp s h) {δD : ℝ} (hδD : 0 < δD)
    (hD : ∀ s h, 0 < |h| → |h| < δD → d2 s h ≠ 0)
    (hM0 : BSmooth 2 (M0fun pp PiM)) {b : ℝ → ℝ} (hb : BSmooth 3 b) :
    UO 3 (fun u h => lB pp PiP PiM b u h - h * transportOp (M0fun pp PiM) b u) :=
  lB_UO3_aux hN hS hM0 hb (Mdev (by omega : 2 ≤ N) hS L hP hδD hD) hδD
    (lB_eq L hD b) (lB_odd L hP b)

/-! ### (iii) the even flux `F_cas` -/

lemma Fcas_expand (pp : ℝ → ℝ → ℝ) (AA BB : ℝ → ℝ → ℝ) (PiM : ℝ → ℝ → M2) (s h : ℝ) :
    Fcas pp AA BB PiM s h =
      (pp s h * PiM (s + h / 2) h 0 1) * (AA (s + h / 2) h * AA (s - h / 2) h)
      + h * (pp s h * PiM (s + h / 2) h 1 1) * (AA (s + h / 2) h * BB (s - h / 2) h)
      - h * (pp s h * PiM (s + h / 2) h 0 0) * (BB (s + h / 2) h * AA (s - h / 2) h)
      - h ^ 2 * (pp s h * PiM (s + h / 2) h 1 0) * (BB (s + h / 2) h * BB (s - h / 2) h) := by
  simp only [Fcas, vrow, rowMul, rowDet, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma Aans_papprox' {N k : ℕ} {g : ℕ → ℝ → ℝ} (hg : ∀ i < k, BSmooth N (g i)) (c : ℝ) {σ : ℝ → ℝ → ℝ}
    (hσ : ∀ u h, σ u h = u + c * h) : PApprox N (fun u h => Aans g k (σ u h) h) :=
  (Aans_papprox hg c).congr fun u h => by rw [hσ]

lemma Bans_papprox' {N l : ℕ} {b : ℕ → ℝ → ℝ} (hb : ∀ i, 1 ≤ i → i ≤ l → BSmooth N (b i)) (c : ℝ)
    {σ : ℝ → ℝ → ℝ} (hσ : ∀ u h, σ u h = u + c * h) : PApprox N (fun u h => Bans b l (σ u h) h) :=
  (Bans_papprox hb c).congr fun u h => by rw [hσ]

lemma Aans_papprox_zero {N k : ℕ} {g : ℕ → ℝ → ℝ} (hg : ∀ i < k, BSmooth N (g i)) :
    PApprox N (fun u h => Aans g k u h) :=
  (Aans_papprox hg 0).congr fun u h => by simp

lemma Bans_papprox_zero {N l : ℕ} {b : ℕ → ℝ → ℝ} (hb : ∀ i, 1 ≤ i → i ≤ l → BSmooth N (b i)) :
    PApprox N (fun u h => Bans b l u h) :=
  (Bans_papprox hb 0).congr fun u h => by simp

/-- `PApprox` of the defect components of any `(AA, BB)` with `PApprox` shifts. -/
lemma defect_papprox {N : ℕ} (hS : SymbolExp N pp qq PiP PiM) {AA BB : ℝ → ℝ → ℝ}
    (hAp : PApprox N (fun u h => AA (u + h) h)) (hAm : PApprox N (fun u h => AA (u - h) h))
    (hA0 : PApprox N AA)
    (hBp : PApprox N (fun u h => BB (u + h) h)) (hBm : PApprox N (fun u h => BB (u - h) h))
    (hB0 : PApprox N BB) (k : Fin 2) :
    PApprox N (fun u h => defectRow pp qq AA BB PiP PiM u h k) := by
  have hh : PApprox N (fun _ h => h) := (PApprox.hpow 1).congr fun _ _ => by simp
  fin_cases k
  · have e : ∀ u h, pp (u + h / 2) h * (AA (u + h) h * PiP u h 0 0 + h * BB (u + h) h * PiP u h 1 0)
        + pp (u - h / 2) h * (AA (u - h) h * PiM u h 0 0 + h * BB (u - h) h * PiM u h 1 0)
        - qq u h * AA u h
        = (AA (u + h) h * (pp (u + h / 2) h * PiP u h 0 0) + (fun _ h => h) u h * BB (u + h) h
            * (pp (u + h / 2) h * PiP u h 1 0))
          + (AA (u - h) h * (pp (u - h / 2) h * PiM u h 0 0) + (fun _ h => h) u h * BB (u - h) h
            * (pp (u - h / 2) h * PiM u h 1 0)) - qq u h * AA u h := by
      intro u h; ring
    refine PApprox.congr (f := fun u h =>
      (AA (u + h) h * (pp (u + h / 2) h * PiP u h 0 0) + (fun _ h => h) u h * BB (u + h) h
            * (pp (u + h / 2) h * PiP u h 1 0))
          + (AA (u - h) h * (pp (u - h / 2) h * PiM u h 0 0) + (fun _ h => h) u h * BB (u - h) h
            * (pp (u - h / 2) h * PiM u h 1 0)) - qq u h * AA u h) ?_ (fun u h => (e u h).symm)
    exact (((hAp.mul (hS.sP 0 0)).add ((hh.mul hBp).mul (hS.sP 1 0))).add
      ((hAm.mul (hS.sM 0 0)).add ((hh.mul hBm).mul (hS.sM 1 0)))).sub (hS.qe.mul hA0)
  · have e : ∀ u h, pp (u + h / 2) h * (AA (u + h) h * PiP u h 0 1 + h * BB (u + h) h * PiP u h 1 1)
        + pp (u - h / 2) h * (AA (u - h) h * PiM u h 0 1 + h * BB (u - h) h * PiM u h 1 1)
        - qq u h * (h * BB u h)
        = (AA (u + h) h * (pp (u + h / 2) h * PiP u h 0 1) + (fun _ h => h) u h * BB (u + h) h
            * (pp (u + h / 2) h * PiP u h 1 1))
          + (AA (u - h) h * (pp (u - h / 2) h * PiM u h 0 1) + (fun _ h => h) u h * BB (u - h) h
            * (pp (u - h / 2) h * PiM u h 1 1)) - qq u h * ((fun _ h => h) u h * BB u h) := by
      intro u h; ring
    refine PApprox.congr (f := fun u h =>
      (AA (u + h) h * (pp (u + h / 2) h * PiP u h 0 1) + (fun _ h => h) u h * BB (u + h) h
            * (pp (u + h / 2) h * PiP u h 1 1))
          + (AA (u - h) h * (pp (u - h / 2) h * PiM u h 0 1) + (fun _ h => h) u h * BB (u - h) h
            * (pp (u - h / 2) h * PiM u h 1 1)) - qq u h * ((fun _ h => h) u h * BB u h)) ?_
      (fun u h => (e u h).symm)
    exact (((hAp.mul (hS.sP 0 1)).add ((hh.mul hBp).mul (hS.sP 1 1))).add
      ((hAm.mul (hS.sM 0 1)).add ((hh.mul hBm).mul (hS.sM 1 1)))).sub (hS.qe.mul (hh.mul hB0))

lemma Fcas_papprox {N : ℕ} (hS : SymbolExp N pp qq PiP PiM) {AA BB : ℝ → ℝ → ℝ}
    (hAp : PApprox N (fun s h => AA (s + h / 2) h)) (hAm : PApprox N (fun s h => AA (s - h / 2) h))
    (hBp : PApprox N (fun s h => BB (s + h / 2) h)) (hBm : PApprox N (fun s h => BB (s - h / 2) h)) :
    PApprox N (fun s h => Fcas pp AA BB PiM s h) := by
  have hh : PApprox N (fun _ h => h) := (PApprox.hpow 1).congr fun _ _ => by simp
  have hh2 : PApprox N (fun _ h => h ^ 2) := PApprox.hpow 2
  refine PApprox.congr (f := fun s h =>
    (pp s h * PiM (s + h / 2) h 0 1) * (AA (s + h / 2) h * AA (s - h / 2) h)
      + (fun _ h => h) s h * (pp s h * PiM (s + h / 2) h 1 1) * (AA (s + h / 2) h * BB (s - h / 2) h)
      - (fun _ h => h) s h * (pp s h * PiM (s + h / 2) h 0 0) * (BB (s + h / 2) h * AA (s - h / 2) h)
      - (fun _ h => h ^ 2) s h * (pp s h * PiM (s + h / 2) h 1 0) * (BB (s + h / 2) h * BB (s - h / 2) h)) ?_
    (fun s h => (Fcas_expand pp AA BB PiM s h).symm)
  exact ((((hS.cM 0 1).mul (hAp.mul hAm)).add ((hh.mul (hS.cM 1 1)).mul (hAp.mul hBm))).sub
    ((hh.mul (hS.cM 0 0)).mul (hBp.mul hAm))).sub ((hh2.mul (hS.cM 1 0)).mul (hBp.mul hBm))

/-- Adding `h^{2k} g` to `A`: the `𝔄`-component changes by `h^{2k} lA g`. -/
lemma defect0_stepA (g : ℕ → ℝ → ℝ) (b : ℕ → ℝ → ℝ) (k l : ℕ) (u h : ℝ) :
    defectRow pp qq (Aans g (k + 1)) (Bans b l) PiP PiM u h 0 =
      defectRow pp qq (Aans g k) (Bans b l) PiP PiM u h 0 + h ^ (2 * k) * lA pp qq PiP PiM (g k) u h := by
  have e : Aans g (k + 1) = fun u h => Aans g k u h + (fun u h => h ^ (2 * k) * g k u) u h :=
    funext fun u => funext fun h => Aans_succ g k u h
  rw [e, defectRow_add_A, defect_zero_A]

/-- Adding `h^{2l} b` to `B`: the `𝔄`-component changes by `h^{2l+1} lB b`. -/
lemma defect0_stepB (g : ℕ → ℝ → ℝ) (b : ℕ → ℝ → ℝ) (k l : ℕ) (u h : ℝ) :
    defectRow pp qq (Aans g k) (Bans b (l + 1)) PiP PiM u h 0 =
      defectRow pp qq (Aans g k) (Bans b l) PiP PiM u h 0 + h ^ (2 * l + 1) * lB pp PiP PiM (b (l + 1)) u h := by
  have e : Bans b (l + 1) = fun u h => Bans b l u h + (fun u h => h ^ (2 * l) * b (l + 1) u) u h :=
    funext fun u => funext fun h => Bans_succ b l u h
  rw [e, defectRow_add_B, defect_zero_B]

/-- **(iii), `A`-variation.** Adding `h^{2k} g_k` to `A` changes `F_cas` by `h^{2k}·2 V₀ g₀ g_k + O(h^{2k+1})`
(`k ≥ 1`); the parity upgrade to `O(h^{2k+2})` is done in `Corrector`. -/
theorem dFA_UO1 {N : ℕ} (hN : 1 ≤ N) (hS : SymbolExp N pp qq PiP PiM) {g b : ℕ → ℝ → ℝ} {k l : ℕ} (hk : 1 ≤ k)
    (hg : ∀ i ≤ k, BSmooth N (g i)) (hb : ∀ i, 1 ≤ i → i ≤ l → BSmooth N (b i)) :
    UO (2 * k + 1) (fun s h => Fcas pp (Aans g (k + 1)) (Bans b l) PiM s h - Fcas pp (Aans g k) (Bans b l) PiM s h
      - h ^ (2 * k) * (2 * V0fun pp PiM s * g 0 s * g k s)) := by
  have hgk : ∀ i < k, BSmooth N (g i) := fun i hi => hg i hi.le
  -- the increment is `h^{2k} Φ`
  set Φ : ℝ → ℝ → ℝ := fun s h =>
    (pp s h * PiM (s + h / 2) h 0 1) * (Aans g k (s + h / 2) h * g k (s - h / 2) + g k (s + h / 2) * Aans g k (s - h / 2) h
      + h ^ (2 * k) * (g k (s + h / 2) * g k (s - h / 2)))
    + h * (pp s h * PiM (s + h / 2) h 1 1) * (g k (s + h / 2) * Bans b l (s - h / 2) h)
    - h * (pp s h * PiM (s + h / 2) h 0 0) * (Bans b l (s + h / 2) h * g k (s - h / 2)) with hΦ
  have hdiff : ∀ s h, Fcas pp (Aans g (k + 1)) (Bans b l) PiM s h - Fcas pp (Aans g k) (Bans b l) PiM s h
      = h ^ (2 * k) * Φ s h := by
    intro s h
    rw [Fcas_expand, Fcas_expand]
    simp only [Aans_succ, hΦ]
    ring
  -- Φ has a `PApprox 1` expansion
  have gp : PApprox N (fun s h => g k (s + h / 2)) :=
    (hg k le_rfl).papprox_shift' (1 / 2) (σ := fun s h => s + h / 2) (fun u h => by ring)
  have gm : PApprox N (fun s h => g k (s - h / 2)) :=
    (hg k le_rfl).papprox_shift' (-1 / 2) (σ := fun s h => s - h / 2) (fun u h => by ring)
  have ap := Aans_papprox' hgk (1 / 2) (σ := fun s h => s + h / 2) (fun u h => by ring)
  have am := Aans_papprox' hgk (-1 / 2) (σ := fun s h => s - h / 2) (fun u h => by ring)
  have bp := Bans_papprox' hb (1 / 2) (σ := fun s h => s + h / 2) (fun u h => by ring)
  have bm := Bans_papprox' hb (-1 / 2) (σ := fun s h => s - h / 2) (fun u h => by ring)
  have hh : PApprox N (fun _ h => h) := (PApprox.hpow 1).congr fun _ _ => by simp
  have hpa : PApprox N Φ := by
    rw [hΦ]
    have gg : PApprox N (fun s h => g k (s + h / 2) * g k (s - h / 2)) := gp.mul gm
    have h2k : PApprox N (fun _ h => h ^ (2 * k)) := PApprox.hpow _
    exact ((((hS.cM 0 1).mul (((ap.mul gm).add (gp.mul am)).add (h2k.mul gg))).add
      ((hh.mul (hS.cM 1 1)).mul (gp.mul bm))).sub ((hh.mul (hS.cM 0 0)).mul (bp.mul gm)))
  have hΦ0 : ∀ s, Φ s 0 = 2 * V0fun pp PiM s * g 0 s * g k s := by
    intro s
    simp only [hΦ, V0fun, zero_div, add_zero, sub_zero, zero_mul,
      Aans_zero_h g hk, zero_pow (by omega : 2 * k ≠ 0)]
    ring
  have h1 : UO 1 (fun s h => Φ s h - 2 * V0fun pp PiM s * g 0 s * g k s) := by
    have := (hpa.mono hN).order1
    simpa [hΦ0] using this
  refine (UO.hpow_mul (2 * k) h1).congr (fun s h => ?_)
  have := hdiff s h
  linear_combination (-1 : ℝ) * this

/-- **(iii), `B`-variation.** Adding `h^{2l} b_{l+1}` to `B` changes `F_cas` by `O(h^{2l+1})`. -/
theorem dFB_UO {N : ℕ} (hS : SymbolExp N pp qq PiP PiM) {g b : ℕ → ℝ → ℝ} {k l : ℕ}
    (hg : ∀ i < k, BSmooth N (g i)) (hb : ∀ i, 1 ≤ i → i ≤ l + 1 → BSmooth N (b i)) :
    UO (2 * l + 1) (fun s h => Fcas pp (Aans g k) (Bans b (l + 1)) PiM s h - Fcas pp (Aans g k) (Bans b l) PiM s h) := by
  have hbl : ∀ i, 1 ≤ i → i ≤ l → BSmooth N (b i) := fun i h1 h2 => hb i h1 (by omega)
  have hbk : BSmooth N (b (l + 1)) := hb (l + 1) (by omega) le_rfl
  set Ψ : ℝ → ℝ → ℝ := fun s h =>
    (pp s h * PiM (s + h / 2) h 1 1) * (Aans g k (s + h / 2) h * b (l + 1) (s - h / 2))
    - (pp s h * PiM (s + h / 2) h 0 0) * (b (l + 1) (s + h / 2) * Aans g k (s - h / 2) h)
    - h * (pp s h * PiM (s + h / 2) h 1 0) * (Bans b l (s + h / 2) h * b (l + 1) (s - h / 2)
        + b (l + 1) (s + h / 2) * Bans b l (s - h / 2) h
        + h ^ (2 * l) * (b (l + 1) (s + h / 2) * b (l + 1) (s - h / 2))) with hΨ
  have hdiff : ∀ s h, Fcas pp (Aans g k) (Bans b (l + 1)) PiM s h - Fcas pp (Aans g k) (Bans b l) PiM s h
      = h ^ (2 * l + 1) * Ψ s h := by
    intro s h
    rw [Fcas_expand, Fcas_expand]
    simp only [Bans_succ, hΨ]
    ring
  have βp : PApprox N (fun s h => b (l + 1) (s + h / 2)) :=
    hbk.papprox_shift' (1 / 2) (σ := fun s h => s + h / 2) (fun u h => by ring)
  have βm : PApprox N (fun s h => b (l + 1) (s - h / 2)) :=
    hbk.papprox_shift' (-1 / 2) (σ := fun s h => s - h / 2) (fun u h => by ring)
  have ap := Aans_papprox' hg (1 / 2) (σ := fun s h => s + h / 2) (fun u h => by ring)
  have am := Aans_papprox' hg (-1 / 2) (σ := fun s h => s - h / 2) (fun u h => by ring)
  have bp := Bans_papprox' hbl (1 / 2) (σ := fun s h => s + h / 2) (fun u h => by ring)
  have bm := Bans_papprox' hbl (-1 / 2) (σ := fun s h => s - h / 2) (fun u h => by ring)
  have hh : PApprox N (fun _ h => h) := (PApprox.hpow 1).congr fun _ _ => by simp
  have h2l : PApprox N (fun _ h => h ^ (2 * l)) := PApprox.hpow _
  have hpa : PApprox N Ψ := by
    rw [hΨ]
    exact (((hS.cM 1 1).mul (ap.mul βm)).sub ((hS.cM 0 0).mul (βp.mul am))).sub
      ((hh.mul (hS.cM 1 0)).mul ((((bp.mul βm).add (βp.mul bm)).add (h2l.mul (βp.mul βm)))))
  have hb0 : UO 0 Ψ := hpa.bdd
  refine (UO.hpow_mul (2 * l + 1) hb0).congr (fun s h => ?_)
  rw [hdiff]

/-! ### The remainders of (eq:eng-factor) and the lower bound for `A` -/

/-- **Remainders.** The terms `h^n R_P`, `h^n R_Q` of (eq:eng-factor) contribute `O(h^n)` to both components of the
defect, for bounded `R_P`, `R_Q`, bounded propagators and bounded `(A, hB)` (no regularity of `R_P, R_Q` is used). -/
lemma defect_remainder {n : ℕ} (hbP : ∀ i j, UO 0 (fun u h => PiP u h i j)) (hbM : ∀ i j, UO 0 (fun u h => PiM u h i j))
    {RP RQ : ℝ → ℝ → ℝ} (hRP : UO 0 RP) (hRQ : UO 0 RQ) {AA BB : ℝ → ℝ → ℝ}
    (hAp : UO 0 (fun u h => AA (u + h) h)) (hAm : UO 0 (fun u h => AA (u - h) h)) (hA0 : UO 0 AA)
    (hBp : UO 0 (fun u h => BB (u + h) h)) (hBm : UO 0 (fun u h => BB (u - h) h)) (hB0 : UO 0 BB) (k : Fin 2) :
    UO n (fun u h => defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h k) := by
  have hh : UO 0 (fun _ h => h) := ((UO.hpow 1).mono (Nat.zero_le 1)).congr fun _ _ => by simp
  have RPp : UO 0 (fun u h => RP (u + h / 2) h) := hRP.shift_half
  have RPm : UO 0 (fun u h => RP (u - h / 2) h) := hRP.shift_neg_half
  fin_cases k
  · change UO n (fun u h => defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h 0)
    have e : ∀ u h, defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h 0 =
        h ^ n * (RP (u + h / 2) h * (AA (u + h) h * PiP u h 0 0 + h * BB (u + h) h * PiP u h 1 0)
          + RP (u - h / 2) h * (AA (u - h) h * PiM u h 0 0 + h * BB (u - h) h * PiM u h 1 0)
          - RQ u h * AA u h) := by
      intro u h; rw [defectRow_zero_eq]; ring
    have br : UO 0 (fun u h => RP (u + h / 2) h * (AA (u + h) h * PiP u h 0 0 + h * BB (u + h) h * PiP u h 1 0)
          + RP (u - h / 2) h * (AA (u - h) h * PiM u h 0 0 + h * BB (u - h) h * PiM u h 1 0)
          - RQ u h * AA u h) :=
      ((RPp.mul ((hAp.mul (hbP 0 0)).add ((hh.mul hBp).mul (hbP 1 0)))).add
        (RPm.mul ((hAm.mul (hbM 0 0)).add ((hh.mul hBm).mul (hbM 1 0))))).sub (hRQ.mul hA0)
    exact (UO.hpow_mul n br).congr fun u h => by rw [e]
  · change UO n (fun u h => defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h 1)
    have e : ∀ u h, defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h 1 =
        h ^ n * (RP (u + h / 2) h * (AA (u + h) h * PiP u h 0 1 + h * BB (u + h) h * PiP u h 1 1)
          + RP (u - h / 2) h * (AA (u - h) h * PiM u h 0 1 + h * BB (u - h) h * PiM u h 1 1)
          - RQ u h * (h * BB u h)) := by
      intro u h; rw [defectRow_one_eq]; ring
    have br : UO 0 (fun u h => RP (u + h / 2) h * (AA (u + h) h * PiP u h 0 1 + h * BB (u + h) h * PiP u h 1 1)
          + RP (u - h / 2) h * (AA (u - h) h * PiM u h 0 1 + h * BB (u - h) h * PiM u h 1 1)
          - RQ u h * (h * BB u h)) :=
      ((RPp.mul ((hAp.mul (hbP 0 1)).add ((hh.mul hBp).mul (hbP 1 1)))).add
        (RPm.mul ((hAm.mul (hbM 0 1)).add ((hh.mul hBm).mul (hbM 1 1))))).sub (hRQ.mul (hh.mul hB0))
    exact (UO.hpow_mul n br).congr fun u h => by rw [e]

/-- The symbol parts are additive in the defect: the defect of `(P + P', Q + Q')` is the sum. -/
lemma defectRow_add_symbols (pp pp' qq qq' AA BB : ℝ → ℝ → ℝ) (u h : ℝ) (k : Fin 2) :
    defectRow (fun s h => pp s h + pp' s h) (fun u h => qq u h + qq' u h) AA BB PiP PiM u h k =
      defectRow pp qq AA BB PiP PiM u h k + defectRow pp' qq' AA BB PiP PiM u h k := by
  fin_cases k <;> simp [defectRow, vrow, rowMul] <;> ring

/-- `A = g₀ + O(h²)` for `k ≥ 1` and bounded `g_i`. -/
lemma Aans_sub_UO2 {g : ℕ → ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k) (hg : ∀ i < k, ∃ C, ∀ x, |g i x| ≤ C) :
    UO 2 (fun u h => Aans g k u h - g 0 u) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e : ∀ u h, Aans g (k + 1) u h - g 0 u = ∑ i ∈ range k, h ^ (2 * (i + 1)) * g (i + 1) u := by
    intro u h
    simp [Aans, Finset.sum_range_succ']
  refine (UO.sum (range k) (f := fun i u h => h ^ (2 * (i + 1)) * g (i + 1) u) fun i hi => ?_).congr
    fun u h => (e u h).symm
  have hgi : UO 0 (fun u (_ : ℝ) => g (i + 1) u) :=
    UO0_of_fun (hg (i + 1) (by have := Finset.mem_range.mp hi; omega))
  have := UO.hpow_mul (2 * (i + 1)) hgi
  exact this.mono (by omega)

/-- Uniform lower bound for `|A|` (`A = g₀ + O(h²)`, `g₀ ≥ m₀ > 0`). -/
lemma Aans_lower {g : ℕ → ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k) (hg : ∀ i < k, ∃ C, ∀ x, |g i x| ≤ C)
    {m0 : ℝ} (hm0 : 0 < m0) (hgm : ∀ u, m0 ≤ g 0 u) :
    ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ u h, |h| < δ → m ≤ |Aans g k u h| := by
  obtain ⟨C, δ, hC, hδ, hδ1, H⟩ := (Aans_sub_UO2 hk hg).norm
  refine ⟨m0 / 2, min δ (m0 / (2 * (C + 1))), by positivity, lt_min hδ (by positivity), fun u h hh => ?_⟩
  have h1 : |h| < δ := lt_of_lt_of_le hh (min_le_left _ _)
  have h2 : |h| < m0 / (2 * (C + 1)) := lt_of_lt_of_le hh (min_le_right _ _)
  have h3 := H u h h1
  have h4 : |h| ≤ 1 := (h1.trans_le hδ1).le
  have h5 : |h| ^ 2 ≤ |h| := by nlinarith [abs_nonneg h]
  have h6 : C * |h| ^ 2 ≤ m0 / 2 := by
    calc C * |h| ^ 2 ≤ C * |h| := mul_le_mul_of_nonneg_left h5 hC
      _ ≤ (C + 1) * |h| := by nlinarith [abs_nonneg h]
      _ ≤ (C + 1) * (m0 / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h2.le (by linarith)
      _ = m0 / 2 := by field_simp
  have h7 : g 0 u - |Aans g k u h - g 0 u| ≤ |Aans g k u h| := by
    have := abs_sub_abs_le_abs_sub (g 0 u) (Aans g k u h)
    rw [abs_of_pos (lt_of_lt_of_le hm0 (hgm u))] at this
    rw [abs_sub_comm] at this
    linarith
  linarith [hgm u]

end Claims

-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JacobiEigenvectors.Engine.lA_UO2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.lA_UO2

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.lB_UO3_of_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.lB_UO3_of_adj

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.lB_UO3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.lB_UO3

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.dFA_UO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.dFA_UO1

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.dFB_UO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.dFB_UO

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.defect_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.defect_remainder

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.Aans_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.Aans_lower

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.Mdev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.Mdev


end FormalResearch.JacobiEigenvectors.Engine

end

end
