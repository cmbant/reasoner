module

public import FormalResearch.JacobiEigenvectors.Engine.CorrectorDefect
public import FormalResearch.JacobiEigenvectors.Engine.Kernel

/-!
# Paper J engine, L1.2 (part 3): the correctors and the defect order, `thm:eng-corr`

Source: Paper J, `engine.tex`, Section 2, `thm:eng-corr` ("Every order", eq:eng-transport, eq:eng-defect-order) with `lem:eng-transport`;
proof in `app_engine.tex`, "Proof of Theorem `thm:eng-corr`" (hypotheses `(H_k)`, steps `(a)_k`, `(b)_k`, remainders).  Namespace
`FormalResearch.JacobiEigenvectors.Engine`; builds on `CorrectorDefect` (facts (i)--(iii)), `CorrectorOrder` (uniform orders, parity lift),
`Defect` (parity, Green identity) and `Kernel` (`transport_solution`).

## Statement formalised
`CorrSetting K` collects the standing hypotheses of the theorem and `Correctors K` the recursively defined correctors:

* `CorrSetting`: a symplectic ladder (SM1)--(SM3) for the smooth parts `P, Q` (`ladder`), the polynomial parts `P, Q` even in `h`,
  the Langer condition (eq:eng-langer) (`langer`), bond nondegeneracy (`nondeg`), `M₀ := P₀ Π₋(·,0)₂₁ = Ω₀²V₀ ∈ BSmooth 2`
  (eq:eng-omega; the paper's `Ω₀²` is `M₀/V₀`, and `q_V = -4 M₀`), and `SymbolExp (2K+3)`: the analytic input (finitely many Taylor
  expansions of the symbols; see `CorrectorDefect`).
* `Correctors`: `g₀ = √(c₀/V₀)` with `c₀/V₀ > 0` and `g₀ ≥ m₀ > 0`; `g_i ∈ BSmooth (2K+3)` (`i ≤ K`), `b_i = B_{2i-1} ∈ BSmooth (2K+3)`
  (`1 ≤ i ≤ K`); and the two recursions of the theorem, in the universally quantified form
  `(a)_k`: for every function `a` that is the coefficient of `h^{2k}` of `𝔄^tot` of the ansatz built so far, `𝒯[b_k] = -a` (eq:eng-transport);
  `(b)_k`: for every `f` that is the coefficient of `h^{2k}` of `F_cas` of the ansatz built so far, `2 V₀ g₀ g_k = c_k - f`
  (this is `g_{2k} = (c_{2k} - F^{kn}_{2k})/(2V₀g₀)` without the division).  "Coefficient of `h^{2k}`" is the unique `a` with
  `𝔄^tot = h^{2k} a + O(h^{2k+2})` (resp. `F_cas - Σ_{i<k} c_i h^{2i} = h^{2k} f + O(h^{2k+2})`); the proof shows that such `a`, `f` exist.
* `eng_corr` (**`thm:eng-corr`**, eq:eng-defect-order, smooth parts): for `1 ≤ m ≤ 2K+1` and the ansatz `v^{[m]} = (A^{[m]}, hB^{[m]})`
  (`Ahat g m = Aans g ((m+1)/2)`, `Bhat b m = Bans b (m/2)`): `m` odd: `𝔄^tot = O(h^{m+1})`, `𝔅^tot = O(h^{m+2})`; `m` even: `𝔄^tot = O(h^{m+2})`,
  `𝔅^tot = O(h^{m+1})`, uniformly in `u ∈ ℝ`.
* `eng_corr_full`: with the remainders `h^{2K+2} R_P`, `h^{2K+2} R_Q` of (eq:eng-factor) (`R_P, R_Q` bounded): for `m ≤ 2K` the same
  orders hold; for `m = 2K+1`, `𝔄^tot = O(h^{m+1})` and `𝔅^tot = O(h^{m+1})`; in all cases `|𝔄^tot| + |𝔅^tot| = O(h^{m+1})`.
* `eng_corr_site`: consequence for the comparison sequence: `|h (L_h ψ̂)_j| ≤ C h^{m+1} (|w_j| + |w̃_j|)`, i.e. `(L_h ψ̂)_j = O(h^m)` times
  the size of `w_j, w̃_j`, at interior lattice sites, for the ladder with the full symbols.
* `transport_corrector` (`lem:eng-transport`(b) for `𝒯`): `B = -4S/√W` of `Kernel.transport_solution` satisfies `𝒯[B] = -f` for `M₀ = -q_V/4`,
  `q_V = (u - u_*) W`; this is the solvability of (a)_k at one simple turning point (regularity and `C^{p-3k}` bookkeeping of
  `prop:eng-corr1` is not formalised).
* `CorrectorExample`: `exCorrSetting`, `exCorrectors` (every hypothesis of `eng_corr` for an explicit `K = 1` instance with `𝒬_h = h² cos u`,
  `b₁ = -sin(u)/2`, `g₁ = (cos 2u - 1)/16`), `ex_eng_corr`, and `exDefect_m1_not_O3` (the order `h^{m+1}` is sharp: the correctors are needed).

## Differences from the paper
1. **Global domain.**  Uniformity over all `u ∈ ℝ`; the data are globally defined with globally bounded derivatives (`BSmooth`).
   (Paper: constants depend on sup norms over `I_u`.)  Together with the global form of the identities of `SymplecticLadder`.
2. **Analytic input `SymbolExp`** (see `CorrectorDefect`): the Taylor expansions of the composite symbol functions are a hypothesis, not
   derived from `C^r` regularity of `P_{2i}, Q_{2i}, Π_±`.
3. **Bond nondegeneracy** `∃ δ_D, ∀ s, 0 < |h| < δ_D → 𝒟²(s,h) ≠ 0`, i.e. `d2 s h ≠ 0` with the real function `d2 = 𝒟²` (the paper's hypothesis; used by the exact inverse formula `Π₊ = adj Π₋(·+h)`).
4. **Correctors as data.**  The correctors are given with their regularity (`BSmooth (2K+3)`, i.e. derivatives up to order `m+2` bounded for `m = 2K+1`
   as in the paper) and the relations (a)_k, (b)_k; existence/regularity of `b_k` for one simple turning point is `prop:eng-corr1` (not formalised;
   the solvability formula is `transport_corrector`).  The paper's "for any constant `c_{2k}`" is the sequence `c`.  The uniform positivity `g₀ ≥ m₀` replaces "`g₀ > 0` on `I_u`".
5. **`𝒟 ≥ 0` and `Ω₀²`.** Neither is used: `V₀ ≠ 0` (through `c₀/V₀ > 0`) and `M₀ = Ω₀²V₀` are all that enter.  (eq:eng-omega) is the definition of `Ω₀²`.
6. The Langer condition is stated with the 0-based entries `(0,0)` of `Π_±`.

7. **Order of the last term of `𝔅^tot`.**  The centred difference in `eq:eng-green` must be `O(h^{2k+3})`, while the
   stated expansion `F_cas = c₀ + … + c_{2k}h^{2k} + O(h^{2k+2})` alone gives only `O(h^{2k+2})` (the `h^{2k+2}`
   coefficient is evaluated at `u ± h/2`).  The missing order comes from the parity of `𝔅^tot` (odd in `h`,
   `defectRow_parity`), which is what `D1_lift` uses (`PApprox.lift` with `σ = -1`); the same applies to (a)_k.  This
   is a proof route; the statement is unaffected.

Not formalised: derivation of `SymbolExp` from `C^r` data, `prop:eng-corr1` (regularity `C^{p-3k+1}`, holomorphic extension, dependence on `μ`), localisation to an interval `I_u`,
the hard-edge bond (`𝒟 = 0`), and the identification of `(A^{[m]}, hB^{[m]})` with a specific chart.
-/

@[expose] public section

noncomputable section

open Finset

namespace FormalResearch.JacobiEigenvectors.Engine

/-! ### Notation -/

/-- `𝔄^tot` of the ansatz `(Aans g k, Bans b l)`. -/
def dA (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (k l : ℕ) (u h : ℝ) : ℝ :=
  defectRow pp qq (Aans g k) (Bans b l) PiP PiM u h 0

/-- `𝔅^tot` of the ansatz `(Aans g k, Bans b l)`. -/
def dB (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (k l : ℕ) (u h : ℝ) : ℝ :=
  defectRow pp qq (Aans g k) (Bans b l) PiP PiM u h 1

/-- `F_cas^tot` of the ansatz `(Aans g k, Bans b l)`. -/
def FF (pp : ℝ → ℝ → ℝ) (PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (k l : ℕ) (s h : ℝ) : ℝ :=
  Fcas pp (Aans g k) (Bans b l) PiM s h

/-- The constant part `c₀ + c₁ h² + … + c_{k-1} h^{2k-2}` of `F_cas`. -/
def Pc (c : ℕ → ℝ) (k : ℕ) (h : ℝ) : ℝ := ∑ i ∈ range k, c i * h ^ (2 * i)

lemma Pc_even (c : ℕ → ℝ) (k : ℕ) (h : ℝ) : Pc c k (-h) = Pc c k h := by
  simp [Pc, pow_mul]

lemma Pc_succ (c : ℕ → ℝ) (k : ℕ) (h : ℝ) : Pc c (k + 1) h = Pc c k h + c k * h ^ (2 * k) := by
  simp [Pc, Finset.sum_range_succ]

/-- The ansatz `v^{[m]} = (A^{[m]}, h B^{[m]})` of the paper: `A^{[m]} = Aans g ((m+1)/2)`, `B^{[m]} = Bans b (m/2)`
(`m = 2k-1`: `(k, k-1)`; `m = 2k`: `(k, k)`). -/
def Ahat (g : ℕ → ℝ → ℝ) (m : ℕ) : ℝ → ℝ → ℝ := Aans g ((m + 1) / 2)

/-- See `Ahat`. -/
def Bhat (b : ℕ → ℝ → ℝ) (m : ℕ) : ℝ → ℝ → ℝ := Bans b (m / 2)

/-! ### The standing hypotheses -/

/-- The standing hypotheses of `thm:eng-corr` on the ladder and the symbols (see the module docstring). -/
structure CorrSetting (K : ℕ) (γ : ℝ) (dd d2 pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2)
    (w : Fin 2 → ℝ → ℝ → V2) (ω : ℝ → ℝ) : Prop where
  /-- (SM1)--(SM3) of `def:eng-ladder`. -/
  ladder : SymplecticLadder γ dd d2 pp qq PiP PiM w ω
  /-- `P_h` even in `h` (the polynomial part of (eq:eng-factor)). -/
  pp_even : ∀ s h, pp s (-h) = pp s h
  /-- `𝒬_h` even in `h`. -/
  qq_even : ∀ u h, qq u (-h) = qq u h
  /-- The analytic input: Taylor expansions of the symbols to order `2K + 3 = m + 2` for `m = 2K+1`. -/
  exp : SymbolExp (2 * K + 3) pp qq PiP PiM
  /-- Nondegenerate bonds: `𝒟²(s,h) ≠ 0` for `0 < |h| < δD` (the paper's `D^2 != 0`). -/
  nondeg : ∃ δD : ℝ, 0 < δD ∧ ∀ s h, 0 < |h| → |h| < δD → d2 s h ≠ 0
  /-- (eq:eng-langer): `P₀ (Π₊₁₁ + Π₋₁₁)(·,0) = Q₀`. -/
  langer : ∀ u, pp u 0 * (PiP u 0 0 0 + PiM u 0 0 0) = qq u 0
  /-- `M₀ = P₀ Π₋(·,0)₂₁ = Ω₀²V₀` (eq:eng-omega) is `C²` with bounded derivatives. -/
  M0_smooth : BSmooth 2 (M0fun pp PiM)

/-- The correctors `g_{2i} = g i`, `B_{2i-1} = b i`, the constants `c_{2i} = c i`, and the recursions (a)_k, (b)_k. -/
structure Correctors (K : ℕ) (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (c : ℕ → ℝ) : Prop where
  /-- `g₀ = √(c₀/V₀)`. -/
  g0 : ∀ u, g 0 u = Real.sqrt (c 0 / V0fun pp PiM u)
  /-- `c₀ ≠ 0` has the sign of `V₀` (so `V₀ ≠ 0`). -/
  c0_sign : ∀ u, 0 < c 0 / V0fun pp PiM u
  /-- `g₀ ≥ m₀ > 0` uniformly. -/
  g0_pos : ∃ m0 : ℝ, 0 < m0 ∧ ∀ u, m0 ≤ g 0 u
  g_reg : ∀ i, i ≤ K → BSmooth (2 * K + 3) (g i)
  b_reg : ∀ i, 1 ≤ i → i ≤ K → BSmooth (2 * K + 3) (b i)
  /-- (a)_k, eq:eng-transport: `𝒯[b_k] = -𝔄^{kn}_{2k}` for the ansatz `(Aans g k, Bans b (k-1))`. -/
  transport : ∀ k, 1 ≤ k → k ≤ K → ∀ a : ℝ → ℝ,
    UO (2 * k + 2) (fun u h => dA pp qq PiP PiM g b k (k - 1) u h - h ^ (2 * k) * a u) →
    ∀ u, transportOp (M0fun pp PiM) (b k) u = -a u
  /-- (b)_k: `g_{2k} = (c_{2k} - F^{kn}_{2k})/(2 V₀ g₀)` for the ansatz `(Aans g k, Bans b k)`. -/
  flux : ∀ k, 1 ≤ k → k ≤ K → ∀ f : ℝ → ℝ,
    UO (2 * k + 2) (fun s h => FF pp PiM g b k k s h - Pc c k h - h ^ (2 * k) * f s) →
    ∀ s, 2 * V0fun pp PiM s * g 0 s * g k s = c k - f s

/-! ### Parity, expansions and the Green bound for `𝔅^tot` -/

section Main

variable {K : ℕ} {γ : ℝ} {dd d2 pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}
  {g b : ℕ → ℝ → ℝ} {c : ℕ → ℝ}

lemma CorrSetting.dA_even (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (k l : ℕ) (u h : ℝ) :
    dA pp qq PiP PiM g b k l u (-h) = dA pp qq PiP PiM g b k l u h :=
  (defectRow_parity S.ladder S.pp_even S.qq_even (Aans_even g k) (Bans_even b l) u h).1

lemma CorrSetting.dB_odd (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (k l : ℕ) (u h : ℝ) :
    dB pp qq PiP PiM g b k l u (-h) = -dB pp qq PiP PiM g b k l u h :=
  (defectRow_parity S.ladder S.pp_even S.qq_even (Aans_even g k) (Bans_even b l) u h).2

lemma CorrSetting.FF_even (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) {δD : ℝ}
    (hD : ∀ s h, 0 < |h| → |h| < δD → d2 s h ≠ 0) (k l : ℕ) (s h : ℝ) (hh : |h| < δD) :
    FF pp PiM g b k l s (-h) = FF pp PiM g b k l s h := by
  by_cases h0 : h = 0
  · subst h0; simp
  · exact Fcas_even S.ladder S.pp_even (Aans_even g k) (Bans_even b l) s h (hD s h (abs_pos.mpr h0) hh)

lemma CorrSetting.dB_zero (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (k l : ℕ) (u : ℝ) :
    dB pp qq PiP PiM g b k l u 0 = 0 := by
  have := S.dB_odd (g := g) (b := b) k l u 0
  rw [neg_zero] at this
  linarith

/-- Expansions of the defect components and of `F_cas` of the ansatz. -/
lemma CorrSetting.ans_papprox (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω)
    (C : Correctors K pp qq PiP PiM g b c) {k l : ℕ} (hk : k ≤ K + 1) (hl : l ≤ K) :
    PApprox (2 * K + 3) (dA pp qq PiP PiM g b k l) ∧ PApprox (2 * K + 3) (dB pp qq PiP PiM g b k l) ∧
      PApprox (2 * K + 3) (FF pp PiM g b k l) := by
  have hgk : ∀ i < k, BSmooth (2 * K + 3) (g i) := fun i hi => C.g_reg i (by omega)
  have hbl : ∀ i, 1 ≤ i → i ≤ l → BSmooth (2 * K + 3) (b i) := fun i h1 h2 => C.b_reg i h1 (by omega)
  have Ap := Aans_papprox' hgk 1 (σ := fun u h => u + h) (fun u h => by ring)
  have Am := Aans_papprox' hgk (-1) (σ := fun u h => u - h) (fun u h => by ring)
  have A0 := Aans_papprox_zero hgk
  have Bp := Bans_papprox' hbl 1 (σ := fun u h => u + h) (fun u h => by ring)
  have Bm := Bans_papprox' hbl (-1) (σ := fun u h => u - h) (fun u h => by ring)
  have B0 := Bans_papprox_zero hbl
  have Ah := Aans_papprox' hgk (1 / 2) (σ := fun u h => u + h / 2) (fun u h => by ring)
  have Ah' := Aans_papprox' hgk (-1 / 2) (σ := fun u h => u - h / 2) (fun u h => by ring)
  have Bh := Bans_papprox' hbl (1 / 2) (σ := fun u h => u + h / 2) (fun u h => by ring)
  have Bh' := Bans_papprox' hbl (-1 / 2) (σ := fun u h => u - h / 2) (fun u h => by ring)
  exact ⟨defect_papprox S.exp Ap Am A0 Bp Bm B0 0, defect_papprox S.exp Ap Am A0 Bp Bm B0 1,
    Fcas_papprox S.exp Ah Ah' Bh Bh'⟩

/-- **The Green bound.** If `F_cas - P(h) = O(h^n)` (`P` independent of `u`) and `h B 𝔄 = O(h^n)`, then `𝔅^tot = O(h^n)`:
the Casoratian--Green identity (eq:eng-green) divides by `A ≥ m > 0`. -/
lemma CorrSetting.D1_bound (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) {AA BB : ℝ → ℝ → ℝ}
    (hAe : ∀ u h, AA u (-h) = AA u h) (hBe : ∀ u h, BB u (-h) = BB u h) {n : ℕ} (_hn : 1 ≤ n)
    (hlow : ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ u h, |h| < δ → m ≤ |AA u h|)
    (hBD : UO n (fun u h => h * BB u h * defectRow pp qq AA BB PiP PiM u h 0))
    {P : ℝ → ℝ} (hF : UO n (fun s h => Fcas pp AA BB PiM s h - P h)) :
    UO n (fun u h => defectRow pp qq AA BB PiP PiM u h 1) := by
  obtain ⟨δD, hδD, hD⟩ := S.nondeg
  have hX : UO n (fun u h => h * BB u h * defectRow pp qq AA BB PiP PiM u h 0
      - ((Fcas pp AA BB PiM (u + h / 2) h - P h) - (Fcas pp AA BB PiM (u - h / 2) h - P h))) :=
    hBD.sub (hF.shift_half.sub hF.shift_neg_half)
  have hAD : UO n (fun u h => AA u h * defectRow pp qq AA BB PiP PiM u h 1) := by
    refine UO.congr_loc hX hδD (fun u h hh => ?_)
    by_cases h0 : h = 0
    · subst h0
      have := (defectRow_parity S.ladder S.pp_even S.qq_even hAe hBe u 0).2
      rw [neg_zero] at this
      have h1 : defectRow pp qq AA BB PiP PiM u 0 1 = 0 := by linarith
      simp [h1]
    · have hD' : Dp d2 u h ≠ 0 := hD (u + h / 2) h (abs_pos.mpr h0) hh
      have := green_identity (AA := AA) (BB := BB) S.ladder u h hD'
      linear_combination (-1 : ℝ) * this
  exact UO.div_of_lower hlow hAD

/-- Odd lift for `𝔅^tot`. -/
lemma CorrSetting.D1_lift (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) {AA BB : ℝ → ℝ → ℝ}
    (hAe : ∀ u h, AA u (-h) = AA u h) (hBe : ∀ u h, BB u (-h) = BB u h) {n : ℕ} (hn : Even n)
    (hpa : PApprox (n + 1) (fun u h => defectRow pp qq AA BB PiP PiM u h 1))
    (h0 : UO n (fun u h => defectRow pp qq AA BB PiP PiM u h 1)) :
    UO (n + 1) (fun u h => defectRow pp qq AA BB PiP PiM u h 1) := by
  refine PApprox.lift (n := n) (σ := -1) (δ0 := 1) (by rw [hn.neg_one_pow]; norm_num) hpa h0 one_pos
    (fun u h _ => ?_)
  have := (defectRow_parity S.ladder S.pp_even S.qq_even hAe hBe u h).2
  rw [this]; ring

lemma Pc_papprox (c : ℕ → ℝ) (k N : ℕ) : PApprox N (fun _ h => Pc c k h) := by
  unfold Pc
  exact PApprox.sum (range k) fun i _ => (PApprox.const (c i)).mul (PApprox.hpow (2 * i))

lemma dA_succ_A (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (k l : ℕ) (u h : ℝ) :
    dA pp qq PiP PiM g b (k + 1) l u h = dA pp qq PiP PiM g b k l u h + h ^ (2 * k) * lA pp qq PiP PiM (g k) u h :=
  defect0_stepA g b k l u h

lemma dA_succ_B (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (k l : ℕ) (u h : ℝ) :
    dA pp qq PiP PiM g b k (l + 1) u h = dA pp qq PiP PiM g b k l u h + h ^ (2 * l + 1) * lB pp PiP PiM (b (l + 1)) u h :=
  defect0_stepB g b k l u h

lemma dA_zero_zero (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (u h : ℝ) :
    dA pp qq PiP PiM g b 0 0 u h = 0 := by
  simp [dA, defectRow_zero_eq, Aans, Bans]

lemma Correctors.g0_sq (C : Correctors K pp qq PiP PiM g b c) (u : ℝ) :
    g 0 u ^ 2 * V0fun pp PiM u = c 0 := by
  have hpos := C.c0_sign u
  have hV : V0fun pp PiM u ≠ 0 := by
    intro h0; rw [h0, div_zero] at hpos; exact lt_irrefl _ hpos
  rw [C.g0 u, Real.sq_sqrt hpos.le]
  field_simp

lemma Correctors.lower (C : Correctors K pp qq PiP PiM g b c) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ K + 1) :
    ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ u h, |h| < δ → m ≤ |Aans g k u h| := by
  obtain ⟨m0, hm0, hgm⟩ := C.g0_pos
  exact Aans_lower hk1 (fun i hi => (C.g_reg i (by omega)).bdd) hm0 hgm

lemma Correctors.Bans_bdd (C : Correctors K pp qq PiP PiM g b c) {l : ℕ} (hl : l ≤ K) :
    UO 0 (Bans b l) := by
  have hbl : ∀ i, 1 ≤ i → i ≤ l → BSmooth (2 * K + 3) (b i) := fun i h1 h2 => C.b_reg i h1 (by omega)
  exact (Bans_papprox_zero hbl).bdd

/-- **Base case `m = 1`**: the ansatz `(g₀, 0)`. -/
theorem PInv_zero (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c) :
    UO 2 (dA pp qq PiP PiM g b 1 0) ∧ UO 3 (dB pp qq PiP PiM g b 1 0) ∧
      UO 2 (fun s h => FF pp PiM g b 1 0 s h - Pc c 1 h) := by
  obtain ⟨δD, hδD, hD⟩ := S.nondeg
  have hd0 : UO 2 (dA pp qq PiP PiM g b 1 0) := by
    refine (lA_UO2 (N := 2 * K + 3) (by omega) S.exp S.ladder S.pp_even S.qq_even S.langer
      ((C.g_reg 0 (by omega)).mono (by omega))).congr fun u h => ?_
    rw [dA_succ_A, dA_zero_zero]
    simp
  have ⟨_, hpaD1, hpaF⟩ := S.ans_papprox C (k := 1) (l := 0) (by omega) (by omega)
  have hF0 : ∀ s, FF pp PiM g b 1 0 s 0 = c 0 := by
    intro s
    have := Fcas_zero pp (Aans g 1) (Bans b 0) PiM s
    have e : Aans g 1 s 0 = g 0 s := Aans_zero_h g le_rfl s
    unfold FF
    rw [this, e, ← C.g0_sq s]
    simp [V0fun]
  have hP1 : ∀ h : ℝ, Pc c 1 h = c 0 := by intro h; simp [Pc]
  have hFP : UO 2 (fun s h => FF pp PiM g b 1 0 s h - Pc c 1 h) := by
    have h1 : UO 1 (fun s h => FF pp PiM g b 1 0 s h - Pc c 1 h) := by
      have := (hpaF.mono (by omega : 1 ≤ 2 * K + 3)).order1
      refine this.congr fun s h => ?_
      rw [hF0, hP1]
    have hpa : PApprox 2 (fun s h => FF pp PiM g b 1 0 s h - Pc c 1 h) :=
      (hpaF.mono (by omega)).sub ((Pc_papprox c 1 2))
    exact PApprox.lift (n := 1) (σ := 1) (δ0 := δD) (by norm_num) hpa h1 hδD
      (fun s h hh => by rw [one_mul, S.FF_even hD 1 0 s h hh, Pc_even])
  refine ⟨hd0, ?_, hFP⟩
  have hAe := Aans_even g 1
  have hBe := Bans_even b 0
  have h2 : UO 2 (dB pp qq PiP PiM g b 1 0) := by
    refine S.D1_bound (AA := Aans g 1) (BB := Bans b 0) hAe hBe (by norm_num) (C.lower le_rfl (by omega)) ?_ hFP
    refine (UO.zero 2).congr fun u h => ?_
    simp [Bans]
  exact S.D1_lift hAe hBe (n := 2) (by decide) (hpaD1.mono (by omega)) h2

/-- `P(j)`: the defect and flux invariants of the ansatz `(Aans g (j+1), Bans b j)`, i.e. `m = 2j+1`
(`𝔄 = O(h^{m+1})`, `𝔅 = O(h^{m+2})`, `F_cas - (c₀ + … + c_j h^{2j}) = O(h^{2j+2})`). -/
def PInv (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (j : ℕ) : Prop :=
  UO (2 * j + 2) (dA pp qq PiP PiM g b (j + 1) j) ∧ UO (2 * j + 3) (dB pp qq PiP PiM g b (j + 1) j) ∧
    UO (2 * j + 2) (fun s h => FF pp PiM g b (j + 1) j s h - Pc c (j + 1) h)

/-- `Q(j)`: the invariants of the ansatz `(Aans g (j+1), Bans b (j+1))`, i.e. `m = 2j+2`
(`𝔄 = O(h^{m+2})`, `𝔅 = O(h^{m+1})`). -/
def QInv (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (g b : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (j : ℕ) : Prop :=
  UO (2 * j + 4) (dA pp qq PiP PiM g b (j + 1) (j + 1)) ∧ UO (2 * j + 3) (dB pp qq PiP PiM g b (j + 1) (j + 1)) ∧
    UO (2 * j + 2) (fun s h => FF pp PiM g b (j + 1) (j + 1) s h - Pc c (j + 1) h)

theorem PInv_base (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c) :
    PInv pp qq PiP PiM g b c 0 := PInv_zero S C

/-- **Step (a)_{j+1}**: adding `h^{2j+1} b_{j+1}` to the second entry (the transport equation) removes the order `h^{2j+2}` of `𝔄^tot`;
the Green identity gives `𝔅^tot = O(h^{2j+2})` and parity `O(h^{2j+3})`. -/
theorem PInv_to_QInv (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c) {j : ℕ}
    (hj : j + 1 ≤ K) (hP : PInv pp qq PiP PiM g b c j) : QInv pp qq PiP PiM g b c j := by
  obtain ⟨hD0, hD1, hF⟩ := hP
  obtain ⟨δD, hδD, hD⟩ := S.nondeg
  have hN4 : 2 * j + 4 ≤ 2 * K + 3 := by omega
  have ⟨hpaD0, _, hpaF⟩ := S.ans_papprox C (k := j + 1) (l := j) (by omega) (by omega)
  have ⟨_, hpaD1', hpaF'⟩ := S.ans_papprox C (k := j + 1) (l := j + 1) (by omega) (by omega)
  -- the coefficient `a` of `h^{2j+2}` in `𝔄^tot`
  obtain ⟨a, _, ha⟩ := PApprox.exists_coeff (n := 2 * j + 2) (σ := 1) (δ0 := 1)
    (by rw [(show Even (2 * j + 2) from ⟨j + 1, by ring⟩).neg_one_pow]; norm_num) (hpaD0.mono hN4) hD0 one_pos
    (fun u h _ => by rw [one_mul]; exact S.dA_even (j + 1) j u h)
  have hTa : ∀ u, transportOp (M0fun pp PiM) (b (j + 1)) u = -a u := by
    refine C.transport (j + 1) (by omega) hj a ?_
    have e : 2 * (j + 1) + 2 = 2 * j + 2 + 2 := by ring
    rw [e]
    refine ha.congr fun u h => ?_
    simp only [Nat.add_sub_cancel]
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
  have hlB := lB_UO3 (N := 2 * K + 3) (by omega) S.exp S.ladder S.pp_even hδD hD S.M0_smooth
    ((C.b_reg (j + 1) (by omega) hj).mono (by omega))
  -- 𝔄 of the new ansatz
  have hq0 : UO (2 * j + 4) (dA pp qq PiP PiM g b (j + 1) (j + 1)) := by
    have := ha.add (UO.hpow_mul (2 * j + 1) hlB)
    have e : 2 * j + 2 + 2 = 2 * j + 4 := by ring
    have e' : 2 * j + 1 + 3 = 2 * j + 4 := by ring
    rw [e] at this
    rw [e'] at this
    refine this.congr fun u h => ?_
    rw [dA_succ_B]
    have := hTa u
    linear_combination (-(h ^ (2 * j + 2))) * this
  -- the flux
  have hΔ : UO (2 * j + 2) (fun s h => FF pp PiM g b (j + 1) (j + 1) s h - FF pp PiM g b (j + 1) j s h) := by
    have h1 := dFB_UO (N := 2 * K + 3) S.exp (g := g) (b := b) (k := j + 1) (l := j)
      (fun i hi => C.g_reg i (by omega)) (fun i h1 h2 => C.b_reg i h1 (by omega))
    have hpa : PApprox (2 * j + 1 + 1) (fun s h => FF pp PiM g b (j + 1) (j + 1) s h - FF pp PiM g b (j + 1) j s h) :=
      (hpaF'.mono (by omega)).sub (hpaF.mono (by omega))
    exact PApprox.lift (n := 2 * j + 1) (σ := 1) (δ0 := δD)
      (by rw [(show Odd (2 * j + 1) from ⟨j, rfl⟩).neg_one_pow]; norm_num) hpa h1 hδD
      (fun s h hh => by rw [one_mul, S.FF_even hD _ _ s h hh, S.FF_even hD _ _ s h hh])
  have hq2 : UO (2 * j + 2) (fun s h => FF pp PiM g b (j + 1) (j + 1) s h - Pc c (j + 1) h) :=
    (hF.add hΔ).congr fun s h => by ring
  refine ⟨hq0, ?_, hq2⟩
  -- 𝔅 of the new ansatz
  have hAe := Aans_even g (j + 1)
  have hBe := Bans_even b (j + 1)
  have hBD : UO (2 * j + 2) (fun u h => h * Bans b (j + 1) u h * defectRow pp qq (Aans g (j + 1)) (Bans b (j + 1)) PiP PiM u h 0) := by
    have hh : UO 1 (fun _ h => h) := (UO.hpow 1).congr fun _ _ => by simp
    have := ((hh.mul (C.Bans_bdd (l := j + 1) hj)).mul hq0)
    exact this.mono (by omega)
  have h2 : UO (2 * j + 2) (dB pp qq PiP PiM g b (j + 1) (j + 1)) :=
    S.D1_bound (AA := Aans g (j + 1)) (BB := Bans b (j + 1)) hAe hBe (by omega) (C.lower (by omega) (by omega)) hBD hq2
  exact S.D1_lift hAe hBe (n := 2 * j + 2) ⟨j + 1, by ring⟩ (hpaD1'.mono (by omega)) h2

/-- **Step (b)_{j+1}**: adding `h^{2j+2} g_{j+1}` to `A` with `g_{j+1} = (c_{j+1} - F^{kn})/(2V₀g₀)` makes the order `h^{2j+2}` of
`F_cas` the constant `c_{j+1}`; the Green identity and parity give `𝔅^tot = O(h^{2j+5})`. -/
theorem QInv_to_PInv (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c) {j : ℕ}
    (hj : j + 1 ≤ K) (hQ : QInv pp qq PiP PiM g b c j) : PInv pp qq PiP PiM g b c (j + 1) := by
  obtain ⟨hq0, hq1, hqF⟩ := hQ
  obtain ⟨δD, hδD, hD⟩ := S.nondeg
  have hN4 : 2 * j + 4 ≤ 2 * K + 3 := by omega
  have ⟨_, _, hpaF⟩ := S.ans_papprox C (k := j + 1) (l := j + 1) (by omega) (by omega)
  have ⟨hpaD0', hpaD1', hpaF'⟩ := S.ans_papprox C (k := j + 2) (l := j + 1) (by omega) (by omega)
  -- the coefficient `f` of `h^{2j+2}` in `F_cas`
  have hpaFP : PApprox (2 * j + 2 + 2) (fun s h => FF pp PiM g b (j + 1) (j + 1) s h - Pc c (j + 1) h) :=
    (hpaF.mono (by omega)).sub (Pc_papprox c (j + 1) _)
  obtain ⟨f, _, hf⟩ := PApprox.exists_coeff (n := 2 * j + 2) (σ := 1) (δ0 := δD)
    (by rw [(show Even (2 * j + 2) from ⟨j + 1, by ring⟩).neg_one_pow]; norm_num) hpaFP hqF hδD
    (fun s h hh => by rw [one_mul, S.FF_even hD _ _ s h hh, Pc_even])
  have hfl : ∀ s, 2 * V0fun pp PiM s * g 0 s * g (j + 1) s = c (j + 1) - f s := by
    refine C.flux (j + 1) (by omega) hj f ?_
    have e : 2 * (j + 1) + 2 = 2 * j + 2 + 2 := by ring
    rw [e]
    refine hf.congr fun u h => ?_
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
  -- boundedness of `2 V₀ g₀ g_{j+1}`
  have hbd : ∃ Cb, ∀ s, |2 * V0fun pp PiM s * g 0 s * g (j + 1) s| ≤ Cb := by
    obtain ⟨CV, δV, hδV, hV⟩ := (S.exp.cM 0 1).bdd'
    obtain ⟨C0, h0⟩ := (C.g_reg 0 (by omega)).bdd
    obtain ⟨C1, h1⟩ := (C.g_reg (j + 1) hj).bdd
    refine ⟨2 * |CV| * |C0| * |C1|, fun s => ?_⟩
    have hv : |V0fun pp PiM s| ≤ |CV| := by
      have := hV s 0 (by simpa using hδV)
      simp only [V0fun]
      simpa using this.trans (le_abs_self CV)
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    have a0 : |g 0 s| ≤ |C0| := (h0 s).trans (le_abs_self _)
    have a1 : |g (j + 1) s| ≤ |C1| := (h1 s).trans (le_abs_self _)
    have t1 : 2 * |V0fun pp PiM s| ≤ 2 * |CV| := by linarith
    exact mul_le_mul (mul_le_mul t1 a0 (abs_nonneg _) (by positivity)) a1 (abs_nonneg _) (by positivity)
  -- the variation of `F_cas`
  have hX1 := dFA_UO1 (N := 2 * K + 3) (by omega) S.exp (g := g) (b := b) (k := j + 1) (l := j + 1) (by omega)
    (fun i hi => C.g_reg i (by omega)) (fun i h1 h2 => C.b_reg i h1 (by omega))
  have hXpa : PApprox (2 * (j + 1) + 1 + 1) (fun s h => Fcas pp (Aans g (j + 1 + 1)) (Bans b (j + 1)) PiM s h
      - Fcas pp (Aans g (j + 1)) (Bans b (j + 1)) PiM s h
      - h ^ (2 * (j + 1)) * (2 * V0fun pp PiM s * g 0 s * g (j + 1) s)) := by
    refine ((hpaF'.mono (by omega)).sub (hpaF.mono (by omega))).sub ?_
    exact (PApprox.hpow_mul (2 * (j + 1)) (PApprox.of_bdd_fun hbd)).congr fun _ _ => rfl
  have hX : UO (2 * (j + 1) + 1 + 1) (fun s h => Fcas pp (Aans g (j + 1 + 1)) (Bans b (j + 1)) PiM s h
      - Fcas pp (Aans g (j + 1)) (Bans b (j + 1)) PiM s h
      - h ^ (2 * (j + 1)) * (2 * V0fun pp PiM s * g 0 s * g (j + 1) s)) :=
    PApprox.lift (n := 2 * (j + 1) + 1) (σ := 1) (δ0 := δD)
      (by rw [(show Odd (2 * (j + 1) + 1) from ⟨j + 1, rfl⟩).neg_one_pow]; norm_num) hXpa hX1 hδD
      (fun s h hh => by
        have e1 := S.FF_even (g := g) (b := b) hD (j + 1 + 1) (j + 1) s h hh
        have e2 := S.FF_even (g := g) (b := b) hD (j + 1) (j + 1) s h hh
        simp only [FF] at e1 e2
        rw [one_mul, e1, e2]
        simp [pow_mul])
  -- assemble the flux invariant
  have hF2 : UO (2 * (j + 1) + 2) (fun s h => FF pp PiM g b (j + 1 + 1) (j + 1) s h - Pc c (j + 1 + 1) h) := by
    have := hf.add hX
    refine this.congr fun s h => ?_
    simp only [FF, Pc_succ]
    have := hfl s
    linear_combination (-(h ^ (2 * (j + 1)))) * this
  -- 𝔄 of the new ansatz
  have hlA := lA_UO2 (N := 2 * K + 3) (by omega) S.exp S.ladder S.pp_even S.qq_even S.langer
    ((C.g_reg (j + 1) hj).mono (by omega))
  have hd0 : UO (2 * (j + 1) + 2) (dA pp qq PiP PiM g b (j + 1 + 1) (j + 1)) := by
    have := (hq0.mono (by omega : 2 * (j + 1) + 2 ≤ 2 * j + 4)).add (UO.hpow_mul (2 * (j + 1)) hlA)
    refine (this.mono (by omega)).congr fun u h => ?_
    rw [dA_succ_A pp qq PiP PiM g b (j + 1) (j + 1) u h]
  -- 𝔅 of the new ansatz
  have hAe := Aans_even g (j + 1 + 1)
  have hBe := Bans_even b (j + 1)
  have hBD : UO (2 * (j + 1) + 2) (fun u h => h * Bans b (j + 1) u h *
      defectRow pp qq (Aans g (j + 1 + 1)) (Bans b (j + 1)) PiP PiM u h 0) := by
    have hh : UO 1 (fun _ h => h) := (UO.hpow 1).congr fun _ _ => by simp
    have := ((hh.mul (C.Bans_bdd (l := j + 1) hj)).mul hd0)
    exact this.mono (by omega)
  have h2 : UO (2 * (j + 1) + 2) (dB pp qq PiP PiM g b (j + 1 + 1) (j + 1)) :=
    S.D1_bound (AA := Aans g (j + 1 + 1)) (BB := Bans b (j + 1)) hAe hBe (by omega)
      (C.lower (by omega) (by omega)) hBD (P := Pc c (j + 1 + 1)) hF2
  exact ⟨hd0, S.D1_lift hAe hBe (n := 2 * (j + 1) + 2) ⟨j + 2, by ring⟩ (hpaD1'.mono (by omega)) h2, hF2⟩

/-- Induction over `m`: all odd stages. -/
theorem PInv_all (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c) :
    ∀ j, j ≤ K → PInv pp qq PiP PiM g b c j := by
  intro j
  induction j with
  | zero => intro _; exact PInv_base S C
  | succ j ih =>
    intro hj
    exact QInv_to_PInv S C (by omega) (PInv_to_QInv S C (by omega) (ih (by omega)))

/-- Induction over `m`: all even stages. -/
theorem QInv_all (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c) :
    ∀ j, j + 1 ≤ K → QInv pp qq PiP PiM g b c j :=
  fun j hj => PInv_to_QInv S C hj (PInv_all S C j (by omega))

lemma Ahat_odd (g : ℕ → ℝ → ℝ) (j : ℕ) : Ahat g (2 * j + 1) = Aans g (j + 1) := by
  unfold Ahat; congr 1; omega

lemma Bhat_odd (b : ℕ → ℝ → ℝ) (j : ℕ) : Bhat b (2 * j + 1) = Bans b j := by
  unfold Bhat; congr 1; omega

lemma Ahat_even (g : ℕ → ℝ → ℝ) (j : ℕ) : Ahat g (2 * j + 2) = Aans g (j + 1) := by
  unfold Ahat; congr 1; omega

lemma Bhat_even (b : ℕ → ℝ → ℝ) (j : ℕ) : Bhat b (2 * j + 2) = Bans b (j + 1) := by
  unfold Bhat; congr 1; omega

/-- **`thm:eng-corr`** (eq:eng-defect-order, smooth parts of `P_h`, `𝒬_h`).  For `1 ≤ m ≤ 2K+1` the ansatz
`v^{[m]} = (A^{[m]}, h B^{[m]})` built from the correctors has defect components
`m` odd: `𝔄^tot = O(h^{m+1})`, `𝔅^tot = O(h^{m+2})`; `m` even: `𝔄^tot = O(h^{m+2})`, `𝔅^tot = O(h^{m+1})`,
uniformly in `u`. -/
theorem eng_corr (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 2 * K + 1) :
    (Odd m → UO (m + 1) (fun u h => defectRow pp qq (Ahat g m) (Bhat b m) PiP PiM u h 0) ∧
        UO (m + 2) (fun u h => defectRow pp qq (Ahat g m) (Bhat b m) PiP PiM u h 1)) ∧
    (Even m → UO (m + 2) (fun u h => defectRow pp qq (Ahat g m) (Bhat b m) PiP PiM u h 0) ∧
        UO (m + 1) (fun u h => defectRow pp qq (Ahat g m) (Bhat b m) PiP PiM u h 1)) := by
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨h0, h1, -⟩ := PInv_all S C j (by omega)
    rw [Ahat_odd, Bhat_odd]
    exact ⟨h0, h1⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 2 := ⟨i - 1, by omega⟩
    obtain ⟨h0, h1, -⟩ := QInv_all S C j (by omega)
    rw [Ahat_even, Bhat_even]
    exact ⟨h0, h1⟩

/-- Bounds for the ansatz entries (needed for the remainders). -/
lemma Correctors.ans_bdd (C : Correctors K pp qq PiP PiM g b c) {k l : ℕ} (hk : k ≤ K + 1) (hl : l ≤ K) :
    UO 0 (fun u h => Aans g k (u + h) h) ∧ UO 0 (fun u h => Aans g k (u - h) h) ∧ UO 0 (Aans g k) ∧
    UO 0 (fun u h => Bans b l (u + h) h) ∧ UO 0 (fun u h => Bans b l (u - h) h) ∧ UO 0 (Bans b l) := by
  have hgk : ∀ i < k, BSmooth (2 * K + 3) (g i) := fun i hi => C.g_reg i (by omega)
  have hbl : ∀ i, 1 ≤ i → i ≤ l → BSmooth (2 * K + 3) (b i) := fun i h1 h2 => C.b_reg i h1 (by omega)
  exact ⟨(Aans_papprox' hgk 1 (σ := fun u h => u + h) (fun u h => by ring)).bdd,
    (Aans_papprox' hgk (-1) (σ := fun u h => u - h) (fun u h => by ring)).bdd,
    (Aans_papprox_zero hgk).bdd,
    (Bans_papprox' hbl 1 (σ := fun u h => u + h) (fun u h => by ring)).bdd,
    (Bans_papprox' hbl (-1) (σ := fun u h => u - h) (fun u h => by ring)).bdd,
    (Bans_papprox_zero hbl).bdd⟩

/-- **`thm:eng-corr` with the remainders of (eq:eng-factor).**  Let `P_h = P + h^{2K+2} R_P`, `𝒬_h = Q + h^{2K+2} R_Q` with bounded
`R_P, R_Q` (no regularity).  For `m ≤ 2K` the orders of `eng_corr` are unchanged; for `m = 2K+1`, `𝔄^tot = O(h^{m+1})` and the
remainders add `O(h^{m+1})` to `𝔅^tot`; in all cases both components of the defect are `O(h^{m+1})`. -/
theorem eng_corr_full (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c)
    {RP RQ : ℝ → ℝ → ℝ} (hRP : UO 0 RP) (hRQ : UO 0 RQ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 * K + 1) :
    (∀ k : Fin 2, UO (m + 1) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
        (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b m) PiP PiM u h k)) ∧
    (m ≤ 2 * K →
      (Odd m → UO (m + 1) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b m) PiP PiM u h 0) ∧
          UO (m + 2) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b m) PiP PiM u h 1)) ∧
      (Even m → UO (m + 2) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b m) PiP PiM u h 0) ∧
          UO (m + 1) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b m) PiP PiM u h 1))) := by
  -- bounds for the ansatz entries at stage `m`
  have hk : (m + 1) / 2 ≤ K + 1 := by omega
  have hl : m / 2 ≤ K := by omega
  obtain ⟨Ap, Am, A0, Bp, Bm, B0⟩ := C.ans_bdd hk hl
  have hrem : ∀ k : Fin 2, UO (2 * K + 2) (fun u h => defectRow (fun s h => h ^ (2 * K + 2) * RP s h)
      (fun u h => h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b m) PiP PiM u h k) :=
    fun k => defect_remainder (n := 2 * K + 2) S.exp.bddP S.exp.bddM hRP hRQ Ap Am A0 Bp Bm B0 k
  have hsplit : ∀ (k : Fin 2) (u h : ℝ),
      defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h) (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
        (Ahat g m) (Bhat b m) PiP PiM u h k
      = defectRow pp qq (Ahat g m) (Bhat b m) PiP PiM u h k
        + defectRow (fun s h => h ^ (2 * K + 2) * RP s h) (fun u h => h ^ (2 * K + 2) * RQ u h)
          (Ahat g m) (Bhat b m) PiP PiM u h k := fun k u h =>
    defectRow_add_symbols (pp := pp) (pp' := fun s h => h ^ (2 * K + 2) * RP s h) (qq := qq)
      (qq' := fun u h => h ^ (2 * K + 2) * RQ u h) _ _ u h k
  have key : ∀ (k : Fin 2) (n : ℕ), n ≤ 2 * K + 2 →
      UO n (fun u h => defectRow pp qq (Ahat g m) (Bhat b m) PiP PiM u h k) →
      UO n (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
        (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b m) PiP PiM u h k) := by
    intro k n hn hs
    exact (hs.add ((hrem k).mono hn)).congr fun u h => (hsplit k u h).symm
  obtain ⟨hodd, heven⟩ := eng_corr S C hm1 hm
  refine ⟨fun k => ?_, fun hm2 => ⟨fun ho => ?_, fun he => ?_⟩⟩
  · rcases Nat.even_or_odd m with he | ho
    · obtain ⟨h0, h1⟩ := heven he
      fin_cases k
      · exact key 0 (m + 1) (by omega) (h0.mono (by omega))
      · exact key 1 (m + 1) (by omega) h1
    · obtain ⟨h0, h1⟩ := hodd ho
      fin_cases k
      · exact key 0 (m + 1) (by omega) h0
      · exact key 1 (m + 1) (by omega) (h1.mono (by omega))
  · obtain ⟨h0, h1⟩ := hodd ho
    exact ⟨key 0 (m + 1) (by omega) h0, key 1 (m + 2) (by omega) h1⟩
  · obtain ⟨h0, h1⟩ := heven he
    exact ⟨key 0 (m + 2) (by omega) h0, key 1 (m + 1) (by omega) h1⟩

/-- The ladder fields do not depend on the symbols `P`, `Q`. -/
lemma SymplecticLadder.of_symbols {γ : ℝ} {dd d2 pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2}
    {ω : ℝ → ℝ} (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (pp' qq' : ℝ → ℝ → ℝ) :
    SymplecticLadder γ dd d2 pp' qq' PiP PiM w ω :=
  ⟨L.wronsk, L.wronsk_ne, L.shift_up, L.shift_dn, L.d2_up, L.d2_dn, L.det_up, L.det_dn, L.prod, L.par_D, L.par_Pi⟩

/-- **The comparison sequence.**  At interior lattice sites (`IsSitePos`) the sequence `ψ̂^{(α)}_j = v^{[m]}(u_j,h)·𝐰^{(α)}_j` satisfies
`|h (L_h ψ̂)_j| ≤ C h^{m+1} (|w_j| + |w̃_j|)`, i.e. `(L_h ψ̂)_j = O(h^m)` times the size of `w_j, w̃_j` (`siteLop = h (L_h ψ̂)_j`), for the full
symbols `P_h = P + h^{2K+2} R_P`, `𝒬_h = Q + h^{2K+2} R_Q`. -/
theorem eng_corr_site (S : CorrSetting K γ dd d2 pp qq PiP PiM w ω) (C : Correctors K pp qq PiP PiM g b c)
    {RP RQ : ℝ → ℝ → ℝ} (hRP : UO 0 RP) (hRQ : UO 0 RQ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 * K + 1) :
    ∃ C₁ δ : ℝ, 0 < δ ∧ ∀ (α : Fin 2) (u h : ℝ), 0 < h → h < δ → IsSitePos γ h u →
      |siteLop dd (fun s h => pp s h + h ^ (2 * K + 2) * RP s h) (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
          (Ahat g m) (Bhat b m) w α u h|
        ≤ C₁ * h ^ (m + 1) * (|w α u h 0| + |w α u h 1|) := by
  obtain ⟨h0, -⟩ := eng_corr_full S C hRP hRQ hm1 hm
  obtain ⟨C0, δ0, hC0, hδ0, hδ01, H0⟩ := (h0 0).norm
  obtain ⟨C1', δ1, hC1, hδ1, hδ11, H1⟩ := (h0 1).norm
  refine ⟨max C0 C1', min δ0 δ1, lt_min hδ0 hδ1, fun α u h hh hlt hs => ?_⟩
  have hL := S.ladder.of_symbols (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
    (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
  rw [defect_identity_interior hL (Ahat g m) (Bhat b m) α u h hh hs]
  have a0 := H0 u h (by rw [abs_of_pos hh]; exact lt_of_lt_of_le hlt (min_le_left _ _))
  have a1 := H1 u h (by rw [abs_of_pos hh]; exact lt_of_lt_of_le hlt (min_le_right _ _))
  rw [abs_of_pos hh] at a0 a1
  have hp : 0 ≤ h ^ (m + 1) := by positivity
  calc |defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h) (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
          (Ahat g m) (Bhat b m) PiP PiM u h 0 * w α u h 0
        + defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h) (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
          (Ahat g m) (Bhat b m) PiP PiM u h 1 * w α u h 1|
      ≤ |defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h) (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
          (Ahat g m) (Bhat b m) PiP PiM u h 0| * |w α u h 0|
        + |defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h) (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
          (Ahat g m) (Bhat b m) PiP PiM u h 1| * |w α u h 1| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ (max C0 C1' * h ^ (m + 1)) * |w α u h 0| + (max C0 C1' * h ^ (m + 1)) * |w α u h 1| := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right (a0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_right (a1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)) (abs_nonneg _)
    _ = max C0 C1' * h ^ (m + 1) * (|w α u h 0| + |w α u h 1|) := by ring

/-- **Solvability of (a)_k at one simple turning point** (`lem:eng-transport`(b), `prop:eng-corr1`).  If `M₀ = Ω₀²V₀ = -q_V/4` with
`q_V = (u - u_*) W`, `W > 0` of class `C¹` on `(a,b) ∋ u_*`, and `f` is `C¹`, then `B = -4 S/√W` of `Kernel.transport_solution`
(`S(u) = ∫₀¹ f/√W (u_* + (u-u_*)t²) dt`, eq:eng-G8) satisfies the transport equation `𝒯[B] = -f` of (eq:eng-transport)
at every point of `(a,b)`.  (Regularity bookkeeping `C^{p-3k+1}` of `prop:eng-corr1` and the uniqueness among bounded solutions are not formalised.) -/
theorem transport_corrector (a b ustar : ℝ) (hJ : ustar ∈ Set.Ioo a b) (f f' W W' : ℝ → ℝ)
    (hWpos : ∀ y ∈ Set.Ioo a b, 0 < W y) (hWd : ∀ y ∈ Set.Ioo a b, HasDerivAt W (W' y) y)
    (hWc : ContinuousOn W' (Set.Ioo a b))
    (hfd : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y) (hfc : ContinuousOn f' (Set.Ioo a b))
    (M0 : ℝ → ℝ) (hM0 : ∀ y ∈ Set.Ioo a b, M0 y = -((y - ustar) * W y) / 4)
    (u : ℝ) (hu : u ∈ Set.Ioo a b) :
    transportOp M0 (fun v => -4 * transportS ustar f W v / Real.sqrt (W v)) u = -f u := by
  obtain ⟨B', hB, heq⟩ := transport_solution a b ustar hJ f f' W W' hWpos hWd hWc hfd hfc u hu
  have hq : HasDerivAt (fun y => -((y - ustar) * W y) / 4)
      (-(1 * W u + (u - ustar) * W' u) / 4) u :=
    ((((hasDerivAt_id u).sub_const ustar).mul (hWd u hu)).neg).div_const 4
  have hM : HasDerivAt M0 (-(1 * W u + (u - ustar) * W' u) / 4) u := by
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hu] with y hy using hM0 y hy
  unfold transportOp
  rw [hB.deriv, hM.deriv, hM0 u hu]
  linear_combination (1 / 2 : ℝ) * heq

end Main

-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JacobiEigenvectors.Engine.PInv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.PInv_zero

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.PInv_to_QInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.PInv_to_QInv

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.QInv_to_PInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.QInv_to_PInv

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.eng_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.eng_corr


/-- info: 'FormalResearch.JacobiEigenvectors.Engine.eng_corr_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.eng_corr_full

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.transport_corrector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.transport_corrector

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.eng_corr_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.eng_corr_site


end FormalResearch.JacobiEigenvectors.Engine

end

end
