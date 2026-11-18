module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroAux

/-!
# Paper J, Layer 2: the analytic core of Step 0 (upper bound for `B_n + a_n + a_{n-1}`)

Part of plan item L2.C8 (the theorems are in `TheoremA/StepZero.lean`).  Source: Paper J `app_thmA.tex`, Step 0 of the proof of `prop:tha-W2` ("where the eigenvalues are").

## What is proved

`CoreReg.upper`: for `P` compact, `G_0 in C^2` and `B_0` continuous (jointly in `(mu, u)`), `|G_h - G_0|, |B_h - B_0| <= C_0 h^e` on `[0,L]` (`e <= 2`, `h <= 1`), `G_0 >= g_* > 0`
and the maximum `X_s^+` of `f_+` attained only at an interior point (`UpHyp`), there are `C, h_0` (uniform in `mu in P`) with
`B_n + a_n + a_{n-1} <= X_s^+ + C h^e` at every site `0 <= n <= N`, `h <= h_0`.  Chain:

1. `bondA_le`, `sqrt_perturb_le`: `a_n <= sqrt E_0(s_n) + C_a h^e` (`s_n = (n+1) h`, `s_{-1} = 0`, `s_N = L`), the hard-edge factor `s (L-s)` cancels in `|sqrt(q G_h) - sqrt(q G_0)|`.
2. `CoreReg.edge_data` (compactness of `P`, no Hausdorff property needed): `f_+ + c <= X_s^+` within `delta` of the two hard edges, uniformly in `mu` (`f_+(0), f_+(L) < X_s^+`
   because the maximiser is interior, and `mu -> X_s^+(mu)` is continuous by `IsCompact.continuous_sSup`), and a uniform modulus of continuity of `sqrt E_0`.
3. `sqrt_E0_sym_le` (via `E0_second_diff`, `second_diff_le`, `sqrt_le_tangent`): away from the edges the two symmetric samples `sqrt E_0(u +- h/2)` exceed `2 sqrt E_0(u)` by `<= C h^2`
   (the odd Taylor terms cancel: the paper's "symmetric samples" argument), with `C` from uniform bounds of `G_0, G_0', G_0''`.
4. `CoreReg.upper` combines the edge case (sum `<= X_s^+ - c/2`) and the interior case (`<= f_+(u_n) + C h^2 <= X_s^+ + C h^2`).

## Differences from the paper

* The edge region is handled by a compactness/modulus argument (no explicit `O(h^2 u^{-3/2})`, no separate site `n = 0`): the same statement `<= X_s^+ + C h^e` follows.
* Only `G_0 >= g_*` and the *uniqueness and interiority* of the maximiser of `f_+` from (H1), (H3) are used; (H2) and the curvature sign `f_+'' < 0` are not needed for Step 0.
* `h <= 1` is assumed in the remainders (the constants are chosen before `N`, so this costs nothing).

## Not formalised

Explicit values of the constants.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

section JetFacts

variable {Par : Type*} [TopologicalSpace Par]

lemma JetReg.mono {f : Par → ℝ → ℝ} {K : Set Par} {L : ℝ} {r r' : ℕ} (h : JetReg f K L r) (hr : r' ≤ r) :
    JetReg f K L r' :=
  ⟨fun μ hμ => (h.1 μ hμ).of_le (by exact_mod_cast hr), fun i hi => h.2 i (hi.trans hr)⟩

/-- Uniform bound of a derivative of a jet over the compact parameter set. -/
lemma jet_bound {P : Set Par} (hP : IsCompact P) {f : Par → ℝ → ℝ} {L : ℝ} {r : ℕ} (hf : JetReg f P L r) {k : ℕ}
    (hk : k ≤ r) : ∃ M, ∀ μ ∈ P, ∀ x ∈ Icc 0 L, |iteratedDerivWithin k (f μ) (Icc 0 L) x| ≤ M := by
  obtain ⟨M, hM⟩ := (hP.prod isCompact_Icc).exists_bound_of_continuousOn (hf.2 k hk)
  exact ⟨M, fun μ hμ x hx => by simpa using hM (μ, x) ⟨hμ, hx⟩⟩

end JetFacts

/-- Derivatives of a `C^2` function on `[0,L]` at an interior point: `deriv` and `deriv deriv` exist, and agree with the iterated derivatives within `[0,L]`. -/
lemma interior_jet {g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hg : ContDiffOn ℝ 2 g (Icc 0 L)) {x : ℝ} (hx : x ∈ Ioo 0 L) :
    HasDerivAt g (deriv g x) x ∧ HasDerivAt (deriv g) (deriv (deriv g) x) x ∧
      iteratedDerivWithin 1 g (Icc 0 L) x = deriv g x ∧ iteratedDerivWithin 2 g (Icc 0 L) x = deriv (deriv g) x := by
  have hxI : x ∈ Icc 0 L := Ioo_subset_Icc_self hx
  have hCA : ContDiffAt ℝ 2 g x := hg.contDiffAt (Icc_mem_nhds hx.1 hx.2)
  have hgo : ContDiffOn ℝ 2 g (Ioo 0 L) := hg.mono Ioo_subset_Icc_self
  have hd1 : ContDiffOn ℝ 1 (deriv g) (Ioo 0 L) := hgo.deriv_of_isOpen isOpen_Ioo (by norm_num)
  refine ⟨(hCA.differentiableAt (by norm_num)).hasDerivAt, ?_, ?_, ?_⟩
  · exact (((hd1.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds hx.1 hx.2))).hasDerivAt
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hL) (hCA.of_le (by norm_num)) hxI, iteratedDeriv_one]
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hL) hCA hxI, iteratedDeriv_succ, iteratedDeriv_one]

/-- Second difference of `E_0 = s (L - s) g(s)`: `E_0(u+d) + E_0(u-d) - 2 E_0(u) <= (2 M_0 + 2 L M_1 + L^2 M_2) d^2` when `|g|, |g'|, |g''| <= M_0, M_1, M_2` on `[u-d, u+d]`. -/
lemma E0_second_diff {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Icc 0 L)) {M0 M1 M2 : ℝ}
    (hb0 : ∀ x ∈ Ioo 0 L, |g x| ≤ M0) (hb1 : ∀ x ∈ Ioo 0 L, |deriv g x| ≤ M1) (hb2 : ∀ x ∈ Ioo 0 L, |deriv (deriv g) x| ≤ M2)
    {u d : ℝ} (hd : 0 ≤ d) (hI : Icc (u - d) (u + d) ⊆ Ioo 0 L) :
    E0 L g (u + d) + E0 L g (u - d) - 2 * E0 L g u ≤ (2 * M0 + 2 * L * M1 + L ^ 2 * M2) * d ^ 2 := by
  have hmem : ∀ t ∈ Icc (u - d) (u + d), t ∈ Ioo 0 L := fun t ht => hI ht
  refine second_diff_le (E0 L g) (fun t => (L - 2 * t) * g t + t * (L - t) * deriv g t)
    (fun t => -2 * g t + 2 * (L - 2 * t) * deriv g t + t * (L - t) * deriv (deriv g) t) u d _ hd ?_ ?_ ?_
  · intro t ht
    obtain ⟨h1, h2, -, -⟩ := interior_jet hL hg (hmem t ht)
    have hq : HasDerivAt (fun s : ℝ => s * (L - s)) (L - 2 * t) t := by
      have := (hasDerivAt_id' t).fun_mul ((hasDerivAt_id' t).const_sub L)
      convert this using 1; ring
    have := hq.fun_mul h1
    show HasDerivAt (fun s => s * (L - s) * g s) _ t
    convert this using 1
  · intro t ht
    obtain ⟨h1, h2, -, -⟩ := interior_jet hL hg (hmem t ht)
    have hq : HasDerivAt (fun s : ℝ => L - 2 * s) (-2) t := by
      have := ((hasDerivAt_id' t).const_mul 2).const_sub L
      convert this using 1; ring
    have hq2 : HasDerivAt (fun s : ℝ => s * (L - s)) (L - 2 * t) t := by
      have := (hasDerivAt_id' t).fun_mul ((hasDerivAt_id' t).const_sub L)
      convert this using 1; ring
    have := (hq.fun_mul h1).add (hq2.fun_mul h2)
    convert this using 1
    ring
  · intro t ht
    have ht' := hmem t ht
    have a0 := hb0 t ht'
    have a1 := hb1 t ht'
    have a2 := hb2 t ht'
    have hM1 : 0 ≤ M1 := (abs_nonneg _).trans a1
    have hM2 : 0 ≤ M2 := (abs_nonneg _).trans a2
    have hM0 : 0 ≤ M0 := (abs_nonneg _).trans a0
    have hL1 : |L - 2 * t| ≤ L := by rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2]
    have hq : t * (L - t) ≤ L ^ 2 := by nlinarith [ht'.1, ht'.2]
    have hq0 : 0 ≤ t * (L - t) := by nlinarith [ht'.1, ht'.2]
    have e1 : -2 * g t ≤ 2 * M0 := by linarith [neg_abs_le (g t), abs_nonneg (g t)]
    have e2 : 2 * (L - 2 * t) * deriv g t ≤ 2 * L * M1 := by
      have : |(L - 2 * t) * deriv g t| ≤ L * M1 := by
        rw [abs_mul]; exact mul_le_mul hL1 a1 (abs_nonneg _) hL.le
      have := (le_abs_self _).trans this
      linarith
    have e3 : t * (L - t) * deriv (deriv g) t ≤ L ^ 2 * M2 := by
      have : t * (L - t) * deriv (deriv g) t ≤ t * (L - t) * M2 :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans a2) hq0
      have : t * (L - t) * M2 ≤ L ^ 2 * M2 := mul_le_mul_of_nonneg_right hq hM2
      linarith
    show -2 * g t + 2 * (L - 2 * t) * deriv g t + t * (L - t) * deriv (deriv g) t ≤ 2 * M0 + 2 * L * M1 + L ^ 2 * M2
    linarith

/-! ### The bonds against the principal symbol -/

/-- `sqrt(q G_h) <= sqrt(q G_0) + L delta/(4 sqrt g)` for `0 < q <= L^2/4`, `G_0 >= g > 0`, `|G_h - G_0| <= delta`
(the hard-edge factor `q = s(L-s)` cancels: `|sqrt E_n - sqrt E_0(s_n)| <= C h^e` uniformly up to the edges). -/
lemma sqrt_perturb_le {q g L δ G0 Gh : ℝ} (hL : 0 ≤ L) (hq : 0 < q) (hqL : q ≤ L ^ 2 / 4) (hg : 0 < g) (hδ : 0 ≤ δ)
    (hG : g ≤ G0) (h : |Gh - G0| ≤ δ) :
    Real.sqrt (q * Gh) ≤ Real.sqrt (q * G0) + L * δ / (4 * Real.sqrt g) := by
  have hy : 0 < q * G0 := mul_pos hq (lt_of_lt_of_le hg hG)
  have h1 := sqrt_le_add (q * Gh) (q * G0) hy
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsqq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  have hqg : Real.sqrt q * Real.sqrt g ≤ Real.sqrt (q * G0) := by
    rw [← Real.sqrt_mul hq.le]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hG hq.le)
  have hsqL : Real.sqrt q ≤ L / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have habs : |q * Gh - q * G0| ≤ q * δ := by
    rw [← mul_sub, abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_left h hq.le
  have hD : 0 < 2 * Real.sqrt (q * G0) := by positivity
  have h2 : |q * Gh - q * G0| / (2 * Real.sqrt (q * G0)) ≤ L * δ / (4 * Real.sqrt g) := by
    calc |q * Gh - q * G0| / (2 * Real.sqrt (q * G0)) ≤ (q * δ) / (2 * (Real.sqrt q * Real.sqrt g)) := by
          apply div_le_div₀ (by positivity) habs (by positivity)
          linarith
      _ = Real.sqrt q * δ / (2 * Real.sqrt g) := by
          field_simp
          nlinarith [hsqq]
      _ ≤ L / 2 * δ / (2 * Real.sqrt g) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hsqL hδ
      _ = L * δ / (4 * Real.sqrt g) := by ring
  linarith

/-- Hypotheses of the analytic core: compact parameter set, `G_0 in C^2` (with jointly continuous jets), `B_0` jointly continuous in `(mu, u)`, and for `h <= 1`
`|G_h - G_0|, |B_h - B_0| <= C_0 h^e` on `[0,L]`. -/
structure CoreReg {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (P : Set Par) (e : ℕ) : Prop where
  compact : IsCompact P
  regG : JetReg (F.G 0) P F.L 2
  regB : ContinuousOn (fun p : Par × ℝ => F.B 0 p.1 p.2) (P ×ˢ Icc 0 F.L)
  rem : ∃ C0 : ℝ, ∀ μ ∈ P, ∀ N : ℕ, F.step N ≤ 1 → ∀ s ∈ Icc 0 F.L,
    |F.Gh μ (F.step N) s - F.G 0 μ s| ≤ C0 * F.step N ^ e ∧ |F.Bh μ (F.step N) s - F.B 0 μ s| ≤ C0 * F.step N ^ e

/-- What the upper bound needs of (H1), (H3): a uniform `g_*`, and the maximum of `f_+` attained only at an interior point. -/
def UpHyp {Par : Type*} (F : SymbolFamily Par) (P : Set Par) : Prop :=
  ∃ g : ℝ, 0 < g ∧ ∀ μ ∈ P, (∀ u ∈ Icc 0 F.L, g ≤ F.G 0 μ u) ∧
    ∃ uc : ℝ, 0 < uc ∧ uc < F.L ∧ ∀ u ∈ Icc 0 F.L, fPlus F.L (F.G 0 μ) (F.B 0 μ) u = F.bandHi μ ↔ u = uc

lemma step_pos {Par : Type*} (F : SymbolFamily Par) (N : ℕ) : 0 < F.step N := by
  unfold SymbolFamily.step FormalResearch.JB.stepSize
  have := F.L_pos
  positivity

lemma step_mul {Par : Type*} (F : SymbolFamily Par) (N : ℕ) : F.step N * ((N : ℝ) + 1) = F.L := by
  unfold SymbolFamily.step FormalResearch.JB.stepSize
  have : ((N : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- `a_n <= sqrt E_0(s_n) + C_a h^e` for `-1 <= n <= N`, with `s_n = (n+1) h` (so `s_{-1} = 0`, `s_N = L`). -/
lemma bondA_le {Par : Type*} (F : SymbolFamily Par) {g C0 : ℝ} (hg : 0 < g) (hC0 : 0 ≤ C0) (μ : Par) (N : ℕ)
    (hG : ∀ u ∈ Icc 0 F.L, g ≤ F.G 0 μ u) {e : ℕ}
    (hrem : ∀ s ∈ Icc 0 F.L, |F.Gh μ (F.step N) s - F.G 0 μ s| ≤ C0 * F.step N ^ e)
    (n : ℤ) :
    F.bondA μ N n ≤ Real.sqrt (E0 F.L (F.G 0 μ) (sNode (F.step N) n)) + F.L * (C0 * F.step N ^ e) / (4 * Real.sqrt g) := by
  have hpos : 0 ≤ F.L * (C0 * F.step N ^ e) / (4 * Real.sqrt g) := by
    have := F.L_pos; have := step_pos F N; positivity
  unfold SymbolFamily.bondA
  split_ifs with hn
  · -- 0 ≤ n < N
    have hh := step_pos F N
    have hhN := step_mul F N
    have hnr : ((n : ℝ) + 1) ≥ 1 := by
      have : (0 : ℤ) ≤ n := hn.1
      have : (0 : ℝ) ≤ n := by exact_mod_cast this
      linarith
    have hnN : ((n : ℝ) + 1) ≤ N := by
      have : n + 1 ≤ (N : ℤ) := by omega
      have : ((n + 1 : ℤ) : ℝ) ≤ N := by exact_mod_cast this
      push_cast at this; exact this
    have hs0 : 0 < sNode (F.step N) n := by unfold sNode; positivity
    have hsL : sNode (F.step N) n < F.L := by
      unfold sNode; nlinarith
    have hq : 0 < sNode (F.step N) n * (F.L - sNode (F.step N) n) := mul_pos hs0 (by linarith)
    have hqL : sNode (F.step N) n * (F.L - sNode (F.step N) n) ≤ F.L ^ 2 / 4 := by
      nlinarith [sq_nonneg (sNode (F.step N) n - F.L / 2)]
    have := sqrt_perturb_le F.L_pos.le hq hqL hg (mul_nonneg hC0 (pow_nonneg hh.le e)) (hG _ ⟨hs0.le, hsL.le⟩)
      (hrem _ ⟨hs0.le, hsL.le⟩)
    simpa [SymbolFamily.entryE, E0, mul_assoc] using this
  · have := Real.sqrt_nonneg (E0 F.L (F.G 0 μ) (sNode (F.step N) n))
    linarith

/-! ### Compactness: uniform margins at the hard edges -/

lemma exists_pos_lower {X : Type*} [TopologicalSpace X] [CompactSpace X] (m : X → ℝ) (hm : Continuous m) (hpos : ∀ x, 0 < m x) :
    ∃ c > 0, ∀ x, c ≤ m x := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, one_pos, fun x => (hX.false x).elim⟩
  · obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hm.continuousOn
    exact ⟨m x0, hpos x0, fun x => hx0 (Set.mem_univ x)⟩

section Edge

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {e : ℕ}

lemma CoreReg.contG (hR : CoreReg F P e) :
    Continuous fun x : P × (Icc (0 : ℝ) F.L) => F.G 0 x.1.1 x.2.1 := by
  have h := hR.regG.2 0 (by norm_num)
  simp only [iteratedDerivWithin_zero] at h
  exact h.comp_continuous (f := fun x : P × (Icc (0 : ℝ) F.L) => ((x.1.1, x.2.1) : Par × ℝ)) (by fun_prop)
    (fun x => ⟨x.1.2, x.2.2⟩)

lemma CoreReg.contB (hR : CoreReg F P e) :
    Continuous fun x : P × (Icc (0 : ℝ) F.L) => F.B 0 x.1.1 x.2.1 := by
  have h := hR.regB
  exact h.comp_continuous (f := fun x : P × (Icc (0 : ℝ) F.L) => ((x.1.1, x.2.1) : Par × ℝ)) (by fun_prop)
    (fun x => ⟨x.1.2, x.2.2⟩)

lemma CoreReg.contF (hR : CoreReg F P e) :
    Continuous fun x : P × (Icc (0 : ℝ) F.L) => fPlus F.L (F.G 0 x.1.1) (F.B 0 x.1.1) x.2.1 := by
  have h1 := hR.contG
  have h2 := hR.contB
  unfold fPlus E0
  fun_prop

lemma CoreReg.contPsi (hR : CoreReg F P e) :
    Continuous fun x : P × (Icc (0 : ℝ) F.L) => Real.sqrt (E0 F.L (F.G 0 x.1.1) x.2.1) := by
  have h1 := hR.contG
  unfold E0
  fun_prop

omit [TopologicalSpace Par] in
lemma bandHi_eq_sSup (μ : Par) : F.bandHi μ = sSup (Set.range fun u : (Icc (0 : ℝ) F.L) => fPlus F.L (F.G 0 μ) (F.B 0 μ) u) := by
  unfold SymbolFamily.bandHi Xsp
  rw [Set.image_eq_range]

lemma CoreReg.contBandHi (hR : CoreReg F P e) : Continuous fun μ : P => F.bandHi μ.1 := by
  have := (isCompact_univ (X := (Icc (0 : ℝ) F.L))).continuous_sSup
    (f := fun (μ : P) (u : Icc (0 : ℝ) F.L) => fPlus F.L (F.G 0 μ.1) (F.B 0 μ.1) u.1) hR.contF
  simp only [Set.image_univ] at this
  convert this using 2 with μ
  exact bandHi_eq_sSup μ.1

lemma CoreReg.fPlus_le (hR : CoreReg F P e) {μ : Par} (hμ : μ ∈ P) {u : ℝ} (hu : u ∈ Icc 0 F.L) :
    fPlus F.L (F.G 0 μ) (F.B 0 μ) u ≤ F.bandHi μ := by
  have hG := (hR.regG.1 μ hμ).continuousOn
  have hB : ContinuousOn (F.B 0 μ) (Icc 0 F.L) :=
    hR.regB.comp (Continuous.continuousOn (by fun_prop : Continuous fun u : ℝ => (μ, u))) (fun u hu => ⟨hμ, hu⟩)
  have hc : ContinuousOn (fPlus F.L (F.G 0 μ) (F.B 0 μ)) (Icc 0 F.L) := by
    unfold fPlus E0
    exact hB.add (continuousOn_const.mul ((((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hG)).sqrt))
  exact le_csSup (isCompact_Icc.bddAbove_image hc) ⟨u, hu, rfl⟩

/-- Uniform margins (compactness of `P`): `f_+ <= X_s^+ - c` near the two hard edges, uniformly in `mu`, and a uniform modulus of continuity of `sqrt E_0`. -/
lemma CoreReg.edge_data (hR : CoreReg F P e) (hU : UpHyp F P) :
    ∃ c δ δ2 : ℝ, 0 < c ∧ 0 < δ ∧ 0 < δ2 ∧
      (∀ μ ∈ P, ∀ u ∈ Icc 0 F.L, min u (F.L - u) < δ → fPlus F.L (F.G 0 μ) (F.B 0 μ) u + c ≤ F.bandHi μ) ∧
      (∀ μ ∈ P, ∀ s ∈ Icc 0 F.L, ∀ u ∈ Icc 0 F.L, |s - u| < δ2 →
        |Real.sqrt (E0 F.L (F.G 0 μ) s) - Real.sqrt (E0 F.L (F.G 0 μ) u)| < c / 4) := by
  have : CompactSpace P := isCompact_iff_compactSpace.mp hR.compact
  obtain ⟨g, hg, hU'⟩ := hU
  have hL := F.L_pos
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) F.L := ⟨le_rfl, hL.le⟩
  have hLmem : F.L ∈ Icc (0 : ℝ) F.L := ⟨hL.le, le_rfl⟩
  -- the maximum is not attained at the endpoints
  have hgap : ∀ μ ∈ P, fPlus F.L (F.G 0 μ) (F.B 0 μ) 0 < F.bandHi μ ∧ fPlus F.L (F.G 0 μ) (F.B 0 μ) F.L < F.bandHi μ := by
    intro μ hμ
    obtain ⟨-, uc, huc0, hucL, hiff⟩ := hU' μ hμ
    constructor
    · refine lt_of_le_of_ne (hR.fPlus_le hμ h0mem) fun h => ?_
      exact huc0.ne' ((hiff 0 h0mem).mp h).symm
    · refine lt_of_le_of_ne (hR.fPlus_le hμ hLmem) fun h => ?_
      exact hucL.ne ((hiff F.L hLmem).mp h).symm
  -- uniform gap at the two endpoints
  let mm : P → ℝ := fun μ => min (F.bandHi μ.1 - fPlus F.L (F.G 0 μ.1) (F.B 0 μ.1) 0)
    (F.bandHi μ.1 - fPlus F.L (F.G 0 μ.1) (F.B 0 μ.1) F.L)
  have hmm_cont : Continuous mm := by
    have c1 : Continuous fun μ : P => fPlus F.L (F.G 0 μ.1) (F.B 0 μ.1) 0 :=
      hR.contF.comp (continuous_id.prodMk (continuous_const (y := (⟨0, h0mem⟩ : Icc (0 : ℝ) F.L))))
    have c2 : Continuous fun μ : P => fPlus F.L (F.G 0 μ.1) (F.B 0 μ.1) F.L :=
      hR.contF.comp (continuous_id.prodMk (continuous_const (y := (⟨F.L, hLmem⟩ : Icc (0 : ℝ) F.L))))
    exact (hR.contBandHi.sub c1).min (hR.contBandHi.sub c2)
  have hmm_pos : ∀ μ : P, 0 < mm μ := fun μ => lt_min (sub_pos.mpr (hgap μ.1 μ.2).1) (sub_pos.mpr (hgap μ.1 μ.2).2)
  obtain ⟨c0, hc0, hc0le⟩ := exists_pos_lower mm hmm_cont hmm_pos
  have hc0' : ∀ μ : P, c0 ≤ F.bandHi μ.1 - fPlus F.L (F.G 0 μ.1) (F.B 0 μ.1) 0 ∧
      c0 ≤ F.bandHi μ.1 - fPlus F.L (F.G 0 μ.1) (F.B 0 μ.1) F.L :=
    fun μ => ⟨(hc0le μ).trans (min_le_left _ _), (hc0le μ).trans (min_le_right _ _)⟩
  -- modulus at the endpoints
  obtain ⟨δ, hδ, hδ'⟩ := exists_modulus (X := P × (Icc (0 : ℝ) F.L))
    (fun x => c0 - (F.bandHi x.1.1 - fPlus F.L (F.G 0 x.1.1) (F.B 0 x.1.1) x.2.1))
    (fun x => min x.2.1 (F.L - x.2.1))
    (continuous_const.sub ((hR.contBandHi.comp continuous_fst).sub hR.contF))
    ((continuous_subtype_val.comp continuous_snd).min (continuous_const.sub (continuous_subtype_val.comp continuous_snd)))
    (fun x => le_min x.2.2.1 (by linarith [x.2.2.2])) (c0 / 2) (by
      intro x hx
      obtain ⟨hm1, hm2⟩ := hc0' x.1
      rcases min_eq_iff.mp hx with ⟨h, -⟩ | ⟨h, -⟩
      · have h' : x.2.1 = 0 := h
        show c0 - (F.bandHi x.1.1 - fPlus F.L (F.G 0 x.1.1) (F.B 0 x.1.1) x.2.1) < c0 / 2
        rw [h']; linarith
      · have h' : x.2.1 = F.L := by linarith
        show c0 - (F.bandHi x.1.1 - fPlus F.L (F.G 0 x.1.1) (F.B 0 x.1.1) x.2.1) < c0 / 2
        rw [h']; linarith)
  -- modulus of continuity of sqrt E_0
  have hc4 : 0 < c0 / 2 / 4 := by positivity
  obtain ⟨δ2, hδ2, hδ2'⟩ := exists_modulus (X := P × (Icc (0 : ℝ) F.L) × (Icc (0 : ℝ) F.L))
    (fun x => |Real.sqrt (E0 F.L (F.G 0 x.1.1) x.2.1.1) - Real.sqrt (E0 F.L (F.G 0 x.1.1) x.2.2.1)|)
    (fun x => |x.2.1.1 - x.2.2.1|)
    (by
      have a1 : Continuous fun x : P × (Icc (0 : ℝ) F.L) × (Icc (0 : ℝ) F.L) => Real.sqrt (E0 F.L (F.G 0 x.1.1) x.2.1.1) :=
        hR.contPsi.comp (f := fun x : P × (Icc (0 : ℝ) F.L) × (Icc (0 : ℝ) F.L) => (x.1, x.2.1)) (by fun_prop)
      have a2 : Continuous fun x : P × (Icc (0 : ℝ) F.L) × (Icc (0 : ℝ) F.L) => Real.sqrt (E0 F.L (F.G 0 x.1.1) x.2.2.1) :=
        hR.contPsi.comp (f := fun x : P × (Icc (0 : ℝ) F.L) × (Icc (0 : ℝ) F.L) => (x.1, x.2.2)) (by fun_prop)
      exact (a1.sub a2).abs)
    (by fun_prop) (fun x => abs_nonneg _) (c0 / 2 / 4) (by
      intro x hx
      have : x.2.1.1 = x.2.2.1 := by
        have := abs_eq_zero.mp hx; linarith
      simp only [this, sub_self, abs_zero]
      exact hc4)
  refine ⟨c0 / 2, δ, δ2, by positivity, hδ, hδ2, ?_, ?_⟩
  · intro μ hμ u hu hlt
    have := hδ' (⟨μ, hμ⟩, ⟨u, hu⟩) hlt
    simp only at this
    linarith
  · intro μ hμ s hs u hu hlt
    exact hδ2' (⟨μ, hμ⟩, ⟨s, hs⟩, ⟨u, hu⟩) hlt

end Edge

/-- Away from the hard edges the two symmetric samples of `sqrt E_0` exceed `2 sqrt E_0(u)` by at most `C d^2` (the odd Taylor terms cancel; app_thmA Step 0). -/
lemma sqrt_E0_sym_le {L g : ℝ} (hL : 0 < L) (hg : 0 < g) {G : ℝ → ℝ} (hGc : ContDiffOn ℝ 2 G (Icc 0 L))
    (hGlb : ∀ u ∈ Icc 0 L, g ≤ G u) {M0 M1 M2 : ℝ}
    (hb0 : ∀ x ∈ Ioo 0 L, |G x| ≤ M0) (hb1 : ∀ x ∈ Ioo 0 L, |deriv G x| ≤ M1) (hb2 : ∀ x ∈ Ioo 0 L, |deriv (deriv G) x| ≤ M2)
    {δ u d : ℝ} (hδ : 0 < δ) (hu1 : δ ≤ u) (hu2 : u ≤ L - δ) (hd : 0 ≤ d) (hdδ : d ≤ δ / 2) :
    Real.sqrt (E0 L G (u + d)) + Real.sqrt (E0 L G (u - d)) ≤
      2 * Real.sqrt (E0 L G u) + (2 * M0 + 2 * L * M1 + L ^ 2 * M2) * d ^ 2 / (2 * Real.sqrt (g * δ * L / 2)) := by
  have hI : Icc (u - d) (u + d) ⊆ Ioo 0 L := by
    intro t ht; constructor <;> linarith [ht.1, ht.2]
  have huI : u ∈ Ioo 0 L := ⟨by linarith, by linarith⟩
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hb0 u huI)
  have hM1 : 0 ≤ M1 := (abs_nonneg _).trans (hb1 u huI)
  have hM2 : 0 ≤ M2 := (abs_nonneg _).trans (hb2 u huI)
  have hq : δ * L / 2 ≤ u * (L - u) := by nlinarith
  have hGu := hGlb u ⟨by linarith, by linarith⟩
  have hy : g * δ * L / 2 ≤ E0 L G u := by
    unfold E0
    have := mul_le_mul hGu hq (by positivity) (by linarith)
    nlinarith
  have hemin : 0 < g * δ * L / 2 := by positivity
  have hypos : 0 < E0 L G u := lt_of_lt_of_le hemin hy
  have hnn : ∀ t ∈ Icc (u - d) (u + d), 0 ≤ E0 L G t := by
    intro t ht
    have ht' := hI ht
    have := hGlb t ⟨ht'.1.le, ht'.2.le⟩
    unfold E0
    have : 0 < G t := lt_of_lt_of_le hg this
    have : 0 < t * (L - t) := mul_pos ht'.1 (by linarith [ht'.2])
    positivity
  have h1 := sqrt_le_tangent (hnn (u + d) ⟨by linarith, le_rfl⟩) hypos
  have h2 := sqrt_le_tangent (hnn (u - d) ⟨le_rfl, by linarith⟩) hypos
  have hsd := E0_second_diff hL hGc hb0 hb1 hb2 hd hI
  have hsy : 0 < Real.sqrt (E0 L G u) := Real.sqrt_pos.mpr hypos
  have hse : Real.sqrt (g * δ * L / 2) ≤ Real.sqrt (E0 L G u) := Real.sqrt_le_sqrt hy
  have hse0 : 0 < Real.sqrt (g * δ * L / 2) := Real.sqrt_pos.mpr hemin
  have hnum : 0 ≤ (2 * M0 + 2 * L * M1 + L ^ 2 * M2) * d ^ 2 := by positivity
  have hfrac : (E0 L G (u + d) - E0 L G u) / (2 * Real.sqrt (E0 L G u)) +
      (E0 L G (u - d) - E0 L G u) / (2 * Real.sqrt (E0 L G u)) ≤
      (2 * M0 + 2 * L * M1 + L ^ 2 * M2) * d ^ 2 / (2 * Real.sqrt (g * δ * L / 2)) := by
    rw [← add_div]
    calc _ ≤ (2 * M0 + 2 * L * M1 + L ^ 2 * M2) * d ^ 2 / (2 * Real.sqrt (E0 L G u)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hnum (by positivity) (by linarith)
  linarith

/-- **Upper bound of the numerical range** (app_thmA Step 0, first half): uniformly in `mu in P` and for `h` small,
`B_n + a_n + a_{n-1} <= X_s^+ + C h^e` at every site `n`. -/
theorem CoreReg.upper {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {e : ℕ}
    (hR : CoreReg F P e) (he : e ≤ 2) (hU : UpHyp F P) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ P, ∀ N : ℕ, F.step N ≤ h0 → ∀ i : Fin (N + 1),
      F.entryB μ N (i : ℤ) + F.bondA μ N (i : ℤ) + F.bondA μ N ((i : ℤ) - 1) ≤ F.bandHi μ + C * F.step N ^ e := by
  have hL := F.L_pos
  obtain ⟨C0, hC0⟩ := hR.rem
  obtain ⟨g, hg, hU'⟩ := hU
  have hC0' : 0 ≤ max C0 0 := le_max_right _ _
  have hrem : ∀ μ ∈ P, ∀ N : ℕ, F.step N ≤ 1 → ∀ s ∈ Icc 0 F.L,
      |F.Gh μ (F.step N) s - F.G 0 μ s| ≤ max C0 0 * F.step N ^ e ∧
        |F.Bh μ (F.step N) s - F.B 0 μ s| ≤ max C0 0 * F.step N ^ e := by
    intro μ hμ N hN1 s hs
    obtain ⟨a, b⟩ := hC0 μ hμ N hN1 s hs
    have hp := pow_nonneg (step_pos F N).le e
    exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp), b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)⟩
  -- jet bounds
  obtain ⟨M0', hM0'⟩ := jet_bound hR.compact hR.regG (k := 0) (by norm_num)
  obtain ⟨M1', hM1'⟩ := jet_bound hR.compact hR.regG (k := 1) (by norm_num)
  obtain ⟨M2', hM2'⟩ := jet_bound hR.compact hR.regG (k := 2) le_rfl
  have hgc : ∀ μ ∈ P, ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) := fun μ hμ => by
    simpa using (hR.regG.1 μ hμ)
  have hb0 : ∀ μ ∈ P, ∀ x ∈ Ioo 0 F.L, |F.G 0 μ x| ≤ max M0' 0 := by
    intro μ hμ x hx
    have := hM0' μ hμ x (Ioo_subset_Icc_self hx)
    simp only [iteratedDerivWithin_zero] at this
    exact this.trans (le_max_left _ _)
  have hb1 : ∀ μ ∈ P, ∀ x ∈ Ioo 0 F.L, |deriv (F.G 0 μ) x| ≤ max M1' 0 := by
    intro μ hμ x hx
    have := hM1' μ hμ x (Ioo_subset_Icc_self hx)
    rw [(interior_jet hL (hgc μ hμ) hx).2.2.1] at this
    exact this.trans (le_max_left _ _)
  have hb2 : ∀ μ ∈ P, ∀ x ∈ Ioo 0 F.L, |deriv (deriv (F.G 0 μ)) x| ≤ max M2' 0 := by
    intro μ hμ x hx
    have := hM2' μ hμ x (Ioo_subset_Icc_self hx)
    rw [(interior_jet hL (hgc μ hμ) hx).2.2.2] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨c, δ, δ2, hc, hδ, hδ2, hedge, hmod⟩ := hR.edge_data ⟨g, hg, hU'⟩
  set Mtot : ℝ := 2 * max M0' 0 + 2 * F.L * max M1' 0 + F.L ^ 2 * max M2' 0 with hMtot
  have hMtot0 : 0 ≤ Mtot := by positivity
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hemin : 0 < g * δ * F.L / 2 := by positivity
  have hse : 0 < Real.sqrt (g * δ * F.L / 2) := Real.sqrt_pos.mpr hemin
  refine ⟨max C0 0 + 2 * (F.L * max C0 0 / (4 * Real.sqrt g)) + Mtot / (8 * Real.sqrt (g * δ * F.L / 2)),
    min 1 (min δ δ2), by positivity, ?_⟩
  intro μ hμ N hN i
  have hh := step_pos F N
  have hhN := step_mul F N
  set h := F.step N with hhdef
  have h1 : h ≤ 1 := hN.trans (min_le_left _ _)
  have hδh : h ≤ δ := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ2h : h ≤ δ2 := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hGlb, uc, huc0, hucL, hiff⟩ := hU' μ hμ
  -- the site
  have hiN : (i : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  set u : ℝ := uNode h (i : ℤ) with hu
  have hu_eq : u = ((i : ℝ) + 1 / 2) * h := by simp [hu, uNode]
  have hu0 : 0 ≤ u := by rw [hu_eq]; positivity
  have huL : u ≤ F.L := by rw [hu_eq]; nlinarith
  have hs1 : sNode h (i : ℤ) = u + h / 2 := by simp [hu_eq, sNode]; ring
  have hs2 : sNode h ((i : ℤ) - 1) = u - h / 2 := by simp [hu_eq, sNode]; ring
  have huI : u ∈ Icc 0 F.L := ⟨hu0, huL⟩
  have hB : F.entryB μ N (i : ℤ) ≤ F.B 0 μ u + max C0 0 * h ^ e := by
    have := (hrem μ hμ N h1 u huI).2
    have h2 : F.entryB μ N (i : ℤ) = F.Bh μ h u := rfl
    rw [h2]; linarith [(abs_le.mp this).2]
  have ha1 := bondA_le F hg hC0' μ N hGlb (fun s hs => (hrem μ hμ N h1 s hs).1) (i : ℤ)
  have ha2 := bondA_le F hg hC0' μ N hGlb (fun s hs => (hrem μ hμ N h1 s hs).1) ((i : ℤ) - 1)
  rw [hs1] at ha1
  rw [hs2] at ha2
  have hEa : F.L * (max C0 0 * h ^ e) / (4 * Real.sqrt g) = (F.L * max C0 0 / (4 * Real.sqrt g)) * h ^ e := by ring
  rw [hEa] at ha1 ha2
  have hfle := hR.fPlus_le hμ huI
  have hhe : h ^ 2 ≤ h ^ e := pow_le_pow_of_le_one hh.le h1 he
  -- the symmetric samples
  have key : F.B 0 μ u + Real.sqrt (E0 F.L (F.G 0 μ) (u + h / 2)) + Real.sqrt (E0 F.L (F.G 0 μ) (u - h / 2)) ≤
      F.bandHi μ + Mtot / (8 * Real.sqrt (g * δ * F.L / 2)) * h ^ e := by
    have hfu : fPlus F.L (F.G 0 μ) (F.B 0 μ) u = F.B 0 μ u + 2 * Real.sqrt (E0 F.L (F.G 0 μ) u) := by
      simp [fPlus]
    by_cases hedge' : min u (F.L - u) < δ
    · have hu1 := hedge μ hμ u huI hedge'
      have hp : u + h / 2 ∈ Icc 0 F.L := by
        have : 0 ≤ u + h / 2 := by positivity
        constructor
        · exact this
        · have : u + h / 2 ≤ F.L := by
            have : ((i : ℝ) + 1 / 2) * h + h / 2 = ((i : ℝ) + 1) * h := by ring
            rw [hu_eq, this]; nlinarith
          exact this
      have hm : u - h / 2 ∈ Icc 0 F.L := by
        constructor
        · rw [hu_eq]; nlinarith
        · linarith
      have m1 := hmod μ hμ _ hp u huI (by rw [add_sub_cancel_left, abs_of_pos (by positivity)]; linarith)
      have m2 := hmod μ hμ _ hm u huI (by
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]; linarith)
      have m1' := (abs_lt.mp m1).2
      have m2' := (abs_lt.mp m2).2
      have : 0 ≤ Mtot / (8 * Real.sqrt (g * δ * F.L / 2)) * h ^ e := by positivity
      linarith
    · push Not at hedge'
      have hu1 : δ ≤ u := le_trans hedge' (min_le_left _ _)
      have hu2 : u ≤ F.L - δ := by linarith [le_trans hedge' (min_le_right _ _)]
      have hs := sqrt_E0_sym_le hL hg (hgc μ hμ) hGlb (hb0 μ hμ) (hb1 μ hμ) (hb2 μ hμ) hδ hu1 hu2
        (show (0 : ℝ) ≤ h / 2 by positivity) (by linarith)
      have hq : Mtot * (h / 2) ^ 2 / (2 * Real.sqrt (g * δ * F.L / 2)) =
          Mtot / (8 * Real.sqrt (g * δ * F.L / 2)) * h ^ 2 := by field_simp; ring
      have hq2 : Mtot / (8 * Real.sqrt (g * δ * F.L / 2)) * h ^ 2 ≤ Mtot / (8 * Real.sqrt (g * δ * F.L / 2)) * h ^ e :=
        mul_le_mul_of_nonneg_left hhe (by positivity)
      rw [hq] at hs
      linarith
  linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.CoreReg.upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.CoreReg.upper

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.CoreReg.edge_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.CoreReg.edge_data

end FormalResearch.JacobiEigenvectors.TheoremA
