module

public import FormalResearch.Racah.P2AnalyticHeadline
public import FormalResearch.Racah.P2AnalyticBridge6j
public import FormalResearch.Racah.P2AnalyticBulk6j
public import FormalResearch.Racah.P2AnalyticUniform6j

/-!
# Weyl P2: the `6j` analytic headline theorems with the Wigner `d`-function

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:6jeven` (`eq:6jleading`, `eq:6jevenexp`),
`thm:uniformedge`(b) (`eq:6juniformedge`).  Companion of `P2AnalyticHeadline` (the `3j` half and the
dictionary); this half is a separate module because it needs `P2AnalyticBridge6j` together with
`P2AnalyticBulk6j` / `P2AnalyticUniform6j`.

## Results

* `thm_6jeven` (**`thm:6jeven`**, proved): the functions `G_{f,2r} = G6even f m n r` are real analytic
  on the whole open strict-triangle cone `StrictTri`, homogeneous of degree `-2r`, with
  `G_{f,0}(A,B,C) = d^f_{nm}(arccos x)`, `x = (A²+B²-C²)/(2AB)` (`wignerSmallDx f n m (cosA A B C)`);
  they are `S^{-2r} a_{f,r}((A,B,C)/S)`, `S = A+B+C`, where `a_{f,r}` is the `t^r` Taylor coefficient
  of the germ `t ↦ G6 f m n (α,β,γ) t`, real analytic jointly in shape and `t` on `Dom6 f m n`, with a
  positive uniform radius `ρ` over every compact set of strict-triangle shapes; `Φ_f` is the germ at
  `t = S⁻²` exactly (`Phi6_eq_G6`); and
  `Φ_f = ∑_{r<R} G_{f,2r} + O(H^{-2R})` uniformly on all large physical triples in `𝒯_δ`.
* `thm_uniformedge_6j` (**`thm:uniformedge`(b)**): `W_{6j} s_0 = d^f_{nm}(arccos x)` and the uniform
  edge-factorised expansion `Φ = E W [∑ s_r (A+B)^{-2r} + O((A+B)^{-2R})]`; `0 < c ≤ E ≤ 1`.

Not covered: that the coefficients of `s_r` are rational in `δ` with poles only at `δ = ±1`
(`analyticOnNhd_cKc` gives analyticity on `(-1,1)` for the canonical sector), the convergence domain.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Set Filter Topology

lemma Wedge_eq_edgeW (p q : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Wedge p q x = edgeW p q x := Wedge_eq_sqrt p q hx

/-- A point of the open strict-triangle cone satisfies the closed triangle inequalities, so its
centred cosine lies in `[-1,1]`. -/
lemma cosA_mem_Icc_of_strictTri {A B C : ℝ} (h : (A, B, C) ∈ StrictTri) :
    cosA A B C ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨hA, hB, hC, h1, h2, h3⟩ := h
  exact cosA_mem_Icc A B C hA hB (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)

/-- **`thm:6jeven`** (uniform homogeneous Weyl-midpoint expansion for the one-small `6j`; proved).
Fix admissible `f, m, n` (`hlab`: `f ± m`, `f ± n` natural numbers).  Then

1. `G_{f,2r} = G6even f m n r` are real analytic on the whole open strict-triangle cone `StrictTri`
   (not merely chamberwise);
2. they are homogeneous of degree `-2r`;
3. `G_{f,0}(A,B,C) = d^f_{nm}(arccos x)`, `x = (A²+B²-C²)/(2AB)` (`eq:6jleading`), on the cone;
4. along each fixed normalised shape the series is the Taylor series of the germ in `S⁻²`:
   `G_{f,2r} = S^{-2r} a_{f,r}((A,B,C)/S)` with `a_{f,r}` the `t^r` Taylor coefficient of `G6 f m n`;
   the germ is real analytic on the open set `Dom6 f m n`, which contains `K × [-ρ, ρ]` for some
   `ρ > 0` for every compact set `K` of strict-triangle shapes (the uniform dilation radius), and
   `Φ_f` is exactly the germ at `t = S⁻²`;
5. for every `δ > 0` and `R` there are `C, H₀` such that at every physical admissible triple with
   `H = max (A,B,C) ≥ H₀` in `𝒯_δ` (`δ H ≤ min (A,B,C,A+B-C,A+C-B,B+C-A)`)
   `|Φ_f - ∑_{r<R} G_{f,2r}| ≤ C H^{-2R}` (`eq:6jevenexp`); the physical triples are the four triads
   `IsTri` of the `6j` family with `A = wA a n`, `B = wB b m`, `C = wC c`.

The hypotheses encode the paper's "admissible `f, m, n`" (`hlab`) and the cone `𝒯_δ`; `0 < δ < 1/3`
in the paper is not needed (for `δ > 1/3` the cone is empty). -/
theorem thm_6jeven (f m n : ℚ)
    (hlab : IsNat (f + m) ∧ IsNat (f - m) ∧ IsNat (f + n) ∧ IsNat (f - n)) :
    (∀ r : ℕ, AnalyticOnNhd ℝ (fun p : Shape6 => G6even f m n r p.1 p.2.1 p.2.2) StrictTri) ∧
    (∀ (r : ℕ) (A B C s : ℝ), s ≠ 0 →
      G6even f m n r (s * A) (s * B) (s * C) = (s ^ (2 * r))⁻¹ * G6even f m n r A B C) ∧
    (∀ A B C : ℝ, (A, B, C) ∈ StrictTri →
      G6even f m n 0 A B C = wignerSmallDx f n m (cosA A B C)) ∧
    (∀ (r : ℕ) (A B C : ℝ), G6even f m n r A B C =
      ((A + B + C) ^ (2 * r))⁻¹ *
        taylorCoeff (fun (z : Shape6) t => G6 f m n z.1 z.2.1 z.2.2 t) r
          (A / (A + B + C), B / (A + B + C), C / (A + B + C))) ∧
    AnalyticOnNhd ℝ (fun q : Shape6 × ℝ => G6 f m n q.1.1 q.1.2.1 q.1.2.2 q.2) (Dom6 f m n) ∧
    (∀ K : Set Shape6, IsCompact K → K ⊆ StrictTri →
      ∃ ρ : ℝ, 0 < ρ ∧ K ×ˢ Icc (-ρ) ρ ⊆ Dom6 f m n) ∧
    (∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) →
      Phi6 a b c f m n =
        G6 f m n (wA a n / (wA a n + wB b m + wC c)) (wB b m / (wA a n + wB b m + wC c))
          (wC c / (wA a n + wB b m + wC c)) (1 / (wA a n + wB b m + wC c) ^ 2)) ∧
    (∀ {δ : ℝ}, 0 < δ → ∀ R : ℕ, ∃ C H₀ : ℝ, ∀ a b c : ℚ,
      IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b → IsTri c (b + m) (a + n) →
      H₀ ≤ Hscale (wA a n) (wB b m) (wC c) →
      δ * Hscale (wA a n) (wB b m) (wC c) ≤ Tmin (wA a n) (wB b m) (wC c) →
      |Phi6 a b c f m n - ∑ r ∈ Finset.range R, G6even f m n r (wA a n) (wB b m) (wC c)| ≤
        C / Hscale (wA a n) (wB b m) (wC c) ^ (2 * R)) := by
  refine ⟨analyticOnNhd_G6even f m n, fun r A B C s hs => G6even_homogeneous f m n r A B C s hs,
    fun A B C h => ?_, fun r A B C => rfl, analyticOnNhd_G6 f m n, fun K hK hKS => ?_,
    fun a b c h1 h2 h3 h4 => Phi6_eq_G6 a b c f m n h1 h2 h3 h4,
    fun {δ} hδ R => Phi6_even_expansion_cone f m n hδ R⟩
  · obtain ⟨hA, hB, hC, h1, h2, h3⟩ := h
    rw [G6even_zero_eq_dZero6 f m n hlab hA hB (by linarith)]
    exact dZero6_eq_wignerD f m n hlab.1 hlab.2.1 hlab.2.2.1 hlab.2.2.2
      (cosA_mem_Icc_of_strictTri ⟨hA, hB, hC, h1, h2, h3⟩)
  · refine exists_tube hK (Dom6_isOpen f m n) ?_
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    have : t = 0 := ht
    subst this
    exact mem_Dom6_zero f m n (hKS hz)

/-- **`thm:uniformedge`(b)** (`eq:6juniformedge`; proved).  Fix admissible `f, m, n` and `0 < λ < 1`.
With `p_min = |m-n|`, `p_max = |m+n|`, `W_{6j}(x) = ((1-x)/2)^{p_min/2} ((1+x)/2)^{p_max/2}`
(`Wedge`) and `s_r = s6 f m n r` (polynomials in `τ = (1-x)/2` of degree at most `d = f - f₀`
with coefficients analytic in `δ = (A-B)/(A+B) ∈ (-1,1)`, `s6c_eq_sum`, `analyticOnNhd_cKc`):

* `W_{6j}(x) s_0(τ; δ) = d^f_{nm}(arccos x)` for every `δ` and every `x ∈ [-1,1]`;
* for every `R` there are `C, S₀` with, uniformly on the whole physical `c`-lattice with
  `λ ≤ A/B ≤ λ⁻¹` and `S = A+B ≥ S₀`,
  `|Φ_f - E_{A,B}(C) W_{6j}(x) ∑_{r<R} s_r(τ;δ) S^{-2r}| ≤ C · E W · S^{-2R}`, i.e.
  `Φ_f = E W [∑ s_r S^{-2r} + O(S^{-2R})]` (`EW = edgeEW p_min p_max A B C`);
* `0 < c ≤ E_{A,B}(C) ≤ 1` on the physical lattice, `c = c_{p_min}² c_{p_max}²` depending on the
  labels only. -/
theorem thm_uniformedge_6j (f m n : ℚ)
    (hlab : IsNat (f + m) ∧ IsNat (f - m) ∧ IsNat (f + n) ∧ IsNat (f - n))
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (∀ x ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ,
      Wedge ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ x * s6 f m n 0 ((1 - x) / 2) δ = wignerSmallDx f n m x) ∧
    (∀ R : ℕ, ∃ C S₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → lam * wB b m ≤ wA a n → wA a n ≤ wB b m / lam →
      S₀ ≤ wA a n + wB b m →
      |Phi6 a b c f m n - edgeEW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) *
          ∑ r ∈ Finset.range R,
            s6 f m n r ((1 - cosA (wA a n) (wB b m) (wC c)) / 2)
              ((wA a n - wB b m) / (wA a n + wB b m)) / (wA a n + wB b m) ^ (2 * r)| ≤
        C * edgeEW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) /
          (wA a n + wB b m) ^ (2 * R)) ∧
    (∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) →
      0 < edgeRlow ⌊|m - n|⌋₊ ^ 2 * edgeRlow ⌊|m + n|⌋₊ ^ 2 ∧
      edgeRlow ⌊|m - n|⌋₊ ^ 2 * edgeRlow ⌊|m + n|⌋₊ ^ 2 ≤
        edgeE ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) ∧
      edgeE ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) ≤ 1) := by
  refine ⟨fun x hx δ => ?_, fun R => Phi6_uniform_edge f m n hlam0 hlam1 R,
    fun a b c h1 h2 h3 h4 => edgeE_bounds f m n h1 h2 h3 h4⟩
  rw [Wedge_eq_edgeW _ _ hx, edgeW_mul_s6_zero,
    dZero6_eq_wignerD f m n hlab.1 hlab.2.1 hlab.2.2.1 hlab.2.2.2 hx]

/-- info: 'FormalResearch.Racah.thm_6jeven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_6jeven

/-- info: 'FormalResearch.Racah.thm_uniformedge_6j' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_uniformedge_6j

end FormalResearch.Racah
