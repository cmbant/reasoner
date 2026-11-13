module

public import FormalResearch.Asymptotics.AnalyticGerm
public import FormalResearch.Racah.P2AnalyticBulk3j

/-!
# Example: the `3j` even expansion (Weyl P2, `thm:3jeven`) in the `HasUniformExpansion` language

`FormalResearch.Racah.Phi3j_even_expansion` states the uniform expansion of the `3j` amplitude
`Φ_L^{M,σ}(x; 1/N)` at the physical lattice points in the parameter `ε = N⁻²` with an explicit
`∃ C N₀` quantification.  Here it is re-derived as a corollary of the bridge theorem
`hasUniformExpansionOn_of_analytic`: the amplitude has the uniform expansion `HasUniformExpansionOn`
on the physical grid, with `ε = 1/N²` and coefficients `f3even`, and the explicit statement
of `Phi3j_even_expansion` is recovered from the unfolded form `hasUniformExpansionOn_iff`.

The parameter space is `ι = ℚ × ℚ` of pairs `(N, μ)`, the filter `l` is `N → ∞`, and the grid
`phys3jGrid` ties the variable `x` to the index by `x = 2 μ / N`.

Nothing in `P2AnalyticTaylor.lean`, `P2AnalyticBulk3j.lean` is changed; the P2 `Racah.taylorCoeff`
agrees with `Asymptotics.taylorCoeff` for real-valued `G` (`taylorCoeff_eq_racah`).
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.Asymptotics

/-- For real-valued germs the generalised `taylorCoeff` is the P2 one. -/
theorem taylorCoeff_eq_racah {E : Type*} (g : E → ℝ → ℝ) (r : ℕ) (z : E) :
    taylorCoeff g r z = FormalResearch.Racah.taylorCoeff g r z := by
  simp [taylorCoeff, FormalResearch.Racah.taylorCoeff, div_eq_inv_mul]

section ThreeJ

open FormalResearch.Racah FormalResearch.Wigner

/-- The physical grid of `thm:3jeven`: pairs `(x, (N, μ))` with `N` admissible, `μ` on the lattice
and `x = 2 μ / N`. -/
def phys3jGrid (M σ : ℚ) : Set (ℝ × (ℚ × ℚ)) :=
  {p | SpecAdm M σ p.2.1 ∧ Lat4 M σ p.2.1 p.2.2 ∧ p.1 = 2 * (p.2.2 : ℝ) / p.2.1}

/-- The filter `N → ∞` on the index `(N, μ)`. -/
def atN : Filter (ℚ × ℚ) := Filter.comap (fun q : ℚ × ℚ => (q.1 : ℝ)) atTop

/-- The expansion parameter `ε = N⁻²`. -/
noncomputable def eps3j (q : ℚ × ℚ) : ℝ := 1 / (q.1 : ℝ) ^ 2

theorem tendsto_eps3j : Tendsto eps3j atN (𝓝 0) :=
  (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)).comp Filter.tendsto_comap

/-- **`thm:3jeven` in the `HasUniformExpansionOn` language.**  For compact `K ⊆ (-1,1)`, the
amplitude `Φ_L^{M,σ}(x; 1/N)`, `L = L₀ + k`, has the uniform asymptotic expansion
`∑ r, N^{-2r} f_{2r}(x)` as `N → ∞` on the physical grid, uniformly for `x ∈ K`. -/
theorem Phi3j_hasUniformExpansionOn (M σ : ℚ) (k : ℕ) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    HasUniformExpansionOn (phys3jGrid M σ)
      (fun _ q => Phi3j (max |M| |σ| + k) M σ q.1 q.2) (f3even M σ k) eps3j atN K := by
  have hKU : K ×ˢ ({0} : Set ℝ) ⊆ Gc3Dom M σ k := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have : t = 0 := ht
    subst this
    exact mem_Gc3Dom_zero M σ k (hKI hx)
  have hcoef : f3even M σ k = taylorCoeff fun z t => Gc3 M σ k z t := by
    funext r x
    exact (taylorCoeff_eq_racah _ r x).symm
  rw [hcoef]
  refine hasUniformExpansionOn_of_analytic (G := fun q : ℝ × ℝ => Gc3 M σ k q.1 q.2)
    (Gc3Dom_isOpen M σ k) (analyticOnNhd_Gc3 M σ k) hK hKU tendsto_eps3j _ ?_
  have hev : ∀ᶠ q in atN, ((max |M| |σ| + k + 1 : ℚ) : ℝ) ≤ (q.1 : ℝ) :=
    Filter.tendsto_comap.eventually (eventually_ge_atTop _)
  filter_upwards [hev] with q hq z hz _
  obtain ⟨hA, hlat, hz'⟩ := hz
  simp only at hA hlat hz'
  rw [hz']
  have hk : max |M| |σ| + k + 1 ≤ q.1 := by exact_mod_cast hq
  have hNpos : 0 < q.1 := by
    have : (0 : ℚ) < max |M| |σ| + k + 1 := by positivity
    exact lt_of_lt_of_le this hk
  exact Phi3j_eq_Gc3_spec M σ q.1 q.2 hA hNpos hlat k hk

/-- **`Phi3j_even_expansion`, recovered from `Phi3j_hasUniformExpansionOn`** (the explicit
`∃ C N₀` form of the paper's `eq:3jevenexp`). -/
theorem Phi3j_even_expansion_of_api (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) {K : Set ℝ}
    (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) (R : ℕ) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      2 * (μ : ℝ) / N ∈ K →
      |Phi3j L M σ N μ -
          ∑ r ∈ Finset.range R, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)| ≤
        C / (N : ℝ) ^ (2 * R) := by
  subst hL
  obtain ⟨C, hC⟩ := (hasUniformExpansionOn_iff.1 (Phi3j_hasUniformExpansionOn M σ k hK hKI)) R
  rw [atN, Filter.eventually_comap] at hC
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hC
  refine ⟨C, N₀, fun N μ hA hlat hN hx => ?_⟩
  have key := hN₀ (N : ℝ) hN (N, μ) rfl _ hx ⟨hA, hlat, rfl⟩
  have e1 : ∀ r : ℕ, eps3j (N, μ) ^ r • f3even M σ k r (2 * (μ : ℝ) / N) =
      f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r) := by
    intro r
    simp only [eps3j, smul_eq_mul]
    rw [one_div, inv_pow, ← pow_mul, inv_mul_eq_div]
  simp only [e1, Real.norm_eq_abs] at key
  unfold eps3j at key
  have e2 : |1 / (N : ℝ) ^ 2| ^ R = 1 / (N : ℝ) ^ (2 * R) := by
    rw [abs_of_nonneg (by positivity), one_div, inv_pow, ← pow_mul, one_div]
  rw [e2] at key
  calc _ ≤ C * (1 / (N : ℝ) ^ (2 * R)) := key
    _ = C / (N : ℝ) ^ (2 * R) := by ring

end ThreeJ

/-- info: 'FormalResearch.Asymptotics.Phi3j_hasUniformExpansionOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_hasUniformExpansionOn

/-- info: 'FormalResearch.Asymptotics.Phi3j_even_expansion_of_api' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_even_expansion_of_api

end FormalResearch.Asymptotics
