module

public import FormalResearch.FourQubitEntropy.GOData.GOAll
public import FormalResearch.FourQubitEntropy.GOProbe.Final
public import FormalResearch.FourQubitEntropy.GOProbe.Remainders

/-!
# GO certificate: the full check and the soundness theorem for the generated data

`check_all` is a `native_decide` step (so `#print axioms` shows the extra axiom
`GOProbe.check_all._native.native_decide.ax_1_1`; the global-overlap certificate uses three such steps in all:
`check_all`, `identCheck_true` in `GOGlue/DataCheck.lean` and `consCheck_true` in `GOGlue/ConsCheck.lean`):
the reflective checker `check` of `Block.lean` returns `true` on the generated data
(`cons`: the 64 constraint matrices, `perms`/`flips`: the 6 signed lower permutations and 8 sign changes
(together the 48 coordinate maps), `lit`: the target polynomial,
`allBlocks`: the 277 Gram blocks).  Everything else is proved: `go_sound` (`Final.lean`) turns it into
`go_certificate_sound`.

The generated modules `FormalResearch/FourQubitEntropy/GOData/*` are not committed (about 22 MB).  Produce
them, then build, with

```
python3 FormalResearch/FourQubitEntropy/gen_go_cert.py
lake build FormalResearch.FourQubitEntropy.GOProbe.Check
```

(the generator reads the certificate file `code/data/m4_global_overlap.json`; its output is byte-reproducible; each data module
elaborates in under 4 GB.)  `Smoke.lean` is a committed toy certificate that needs no generated data.

Interface to the paper's objects: `GOGlue/Final.lean` (data-dependent, like this module) proves that `lit / (mapDen · gridC)`
is the paper's `(Q − n²e)/36 − R_sq − R_ax` on the 19 slice coordinates (`GOGlue/DataCheck.lean`; `Remainders.lean` has `Rsq`,
`Rax`), that the literal constraint matrices `cons[c]` evaluated at `g • (f • x)` are positive semidefinite at a closest point
(`GOGlue/ConsCheck.lean`, `GOGlue/OrbitMaps.lean`), and `h0 ≥ 0`; it concludes `globalOverlap_all`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.GOProbe

set_option maxRecDepth 100000

/-- `s² = 2^(2 · factorBits)`, the square of the factor scale. -/
def goS2 : Int := (2 : Int) ^ (2 * factorBits)

theorem check_all : check cons perms flips lit (gridC : Int) goS2 (corrDen : Int) allBlocks = true := by
  native_decide

/-- **Soundness of the GO certificate.**  If every constraint matrix is positive semidefinite at every point
`g • (f • x)` of the orbit of `x`, then the target polynomial `lit` is nonnegative at `x`. -/
theorem go_certificate_sound (x : ℕ → ℝ)
    (hpsd : ∀ g ∈ perms, ∀ f ∈ flips, ∀ c < cons.length, Psd (act g (flipPt f x)) (cons.getD c [])) :
    0 ≤ ev x lit :=
  go_sound check_all x hpsd

/-- The scale `mapDen · grid` of `lit`. -/
def goK : ℝ := (mapDen : ℝ) * (gridC : ℝ)

theorem go_target_nonneg (x : ℕ → ℝ)
    (hpsd : ∀ g ∈ perms, ∀ f ∈ flips, ∀ c < cons.length, Psd (act g (flipPt f x)) (cons.getD c []))
    (hh : 0 ≤ h0 x) (hL : ∀ v : ℕ → ℝ, 0 ≤ ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, v i * Lstar x i j * v j) :
    0 ≤ ev x lit / goK + Rsq x + Rax x := by
  have h1 := go_certificate_sound x hpsd
  have hK : 0 ≤ goK := by unfold goK; positivity
  have := div_nonneg h1 hK
  have := Rsq_nonneg x
  have := Rax_nonneg x hh hL
  linarith

#print axioms go_certificate_sound

end FormalResearch.FourQubitEntropy.GOProbe
