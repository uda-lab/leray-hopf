# Literature References — Leray–Hopf Formalization

Source-of-truth reference list for the Lean formalization. Every entry is verified against a
primary source or a stable URL. `UNVERIFIED` entries are marked and must not be used as
proof-of-content claims.

---

## Primary papers

### L1 — Leray 1934 (whole-space existence)

> J. Leray, "Sur le mouvement d'un liquide visqueux emplissant l'espace,"
> *Acta Mathematica* **63** (1934), 193–248.
> DOI: [10.1007/BF02547354](https://doi.org/10.1007/BF02547354)

**Relevance:** Founding paper for Leray–Hopf weak solutions on ℝ³. Introduces the energy
inequality, the mollification-based construction of approximate solutions, and the local
compactness argument (an early form of Fréchet–Kolmogorov applied ball-by-ball). The
`exists_lerayHopf_r3_axiomatic` capstone is the Lean statement of the main result of this
paper.

**Verification status:** DOI resolves to the Springer-hosted Project Euclid digitization.
Full text confirmed accessible at the URL above.

---

### L2 — Hopf 1951 (torus/periodic domain existence)

> E. Hopf, "Über die Anfangswertaufgabe für die hydrodynamischen Grundgleichungen,"
> *Mathematische Nachrichten* **4** (1951), 213–231.
> DOI: [10.1002/mana.3210040121](https://doi.org/10.1002/mana.3210040121)

**Relevance:** Proves Leray–Hopf existence on bounded/periodic domains using Galerkin
approximations. The T³ capstone `exists_lerayHopf_torus3_axiomatic` follows the Hopf
construction: finite-dim Galerkin ODE → Aubin–Lions compactness → limit passage.
Axioms `aubin_lions` and `galerkin_limit_passage` (T³) and their R³ analogues are exactly
the two non-constructive steps Hopf leaves implicit.

**Verification status:** DOI resolves. Year and page range confirmed via SCIRP reference
database entry and Springer link page (abstract visible without paywall).

---

### L3 — Aubin 1963 (compact embedding / time-compactness)

> J.-P. Aubin, "Un théorème de compacité,"
> *Comptes Rendus de l'Académie des Sciences*, Paris **256** (1963), 5042–5044.

**Relevance:** Earliest statement of what became the Aubin–Lions lemma: if a sequence is
bounded in W^{1,p}(0,T;X) then it is relatively compact in L^p(0,T;H) for H compactly
embedded in X. Directly motivates axiom `aubin_lions` (T³) and
`galerkin_spacetime_precompact_R3` (R³, PR #45).

**Verification status:** Verified via SCIRP citation index entry (title, journal, year,
pages confirmed). Full text not freely accessible; bibliographic data confirmed from two
independent citation databases.

---

### L4 — Simon 1986 (compact sets in L^p(0,T;B))

> J. Simon, "Compact sets in the space L^p(0,T;B),"
> *Annali di Matematica Pura ed Applicata* **146** (1986), 65–96.
> DOI: [10.1007/BF01762360](https://doi.org/10.1007/BF01762360)

**Note on year:** The paper is dated 1986 (volume 146 publication); it is sometimes cited
as "Simon 1987" in secondary sources due to print-delivery lag. The authoritative DOI gives
1986. The Springer link resolves to the same article regardless of cited year.

**Relevance:** The standard reference for Aubin–Lions–Simon compactness with sharp Banach-
space hypotheses. Characterizes relative compactness in L^p(0,T;B) by: (i) uniform
boundedness in a "tighter" space, (ii) uniform modulus of continuity in a "looser" space.
`galerkin_spacetime_precompact_R3` (`ArzelaAscoliTime.lean`) axiomatizes the Bochner
L²(0,T;L²(B_R)) compactness step that Simon's theorem provides, and the ALLOW_AXIOM
comments cite this work.

**Verification status:** DOI resolves to Springer full text (paywall, title/abstract
confirmed free). Year, volume, and pages confirmed from three sources (Springer, Mendeley,
Semantic Scholar).

---

### L5 — Alaoglu 1940 (Banach–Alaoglu theorem)

> L. Alaoglu, "Weak topologies of normed linear spaces,"
> *Annals of Mathematics* **41** no. 2 (1940), 252–267.

**Relevance:** The closed unit ball of the dual of any normed space is weak-* compact
(Banach–Alaoglu theorem). For a reflexive Hilbert space, this implies every bounded
sequence has a weakly convergent subsequence. Directly motivates axiom
`galerkin_weakLimit_R3` (`ArzelaAscoliTime.lean`, PR #45), whose ALLOW_AXIOM comment
cites "Banach–Alaoglu (bounded ball weakly compact in reflexive Hilbert space L2VF_R3)."

**Verification status:** Wikipedia and Wolfram MathWorld entries confirm title, journal,
year, volume, pages. Full bibliographic data cross-checked against the Banach–Alaoglu
Wikipedia article (which cites the Annals 1940 paper directly).

**Mathlib counterpart:** `WeakDual.isCompact_closedBall` and `WeakDual.isSeqCompact_closedBall`
in `Mathlib.Analysis.Normed.Module.WeakDual` — but only for the *dual* space, not for a
reflexive Hilbert space identified with its own dual. The gap (identifying L2VF_R3 with
its dual via Riesz) is what makes the axiom necessary.

---

### L6 — Mazur's theorem (weak closedness of closed convex sets)

> S. Mazur, "Über konvexe Mengen in linearen normierten Räumen,"
> *Studia Mathematica* **4** (1933), 70–84.

**Relevance:** A norm-closed convex set in a normed space is also weakly closed
(equivalently: the norm closure equals the weak closure for convex sets). This is needed
to establish that `L2Sigma_R3` (a closed linear subspace) is weakly closed, which is the
second component of `galerkin_weakLimit_R3`'s justification.

**Verification status:** Theorem statement and attribution (Mazur 1933 via Hahn–Banach)
confirmed via the Mazur's Theorem page on ProofWiki and the Wikipedia article on Mazur's
lemma. Full text of the original paper not verified (pre-WWII Polish journal, difficult to
access). The theorem statement itself is a standard consequence of Hahn–Banach and is
uncontroversial.

---

## Monographs

### M1 — Temam 1977 (standard NS reference)

> R. Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*,
> Studies in Mathematics and its Applications **2**.
> North-Holland Publishing, Amsterdam–New York, 1977.
> ISBN: 0-7204-2840-8.
> (AMS Chelsea reprint available: ISBN 978-0-8218-2737-3)

**Relevance:**
- §III.2.1: Aubin–Lions compactness on bounded domains with the energy-bound setup.
  Referenced by axiom `aubin_lions` (`AxiomaticClosure.lean`, T³).
- §III.3: Galerkin limit passage — constructing a weak solution from the compactness
  output. Referenced by axioms `galerkin_limit_passage` (T³) and
  `galerkin_limit_passage_R3` (R³).
- §II.§1: Bilinear form b(u,v,w) on torus/bounded domain, antisymmetry, bounds.
  Referenced by axioms `torusConvectionGap_exists` and `r3_NSForms_exist`.

**Verification status:** Title, publisher, series, year, and ISBN confirmed via Google
Books entry and AMS catalogue entry. Chapter references (III.2.1, III.3, II.1) are
standard and corroborated by the project's own inline citations.

---

### M2 — Lions 1969 (nonlinear BVP / weak NS on bounded domain)

> J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non linéaires*.
> Dunod / Gauthier-Villars, Paris, 1969.

**Relevance:** Establishes Galerkin + Aubin–Lions existence for NS on bounded domains.
Foundational for the abstract framework underlying the T³ capstone. Referenced implicitly
via Temam, who builds on Lions's framework.

**Verification status:** Title, publisher, year confirmed via HathiTrust catalogue record
and Stanford SearchWorks entry. No ISBN (pre-ISBN era). Full text not verified beyond
catalogue records.

---

### M3 — Lemarié-Rieusset 2002 (modern whole-space analysis)

> P.-G. Lemarié-Rieusset, *Recent Developments in the Navier–Stokes Problem*,
> Research Notes in Mathematics. Chapman & Hall/CRC, Boca Raton, 2002.
> ISBN: 1-58488-220-4.

**Relevance:** Modern harmonic-analysis treatment; §5 contains the bilinear convection
form b on ℝ³ (referenced in `r3_NSForms_exist`'s ALLOW_AXIOM comment as "Lemarié-Rieusset
§5"); §6 treats local Rellich/compactness arguments on ℝ³ (the context for
`LocalRellichInput` / `SpatialCompactness.lean`).

**Verification status:** Title, publisher, year, and ISBN confirmed via the Routledge
catalogue page. Chapter-level claims (§5 for b, §6 for local Rellich) are UNVERIFIED
in content — the inline code comments assert these, but the actual chapter structure has
not been directly inspected by this reference audit. These claims follow the standard
book structure; readers should confirm if used as a proof-of-content citation.

---

### M4 — Robinson–Rodrigo–Sadowski 2016 (Navier-Stokes equations)

> J. C. Robinson, J. L. Rodrigo, W. Sadowski,
> *The Three-Dimensional Navier–Stokes Equations: Classical Theory*.
> Cambridge Studies in Advanced Mathematics **157**, Cambridge University Press, 2016.
> ISBN: 978-1-107-01966-9.

**Relevance:** Modern treatment used in the project as "RRS" (Robinson–Rodrigo–Sadowski).
Referenced in the axiom ledger for `torusConvectionGap_exists` (§3.2 for bilinear form
bounds) and in `r3_NSForms_exist` context.

**Verification status:** Title, series, publisher, year, and ISBN confirmed via Cambridge
University Press catalogue. Chapter §3.2 claim is from inline code comment; content not
directly verified by this audit.

---

## Fréchet–Kolmogorov compactness

### FK1 — Hanche-Olsen & Holden 2010 (Kolmogorov–Riesz theorem)

> H. Hanche-Olsen and H. Holden, "The Kolmogorov–Riesz compactness theorem,"
> *Expositiones Mathematicae* **28** no. 4 (2010), 385–394.
> arXiv: [0906.4883](https://arxiv.org/abs/0906.4883)

**Relevance:** Provides the modern statement and proof of the Fréchet–Kolmogorov theorem
(L^p compactness via translation modulus + tail condition) in a self-contained reference.
The Fréchet–Kolmogorov chain in `FrechetKolmogorov.lean` / `RellichBall.lean` (Stream B,
discharged `spatial_compactness_R3`) relies on this criterion.

**Verification status:** arXiv preprint confirmed accessible. Published in *Exposit.
Math.* 2010 confirmed via journal entry on the Expositiones website and multiple
secondary citations. Year, volume, pages confirmed.

---

## Mathlib 4 modules (current pinned version)

The following Mathlib module paths are confirmed present in the pinned version of Mathlib
used by this project (checked against `ArzelaAscoliTime.lean` imports, grep of `.lake/`,
and the project's import statements).

| Module path | Key declarations | Used in this project |
|---|---|---|
| `Mathlib.MeasureTheory.Function.ConvergenceInMeasure` | `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`, `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` | `ArzelaAscoliTime.lean` — extraction chain for `galerkin_spacetime_precompact_R3` plumbing |
| `Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable` | `aestronglyMeasurable_of_tendsto_ae` (line ~1009) | `ArzelaAscoliTime.lean` — measurability of the assembled limit curve |
| `Mathlib.Analysis.Normed.Module.WeakDual` | `WeakDual.isCompact_closedBall`, `WeakDual.isSeqCompact_closedBall` | Background for `galerkin_weakLimit_R3` (not yet a direct import — the gap is identifying L2VF_R3 with its own dual) |
| `Mathlib.Topology.Sequences` | `IsCompact.tendsto_subseq`, `IsCompact.isSeqCompact`, `IsSeqCompact.subseq_of_frequently_in` | `SpatialCompactness.lean`, `ArzelaAscoliTime.lean` |
| `Mathlib.MeasureTheory.Function.L2Space` | `MeasureTheory.L2.norm_sq_eq_re_inner` | `SpatialCompactness.lean` — bridge between set-integral and L²(B_R) metric |
| `Mathlib.Analysis.InnerProductSpace.Projection` | `Submodule.starProjection`, orthogonal projection API | `GalerkinScheme.lean` |
| `Mathlib.MeasureTheory.Integral.IntervalIntegral` | `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `intervalIntegral.norm_integral_le_integral_norm` | `GalerkinODE.lean` — energy identity via FTC |
| `Mathlib.Analysis.SpecialFunctions.FourierMult` / `Lp.fourierTransformₗᵢ` | Plancherel / L² Fourier isometry | `FourierL2.lean`, `RellichBall.lean` |

**Verification status:** Module paths confirmed by grep of import statements in the actual
Lean source files in this repository and cross-check against the mathlib4 online docs
(leanprover-community.github.io/mathlib4_docs/). Declaration names for
`tendstoInMeasure_of_tendsto_eLpNorm` and `TendstoInMeasure.exists_seq_tendsto_ae`
confirmed by direct fetch of the mathlib4 docs page for
`Mathlib.MeasureTheory.Function.ConvergenceInMeasure`. Declaration
`aestronglyMeasurable_of_tendsto_ae` confirmed at line ~1009 of the source file per
docs fetch. `WeakDual.isCompact_closedBall` and `WeakDual.isSeqCompact_closedBall`
confirmed by docs fetch of `Mathlib.Analysis.Normed.Module.WeakDual`.

---

## New axiom frontier references (PR #44 / PR #45 — merged)

The two axioms introduced in PR #45 (`galerkinSpaceTimeExtraction_R3` replaced by
`galerkin_spacetime_precompact_R3` + `galerkin_weakLimit_R3`) have the following
literature grounding:

### `galerkin_spacetime_precompact_R3`

**Mathematical content:** LOCAL Aubin–Lions–Simon spacetime precompactness in
L²(0,T;L²(B_k)). For every input subsequence ψ and every ball radius k, the per-ball
Galerkin curve sequence has a further subsequence converging to zero in the Bochner
L²(0,T;L²(B_k)) norm.

**Literature grounding:**
- Simon [L4]: the fundamental compactness criterion in L^p(0,T;B).
- Aubin [L3]: the original compact-embedding theorem for time-varying Banach-space
  functions.
- Temam [M1] §III.2.1: the Galerkin-sequence setup in which the theorem is applied.

**What is NOT in Mathlib:** Mathlib has no Bochner-valued Aubin–Lions lemma / Simon
theorem / Fréchet–Kolmogorov theorem in L^p(0,T;X). The Mathlib extraction chain used
(`tendstoInMeasure_of_tendsto_eLpNorm` → `TendstoInMeasure.exists_seq_tendsto_ae`) gives
a.e.-t subsequence convergence FROM an L²-in-time norm bound; the axiom asserts the
existence of such a further subsequence with the norm bound going to zero.

### `galerkin_weakLimit_R3`

**Mathematical content:** From per-ball a.e.-t convergence of a bounded Galerkin
subsequence, extract a measurable weak limit u in L2Sigma_R3 (divergence-free), with
a.e.-t per-ball convergence to it.

**Literature grounding (two components):**
1. Banach–Alaoglu [L5] / weak compactness of bounded sets in reflexive Hilbert spaces:
   the bounded Galerkin sequence has a weakly convergent subsequence for a.e. t.
2. Mazur [L6] / weak closedness of closed linear subspaces: L2Sigma_R3 = ker(div) is
   closed, hence weakly closed, so the weak limit is divergence-free.

**Mathlib gap:** `WeakDual.isSeqCompact_closedBall` covers the *dual* space; applying it
to L2VF_R3 requires the Riesz identification L2VF_R3 ≅ L2VF_R3* (reflexivity), which
is not yet threaded through the project's type definitions. Weak closedness of
`L2Sigma_R3 = ⨅_k ker(divTestFunctional k)` (as a closed submodule of L2VF_R3) follows
from Mazur but is not formalized in Mathlib at this interface.
