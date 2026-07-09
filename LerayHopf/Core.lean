-- Abstract types and domain definitions
import LerayHopf.Torus.Basic
import LerayHopf.Torus.Domain
import LerayHopf.Torus.FunctionSpaces

-- Functional-analytic spatial layer (𝕋³)
import LerayHopf.Torus.DivergenceFree
import LerayHopf.Torus.SobolevTorus
import LerayHopf.Torus.Leray
import LerayHopf.Torus.GalerkinProjection
import LerayHopf.Torus.VelocityGalerkin

-- Abstract ODE/energy skeleton (no axioms, no sorry)
import LerayHopf.EnergySkeleton

-- Scaffold-era declarations (sorry-free, axiom-free; included for module-graph completeness)
import LerayHopf.GalerkinPackage
import LerayHopf.NonuniquenessStatement

-- Side branches
import LerayHopf.BlowupLowerBound

-- ℝ³ spatial/Fourier sublayer — fully sorry-free and axiom-free.
-- These do NOT import R3/AxiomaticClosure or any file that does.
import LerayHopf.R3.Domain
import LerayHopf.R3.DivergenceFree
import LerayHopf.R3.Regularity
import LerayHopf.R3.FourierL2
import LerayHopf.R3.RellichBall
import LerayHopf.R3.SpatialCompactness
import LerayHopf.R3.TrilinearEstimate

/-!
# LerayHopf.Core — axiom-free, sorryAx-free import surface

This module collects the spatial/regularity/Fourier/Rellich layer of the
Leray–Hopf formalization.  Every declaration reachable via this module must be
**project-axiom-free** and **sorryAx-free**: `#print axioms` on any theorem
imported here should show only

    propext  Classical.choice  Quot.sound

and none of the project-specific `axiom` declarations from the axiomatic
closure modules (`AxiomaticClosure`, `R3/AxiomaticClosure`).

Downstream core work that does not need the axiomatic closures should
`import LerayHopf.Core` instead of `import LerayHopf`.

Axiomatic layers live in:
- `LerayHopf.Torus.Axiomatic` (imports `LerayHopf.Torus.AxiomaticClosure`)
- `LerayHopf.R3Axiomatic`   (imports `LerayHopf.R3.AxiomaticClosure`)

The full `import LerayHopf` surface continues to export both layers.

## Included modules

### Torus (𝕋³) layer — fully sorry-free and axiom-free

`Torus.Basic`, `Torus.Domain`, `Torus.FunctionSpaces`, `Torus.DivergenceFree`,
`Torus.SobolevTorus`, `Torus.Leray`, `Torus.GalerkinProjection`,
`Torus.VelocityGalerkin`, `EnergySkeleton`,
`GalerkinPackage`, `NonuniquenessStatement`, `BlowupLowerBound`.

### ℝ³ layer — fully sorry-free and axiom-free (spatial/Fourier sublayer)

`R3.Domain`, `R3.DivergenceFree`, `R3.Regularity`, `R3.FourierL2`,
`R3.RellichBall`, `R3.SpatialCompactness`, `R3.TrilinearEstimate`.
-/
