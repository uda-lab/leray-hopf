import LerayHopf.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Fourier.AddCircle

open MeasureTheory

/-!
# Torus domain: instances and type aliases

**M2 — D-02, D-03.**  This file consolidates the domain type `Torus3 = UnitAddTorus (Fin 3)`,
verifies the measure-space instance chain, introduces basic type aliases, and defines the
canonical Haar product measure `haarTorus3` used by all function spaces in this project.

## Instance chain for `Torus3`

`Torus3 = UnitAddTorus (Fin 3) = Fin 3 → UnitAddCircle` inherits its `MeasureSpace`
from `MeasureTheory.MeasureSpace.pi` (`Mathlib/MeasureTheory/Constructions/Pi.lean:215`),
which uses the `MeasureSpace UnitAddCircle` instance provided by
`AddCircle.measureSpace` (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:67`).

For `UnitAddCircle = AddCircle (1 : ℝ)`, the measure has total mass `ENNReal.ofReal 1 = 1`,
as recorded by `UnitAddCircle.measure_univ`. Hence `volume : Measure UnitAddCircle` is a
probability measure.  Since `AddCircleMulti` only registers this as a `local instance`, we
provide the global instance here so that the Pi probability instance fires.

## Single-measure design

All function spaces (`L2VF`, `L2C`) and the Fourier Hilbert basis use the single canonical
measure `haarTorus3 := Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)`.  This is the
measure under which `UnitAddTorus.mFourierBasis` is a Hilbert basis.  The global `volume` on
`Torus3` (from `AddCircle.measureSpace`) equals `haarTorus3` propositionally; the bridge
lemma `volume_torus3_eq_haarTorus3` records this fact.
-/

namespace LerayHopf

-- D-02: Provide the missing global IsProbabilityMeasure instance for UnitAddCircle.
-- UnitAddCircle.measure_univ proves volume (univ : Set UnitAddCircle) = 1, which is
-- exactly the defining condition for IsProbabilityMeasure.
noncomputable instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  IsProbabilityMeasure.mk UnitAddCircle.measure_univ

-- D-02: Instance-resolution checks (friction probe).
-- These must typecheck; they verify the full instance chain from imports to Torus3.
noncomputable example : MeasureSpace Torus3 := inferInstance
noncomputable example : IsProbabilityMeasure (volume : Measure Torus3) := inferInstance

-- D-03: Fiber type of a velocity field: a real 3-vector.
/-- The fiber type of a velocity field: a 3-vector of real numbers.

`EuclideanSpace ℝ (Fin 3) = PiLp 2 (fun _ : Fin 3 => ℝ)` carries
`NormedAddCommGroup`, `InnerProductSpace ℝ`, and `CompleteSpace` for free. -/
abbrev VelocityValue := EuclideanSpace ℝ (Fin 3)

/-- The canonical measure on `Torus3`: the product Haar (probability) measure
`Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)`.

This is the measure under which `UnitAddTorus.mFourierBasis` is a Hilbert basis, so
**all** torus L² spaces in this project (`L2VF`, `L2C`) use it.  It coincides with the
global `volume : Measure Torus3` propositionally (see `volume_torus3_eq_haarTorus3`). -/
noncomputable def haarTorus3 : Measure Torus3 :=
  Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)

/-- The canonical `volume` on `Torus3` coincides with the Haar product measure `haarTorus3`.

`AddCircle.measureSpace` sets `volume = ENNReal.ofReal 1 • haarAddCircle` on each
`UnitAddCircle` fiber, so `volume` on `Torus3` is the Pi product of these, which equals
`Measure.pi (fun _ => haarAddCircle) = haarTorus3` after simplifying the `1 • _` scalar. -/
theorem volume_torus3_eq_haarTorus3 : (volume : Measure Torus3) = haarTorus3 := by
  have hfiber : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  rw [MeasureTheory.volume_pi]
  exact congrArg Measure.pi (funext fun _ => hfiber)

end LerayHopf
