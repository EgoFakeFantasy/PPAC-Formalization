/-
PPAC.lean — aggregate module.

Batch 1: pullback identity under an old surjection (part A) and
capture/stabilization of Final `s`-subsets at transitive stages (part B).
Batch 2: semantic interfaces (PP, AC_WO, SVC, OrdIndex) and the
non-well-ordered splitting lemma with its PP+SVC application.
Batch 3: repair-forcing primitives — finite/countable section conditions,
the finite swap-coding projection and its countability collapse, the
countable parity projection and block-coding density, name evaluation
preserving a fixed SVC seed, and the free partial-injection collapse.
Batch 4: the fixed-seed pollution obstruction — two-branch density, trace
newness, pullback newness and the stage-freeze contradiction.
Batch 5: the Cohen-locality rank argument (LC kept as an interface).
Batch 6: random-side finite approximation, support localization, choice
recovery, and the R139 negative boundary (no category-acceleration
instance for the measure side).
Batch 7: the Fuchs-Prikry choice criterion (DC interface, position ideal
with the maximum support mod finite, the orbit-family choice direction).

`Audit.lean` (run via `lake env lean Audit.lean`) prints the axiom
footprint of every exported theorem below.

No claim is made about ZF + PP → AC, countermodels, forcing, SVC, or any
complete fixed-seed forcing obstruction.
-/

import PPAC.Pullback
import PPAC.StageCapture
import PPAC.Choice.Basic
import PPAC.Choice.Splice
import PPAC.Choice.Splitting
import PPAC.Repair.Forcing
import PPAC.Repair.Projection
import PPAC.Repair.Parity
import PPAC.Repair.NameEval
import PPAC.ClassObstruction.Obstruction
import PPAC.Cohen.Locality
import PPAC.Random.Approx
import PPAC.FuchsPrikry.Criterion
