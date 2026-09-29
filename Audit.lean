/-
Audit.lean — enumerated declaration audit.

Run with:  lake env lean Audit.lean

Prints the axiom footprint of the declarations explicitly listed below. The
acceptance rules are:

* no `sorryAx` may appear anywhere (equivalently: no `sorry`/`admit`);
* no custom `axiom` declarations exist in the modules (only Lean's
  built-in `propext` / `Quot.sound` may show up, and they are listed
  honestly below);
* `Classical.choice` must NOT appear in any footprint;
* no `unsafe` or `native_decide` is used in the modules.

Any deviation shows up directly in the printed lists.
-/

import PPAC

/-! ## Part A: pullback along an old surjection -/

#print axioms PPAC.image
#print axioms PPAC.preimage
#print axioms PPAC.image_preimage_iff
#print axioms PPAC.image_preimage_eq
#print axioms PPAC.ImageClosed
#print axioms PPAC.notOld_preimage

/-! ## Part A: nonvacuity examples -/

#print axioms PPAC.two_point_surjection_example
#print axioms PPAC.pullback_identity_example
#print axioms PPAC.image_closed_empty_example
#print axioms PPAC.notOld_example

/-! ## Part B: stage capture and stabilization -/

#print axioms PPAC.ssub
#print axioms PPAC.StageTransitive
#print axioms PPAC.StageMonotone
#print axioms PPAC.FinalSubsetsInFinal
#print axioms PPAC.CofinallyFresh
#print axioms PPAC.single_stage_capture
#print axioms PPAC.eventual_stability
#print axioms PPAC.not_cofinal_fresh
#print axioms PPAC.not_cofinal_fresh_of_stability

/-! ## Part B: nonvacuity examples -/

#print axioms PPAC.example_stage_transitive
#print axioms PPAC.example_captured
#print axioms PPAC.example_final_subsets_in_final
#print axioms PPAC.example_monotone
#print axioms PPAC.example_single_capture
#print axioms PPAC.example_no_cofinal_fresh

/-! ## Batch 2: choice interfaces (PPAC/Choice/Basic.lean) -/

#print axioms PPAC.Choice.Trich
#print axioms PPAC.Choice.WO
#print axioms PPAC.Choice.wo_empty
#print axioms PPAC.Choice.wo_subsingleton
#print axioms PPAC.Choice.least_unique
#print axioms PPAC.Choice.PP
#print axioms PPAC.Choice.OrdIndex
#print axioms PPAC.Choice.AC_WO
#print axioms PPAC.Choice.SVC

/-! ## Batch 2: splicing engine (PPAC/Choice/Splice.lean) -/

#print axioms PPAC.Choice.FiberRel
#print axioms PPAC.Choice.rho_transport
#print axioms PPAC.Choice.spliceRel
#print axioms PPAC.Choice.spliceRel_index
#print axioms PPAC.Choice.spliceRel_fiber
#print axioms PPAC.Choice.splice_trich
#print axioms PPAC.Choice.splice_wf
#print axioms PPAC.Choice.partition_splice_wo

/-! ## Batch 2: splitting lemma (PPAC/Choice/Splitting.lean) -/

#print axioms PPAC.Choice.sec
#print axioms PPAC.Choice.Fiber
#print axioms PPAC.Choice.BlockMem
#print axioms PPAC.Choice.Block
#print axioms PPAC.Choice.blockFwd
#print axioms PPAC.Choice.blockFwd_inj
#print axioms PPAC.Choice.pullback_trich
#print axioms PPAC.Choice.pullback_wf
#print axioms PPAC.Choice.fiber_wo_of_block_wo
#print axioms PPAC.Choice.block_disjoint
#print axioms PPAC.Choice.badFiberExists
#print axioms PPAC.Choice.minBadIdx
#print axioms PPAC.Choice.minBadIdx_bad
#print axioms PPAC.Choice.nonwo_splitting
#print axioms PPAC.Choice.countable_blocks
#print axioms PPAC.Choice.svc_pp_splitting

/-! ## Batch 3: repair-forcing primitives (PPAC/Repair/Forcing.lean) -/

#print axioms PPAC.Repair.AC_omega_count
#print axioms PPAC.Repair.Countable
#print axioms PPAC.Repair.countable_sum
#print axioms PPAC.Repair.countable_of_injective
#print axioms PPAC.Repair.jrelOf
#print axioms PPAC.Repair.jrelOf_fun
#print axioms PPAC.Repair.jrelOf_sec
#print axioms PPAC.Repair.jrelOf_inj
#print axioms PPAC.Repair.jrelOf_injDir
#print axioms PPAC.Repair.jrelOf_total
#print axioms PPAC.Repair.SecList
#print axioms PPAC.Repair.SecListLe
#print axioms PPAC.Repair.secList_grow
#print axioms PPAC.Repair.Cover
#print axioms PPAC.Repair.SecCnt
#print axioms PPAC.Repair.SecCntLe
#print axioms PPAC.Repair.CntPartFun
#print axioms PPAC.Repair.CPFLe

/-! ## Batch 3: finite-support projection (PPAC/Repair/Projection.lean) -/

#print axioms PPAC.Repair.SwapCoding
#print axioms PPAC.Repair.jrelSec
#print axioms PPAC.Repair.projRel
#print axioms PPAC.Repair.projRel_mono
#print axioms PPAC.Repair.denseD_r
#print axioms PPAC.Repair.collapse_fin
#print axioms PPAC.Repair.collapse_fin_fun

/-! ## Batch 3: countable parity projection (PPAC/Repair/Parity.lean) -/

#print axioms PPAC.Repair.BitCoding
#print axioms PPAC.Repair.BlockCoding
#print axioms PPAC.Repair.jrelCnt
#print axioms PPAC.Repair.projCnt
#print axioms PPAC.Repair.projCnt_mono
#print axioms PPAC.Repair.denseBlock
#print axioms PPAC.Repair.collapse_cnt
#print axioms PPAC.Repair.collapse_cnt_fun

/-! ## Batch 3: name evaluation and free-injection collapse
(PPAC/Repair/NameEval.lean) -/

#print axioms PPAC.Repair.WOrd
#print axioms PPAC.Repair.prodLex
#print axioms PPAC.Repair.fiberTrich
#print axioms PPAC.Repair.prodLex_trich
#print axioms PPAC.Repair.prodLex_wf
#print axioms PPAC.Repair.prodLexLeast
#print axioms PPAC.Repair.svc_name_eval
#print axioms PPAC.Repair.wo_of_surjection
#print axioms PPAC.Repair.InjCnt
#print axioms PPAC.Repair.InjCntLe
#print axioms PPAC.Repair.jrelInj
#print axioms PPAC.Repair.FreshPool
#print axioms PPAC.Repair.denseD_s
#print axioms PPAC.Repair.collapse_free
#print axioms PPAC.Repair.collapse_free_fun

/-! ## Batch 4: fixed-seed pollution obstruction
(PPAC/ClassObstruction/Obstruction.lean) -/

#print axioms PPAC.ClassObstruction.PredFamily
#print axioms PPAC.ClassObstruction.countable_unit
#print axioms PPAC.ClassObstruction.RCond
#print axioms PPAC.ClassObstruction.RCondLe
#print axioms PPAC.ClassObstruction.DomFresh
#print axioms PPAC.ClassObstruction.SliceFresh
#print axioms PPAC.ClassObstruction.RCond.pairExt
#print axioms PPAC.ClassObstruction.RCond.forbidExt
#print axioms PPAC.ClassObstruction.denseTwoBranch
#print axioms PPAC.ClassObstruction.RanG
#print axioms PPAC.ClassObstruction.TG
#print axioms PPAC.ClassObstruction.FGRan_false
#print axioms PPAC.ClassObstruction.trace_not_old
#print axioms PPAC.ClassObstruction.Upred
#print axioms PPAC.ClassObstruction.pollution_pullback
#print axioms PPAC.ClassObstruction.StageFreeze
#print axioms PPAC.ClassObstruction.stage_freeze_contra

/-! ## Batch 5: Cohen-locality rank argument (PPAC/Cohen/Locality.lean) -/

#print axioms PPAC.Cohen.CohenLocality
#print axioms PPAC.Cohen.wf_desc_false
#print axioms PPAC.Cohen.RankAux
#print axioms PPAC.Cohen.HFamily
#print axioms PPAC.Cohen.rank_contra

/-! ## Batch 6: random-side primitives (PPAC/Random/Approx.lean) -/

#print axioms PPAC.Random.FinBit
#print axioms PPAC.Random.FinBitLe
#print axioms PPAC.Random.finBit_grow
#print axioms PPAC.Random.list_le_foldr_max
#print axioms PPAC.Random.exists_fresh_nat
#print axioms PPAC.Random.rand_finite_approx
#print axioms PPAC.Random.support_localize
#print axioms PPAC.Random.choice_recovery
#print axioms PPAC.Random.CategoryAcc

/-! ## Batch 7: Fuchs-Prikry choice criterion (PPAC/FuchsPrikry/Criterion.lean) -/

#print axioms PPAC.FuchsPrikry.DC
#print axioms PPAC.FuchsPrikry.PosIdeal
#print axioms PPAC.FuchsPrikry.IdealMax
#print axioms PPAC.FuchsPrikry.OrbitFamily
#print axioms PPAC.FuchsPrikry.ordIndexUnit
#print axioms PPAC.FuchsPrikry.criterion_forward

#print axioms PPAC.FuchsPrikry.dc_empty
