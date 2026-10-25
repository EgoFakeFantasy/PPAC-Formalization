/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Apache 2.0; see third_party/constructible-universe/LICENSE.
Literal pure-syntax dependency slice of lean-constructible-universe
7f5a7d03d63d9769172f17350bbe8303996e5b53. Source declaration bodies are
preserved. Model/Mathlib imports and theorems are omitted; finite-vector
notation is elaborated to Fin.cases. Existing syntax is retained as data for
translation into PPAC Source; no checker, satisfaction recursion or proof
kernel is introduced here. Source mapping/hashes are in SOURCE_LOCK.json.
-/
import Std
import Lean.Elab.Tactic.Omega

namespace PPAC.Migration.ExistingConstructible
set_option autoImplicit false
universe u v
scoped syntax "![" term,* "]" : term
open scoped PPAC.Migration.ExistingConstructible
macro_rules
  | `(![$xs:term,*]) => do
      let mut body ← `(Fin.elim0)
      for x in xs.getElems.reverse do
        body ← `(Fin.cases $x $body)
      pure body
namespace Constructible
end Constructible
namespace Constructible.FiniteSequenceZF
end Constructible.FiniteSequenceZF
namespace Constructible.Delta0Formula
end Constructible.Delta0Formula
namespace Constructible.FOFormula
end Constructible.FOFormula
namespace Constructible.Godel
end Constructible.Godel
namespace Constructible.Godel.RudimentaryTerm
end Constructible.Godel.RudimentaryTerm
namespace Constructible.IndexedSequenceZF
end Constructible.IndexedSequenceZF
namespace Constructible


-- BEGIN ORIGINAL Constructible.FOFormula
inductive FOFormula : Nat → Type
  | mem {n : Nat} (i j : Fin n) : FOFormula n
  | eq {n : Nat} (i j : Fin n) : FOFormula n
  | neg {n : Nat} (φ : FOFormula n) : FOFormula n
  | conj {n : Nat} (φ ψ : FOFormula n) : FOFormula n
  | ex {n : Nat} (φ : FOFormula (n + 1)) : FOFormula n
-- END ORIGINAL Constructible.FOFormula
end Constructible

namespace Constructible.FOFormula


-- BEGIN ORIGINAL Constructible.FOFormula.disj
def disj {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  .neg (.conj (.neg φ) (.neg ψ))
-- END ORIGINAL Constructible.FOFormula.disj

-- BEGIN ORIGINAL Constructible.FOFormula.imp
def imp {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  disj (.neg φ) ψ
-- END ORIGINAL Constructible.FOFormula.imp

-- BEGIN ORIGINAL Constructible.FOFormula.biimp
def biimp {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  .conj (imp φ ψ) (imp ψ φ)
-- END ORIGINAL Constructible.FOFormula.biimp

-- BEGIN ORIGINAL Constructible.FOFormula.all
def all {n : Nat} (φ : FOFormula (n + 1)) : FOFormula n :=
  .neg (.ex (.neg φ))
-- END ORIGINAL Constructible.FOFormula.all

-- BEGIN ORIGINAL Constructible.FOFormula.liftRename
def liftRename {n m : Nat} (ρ : Fin n → Fin m) :
    Fin (n + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (ρ i).castSucc)
-- END ORIGINAL Constructible.FOFormula.liftRename

-- BEGIN ORIGINAL Constructible.FOFormula.rename
def rename {n m : Nat} (ρ : Fin n → Fin m) : FOFormula n → FOFormula m
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .neg φ => .neg (rename ρ φ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .ex φ => .ex (rename (liftRename ρ) φ)
-- END ORIGINAL Constructible.FOFormula.rename

-- BEGIN ORIGINAL Constructible.FOFormula.weaken
def weaken {n : Nat} (φ : FOFormula n) : FOFormula (n + 1) :=
  rename Fin.castSucc φ
-- END ORIGINAL Constructible.FOFormula.weaken

-- BEGIN ORIGINAL Constructible.FOFormula.boundedEx
def boundedEx {n : Nat} (i : Fin n) (φ : FOFormula (n + 1)) : FOFormula n :=
  .ex (.conj (.mem (Fin.last n) i.castSucc) φ)
-- END ORIGINAL Constructible.FOFormula.boundedEx

-- BEGIN ORIGINAL Constructible.FOFormula.boundedAll
def boundedAll {n : Nat} (i : Fin n) (φ : FOFormula (n + 1)) : FOFormula n :=
  .neg (boundedEx i (.neg φ))
-- END ORIGINAL Constructible.FOFormula.boundedAll
end Constructible.FOFormula

namespace Constructible


-- BEGIN ORIGINAL Constructible.Delta0Formula
inductive Delta0Formula : Nat → Type
  | mem {n : Nat} (i j : Fin n) : Delta0Formula n
  | eq {n : Nat} (i j : Fin n) : Delta0Formula n
  | neg {n : Nat} (φ : Delta0Formula n) : Delta0Formula n
  | conj {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n
  | boundedEx {n : Nat} (i : Fin n) (φ : Delta0Formula (n + 1)) :
      Delta0Formula n
-- END ORIGINAL Constructible.Delta0Formula
end Constructible

namespace Constructible.Delta0Formula


-- BEGIN ORIGINAL Constructible.Delta0Formula.toFO
def toFO : {n : Nat} → Delta0Formula n → FOFormula n
  | _, .mem i j => .mem i j
  | _, .eq i j => .eq i j
  | _, .neg φ => .neg (toFO φ)
  | _, .conj φ ψ => .conj (toFO φ) (toFO ψ)
  | _, .boundedEx i φ => FOFormula.boundedEx i (toFO φ)
-- END ORIGINAL Constructible.Delta0Formula.toFO

-- BEGIN ORIGINAL Constructible.Delta0Formula.relativize
def relativize : {n : Nat} → FOFormula n → Delta0Formula (n + 1)
  | _, .mem i j => .mem i.succ j.succ
  | _, .eq i j => .eq i.succ j.succ
  | _, .neg φ => .neg (relativize φ)
  | _, .conj φ ψ => .conj (relativize φ) (relativize ψ)
  | _, .ex φ => .boundedEx 0 (relativize φ)
-- END ORIGINAL Constructible.Delta0Formula.relativize

-- BEGIN ORIGINAL Constructible.Delta0Formula.disj
def disj {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  .neg (.conj (.neg φ) (.neg ψ))
-- END ORIGINAL Constructible.Delta0Formula.disj

-- BEGIN ORIGINAL Constructible.Delta0Formula.imp
def imp {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  disj (.neg φ) ψ
-- END ORIGINAL Constructible.Delta0Formula.imp

-- BEGIN ORIGINAL Constructible.Delta0Formula.biimp
def biimp {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  .conj (imp φ ψ) (imp ψ φ)
-- END ORIGINAL Constructible.Delta0Formula.biimp

-- BEGIN ORIGINAL Constructible.Delta0Formula.boundedAll
def boundedAll {n : Nat} (i : Fin n) (φ : Delta0Formula (n + 1)) :
    Delta0Formula n :=
  .neg (.boundedEx i (.neg φ))
-- END ORIGINAL Constructible.Delta0Formula.boundedAll

-- BEGIN ORIGINAL Constructible.Delta0Formula.liftRename
abbrev liftRename {n m : Nat} (ρ : Fin n → Fin m) :
    Fin (n + 1) → Fin (m + 1) :=
  FOFormula.liftRename ρ
-- END ORIGINAL Constructible.Delta0Formula.liftRename

-- BEGIN ORIGINAL Constructible.Delta0Formula.rename
def rename {n m : Nat} (ρ : Fin n → Fin m) :
    Delta0Formula n → Delta0Formula m
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .neg φ => .neg (rename ρ φ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .boundedEx i φ => .boundedEx (ρ i) (rename (liftRename ρ) φ)
-- END ORIGINAL Constructible.Delta0Formula.rename

-- BEGIN ORIGINAL Constructible.Delta0Formula.subsetAt
def subsetAt {n : Nat} (left right : Fin n) : Delta0Formula n :=
  .boundedAll left
    (.mem (Fin.last n) right.castSucc)
-- END ORIGINAL Constructible.Delta0Formula.subsetAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.singletonEqAt
def singletonEqAt {n : Nat} (set x : Fin n) : Delta0Formula n :=
  .conj (.mem x set)
    (.boundedAll set
      (.eq (Fin.last n) x.castSucc))
-- END ORIGINAL Constructible.Delta0Formula.singletonEqAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.unorderedPairEqAt
def unorderedPairEqAt {n : Nat} (set x y : Fin n) : Delta0Formula n :=
  .conj (.mem x set)
    (.conj (.mem y set)
      (.boundedAll set
        (.disj
          (.eq (Fin.last n) x.castSucc)
          (.eq (Fin.last n) y.castSucc))))
-- END ORIGINAL Constructible.Delta0Formula.unorderedPairEqAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.kuratowskiPairEqAt
def kuratowskiPairEqAt {n : Nat} (pair x y : Fin n) : Delta0Formula n :=
  .conj
    (.boundedEx pair
      (singletonEqAt (Fin.last n) x.castSucc))
    (.conj
      (.boundedEx pair
        (unorderedPairEqAt (Fin.last n) x.castSucc y.castSucc))
      (.boundedAll pair
        (.disj
          (singletonEqAt (Fin.last n) x.castSucc)
          (unorderedPairEqAt (Fin.last n) x.castSucc y.castSucc))))
-- END ORIGINAL Constructible.Delta0Formula.kuratowskiPairEqAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.tripleEqAt
def tripleEqAt {n : Nat} (out x y z : Fin n) : Delta0Formula n :=
  .boundedEx out
    (.boundedEx (Fin.last n)
      (.conj
        (kuratowskiPairEqAt (Fin.last (n + 1))
          y.castSucc.castSucc z.castSucc.castSucc)
        (kuratowskiPairEqAt out.castSucc.castSucc x.castSucc.castSucc
          (Fin.last (n + 1)))))
-- END ORIGINAL Constructible.Delta0Formula.tripleEqAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.withBoundedPairComponents
def withBoundedPairComponents {n : Nat} (relation : Fin n)
    (body : Delta0Formula (n + 5)) : Delta0Formula n :=
  .boundedEx relation
    (.boundedEx (Fin.last n)
      (.boundedEx (Fin.last (n + 1))
        (.boundedEx (Fin.last n).castSucc.castSucc
          (.boundedEx (Fin.last (n + 3)) body))))
-- END ORIGINAL Constructible.Delta0Formula.withBoundedPairComponents

-- BEGIN ORIGINAL Constructible.Delta0Formula.fiberEqAt
def fiberEqAt {n : Nat} (q x z : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll q
      (.boundedEx x.castSucc
        (kuratowskiPairEqAt
          (Fin.last (n + 1))
          (Fin.last n).castSucc
          z.castSucc.castSucc)))
    (.boundedAll x
      (.boundedAll (Fin.last n)
        (.boundedAll (Fin.last (n + 1))
          (.imp
            (kuratowskiPairEqAt
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 2))
              z.castSucc.castSucc.castSucc)
            (.mem (Fin.last (n + 2)) q.castSucc.castSucc.castSucc)))))
-- END ORIGINAL Constructible.Delta0Formula.fiberEqAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.f6MemAt
def f6MemAt {n : Nat} (q x : Fin n) : Delta0Formula n :=
  .boundedEx x
    (.boundedEx (Fin.last n)
      (.boundedEx (Fin.last (n + 1))
        (kuratowskiPairEqAt
          (Fin.last n).castSucc.castSucc
          (Fin.last (n + 2))
          q.castSucc.castSucc.castSucc)))
-- END ORIGINAL Constructible.Delta0Formula.f6MemAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.f8MemAt
def f8MemAt {n : Nat} (q x y : Fin n) : Delta0Formula n :=
  .boundedEx y
    (fiberEqAt q.castSucc x.castSucc (Fin.last n))
-- END ORIGINAL Constructible.Delta0Formula.f8MemAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.successorAt
def successorAt {n : Nat} (succ index : Fin n) : Delta0Formula n :=
  .conj
    (.mem index succ)
    (.conj
      (.boundedAll succ
        (disj
          (.mem (Fin.last n) index.castSucc)
          (.eq (Fin.last n) index.castSucc)))
      (.boundedAll index
        (.mem (Fin.last n) succ.castSucc)))
-- END ORIGINAL Constructible.Delta0Formula.successorAt

-- BEGIN ORIGINAL Constructible.Delta0Formula.successorFOAt
def successorFOAt {n : Nat} (succ index : Fin n) : FOFormula n :=
  (successorAt succ index).toFO
-- END ORIGINAL Constructible.Delta0Formula.successorFOAt
end Constructible.Delta0Formula

namespace Constructible.Godel.RudimentaryTerm
open Constructible.IndexedSequenceZF
open Constructible.Delta0Formula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.godelDefEvalRename
def godelDefEvalRename : Fin 16 → Fin 17 :=
  Fin.lastCases (15 : Fin 17)
    (fun i14 => Fin.lastCases (16 : Fin 17)
      (fun i13 => i13.castSucc.castSucc.castSucc) i14)
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.godelDefEvalRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalOmegaIndex
def evalOmegaIndex : Fin 16 := 13
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalOmegaIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalProgramIndex
def evalProgramIndex : Fin 16 := 14
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalProgramIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalProgramValidityRename
def evalProgramValidityRename : Fin 2 → Fin 16 :=
  ![evalOmegaIndex, evalProgramIndex]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalProgramValidityRename
end Constructible.Godel.RudimentaryTerm

namespace Constructible.IndexedSequenceZF
open FiniteSequenceZF

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.formulaImp
def formulaImp {n : Nat} (phi psi : FOFormula n) : FOFormula n :=
  FOFormula.disj (.neg phi) psi
-- END ORIGINAL Constructible.IndexedSequenceZF.formulaImp

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.functionGraphValueAt
def functionGraphValueAt {n : Nat} (graph value index : Fin n) :
    FOFormula n :=
  (Delta0Formula.boundedEx graph
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) value.castSucc index.castSucc)).toFO
-- END ORIGINAL Constructible.IndexedSequenceZF.functionGraphValueAt

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.uniqueValueAtBody
def uniqueValueAtBody : FOFormula 6 :=
  .conj
    (functionGraphValueAt (3 : Fin 6) (5 : Fin 6) (4 : Fin 6))
    (.all
      (formulaImp
        (functionGraphValueAt (3 : Fin 7) (6 : Fin 7) (4 : Fin 7))
        (.eq (6 : Fin 7) (5 : Fin 7))))
-- END ORIGINAL Constructible.IndexedSequenceZF.uniqueValueAtBody

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.totalFunctionalBody
def totalFunctionalBody : FOFormula 5 :=
  formulaImp
    (.mem (4 : Fin 5) (2 : Fin 5))
    (.ex uniqueValueAtBody)
-- END ORIGINAL Constructible.IndexedSequenceZF.totalFunctionalBody

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.sequenceValidityFormula
def sequenceValidityFormula : FOFormula 2 :=
  .ex (.ex
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO
      (.conj
        (.mem (2 : Fin 4) (0 : Fin 4))
        (.all totalFunctionalBody))))
-- END ORIGINAL Constructible.IndexedSequenceZF.sequenceValidityFormula
end Constructible.IndexedSequenceZF

namespace Constructible.Godel.RudimentaryTerm
open Constructible.IndexedSequenceZF
open Constructible.Delta0Formula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalTraceValidityRename
def evalTraceValidityRename : Fin 2 → Fin 17 :=
  ![(13 : Fin 17), (16 : Fin 17)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalTraceValidityRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalProgramLengthRename
def evalProgramLengthRename : Fin 2 → Fin 20 :=
  ![(14 : Fin 20), (17 : Fin 20)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalProgramLengthRename
end Constructible.Godel.RudimentaryTerm

namespace Constructible.IndexedSequenceZF
open FiniteSequenceZF

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.hasLengthFormula
def hasLengthFormula : FOFormula 2 :=
  .ex (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO
-- END ORIGINAL Constructible.IndexedSequenceZF.hasLengthFormula
end Constructible.IndexedSequenceZF

namespace Constructible.Godel.RudimentaryTerm
open Constructible.IndexedSequenceZF
open Constructible.Delta0Formula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalTraceLengthRename
def evalTraceLengthRename : Fin 2 → Fin 20 :=
  ![(16 : Fin 20), (18 : Fin 20)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalTraceLengthRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalInitialValueRename
def evalInitialValueRename : Fin 3 → Fin 20 :=
  Fin.cases (16 : Fin 20)
    (fun j => Fin.cases (3 : Fin 20) (fun _ => (3 : Fin 20)) j)
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalInitialValueRename
end Constructible.Godel.RudimentaryTerm

namespace Constructible.IndexedSequenceZF
open FiniteSequenceZF

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.withBoundedKuratowskiComponents
def withBoundedKuratowskiComponents {n : Nat} (pair : Fin n)
    (body : Delta0Formula (n + 4)) : Delta0Formula n :=
  .boundedEx pair
    (.boundedEx (Fin.last n)
      (.boundedEx pair.castSucc.castSucc
        (.boundedEx (Fin.last (n + 2)) body)))
-- END ORIGINAL Constructible.IndexedSequenceZF.withBoundedKuratowskiComponents

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.graphPairMemAt
def graphPairMemAt {n : Nat} (relation output input : Fin n) :
    Delta0Formula n :=
  .boundedEx relation
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) output.castSucc input.castSucc)
-- END ORIGINAL Constructible.IndexedSequenceZF.graphPairMemAt

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.valueAtDelta0
def valueAtDelta0 : Delta0Formula 3 :=
  withBoundedKuratowskiComponents 0
    (.conj
      (Delta0Formula.kuratowskiPairEqAt 0 4 6)
      (.conj (.mem 1 4) (graphPairMemAt 6 2 1)))
-- END ORIGINAL Constructible.IndexedSequenceZF.valueAtDelta0

-- BEGIN ORIGINAL Constructible.IndexedSequenceZF.valueAtFormula
def valueAtFormula : FOFormula 3 :=
  valueAtDelta0.toFO
-- END ORIGINAL Constructible.IndexedSequenceZF.valueAtFormula
end Constructible.IndexedSequenceZF

namespace Constructible.Godel.RudimentaryTerm
open Constructible.IndexedSequenceZF
open Constructible.Delta0Formula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalFinalValueRename
def evalFinalValueRename : Fin 3 → Fin 20 :=
  ![(16 : Fin 20), (17 : Fin 20), (19 : Fin 20)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalFinalValueRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.evalTraceStepRename
def evalTraceStepRename : Fin 16 → Fin 21 :=
  Fin.lastCases (20 : Fin 21)
    (fun i15 => Fin.lastCases (16 : Fin 21)
      (fun i14 => Fin.lastCases (14 : Fin 21)
        (fun i13 =>
          i13.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        i14) i15)
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.evalTraceStepRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepProgramValueRename
def traceStepProgramValueRename : Fin 3 -> Fin 20 :=
  ![(13 : Fin 20), (15 : Fin 20), (16 : Fin 20)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepProgramValueRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepInputValueRename
def traceStepInputValueRename : Fin 3 -> Fin 20 :=
  ![(14 : Fin 20), (15 : Fin 20), (17 : Fin 20)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepInputValueRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepOutputValueRename
def traceStepOutputValueRename : Fin 3 -> Fin 20 :=
  ![(14 : Fin 20), (18 : Fin 20), (19 : Fin 20)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepOutputValueRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepStackStepRename
def traceStepStackStepRename : Fin 16 -> Fin 20 :=
  Fin.lastCases (19 : Fin 20)
    (fun i15 => Fin.lastCases (17 : Fin 20)
      (fun i14 => Fin.lastCases (16 : Fin 20)
        (fun i13 =>
          i13.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        i14) i15)
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepStackStepRename

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepLiftOne
def stackStepLiftOne (i : Fin 16) : Fin 17 :=
  i.castSucc
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepLiftOne

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepTokenIndex
def stackStepTokenIndex : Fin 16 := 13
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepTokenIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepVarTagIndex
def stackStepVarTagIndex : Fin 16 := 1
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepVarTagIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepEmptyIndex
def stackStepEmptyIndex : Fin 16 := 3
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepEmptyIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepUniverseIndex
def stackStepUniverseIndex : Fin 16 := 0
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepUniverseIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepOutputIndex
def stackStepOutputIndex : Fin 16 := 15
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepOutputIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepInputIndex
def stackStepInputIndex : Fin 16 := 14
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepInputIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.variableStackStepFormula
def variableStackStepFormula : FOFormula 16 :=
  .ex
    (.conj
      (Delta0Formula.tripleEqAt
        (stackStepLiftOne stackStepTokenIndex)
        (stackStepLiftOne stackStepVarTagIndex)
        (Fin.last 16)
        (stackStepLiftOne stackStepEmptyIndex)).toFO
      (.conj
        (FOFormula.disj
          (.eq (Fin.last 16)
            (stackStepUniverseIndex.castSucc))
          (.mem (Fin.last 16)
            (stackStepUniverseIndex.castSucc)))
        (Delta0Formula.kuratowskiPairEqAt
          (stackStepOutputIndex.castSucc)
          (Fin.last 16)
          (stackStepInputIndex.castSucc)).toFO))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.variableStackStepFormula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepLiftFive
def stackStepLiftFive (i : Fin 16) : Fin 21 :=
  i.castSucc.castSucc.castSucc.castSucc.castSucc
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepLiftFive

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepAppTagIndex
def stackStepAppTagIndex : Fin 16 := 2
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepAppTagIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepOperationIndex
def stackStepOperationIndex (i : Fin 9) : Fin 16 :=
  ⟨4 + i.1, by omega⟩
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepOperationIndex

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepOpGraphRename
def stackStepOpGraphRename : Fin 3 → Fin 21 :=
  ![(19 : Fin 21), (17 : Fin 21), (16 : Fin 21)]
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepOpGraphRename
end Constructible.Godel.RudimentaryTerm

namespace Constructible.Godel
open Constructible.Delta0Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF0Formula
def graphF0Formula : Delta0Formula 3 :=
  unorderedPairEqAt 0 1 2
-- END ORIGINAL Constructible.Godel.graphF0Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF1Formula
def graphF1Formula : Delta0Formula 3 :=
  .conj
    (subsetAt 0 1)
    (.boundedAll 1
      (.biimp
        (.mem 3 0)
        (.neg (.mem 3 2))))
-- END ORIGINAL Constructible.Godel.graphF1Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF2Formula
def graphF2Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.boundedEx 2
          (kuratowskiPairEqAt 3 4 5))))
    (.boundedAll 1
      (.boundedAll 2
        (.boundedEx 0
          (kuratowskiPairEqAt 5 3 4))))
-- END ORIGINAL Constructible.Godel.graphF2Formula

-- BEGIN ORIGINAL Constructible.Godel.memF0Formula
def memF0Formula : Delta0Formula 3 :=
  .disj (.eq 0 1) (.eq 0 2)
-- END ORIGINAL Constructible.Godel.memF0Formula

-- BEGIN ORIGINAL Constructible.Godel.memF1Formula
def memF1Formula : Delta0Formula 3 :=
  .conj (.mem 0 1) (.neg (.mem 0 2))
-- END ORIGINAL Constructible.Godel.memF1Formula

-- BEGIN ORIGINAL Constructible.Godel.memF2Formula
def memF2Formula : Delta0Formula 3 :=
  .boundedEx 1
    (.boundedEx 2
      (kuratowskiPairEqAt 0 3 4))
-- END ORIGINAL Constructible.Godel.memF2Formula

-- BEGIN ORIGINAL Constructible.Godel.memF3Formula
def memF3Formula : Delta0Formula 3 :=
  .boundedEx 1
    (withBoundedPairComponents 2
      (.conj
        (kuratowskiPairEqAt 4 6 8)
        (tripleEqAt 0 6 3 8)))
-- END ORIGINAL Constructible.Godel.memF3Formula

-- BEGIN ORIGINAL Constructible.Godel.memF4Formula
def memF4Formula : Delta0Formula 3 :=
  .boundedEx 1
    (withBoundedPairComponents 2
      (.conj
        (kuratowskiPairEqAt 4 6 8)
        (tripleEqAt 0 6 8 3)))
-- END ORIGINAL Constructible.Godel.memF4Formula

-- BEGIN ORIGINAL Constructible.Godel.memF5Formula
def memF5Formula : Delta0Formula 3 :=
  .boundedEx 1 (.mem 0 3)
-- END ORIGINAL Constructible.Godel.memF5Formula

-- BEGIN ORIGINAL Constructible.Godel.memF6Formula
def memF6Formula : Delta0Formula 3 :=
  f6MemAt 0 1
-- END ORIGINAL Constructible.Godel.memF6Formula

-- BEGIN ORIGINAL Constructible.Godel.memF7Formula
def memF7Formula : Delta0Formula 3 :=
  .boundedEx 1
    (.boundedEx 1
      (.conj (kuratowskiPairEqAt 0 3 4) (.mem 3 4)))
-- END ORIGINAL Constructible.Godel.memF7Formula

-- BEGIN ORIGINAL Constructible.Godel.memF8Formula
def memF8Formula : Delta0Formula 3 :=
  f8MemAt 0 1 2
-- END ORIGINAL Constructible.Godel.memF8Formula

-- BEGIN ORIGINAL Constructible.Godel.memOpFormula
def memOpFormula (i : Fin 9) : Delta0Formula 3 :=
  match i.1 with
  | 0 => memF0Formula
  | 1 => memF1Formula
  | 2 => memF2Formula
  | 3 => memF3Formula
  | 4 => memF4Formula
  | 5 => memF5Formula
  | 6 => memF6Formula
  | 7 => memF7Formula
  | 8 => memF8Formula
  | _ => .neg (.eq 0 0)
-- END ORIGINAL Constructible.Godel.memOpFormula

-- BEGIN ORIGINAL Constructible.Godel.memOpAt
def memOpAt {n : Nat} (i : Fin 9) (q x y : Fin n) : Delta0Formula n :=
  Delta0Formula.rename ![q, x, y] (memOpFormula i)
-- END ORIGINAL Constructible.Godel.memOpAt

-- BEGIN ORIGINAL Constructible.Godel.outputSubsetOpAt
def outputSubsetOpAt {n : Nat} (i : Fin 9) (out x y : Fin n) :
    Delta0Formula n :=
  .boundedAll out
    (memOpAt i (Fin.last n) x.castSucc y.castSucc)
-- END ORIGINAL Constructible.Godel.outputSubsetOpAt

-- BEGIN ORIGINAL Constructible.Godel.containsF3Formula
def containsF3Formula : Delta0Formula 3 :=
  .boundedAll 1
    (.boundedAll 2
      (.boundedAll 4
        (.boundedAll 5
          (.boundedAll 4
            (.boundedAll 7
              (.imp
                (kuratowskiPairEqAt 4 6 8)
                (.boundedEx 0
                  (tripleEqAt 9 6 3 8))))))))
-- END ORIGINAL Constructible.Godel.containsF3Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF3Formula
def graphF3Formula : Delta0Formula 3 :=
  .conj (outputSubsetOpAt (3 : Fin 9) 0 1 2) containsF3Formula
-- END ORIGINAL Constructible.Godel.graphF3Formula

-- BEGIN ORIGINAL Constructible.Godel.containsF4Formula
def containsF4Formula : Delta0Formula 3 :=
  .boundedAll 1
    (.boundedAll 2
      (.boundedAll 4
        (.boundedAll 5
          (.boundedAll 4
            (.boundedAll 7
              (.imp
                (kuratowskiPairEqAt 4 6 8)
                (.boundedEx 0
                  (tripleEqAt 9 6 8 3))))))))
-- END ORIGINAL Constructible.Godel.containsF4Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF4Formula
def graphF4Formula : Delta0Formula 3 :=
  .conj (outputSubsetOpAt (4 : Fin 9) 0 1 2) containsF4Formula
-- END ORIGINAL Constructible.Godel.graphF4Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF5Formula
def graphF5Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.mem 3 4)))
    (.boundedAll 1
      (.boundedAll 3
        (.mem 4 0)))
-- END ORIGINAL Constructible.Godel.graphF5Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF6Formula
def graphF6Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (f6MemAt 3 1))
    (.boundedAll 1
      (.boundedAll 3
        (.boundedAll 4
          (.imp
            (f6MemAt 5 1)
            (.mem 5 0)))))
-- END ORIGINAL Constructible.Godel.graphF6Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF7Formula
def graphF7Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.boundedEx 1
          (.conj
            (kuratowskiPairEqAt 3 4 5)
            (.mem 4 5)))))
    (.boundedAll 1
      (.boundedAll 1
        (.imp (.mem 3 4)
          (.boundedEx 0
            (kuratowskiPairEqAt 5 3 4)))))
-- END ORIGINAL Constructible.Godel.graphF7Formula

-- BEGIN ORIGINAL Constructible.Godel.graphF8Formula
def graphF8Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (f8MemAt 3 1 2))
    (.boundedAll 2
      (.boundedEx 0
        (fiberEqAt 4 1 3)))
-- END ORIGINAL Constructible.Godel.graphF8Formula

-- BEGIN ORIGINAL Constructible.Godel.opGraphFormula
def opGraphFormula (i : Fin 9) : Delta0Formula 3 :=
  match i.1 with
  | 0 => graphF0Formula
  | 1 => graphF1Formula
  | 2 => graphF2Formula
  | 3 => graphF3Formula
  | 4 => graphF4Formula
  | 5 => graphF5Formula
  | 6 => graphF6Formula
  | 7 => graphF7Formula
  | 8 => graphF8Formula
  | _ => .neg (.eq 0 0)
-- END ORIGINAL Constructible.Godel.opGraphFormula
end Constructible.Godel

namespace Constructible.Godel.RudimentaryTerm
open Constructible.IndexedSequenceZF
open Constructible.Delta0Formula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.operationStackStepBody
def operationStackStepBody (i : Fin 9) : FOFormula 21 :=
  .conj
    (Delta0Formula.tripleEqAt
      (stackStepLiftFive stackStepTokenIndex)
      (stackStepLiftFive stackStepAppTagIndex)
      (stackStepLiftFive (stackStepOperationIndex i))
      (stackStepLiftFive stackStepEmptyIndex)).toFO
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (stackStepLiftFive stackStepInputIndex)
        (16 : Fin 21) (20 : Fin 21)).toFO
      (.conj
        (Delta0Formula.kuratowskiPairEqAt
          (20 : Fin 21) (17 : Fin 21) (18 : Fin 21)).toFO
        (.conj
          (Delta0Formula.kuratowskiPairEqAt
            (stackStepLiftFive stackStepOutputIndex)
            (19 : Fin 21) (18 : Fin 21)).toFO
          (FOFormula.rename stackStepOpGraphRename
            (opGraphFormula i).toFO))))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.operationStackStepBody

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.operationStackStepFormula
def operationStackStepFormula (i : Fin 9) : FOFormula 16 :=
  .ex (.ex (.ex (.ex (.ex (operationStackStepBody i)))))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.operationStackStepFormula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.anyOperationStackStepFormula
def anyOperationStackStepFormula : FOFormula 16 :=
  FOFormula.disj (operationStackStepFormula 0)
    (FOFormula.disj (operationStackStepFormula 1)
      (FOFormula.disj (operationStackStepFormula 2)
        (FOFormula.disj (operationStackStepFormula 3)
          (FOFormula.disj (operationStackStepFormula 4)
            (FOFormula.disj (operationStackStepFormula 5)
              (FOFormula.disj (operationStackStepFormula 6)
                (FOFormula.disj (operationStackStepFormula 7)
                  (operationStackStepFormula 8))))))))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.anyOperationStackStepFormula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepFormula
def stackStepFormula : FOFormula 16 :=
  FOFormula.disj variableStackStepFormula anyOperationStackStepFormula
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackStepFormula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepBody
def traceStepBody : FOFormula 20 :=
  .conj
    (FOFormula.rename traceStepProgramValueRename
      Constructible.IndexedSequenceZF.valueAtFormula)
    (.conj
      (FOFormula.rename traceStepInputValueRename
        Constructible.IndexedSequenceZF.valueAtFormula)
      (.conj
        (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20))
        (.conj
          (FOFormula.rename traceStepOutputValueRename
            Constructible.IndexedSequenceZF.valueAtFormula)
          (FOFormula.rename traceStepStackStepRename stackStepFormula))))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepBody

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepFormula
def traceStepFormula : FOFormula 16 :=
  .ex (.ex (.ex (.ex traceStepBody)))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.traceStepFormula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackProgramEvalCore
def stackProgramEvalCore : FOFormula 20 :=
  .conj
    (FOFormula.rename evalProgramLengthRename hasLengthFormula)
    (.conj
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (.conj
        (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
        (.conj
          (FOFormula.rename evalInitialValueRename valueAtFormula)
          (.conj
            (FOFormula.rename evalFinalValueRename valueAtFormula)
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
              (FOFormula.boundedAll (17 : Fin 20)
                (FOFormula.rename evalTraceStepRename
                  traceStepFormula)))))))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackProgramEvalCore

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.stackProgramEvalFormula
def stackProgramEvalFormula : FOFormula 16 :=
  .conj
    (FOFormula.rename evalProgramValidityRename sequenceValidityFormula)
    (.ex
      (.conj
        (FOFormula.rename evalTraceValidityRename sequenceValidityFormula)
        (.ex (.ex (.ex stackProgramEvalCore)))))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.stackProgramEvalFormula

-- BEGIN ORIGINAL Constructible.Godel.RudimentaryTerm.godelDefOutputFormula
def godelDefOutputFormula : FOFormula 15 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (15 : Fin 16) (14 : Fin 16))
      (.conj
        (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
        (.ex (FOFormula.rename godelDefEvalRename
          stackProgramEvalFormula))))
-- END ORIGINAL Constructible.Godel.RudimentaryTerm.godelDefOutputFormula
end Constructible.Godel.RudimentaryTerm


namespace Constructible.Model
open Constructible

-- BEGIN ORIGINAL Constructible.Model.bareHistoryEntryAt
def bareHistoryEntryAt {n : Nat}
    (history index stage : Fin n) : FOFormula n :=
  .ex (.conj
    (.mem (Fin.last n) history.castSucc)
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) index.castSucc stage.castSucc).toFO)
-- END ORIGINAL Constructible.Model.bareHistoryEntryAt

-- BEGIN ORIGINAL Constructible.Model.bareHistoryStateRename
def bareHistoryStateRename : Fin 3 → Fin 16 :=
  ![13, 14, 15]
-- END ORIGINAL Constructible.Model.bareHistoryStateRename

-- BEGIN ORIGINAL Constructible.Model.bareHistoryBaseStateFormula
def bareHistoryBaseStateFormula : FOFormula 16 :=
  .conj
    (.eq (14 : Fin 16) (2 : Fin 16))
    (.eq (15 : Fin 16) (2 : Fin 16))
-- END ORIGINAL Constructible.Model.bareHistoryBaseStateFormula

-- BEGIN ORIGINAL Constructible.Model.bareHistorySuccessorDefRename
def bareHistorySuccessorDefRename : Fin 15 → Fin 18 :=
  Fin.lastCases
    (15 : Fin 18)
    (fun i14 => Fin.cases
      (17 : Fin 18)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)
-- END ORIGINAL Constructible.Model.bareHistorySuccessorDefRename

-- BEGIN ORIGINAL Constructible.Model.bareHistorySuccessorStateFormula
def bareHistorySuccessorStateFormula : FOFormula 16 :=
  .ex (.ex
    (.conj
      (Delta0Formula.successorFOAt (14 : Fin 18) (16 : Fin 18))
      (.conj
        (bareHistoryEntryAt
          (13 : Fin 18) (16 : Fin 18) (17 : Fin 18))
        (FOFormula.rename bareHistorySuccessorDefRename
          Godel.RudimentaryTerm.godelDefOutputFormula))))
-- END ORIGINAL Constructible.Model.bareHistorySuccessorStateFormula

-- BEGIN ORIGINAL Constructible.Model.bareHistoryLimitStateFormula
def bareHistoryLimitStateFormula : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (3 : Fin 4) (2 : Fin 4))
      (FOFormula.boundedEx (1 : Fin 4)
        (.ex
          (.conj
            (bareHistoryEntryAt
              (0 : Fin 6) (4 : Fin 6) (5 : Fin 6))
            (.mem (3 : Fin 6) (5 : Fin 6))))))
-- END ORIGINAL Constructible.Model.bareHistoryLimitStateFormula

-- BEGIN ORIGINAL Constructible.Model.bareHistoryIndexIsZeroFormula
def bareHistoryIndexIsZeroFormula : FOFormula 16 :=
  .eq (14 : Fin 16) (2 : Fin 16)
-- END ORIGINAL Constructible.Model.bareHistoryIndexIsZeroFormula

-- BEGIN ORIGINAL Constructible.Model.bareHistoryIndexHasPredecessorFormula
def bareHistoryIndexHasPredecessorFormula : FOFormula 16 :=
  .ex (Delta0Formula.successorFOAt (14 : Fin 17) (16 : Fin 17))
-- END ORIGINAL Constructible.Model.bareHistoryIndexHasPredecessorFormula

-- BEGIN ORIGINAL Constructible.Model.bareHistoryLocalStateFormula
def bareHistoryLocalStateFormula : FOFormula 16 :=
  .disj
    bareHistoryBaseStateFormula
    (.disj
      bareHistorySuccessorStateFormula
      (.conj
        (.conj
          (.neg bareHistoryIndexIsZeroFormula)
          (.neg bareHistoryIndexHasPredecessorFormula))
        (FOFormula.rename bareHistoryStateRename
          bareHistoryLimitStateFormula)))
-- END ORIGINAL Constructible.Model.bareHistoryLocalStateFormula

-- BEGIN ORIGINAL Constructible.Model.bareValidHistoryLocalRename
def bareValidHistoryLocalRename : Fin 16 → Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i15 => Fin.lastCases
      (15 : Fin 17)
      (fun i14 => Fin.lastCases
        (13 : Fin 17)
        (fun i13 => Fin.castLE (by decide) i13)
        i14)
      i15)
-- END ORIGINAL Constructible.Model.bareValidHistoryLocalRename

-- BEGIN ORIGINAL Constructible.Model.bareValidStageHistoryIndexBody
def bareValidStageHistoryIndexBody : FOFormula 16 :=
  .ex
    (.conj
      (bareHistoryEntryAt
        (13 : Fin 17) (15 : Fin 17) (16 : Fin 17))
      (.conj
        (FOFormula.all
          (FOFormula.imp
            (bareHistoryEntryAt
              (13 : Fin 18) (15 : Fin 18) (17 : Fin 18))
            (.eq (17 : Fin 18) (16 : Fin 18))))
        (FOFormula.rename bareValidHistoryLocalRename
          bareHistoryLocalStateFormula)))
-- END ORIGINAL Constructible.Model.bareValidStageHistoryIndexBody

-- BEGIN ORIGINAL Constructible.Model.bareValidStageHistoryFormula
def bareValidStageHistoryFormula : FOFormula 15 :=
  FOFormula.all
    (FOFormula.imp
      (FOFormula.disj
        (.mem (15 : Fin 16) (14 : Fin 16))
        (.eq (15 : Fin 16) (14 : Fin 16)))
      bareValidStageHistoryIndexBody)
-- END ORIGINAL Constructible.Model.bareValidStageHistoryFormula

-- BEGIN ORIGINAL Constructible.Model.bareStageAtValidHistoryRename
def bareStageAtValidHistoryRename : Fin 15 → Fin 16 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 13]
-- END ORIGINAL Constructible.Model.bareStageAtValidHistoryRename

-- BEGIN ORIGINAL Constructible.Model.bareStageAtFormula
def bareStageAtFormula : FOFormula 15 :=
  .ex
    (.conj
      (FOFormula.rename bareStageAtValidHistoryRename
        bareValidStageHistoryFormula)
      (bareHistoryEntryAt
        (15 : Fin 16) (13 : Fin 16) (14 : Fin 16)))
-- END ORIGINAL Constructible.Model.bareStageAtFormula
end Constructible.Model

end PPAC.Migration.ExistingConstructible
