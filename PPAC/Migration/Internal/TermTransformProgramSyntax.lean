import PPAC.Migration.Internal.ObjectNativeTopQuotation

/-! 纯签名项变换的独立有限程序及组合执行公式；核心不调用CodedMixedTerm或宿主语法输入。 -/
namespace PPAC.Migration.Internal.TermTransformProgramSyntax
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)

inductive Action where
  | copySource
  | reject
  | readImage (isBound : Bool)

inductive Program where
  | copySource
  | reject
  | dispatchVariable (isBound : Bool) (action : Action) (otherwise : Program)

def booleanTag (value : Bool) : Nat := if value then 0 else 1

def actionTree : Action → Tree
  | .copySource => leaf 0
  | .reject => leaf 1
  | .readImage b => .node 2 [leaf (booleanTag b)]

def programTree : Program → Tree
  | .copySource => leaf 0
  | .reject => leaf 1
  | .dispatchVariable b action otherwise => .node 2 [leaf (booleanTag b), actionTree action, programTree otherwise]

def termProgram : Program := .dispatchVariable true (.readImage true) (.dispatchVariable false (.readImage false) .copySource)

def actionValue {m} (action : Action) (w R S n i q : Fin m) : Formula m := match action with
  | .copySource => .equal q n
  | .reject => .bot
  | .readImage b => StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap b R S) i q

def armBody {m} (isBound : Bool) (action : Action) (w R S n q : Fin m) : Formula (m+1) :=
  (SyntaxVariableSyntax.code isBound w.castSucc (Fin.last m) n.castSucc).conj
    (actionValue action w.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) q.castSucc)

def arm {m} (isBound : Bool) (action : Action) (w R S n q : Fin m) : Formula m := .ex (armBody isBound action w R S n q)

def run {m} : Program → Fin m → Fin m → Fin m → Fin m → Fin m → Formula m
  | .copySource, _, _, _, n, q => .equal q n
  | .reject, _, _, _, _, _ => .bot
  | .dispatchVariable b action otherwise, w, R, S, n, q => (arm b action w R S n q).disj
      ((SyntaxVariableDecodeSyntax.recognized b w n).neg.conj (run otherwise w R S n q))

def inputGuard {m} (w R S a b c d n : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termLists w a b c d R S).conj (SyntaxTermSyntax.term w a b n)

def checked {m} (w R S a b c d n q : Fin m) : Formula m :=
  (inputGuard w R S a b c d n).conj (run termProgram w R S n q)

theorem actionValue_rename {m k} (action : Action) (w R S n i q : Fin m) (ρ : Fin m → Fin k) :
    (actionValue action w R S n i q).rename ρ = actionValue action (ρ w) (ρ R) (ρ S) (ρ n) (ρ i) (ρ q) := by
  cases action with
  | copySource | reject => rfl
  | readImage b => simp only [actionValue, StructuralListFieldSyntax.field_rename, SyntaxIndexMapSyntax.selectMap_map]

theorem arm_rename {m k} (isBound : Bool) (action : Action) (w R S n q : Fin m) (ρ : Fin m → Fin k) :
    (arm isBound action w R S n q).rename ρ = arm isBound action (ρ w) (ρ R) (ρ S) (ρ n) (ρ q) := by
  simp only [arm, armBody, Formula.rename, SyntaxVariableSyntax.code_rename, actionValue_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem run_rename {m k} (program : Program) (w R S n q : Fin m) (ρ : Fin m → Fin k) :
    (run program w R S n q).rename ρ = run program (ρ w) (ρ R) (ρ S) (ρ n) (ρ q) := by
  induction program with
  | copySource | reject => rfl
  | dispatchVariable b action otherwise ih =>
    simp only [run, Formula.rename, arm_rename, SyntaxVariableDecodeSyntax.recognized_rename, ih]

theorem inputGuard_rename {m k} (w R S a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (inputGuard w R S a b c d n).rename ρ = inputGuard (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [inputGuard, Formula.rename, SyntaxMixedImageCodeSyntax.termLists_rename, SyntaxTermSyntax.term_rename]

theorem checked_rename {m k} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (checked w R S a b c d n q).rename ρ = checked (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [checked, Formula.rename, inputGuard_rename, run_rename]

end PPAC.Migration.Internal.TermTransformProgramSyntax
