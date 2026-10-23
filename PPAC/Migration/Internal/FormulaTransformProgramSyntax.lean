import PPAC.Migration.Internal.FormulaTransformLogicalSyntax

/-! 固定十一分支公式程序；分支由原节点形状匹配，递归调用读取实际内部历史。 -/
namespace PPAC.Migration.Internal.FormulaTransformProgramSyntax
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)

inductive Instruction where
  | nullary (truth : Bool)
  | membership
  | equality
  | single (tag : Nat) (advance : Bool)
  | binary (kind : Fin 4)

inductive Program where
  | branch (instruction : Instruction)
  | either (left right : Program)
  | reject

def instructionTree : Instruction → Tree
  | .nullary truth => .node 0 [leaf (if truth then 1 else 0)]
  | .membership => leaf 1
  | .equality => leaf 2
  | .single tag advance => .node 3 [leaf tag, leaf (if advance then 1 else 0)]
  | .binary kind => .node 4 [leaf kind.val]

def programTree : Program → Tree
  | .branch instruction => .node 0 [instructionTree instruction]
  | .either left right => .node 1 [programTree left, programTree right]
  | .reject => leaf 2

def formulaProgram : Program := .either
  (.either (.branch (.nullary false)) (.branch (.nullary true)))
  (.either (.branch .membership)
    (.either (.branch .equality)
      (.either (.branch (.single 4 false))
        (.either (.branch (.binary 0))
          (.either (.branch (.binary 1))
            (.either (.branch (.binary 2))
              (.either (.branch (.binary 3))
                (.either (.branch (.single 9 true)) (.branch (.single 10 true))))))))))

def compileInstruction {m} (instruction : Instruction) (w R S a b c d h n q : Fin m) : Formula m :=
  match instruction with
  | .nullary truth => FormulaTransformAtomSyntax.nullary truth w a b c d n q
  | .membership => FormulaTransformAtomSyntax.membership w R S a b c d n q
  | .equality => FormulaTransformAtomSyntax.equality w R S a b c d n q
  | .single tag advance => FormulaTransformLogicalSyntax.single tag advance w h R S a b c d n q
  | .binary kind => FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q

def run {m} : Program → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula m
  | .branch instruction, w,R,S,a,b,c,d,h,n,q => compileInstruction instruction w R S a b c d h n q
  | .either left right, w,R,S,a,b,c,d,h,n,q => (run left w R S a b c d h n q).disj (run right w R S a b c d h n q)
  | .reject, _,_,_,_,_,_,_,_,_,_ => .bot

def step {m} (w R S a b c d h n q : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n a b).conj (run formulaProgram w R S a b c d h n q)

theorem compileInstruction_rename {m k} (instruction : Instruction) (w R S a b c d h n q : Fin m) (ρ : Fin m → Fin k) :
    (compileInstruction instruction w R S a b c d h n q).rename ρ = compileInstruction instruction (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ h) (ρ n) (ρ q) := by
  cases instruction with
  | nullary truth => simp only [compileInstruction, FormulaTransformAtomSyntax.nullary_rename]
  | membership => simp only [compileInstruction, FormulaTransformAtomSyntax.membership_rename]
  | equality => simp only [compileInstruction, FormulaTransformAtomSyntax.equality_rename]
  | single tag advance => simp only [compileInstruction, FormulaTransformLogicalSyntax.single_rename]
  | binary kind => simp only [compileInstruction, FormulaTransformLogicalSyntax.binary_rename]

theorem run_rename {m k} (program : Program) (w R S a b c d h n q : Fin m) (ρ : Fin m → Fin k) :
    (run program w R S a b c d h n q).rename ρ = run program (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ h) (ρ n) (ρ q) := by
  induction program with
  | branch instruction => exact compileInstruction_rename instruction w R S a b c d h n q ρ
  | either left right hl hr => simp only [run, Formula.rename, hl, hr]
  | reject => rfl

theorem step_rename {m k} (w R S a b c d h n q : Fin m) (ρ : Fin m → Fin k) :
    (step w R S a b c d h n q).rename ρ = step (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ h) (ρ n) (ρ q) := by
  simp only [step, Formula.rename, FormulaCodeSyntax.formulaCode_rename, run_rename]

end PPAC.Migration.Internal.FormulaTransformProgramSyntax
