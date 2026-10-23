import PPAC.Migration.Internal.ObjectStrictLookup

/-! 固定lookup程序按原表码递归；运行时只匹配Cons和读取实际旧历史，不调用旧查表判断。 -/
namespace PPAC.Migration.Internal.LookupTableProgramSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)

def legal {m} (w i y : Fin m) : Formula m := (Formula.mem i w).conj (.mem y w)

def state {m} (w i y p : Fin m) : Formula m :=
  (legal w i y).conj ((Formula.mem p w).conj (GodelPairSyntax.code w i y p))

def contains {m} (w v i y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) v.castSucc).conj (state w.castSucc i.castSucc y.castSucc (Fin.last m)))

def read {m} (w h n i y : Fin m) : Formula m := .ex
  ((edge h.castSucc n.castSucc (Fin.last m)).conj (contains w.castSucc (Fin.last m) i.castSucc y.castSucc))

def zeroCase {m} (w n i y : Fin m) : Formula m :=
  (empty i).conj (StructuralListProjectionSyntax.selected true w n y)

def successorBody {m} (w h n i y : Fin m) : Formula (m+2) :=
  (StructuralListProjectionSyntax.selected false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).conj
    (((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor i.castSucc.castSucc (Fin.last (m+1)))).conj
      (read w.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc))

def successorCase {m} (w h n i y : Fin m) : Formula m := .ex (.ex (successorBody w h n i y))

inductive Instruction where
  | returnHead
  | recurseTail

inductive Program where
  | branch (instruction : Instruction)
  | either (left right : Program)
  | reject

def instructionTree : Instruction → Tree
  | .returnHead => leaf 0
  | .recurseTail => leaf 1

def programTree : Program → Tree
  | .branch instruction => .node 0 [instructionTree instruction]
  | .either left right => .node 1 [programTree left, programTree right]
  | .reject => leaf 2

def compileInstruction {m} (instruction : Instruction) (w h n i y : Fin m) : Formula m :=
  match instruction with
  | .returnHead => zeroCase w n i y
  | .recurseTail => successorCase w h n i y

def compile {m} (program : Program) (w h n i y : Fin m) : Formula m :=
  match program with
  | .branch instruction => compileInstruction instruction w h n i y
  | .either left right => (compile left w h n i y).disj (compile right w h n i y)
  | .reject => .bot

def lookupProgram : Program := .either (.branch .returnHead) (.branch .recurseTail)

def run {m} (w h n i y : Fin m) : Formula m := compile lookupProgram w h n i y

theorem legal_rename {m k} (w i y : Fin m) (ρ : Fin m → Fin k) :
    (legal w i y).rename ρ = legal (ρ w) (ρ i) (ρ y) := rfl

theorem state_rename {m k} (w i y p : Fin m) (ρ : Fin m → Fin k) :
    (state w i y p).rename ρ = state (ρ w) (ρ i) (ρ y) (ρ p) := by
  simp only [state, Formula.rename, legal_rename, GodelPairSyntax.code_rename]

theorem contains_rename {m k} (w v i y : Fin m) (ρ : Fin m → Fin k) :
    (contains w v i y).rename ρ = contains (ρ w) (ρ v) (ρ i) (ρ y) := by
  simp only [contains, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem read_rename {m k} (w h n i y : Fin m) (ρ : Fin m → Fin k) :
    (read w h n i y).rename ρ = read (ρ w) (ρ h) (ρ n) (ρ i) (ρ y) := by
  simp only [read, Formula.rename, edge_rename, contains_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem zeroCase_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (zeroCase w n i y).rename ρ = zeroCase (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [zeroCase, Formula.rename, empty_rename, StructuralListProjectionSyntax.selected_rename]

theorem successorCase_rename {m k} (w h n i y : Fin m) (ρ : Fin m → Fin k) :
    (successorCase w h n i y).rename ρ = successorCase (ρ w) (ρ h) (ρ n) (ρ i) (ρ y) := by
  simp only [successorCase, successorBody, Formula.rename, StructuralListProjectionSyntax.selected_rename, successor_rename, read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem run_rename {m k} (w h n i y : Fin m) (ρ : Fin m → Fin k) :
    (run w h n i y).rename ρ = run (ρ w) (ρ h) (ρ n) (ρ i) (ρ y) := by
  simp only [run, lookupProgram, compile, compileInstruction, Formula.rename, zeroCase_rename, successorCase_rename]

theorem intro_contains {m} {Γ : Context m} (w v i y p : Fin m)
    (hp : Derives Γ (.mem p v)) (hs : Derives Γ (state w i y p)) : Derives Γ (contains w v i y) := by
  apply Derives.exI p
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, state_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hp hs)

theorem intro_read {m} {Γ : Context m} (w h n i y v : Fin m)
    (he : Derives Γ (edge h n v)) (hc : Derives Γ (contains w v i y)) : Derives Γ (read w h n i y) := by
  apply Derives.exI v
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, edge_rename, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI he hc)

theorem intro_successor {m} {Γ : Context m} (w h n i y t j : Fin m)
    (ht : Derives Γ (StructuralListProjectionSyntax.selected false w n t)) (hj : Derives Γ (.mem j w))
    (hi : Derives Γ (successor i j)) (hr : Derives Γ (read w h t j y)) : Derives Γ (successorCase w h n i y) := by
  apply Derives.exI t
  apply Derives.exI j
  exact of_eq (by simp only [successorBody, Formula.instantiate, Formula.rename, StructuralListProjectionSyntax.selected_rename, successor_rename, read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI ht (.conjI (.conjI hj hi) hr))

theorem contains_subst_set {m} {Γ : Context m} (w v t i y : Fin m)
    (he : Derives Γ (.equal v t)) (hc : Derives Γ (contains w v i y)) : Derives Γ (contains w t i y) := by
  let P := contains w.castSucc (Fin.last m) i.castSucc y.castSucc
  have e0 : P.instantiate v = contains w v i y := by
    simp only [P, Formula.instantiate, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate t = contains w t i y := by
    simp only [P, Formula.instantiate, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

end PPAC.Migration.Internal.LookupTableProgramSyntax
