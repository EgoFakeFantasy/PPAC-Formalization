import PPAC.Migration.Internal.SyntaxTopFormulaLogicalEndpoints
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacket

/-! 固定原树形的有限纯quotation模式；原树仅索引公式，所有实际码值均为内部对象量词。 -/
namespace PPAC.Migration.Internal.OriginalTreeQuotationSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)

mutual
def tree {m} : Tree → Fin m → Fin m → Formula m
  | .node tag children, w, n => .ex (.ex
      ((SyntaxNumeralSyntax.numeral tag (Fin.last (m+1))).conj
        ((forest children w.castSucc.castSucc (Fin.last m).castSucc).conj
          (StructuralNodeSyntax.raw w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc))))
termination_by input _ _ => sizeOf input

def forest {m} : List Tree → Fin m → Fin m → Formula m
  | [], w, n => StructuralListSyntax.nilCode w n
  | head :: tail, w, n => .ex (.ex
      ((tree head w.castSucc.castSucc (Fin.last m).castSucc).conj
        ((forest tail w.castSucc.castSucc (Fin.last (m+1))).conj
          (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc))))
termination_by input _ _ => sizeOf input
end

mutual
theorem tree_rename {m k} (input : Tree) (w n : Fin m) (ρ : Fin m → Fin k) :
    (tree input w n).rename ρ = tree input (ρ w) (ρ n) := by
  cases input with
  | node tag children =>
    simp only [tree, Formula.rename, SyntaxNumeralSyntax.numeral_rename, forest_rename children,
      StructuralNodeSyntax.raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
termination_by sizeOf input

theorem forest_rename {m k} (input : List Tree) (w n : Fin m) (ρ : Fin m → Fin k) :
    (forest input w n).rename ρ = forest input (ρ w) (ρ n) := by
  cases input with
  | nil => simpa only [forest] using StructuralListSyntax.nilCode_rename w n ρ
  | cons head tail =>
    simp only [forest, Formula.rename, tree_rename head, forest_rename tail, StructuralListSyntax.consCode_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
termination_by sizeOf input
end

def nodeState {m} (tag : Nat) (children : List Tree) (w n p t : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral tag t).conj ((forest children w p).conj (StructuralNodeSyntax.raw w t p n))

def nodeBody {m} (tag : Nat) (children : List Tree) (w n : Fin m) : Formula (m+2) :=
  nodeState tag children w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def consState {m} (head : Tree) (tail : List Tree) (w n h t : Fin m) : Formula m :=
  (tree head w h).conj ((forest tail w t).conj (StructuralListSyntax.consCode w h t n))

def consBody {m} (head : Tree) (tail : List Tree) (w n : Fin m) : Formula (m+2) :=
  consState head tail w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

theorem nodeState_rename {m k} (tag : Nat) (children : List Tree) (w n p t : Fin m) (ρ : Fin m → Fin k) :
    (nodeState tag children w n p t).rename ρ = nodeState tag children (ρ w) (ρ n) (ρ p) (ρ t) := by
  simp only [nodeState, Formula.rename, SyntaxNumeralSyntax.numeral_rename, forest_rename children, StructuralNodeSyntax.raw_rename]

theorem consState_rename {m k} (head : Tree) (tail : List Tree) (w n h t : Fin m) (ρ : Fin m → Fin k) :
    (consState head tail w n h t).rename ρ = consState head tail (ρ w) (ρ n) (ρ h) (ρ t) := by
  simp only [consState, Formula.rename, tree_rename, forest_rename, StructuralListSyntax.consCode_rename]

def treeExists {m} (input : Tree) (w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (tree input w.castSucc (Fin.last m)))

def forestExists {m} (input : List Tree) (w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (forest input w.castSucc (Fin.last m)))

def treeUnique {m} (input : Tree) (w n : Fin m) : Formula m := .all
  ((tree input w.castSucc (Fin.last m)).imp (.equal (Fin.last m) n.castSucc))

def forestUnique {m} (input : List Tree) (w n : Fin m) : Formula m := .all
  ((forest input w.castSucc (Fin.last m)).imp (.equal (Fin.last m) n.castSucc))

def treeFiber {m} (input : Tree) (w : Fin m) : Formula m := .ex
  ((tree input w.castSucc (Fin.last m)).conj (treeUnique input w.castSucc (Fin.last m)))

def forestFiber {m} (input : List Tree) (w : Fin m) : Formula m := .ex
  ((forest input w.castSucc (Fin.last m)).conj (forestUnique input w.castSucc (Fin.last m)))

theorem treeExists_rename {m k} (input : Tree) (w : Fin m) (ρ : Fin m → Fin k) :
    (treeExists input w).rename ρ = treeExists input (ρ w) := by
  simp only [treeExists, Formula.rename, tree_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem forestExists_rename {m k} (input : List Tree) (w : Fin m) (ρ : Fin m → Fin k) :
    (forestExists input w).rename ρ = forestExists input (ρ w) := by
  simp only [forestExists, Formula.rename, forest_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem treeFiber_rename {m k} (input : Tree) (w : Fin m) (ρ : Fin m → Fin k) :
    (treeFiber input w).rename ρ = treeFiber input (ρ w) := by
  simp only [treeFiber, treeUnique, Formula.rename, tree_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem forestFiber_rename {m k} (input : List Tree) (w : Fin m) (ρ : Fin m → Fin k) :
    (forestFiber input w).rename ρ = forestFiber input (ρ w) := by
  simp only [forestFiber, forestUnique, Formula.rename, forest_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_tree {m} {Γ : Context m} (tag : Nat) (children : List Tree) (w n p t : Fin m)
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral tag t)) (hp : Derives Γ (forest children w p))
    (hn : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ (tree (.node tag children) w n) := by
  rw [tree]
  apply Derives.exI p
  apply Derives.exI t
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.rename,
    SyntaxNumeralSyntax.numeral_rename, forest_rename children, StructuralNodeSyntax.raw_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI ht (.conjI hp hn))

theorem intro_cons {m} {Γ : Context m} (head : Tree) (tail : List Tree) (w n h t : Fin m)
    (hh : Derives Γ (tree head w h)) (ht : Derives Γ (forest tail w t))
    (hn : Derives Γ (StructuralListSyntax.consCode w h t n)) : Derives Γ (forest (head :: tail) w n) := by
  rw [forest]
  apply Derives.exI h
  apply Derives.exI t
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.rename,
    tree_rename, forest_rename, StructuralListSyntax.consCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hh (.conjI ht hn))

end PPAC.Migration.Internal.OriginalTreeQuotationSyntax
