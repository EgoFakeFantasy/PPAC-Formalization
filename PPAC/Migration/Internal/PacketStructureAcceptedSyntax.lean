import PPAC.Migration.Internal.PacketStructureRootEquation

/-! Independent real tree, forest and packet acceptance uses the original row and Packet condition; recursive criteria are separate. -/
namespace PPAC.Migration.Internal.PacketStructureAcceptedSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)

def accepted {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  ((row k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (PacketTraceSyntax.condition w.castSucc (Fin.last m)))

def tree {m} (w n t a : Fin m) : Formula m := accepted 3 3 w (SyntaxAtomSyntax.three n t a)

def forest {m} (w n l t a : Fin m) : Formula m := accepted 4 4 w (four n l t a)

def packet {m} (w a n : Fin m) : Formula m := accepted 2 5 w (SyntaxAtomSyntax.two a n)

def treeCaseBody {m} (w n t a : Fin m) : Formula (m+5) :=
  (StructuralNodeSyntax.raw (old 5 w) (slot 5 0) (slot 5 1) (old 5 n)).conj
    ((forest (old 5 w) (slot 5 1) (slot 5 2) (old 5 t) (slot 5 3)).conj
      ((PacketTokenAcceptedSyntax.accepted (old 5 w) (slot 5 2) (slot 5 3) (slot 5 4)).conj
        (PacketTokenAcceptedSyntax.accepted (old 5 w) (slot 5 0) (slot 5 4) (old 5 a))))

def treeCase {m} (w n t a : Fin m) : Formula m := existsMany 5 (treeCaseBody w n t a)

def consCaseBody {m} (w n l t a : Fin m) : Formula (m+4) :=
  (StructuralListSyntax.consCode (old 4 w) (slot 4 0) (slot 4 1) (old 4 n)).conj
    ((successor (old 4 l) (slot 4 2)).conj
      ((forest (old 4 w) (slot 4 1) (slot 4 2) (old 4 t) (slot 4 3)).conj
        (tree (old 4 w) (slot 4 0) (slot 4 3) (old 4 a))))

def consCase {m} (w n l t a : Fin m) : Formula m := existsMany 4 (consCaseBody w n l t a)

def packetCaseBody {m} (w a n : Fin m) : Formula (m+2) :=
  (SyntaxNumeralSyntax.numeral 1 (slot 2 0)).conj
    ((PacketTokenAcceptedSyntax.tagAccepted 1 (old 2 w) (slot 2 0) (slot 2 1) (old 2 a)).conj
      (tree (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)))

def packetCase {m} (w a n : Fin m) : Formula m := existsMany 2 (packetCaseBody w a n)

def criterion {m} : (f : Family) → Fin m → (Fin (width f) → Fin m) → Formula m
  | .tree, w, xs => treeCase w (xs (0 : Fin 3)) (xs (1 : Fin 3)) (xs (2 : Fin 3))
  | .forest, w, xs => (PacketStructureRootSyntax.nilCase (xs (0 : Fin 4)) (xs (1 : Fin 4)) (xs (2 : Fin 4)) (xs (3 : Fin 4))).disj
      (consCase w (xs (0 : Fin 4)) (xs (1 : Fin 4)) (xs (2 : Fin 4)) (xs (3 : Fin 4)))
  | .packet, w, xs => packetCase w (xs (0 : Fin 2)) (xs (1 : Fin 2))

theorem accepted_rename {m j} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (ρ : Fin m → Fin j) :
    (accepted k tag w xs).rename ρ = accepted k tag (ρ w) (fun i => ρ (xs i)) := by
  simp only [accepted,Formula.rename,row_rename,PacketTraceSyntax.condition_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem tree_rename {m j} (w n t a : Fin m) (ρ : Fin m → Fin j) :
    (tree w n t a).rename ρ = tree (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [tree,accepted_rename,SyntaxAtomSyntax.three_map]

theorem forest_rename {m j} (w n l t a : Fin m) (ρ : Fin m → Fin j) :
    (forest w n l t a).rename ρ = forest (ρ w) (ρ n) (ρ l) (ρ t) (ρ a) := by
  simp only [forest,accepted_rename,four_map]

theorem packet_rename {m j} (w a n : Fin m) (ρ : Fin m → Fin j) :
    (packet w a n).rename ρ = packet (ρ w) (ρ a) (ρ n) := by
  simp only [packet,accepted_rename,SyntaxAtomSyntax.two_map]

theorem treeCaseBody_lift {m j} (w n t a : Fin m) (ρ : Fin m → Fin j) :
    (treeCaseBody w n t a).rename (lift 5 ρ) = treeCaseBody (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [treeCaseBody,Formula.rename,StructuralNodeSyntax.raw_rename,forest_rename,PacketTokenAcceptedSyntax.accepted_rename,lift_old,lift_slot]

theorem treeCase_rename {m j} (w n t a : Fin m) (ρ : Fin m → Fin j) :
    (treeCase w n t a).rename ρ = treeCase (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [treeCase,existsMany_rename,treeCaseBody_lift]

theorem consCaseBody_lift {m j} (w n l t a : Fin m) (ρ : Fin m → Fin j) :
    (consCaseBody w n l t a).rename (lift 4 ρ) = consCaseBody (ρ w) (ρ n) (ρ l) (ρ t) (ρ a) := by
  simp only [consCaseBody,Formula.rename,StructuralListSyntax.consCode_rename,successor_rename,forest_rename,tree_rename,lift_old,lift_slot]

theorem consCase_rename {m j} (w n l t a : Fin m) (ρ : Fin m → Fin j) :
    (consCase w n l t a).rename ρ = consCase (ρ w) (ρ n) (ρ l) (ρ t) (ρ a) := by
  simp only [consCase,existsMany_rename,consCaseBody_lift]

theorem packetCaseBody_lift {m j} (w a n : Fin m) (ρ : Fin m → Fin j) :
    (packetCaseBody w a n).rename (lift 2 ρ) = packetCaseBody (ρ w) (ρ a) (ρ n) := by
  simp only [packetCaseBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,PacketTokenAcceptedSyntax.tagAccepted_rename,tree_rename,lift_old,lift_slot]

theorem packetCase_rename {m j} (w a n : Fin m) (ρ : Fin m → Fin j) :
    (packetCase w a n).rename ρ = packetCase (ρ w) (ρ a) (ρ n) := by
  simp only [packetCase,existsMany_rename,packetCaseBody_lift]

theorem criterion_rename {m j} (f : Family) (w : Fin m) (xs : Fin (width f) → Fin m) (ρ : Fin m → Fin j) :
    (criterion f w xs).rename ρ = criterion f (ρ w) (fun i => ρ (xs i)) := by
  cases f
  · exact treeCase_rename _ _ _ _ ρ
  · simp only [criterion,Formula.rename,PacketStructureRootSyntax.nilCase_rename,consCase_rename]
  · exact packetCase_rename _ _ _ ρ

theorem intro_accepted {m} {Γ : Context m} (k tag : Nat) (w r : Fin m) (xs : Fin k → Fin m)
    (hr : Derives Γ (row k tag w xs r)) (hc : Derives Γ (PacketTraceSyntax.condition w r)) : Derives Γ (accepted k tag w xs) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,row_rename,PacketTraceSyntax.condition_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hr hc)

end PPAC.Migration.Internal.PacketStructureAcceptedSyntax
