import PPAC.Migration.Internal.PacketStructureRootTransport

/-! Specified root formulas retain exactly the real recursive witnesses after head-field alignment. -/
namespace PPAC.Migration.Internal.PacketStructureRootSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)

def five {m} (a b c d e : Fin m) : Fin 5 → Fin m := Fin.cases a (four b c d e)

def treeCaseBody {m} (w V n t a : Fin m) : Formula (m+5) :=
  (StructuralNodeSyntax.raw (old 5 w) (slot 5 0) (slot 5 1) (old 5 n)).conj
    ((forestEntry (old 5 w) (old 5 V) (slot 5 1) (slot 5 2) (old 5 t) (slot 5 3)).conj
      ((PacketTokenSyntax.entry (old 5 w) (old 5 V) (slot 5 2) (slot 5 3) (slot 5 4)).conj
        (PacketTokenSyntax.entry (old 5 w) (old 5 V) (slot 5 0) (slot 5 4) (old 5 a))))

def treeCase {m} (w V n t a : Fin m) : Formula m := existsMany 5 (treeCaseBody w V n t a)

def nilCase {m} (n l t a : Fin m) : Formula m := (empty l).conj ((successor n l).conj (.equal t a))

def consCaseBody {m} (w V n l t a : Fin m) : Formula (m+4) :=
  (StructuralListSyntax.consCode (old 4 w) (slot 4 0) (slot 4 1) (old 4 n)).conj
    ((successor (old 4 l) (slot 4 2)).conj
      ((forestEntry (old 4 w) (old 4 V) (slot 4 1) (slot 4 2) (old 4 t) (slot 4 3)).conj
        (treeEntry (old 4 w) (old 4 V) (slot 4 0) (slot 4 3) (old 4 a))))

def consCase {m} (w V n l t a : Fin m) : Formula m := existsMany 4 (consCaseBody w V n l t a)

def packetCaseBody {m} (w V a n : Fin m) : Formula (m+2) :=
  (SyntaxNumeralSyntax.numeral 1 (slot 2 0)).conj
    ((PacketTokenSyntax.tagEntry 1 (old 2 w) (old 2 V) (slot 2 0) (slot 2 1) (old 2 a)).conj
      (treeEntry (old 2 w) (old 2 V) (old 2 n) (slot 2 0) (slot 2 1)))

def packetCase {m} (w V a n : Fin m) : Formula m := existsMany 2 (packetCaseBody w V a n)

def criterion {m} : (f : Family) → Fin m → Fin m → (Fin (width f) → Fin m) → Formula m
  | .tree, w, V, xs => treeCase w V (xs (0 : Fin 3)) (xs (1 : Fin 3)) (xs (2 : Fin 3))
  | .forest, w, V, xs => (nilCase (xs (0 : Fin 4)) (xs (1 : Fin 4)) (xs (2 : Fin 4)) (xs (3 : Fin 4))).disj (consCase w V (xs (0 : Fin 4)) (xs (1 : Fin 4)) (xs (2 : Fin 4)) (xs (3 : Fin 4)))
  | .packet, w, V, xs => packetCase w V (xs (0 : Fin 2)) (xs (1 : Fin 2))

theorem nilCase_rename {m j} (n l t a : Fin m) (ρ : Fin m → Fin j) :
    (nilCase n l t a).rename ρ = nilCase (ρ n) (ρ l) (ρ t) (ρ a) := by
  simp only [nilCase,Formula.rename,empty_rename,successor_rename]

theorem treeCaseBody_lift {m j} (w V n t a : Fin m) (ρ : Fin m → Fin j) :
    (treeCaseBody w V n t a).rename (lift 5 ρ) = treeCaseBody (ρ w) (ρ V) (ρ n) (ρ t) (ρ a) := by
  simp only [treeCaseBody,Formula.rename,StructuralNodeSyntax.raw_rename,forestEntry_rename,PacketTokenSyntax.entry_rename,lift_old,lift_slot]

theorem treeCase_rename {m j} (w V n t a : Fin m) (ρ : Fin m → Fin j) :
    (treeCase w V n t a).rename ρ = treeCase (ρ w) (ρ V) (ρ n) (ρ t) (ρ a) := by
  simp only [treeCase,existsMany_rename,treeCaseBody_lift]

theorem consCaseBody_lift {m j} (w V n l t a : Fin m) (ρ : Fin m → Fin j) :
    (consCaseBody w V n l t a).rename (lift 4 ρ) = consCaseBody (ρ w) (ρ V) (ρ n) (ρ l) (ρ t) (ρ a) := by
  simp only [consCaseBody,Formula.rename,StructuralListSyntax.consCode_rename,successor_rename,forestEntry_rename,treeEntry_rename,lift_old,lift_slot]

theorem consCase_rename {m j} (w V n l t a : Fin m) (ρ : Fin m → Fin j) :
    (consCase w V n l t a).rename ρ = consCase (ρ w) (ρ V) (ρ n) (ρ l) (ρ t) (ρ a) := by
  simp only [consCase,existsMany_rename,consCaseBody_lift]

theorem packetCaseBody_lift {m j} (w V a n : Fin m) (ρ : Fin m → Fin j) :
    (packetCaseBody w V a n).rename (lift 2 ρ) = packetCaseBody (ρ w) (ρ V) (ρ a) (ρ n) := by
  simp only [packetCaseBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,PacketTokenSyntax.tagEntry_rename,treeEntry_rename,lift_old,lift_slot]

theorem packetCase_rename {m j} (w V a n : Fin m) (ρ : Fin m → Fin j) :
    (packetCase w V a n).rename ρ = packetCase (ρ w) (ρ V) (ρ a) (ρ n) := by
  simp only [packetCase,existsMany_rename,packetCaseBody_lift]

theorem criterion_rename {m j} (f : Family) (w V : Fin m) (xs : Fin (width f) → Fin m) (ρ : Fin m → Fin j) :
    (criterion f w V xs).rename ρ = criterion f (ρ w) (ρ V) (fun i => ρ (xs i)) := by
  cases f
  · exact treeCase_rename _ _ _ _ _ ρ
  · simp only [criterion,Formula.rename,nilCase_rename,consCase_rename]
  · exact packetCase_rename _ _ _ _ ρ

theorem intro_tree {m} {Γ : Context m} (w V n t a tag p l u v : Fin m)
    (hr : Derives Γ (StructuralNodeSyntax.raw w tag p n)) (hf : Derives Γ (forestEntry w V p l t u))
    (h0 : Derives Γ (PacketTokenSyntax.entry w V l u v)) (h1 : Derives Γ (PacketTokenSyntax.entry w V tag v a)) : Derives Γ (treeCase w V n t a) := by
  apply HornBinderRules.intro_many 5 (treeCaseBody w V n t a) (five tag p l u v)
  exact of_eq (by simp only [treeCaseBody,Formula.rename,StructuralNodeSyntax.raw_rename,forestEntry_rename,PacketTokenSyntax.entry_rename,assign_old,assign_slot]; rfl)
    (.conjI hr (.conjI hf (.conjI h0 h1)))

theorem intro_cons {m} {Γ : Context m} (w V n l t a h q k u : Fin m)
    (hc : Derives Γ (StructuralListSyntax.consCode w h q n)) (hs : Derives Γ (successor l k))
    (hf : Derives Γ (forestEntry w V q k t u)) (ht : Derives Γ (treeEntry w V h u a)) : Derives Γ (consCase w V n l t a) := by
  apply HornBinderRules.intro_many 4 (consCaseBody w V n l t a) (four h q k u)
  exact of_eq (by simp only [consCaseBody,Formula.rename,StructuralListSyntax.consCode_rename,successor_rename,forestEntry_rename,treeEntry_rename,assign_old,assign_slot]; rfl)
    (.conjI hc (.conjI hs (.conjI hf ht)))

theorem intro_packet {m} {Γ : Context m} (w V a n e u : Fin m)
    (he : Derives Γ (SyntaxNumeralSyntax.numeral 1 e)) (ha : Derives Γ (PacketTokenSyntax.tagEntry 1 w V e u a))
    (ht : Derives Γ (treeEntry w V n e u)) : Derives Γ (packetCase w V a n) := by
  apply HornBinderRules.intro_many 2 (packetCaseBody w V a n) (SyntaxAtomSyntax.two e u)
  exact of_eq (by simp only [packetCaseBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,PacketTokenSyntax.tagEntry_rename,treeEntry_rename,assign_old,assign_slot]; rfl)
    (.conjI he (.conjI ha ht))

end PPAC.Migration.Internal.PacketStructureRootSyntax
