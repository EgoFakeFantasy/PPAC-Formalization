import PPAC.Migration.Internal.PacketStructureRootSyntax

/-! No original witness is omitted before constructor injectivity aligns its real head fields. -/
namespace PPAC.Migration.Internal.PacketStructureRootWitness
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax

def treeWitness {m} (w V r : Fin m) : Formula (m+8) :=
  (StructuralNodeSyntax.raw (old 8 w) (slot 8 0) (slot 8 1) (slot 8 7)).conj (treeAt (old 8 w) (old 8 V) (old 8 r) (slot 8 7) (fun i => slot 8 i.castSucc))

theorem actual_tree_witness {m} (w V r : Fin m) :
    PacketStructureApplicationSyntax.outcome .tree w V r = existsMany 8 (treeWitness w V r) := rfl

def nilWitness {m} (w _V r : Fin m) : Formula (m+3) :=
  (empty (slot 3 1)).conj ((successor (slot 3 2) (slot 3 1)).conj (nilAt (old 3 w) (old 3 r) (slot 3 1) (slot 3 2) (fun _ : Fin 1 => slot 3 0)))

theorem actual_nil_witness {m} (w V r : Fin m) :
    PacketStructureApplicationSyntax.outcome .nil w V r = existsMany 3 (nilWitness w V r) := rfl

def consWitness {m} (w V r : Fin m) : Formula (m+8) :=
  (StructuralListSyntax.consCode (old 8 w) (slot 8 0) (slot 8 1) (slot 8 6)).conj ((successor (slot 8 7) (slot 8 2)).conj (consAt (old 8 w) (old 8 V) (old 8 r) (slot 8 6) (slot 8 7) (fun i => slot 8 i.castSucc.castSucc)))

theorem actual_cons_witness {m} (w V r : Fin m) :
    PacketStructureApplicationSyntax.outcome .cons w V r = existsMany 8 (consWitness w V r) := rfl

def packetWitness {m} (w V r : Fin m) : Formula (m+4) :=
  (SyntaxNumeralSyntax.numeral 1 (slot 4 3)).conj (packetAt (old 4 w) (old 4 V) (old 4 r) (slot 4 3) (fun i => slot 4 i.castSucc))

theorem actual_packet_witness {m} (w V r : Fin m) :
    PacketStructureApplicationSyntax.outcome .packet w V r = existsMany 4 (packetWitness w V r) := rfl

end PPAC.Migration.Internal.PacketStructureRootWitness
