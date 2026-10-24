import PPAC.Migration.Internal.PacketStructureMatrix

/-! Actual structural and literal witnesses remain internal existentials, with exact original environments. -/
namespace PPAC.Migration.Internal.PacketStructureLocalSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax
open SyntaxRenameQuerySyntax (of_eq)

def treeBody {m} (w V r : Fin m) (env : Fin 7 → Fin m) : Formula (m+1) :=
  (StructuralNodeSyntax.raw (old 1 w) (old 1 (env 0)) (old 1 (env 1)) (slot 1 0)).conj (treeAt (old 1 w) (old 1 V) (old 1 r) (slot 1 0) (fun i => old 1 (env i)))

def treeLocal {m} (w V r : Fin m) (env : Fin 7 → Fin m) : Formula m := existsMany 1 (treeBody w V r env)

theorem treeBody_lift {m j} (w V r : Fin m) (env : Fin 7 → Fin m) (ρ : Fin m → Fin j) :
    (treeBody w V r env).rename (lift 1 ρ) = treeBody (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [treeBody,Formula.rename,StructuralNodeSyntax.raw_rename,treeAt_rename,lift_old,lift_slot]

theorem treeLocal_rename {m j} (w V r : Fin m) (env : Fin 7 → Fin m) (ρ : Fin m → Fin j) :
    (treeLocal w V r env).rename ρ = treeLocal (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [treeLocal,existsMany_rename,treeBody_lift]

theorem intro_tree {m} {Γ : Context m} (w V r n : Fin m) (env : Fin 7 → Fin m)
    (hr : Derives Γ (StructuralNodeSyntax.raw w (env 0) (env 1) n))
    (ha : Derives Γ (treeAt w V r n env)) : Derives Γ (treeLocal w V r env) := by
  apply HornBinderRules.intro_many 1 (treeBody w V r env) (fun _ : Fin 1 => n)
  exact of_eq (by simp only [treeBody,Formula.rename,StructuralNodeSyntax.raw_rename,treeAt_rename,assign_old,assign_slot]) (.conjI hr ha)

def nilBody {m} (w _V r : Fin m) (env : Fin 1 → Fin m) : Formula (m+2) :=
  (empty (slot 2 0)).conj ((successor (slot 2 1) (slot 2 0)).conj (nilAt (old 2 w) (old 2 r) (slot 2 0) (slot 2 1) (fun i => old 2 (env i))))

def nilLocal {m} (w V r : Fin m) (env : Fin 1 → Fin m) : Formula m := existsMany 2 (nilBody w V r env)

theorem nilBody_lift {m j} (w V r : Fin m) (env : Fin 1 → Fin m) (ρ : Fin m → Fin j) :
    (nilBody w V r env).rename (lift 2 ρ) = nilBody (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [nilBody,Formula.rename,empty_rename,successor_rename,nilAt_rename,lift_old,lift_slot]

theorem nilLocal_rename {m j} (w V r : Fin m) (env : Fin 1 → Fin m) (ρ : Fin m → Fin j) :
    (nilLocal w V r env).rename ρ = nilLocal (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [nilLocal,existsMany_rename,nilBody_lift]

theorem intro_nil {m} {Γ : Context m} (w V r z e : Fin m) (env : Fin 1 → Fin m)
    (hz : Derives Γ (empty z))
    (he : Derives Γ (successor e z))
    (ha : Derives Γ (nilAt w r z e env)) : Derives Γ (nilLocal w V r env) := by
  apply HornBinderRules.intro_many 2 (nilBody w V r env) (SyntaxAtomSyntax.two z e)
  exact of_eq (by simp only [nilBody,Formula.rename,empty_rename,successor_rename,nilAt_rename,assign_old,assign_slot]; rfl) (.conjI hz (.conjI he ha))

def consBody {m} (w V r : Fin m) (env : Fin 6 → Fin m) : Formula (m+2) :=
  (StructuralListSyntax.consCode (old 2 w) (old 2 (env 0)) (old 2 (env 1)) (slot 2 0)).conj ((successor (slot 2 1) (old 2 (env 2))).conj (consAt (old 2 w) (old 2 V) (old 2 r) (slot 2 0) (slot 2 1) (fun i => old 2 (env i))))

def consLocal {m} (w V r : Fin m) (env : Fin 6 → Fin m) : Formula m := existsMany 2 (consBody w V r env)

theorem consBody_lift {m j} (w V r : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin j) :
    (consBody w V r env).rename (lift 2 ρ) = consBody (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,successor_rename,consAt_rename,lift_old,lift_slot]

theorem consLocal_rename {m j} (w V r : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin j) :
    (consLocal w V r env).rename ρ = consLocal (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [consLocal,existsMany_rename,consBody_lift]

theorem intro_cons {m} {Γ : Context m} (w V r n s : Fin m) (env : Fin 6 → Fin m)
    (hc : Derives Γ (StructuralListSyntax.consCode w (env 0) (env 1) n))
    (hs : Derives Γ (successor s (env 2)))
    (ha : Derives Γ (consAt w V r n s env)) : Derives Γ (consLocal w V r env) := by
  apply HornBinderRules.intro_many 2 (consBody w V r env) (SyntaxAtomSyntax.two n s)
  exact of_eq (by simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,successor_rename,consAt_rename,assign_old,assign_slot]; rfl) (.conjI hc (.conjI hs ha))

def packetBody {m} (w V r : Fin m) (env : Fin 3 → Fin m) : Formula (m+1) :=
  (SyntaxNumeralSyntax.numeral 1 (slot 1 0)).conj (packetAt (old 1 w) (old 1 V) (old 1 r) (slot 1 0) (fun i => old 1 (env i)))

def packetLocal {m} (w V r : Fin m) (env : Fin 3 → Fin m) : Formula m := existsMany 1 (packetBody w V r env)

theorem packetBody_lift {m j} (w V r : Fin m) (env : Fin 3 → Fin m) (ρ : Fin m → Fin j) :
    (packetBody w V r env).rename (lift 1 ρ) = packetBody (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [packetBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,packetAt_rename,lift_old,lift_slot]

theorem packetLocal_rename {m j} (w V r : Fin m) (env : Fin 3 → Fin m) (ρ : Fin m → Fin j) :
    (packetLocal w V r env).rename ρ = packetLocal (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [packetLocal,existsMany_rename,packetBody_lift]

theorem intro_packet {m} {Γ : Context m} (w V r e : Fin m) (env : Fin 3 → Fin m)
    (he : Derives Γ (SyntaxNumeralSyntax.numeral 1 e))
    (ha : Derives Γ (packetAt w V r e env)) : Derives Γ (packetLocal w V r env) := by
  apply HornBinderRules.intro_many 1 (packetBody w V r env) (fun _ : Fin 1 => e)
  exact of_eq (by simp only [packetBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,packetAt_rename,assign_old,assign_slot]) (.conjI he ha)

end PPAC.Migration.Internal.PacketStructureLocalSyntax
