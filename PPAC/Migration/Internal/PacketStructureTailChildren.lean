import PPAC.Migration.Internal.PacketStructureTailSyntax

/-! Real accepted children provide their naturality and strict internal subcode descent. -/
namespace PPAC.Migration.Internal.PacketStructureTailChildren
open Source SourceAlgebra SourceLogic OmegaSyntax PacketStructureAcceptedSyntax

theorem tree_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (i : Fin 3)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (tree w n t a)) : Derives Γ (.mem (SyntaxAtomSyntax.three n t a i) w) :=
  HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a)
    (PacketStructureAcceptedForward.accepted_environment hZ 3 3 w (SyntaxAtomSyntax.three n t a) hw ha) i

theorem forest_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l t a : Fin m) (i : Fin 4)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (forest w n l t a)) : Derives Γ (.mem (PacketStructureSyntax.four n l t a i) w) :=
  HornExprSyntax.environmentNat_at w (PacketStructureSyntax.four n l t a)
    (PacketStructureAcceptedForward.accepted_environment hZ 4 4 w (PacketStructureSyntax.four n l t a) hw ha) i

theorem token_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (i : Fin 3)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (PacketTokenAcceptedSyntax.accepted w n t a)) : Derives Γ (.mem (SyntaxAtomSyntax.three n t a i) w) :=
  HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a) (PacketTokenAcceptedNatural.accepted_environment hZ w n t a hw ha) i

theorem raw_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag p n l t u v a : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (StructuralNodeSyntax.raw w tag p n))
    (hf : Derives Γ (forest w p l t u)) (ht : Derives Γ (PacketTokenAcceptedSyntax.accepted w tag v a)) : Derives Γ (.mem p n) :=
  .conjR (StructuralNodeProperties.components hZ w tag p n hw (token_natural hZ w tag v a 0 hw ht) (forest_natural hZ w p l t u 0 hw hf) hr)

theorem cons_children {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h q n k t u a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (StructuralListSyntax.consCode w h q n))
    (hf : Derives Γ (forest w q k t u)) (ht : Derives Γ (tree w h u a)) : Derives Γ ((Formula.mem h n).conj (.mem q n)) :=
  StructuralConsCore.components hZ w h q n hw (tree_natural hZ w h u a 0 hw ht) (forest_natural hZ w q k t u 0 hw hf) hc

end PPAC.Migration.Internal.PacketStructureTailChildren
