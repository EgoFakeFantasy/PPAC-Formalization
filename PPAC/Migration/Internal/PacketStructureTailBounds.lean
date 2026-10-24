import PPAC.Migration.Internal.PacketStructureTailInduction

/-! Final scalar tail bounds are derived from actual acceptance with no IH, traces or external runtime inputs. -/
namespace PPAC.Migration.Internal.PacketStructureTailBounds
open Source SourceAlgebra SourceLogic OmegaSyntax PacketStructureAcceptedSyntax PacketStructureTailSyntax
open NaturalAdditionBounds (below)
open SyntaxRenameQuerySyntax (of_eq)

theorem property_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have hi : Derives Γ ((Formula.mem n w).imp (property w n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
      (Derives.allE n (PacketStructureTailInduction.all_property hZ w hw))
  exact .impE hi hn

theorem tree_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (tree w n t a)) : Derives Γ (below t a) :=
  tree_at w n t a (.conjL (property_at hZ w n hw (PacketStructureTailChildren.tree_natural hZ w n t a 0 hw ha))) ha

theorem forest_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (forest w n l t a)) : Derives Γ (below t a) :=
  forest_at w n l t a (.conjR (property_at hZ w n hw (PacketStructureTailChildren.forest_natural hZ w n l t a 0 hw ha))) ha

theorem tree_contained {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (tree w n t a)) (hr : Derives Γ (.mem r w))
    (har : Derives Γ (below a r)) : Derives Γ (below t r) :=
  NaturalOrderBasic.transitive hZ w t a r hw hr (tree_tail hZ w n t a hw ha) har

theorem forest_contained {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l t a r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (forest w n l t a)) (hr : Derives Γ (.mem r w))
    (har : Derives Γ (below a r)) : Derives Γ (below t r) :=
  NaturalOrderBasic.transitive hZ w t a r hw hr (forest_tail hZ w n l t a hw ha) har

end PPAC.Migration.Internal.PacketStructureTailBounds
