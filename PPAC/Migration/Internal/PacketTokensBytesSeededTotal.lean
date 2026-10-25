import PPAC.Migration.Internal.PacketTokensBytesSeededTotalInduction

/-! Every pair of actual internal lists has an actual unique seeded code, with uniqueness over all candidate outputs. -/
namespace PPAC.Migration.Internal.PacketTokensBytesSeededTotal
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokensBytesSyntax PacketTokensBytesSeededTotalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListTraceSyntax.valid w n))
    (ht : Derives Γ (StructuralListTraceSyntax.valid w t)) : Derives Γ (fiber w n t) :=
  at_tail w n t (PacketTokensBytesSeededTotalInduction.at_code hZ w n hw (StructuralListValidity.range w n hn)) hn ht

theorem natural {m} {Γ : Context m} (w n t a : Fin m) (hs : Derives Γ (seeded w n t a)) : Derives Γ (.mem a w) :=
  StructuralListValidity.range w a (PacketTokensBytesSeeded.joined_valid _ _ _ _ hs)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (seeded w n t a)) (hb : Derives Γ (seeded w n t b)) : Derives Γ (.equal a b) := by
  let R := fiberBody w n t
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (exists_unique hZ w n t hw (PacketTokensBytesSeeded.prefix_valid _ _ _ _ ha) (PacketTokensBytesSeeded.tail_valid _ _ _ _ ha))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ha1 := of_eq (seeded_rename w n t a Fin.castSucc) (under ha R)
  have hb1 := of_eq (seeded_rename w n t b Fin.castSucc) (under hb R)
  have hEqA := unique_at _ _ _ _ _ (.conjR hR) ha1
  have hEqB := unique_at _ _ _ _ _ (.conjR hR) hb1
  exact eq_trans hEqA (eq_symm hEqB)

end PPAC.Migration.Internal.PacketTokensBytesSeededTotal
