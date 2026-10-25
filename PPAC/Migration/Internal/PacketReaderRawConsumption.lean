import PPAC.Migration.Internal.PacketReaderConsumptionTransport

/-! Every raw step consumes exactly one actual original Cons cell, hence strictly lowers the natural input code. -/
namespace PPAC.Migration.Internal.PacketReaderRawConsumption
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderConsumptionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem local_rest {m} {Γ : Context m} (w B z o b x v s a r y q c : Fin m)
    (ht : Derives Γ (PacketReaderStepSyntax.step w B z o b x v s a r y q c)) : Derives Γ (.equal r x) := by
  apply Derives.disjE ht
  · exact .conjL (.conjR (.hyp (Or.inl rfl)))
  · exact .conjL (.conjR (.hyp (Or.inl rfl)))

theorem raw_tail {m} {Γ : Context m} (w B z o l v s a r y q c : Fin m)
    (ha : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a r y q c)) : Derives Γ (tail w l r) := by
  let R := PacketReaderInputSyntax.advanceBody w B z o l v s a r y q c
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ (.conjR ha)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := local_rest _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjR hR)
  have hh := PacketReaderConsumptionTransport.head_rest _ _ _ _ _ (eq_symm he) (.conjL hR)
  exact of_eq (tail_rename w l r (old 2)).symm (intro_tail _ _ _ _ hh)

theorem tail_strict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l r : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (tail w l r)) : Derives Γ (.mem r l) := by
  let H := PacketReaderInputSyntax.headRest w.castSucc l.castSucc (Fin.last m) r.castSucc
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) ht
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  exact .conjR (StructuralConsCore.components hZ1 _ _ _ _ hw1 (.conjL hH)
    (StructuralListValidity.range _ _ (.conjL (.conjR hH))) (.conjR (.conjR hH)))

theorem raw_strict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a r y q c)) : Derives Γ (.mem r l) :=
  tail_strict hZ w l r hw (raw_tail w B z o l v s a r y q c ha)

end PPAC.Migration.Internal.PacketReaderRawConsumption
