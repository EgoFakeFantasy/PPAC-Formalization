import PPAC.Migration.Internal.PacketReaderInitParser

/-! At a fixed genuine terminal cause the actual option value is characterized on every output candidate, without a presumed option tag. -/
namespace PPAC.Migration.Internal.PacketReaderFixedReturn
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_success {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a u q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketReaderInputSyntax.eofSuccess w z o L v s a))
    (hu : Derives Γ (StructuralListReverseSyntax.reverses w a u)) :
    Derives Γ ((result w B z o L v s a q).iff (some w u q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := result w B z o L v s a q
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add H Γ) H)
    · let S := success w z o L v s a q
      let R := (StructuralListReverseSyntax.reverses w.castSucc a.castSucc (Fin.last m)).conj (some w.castSucc (Fin.last m) q.castSucc)
      let Δ := Context.add R (Context.image Formula.raise (Context.add S (Context.add H Γ)))
      apply Derives.exE (p := R) (.conjR (.hyp (Or.inl rfl) : Derives (Context.add S (Context.add H Γ)) S))
      have hR : Derives Δ R := .hyp (Or.inl rfl)
      have hZ1 := ZFContext.under (ZFContext.add (ZFContext.add hZ H) S) R
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add (add hw H) S) R)
      have hu1 := of_eq (StructuralListReverseSyntax.reverses_rename w a u Fin.castSucc) (under (add (add hu H) S) R)
      have heq := StructuralListReverseUnique.unique hZ1 _ _ _ _ hw1 (.conjL hR) hu1
      simpa only [Formula.raise,some_rename] using PacketReaderReturnPayload.payload_subst _ _ _ _ heq (.conjR hR)
    · exact .botE (PacketReaderReturnUnique.success_rejection_disjoint (ZFContext.add (ZFContext.add hZ H) _) _ _ _ _ _ _ _ _ (add (add hw H) _) (add (add he H) _) (.conjL (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .disjL (intro_success _ _ _ _ _ _ _ _ _ (add he _) (add hu _) (.hyp (Or.inl rfl)))

theorem at_rejection {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (rejection w B z o L v s a)) :
    Derives Γ ((result w B z o L v s a q).iff (none w q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := result w B z o L v s a q
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add H Γ) H)
    · exact .botE (PacketReaderReturnUnique.success_rejection_disjoint (ZFContext.add (ZFContext.add hZ H) _) _ _ _ _ _ _ _ _ (add (add hw H) _) (.conjL (.hyp (Or.inl rfl))) (add (add hr H) _))
    · exact .conjR (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .disjR (.conjI (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketReaderFixedReturn
