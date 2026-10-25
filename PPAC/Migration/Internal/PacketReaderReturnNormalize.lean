import PPAC.Migration.Internal.PacketReaderReturnTransport

/-! Actual Some returns exactly the real reversed payload; actual None returns exactly the original rejection causes. -/
namespace PPAC.Migration.Internal.PacketReaderReturnNormalize
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem success_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z o L v s a r q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (some w r q)) (hs : Derives Γ (success w z o L v s a q)) :
    Derives Γ (StructuralListReverseSyntax.reverses w a r) := by
  let R := (StructuralListReverseSyntax.reverses w.castSucc a.castSucc (Fin.last m)).conj (some w.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR hs)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hr1 := of_eq (some_rename w r q Fin.castSucc) (under hr R)
  have he := PacketReaderReturnPayload.some_payload_unique hZ1 _ _ _ _ hw1 (.conjR hR) hr1
  simpa only [Formula.raise,StructuralListReverseSyntax.reverses_rename] using StructuralListReverseConsContract.output_subst _ _ _ _ he (.conjL hR)

theorem at_some {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a r q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (some w r q)) :
    Derives Γ ((result w B z o L v s a q).iff ((PacketReaderInputSyntax.eofSuccess w z o L v s a).conj (StructuralListReverseSyntax.reverses w a r))) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := result w B z o L v s a q
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add H Γ) H)
    · let S := success w z o L v s a q
      have hS : Derives (Context.add S (Context.add H Γ)) S := .hyp (Or.inl rfl)
      exact .conjI (.conjL hS) (success_payload (ZFContext.add (ZFContext.add hZ H) S) w z o L v s a r q (add (add hw H) S) (add (add hr H) S) hS)
    · exact .botE (PacketReaderReturnPayload.disjoint (ZFContext.add (ZFContext.add hZ H) _) w r q (add (add hw H) _) (.conjR (.hyp (Or.inl rfl))) (add (add hr H) _))
  · apply Derives.impI
    have hH : Derives (Context.add ((PacketReaderInputSyntax.eofSuccess w z o L v s a).conj (StructuralListReverseSyntax.reverses w a r)) Γ) ((PacketReaderInputSyntax.eofSuccess w z o L v s a).conj (StructuralListReverseSyntax.reverses w a r)) := .hyp (Or.inl rfl)
    exact .disjL (intro_success w z o L v s a r q (.conjL hH) (.conjR hH) (add hr _))

theorem at_none {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (none w q)) :
    Derives Γ ((result w B z o L v s a q).iff (rejection w B z o L v s a)) := by
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
      have hn1 := of_eq (none_rename w q Fin.castSucc) (under (add (add hn H) S) R)
      exact .botE (PacketReaderReturnPayload.disjoint hZ1 _ _ _ hw1 hn1 (.conjR hR))
    · exact .conjL (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .disjR (.conjI (.hyp (Or.inl rfl)) (add hn _))

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (result w B z o L v s a q)) : Derives Γ (.mem q w) := by
  apply Derives.disjE hr
  · let S := success w z o L v s a q
    let R := (StructuralListReverseSyntax.reverses w.castSucc a.castSucc (Fin.last m)).conj (some w.castSucc (Fin.last m) q.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add S Γ))
    apply Derives.exE (p := R) (.conjR (.hyp (Or.inl rfl) : Derives (Context.add S Γ) S))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw S) R)
    exact PacketReaderReturnPayload.some_natural (ZFContext.under (ZFContext.add hZ S) R) _ _ _ hw1 (.conjR hR)
  · exact PacketReaderReturnPayload.none_natural (ZFContext.add hZ _) _ _ (add hw _) (.conjR (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketReaderReturnNormalize
