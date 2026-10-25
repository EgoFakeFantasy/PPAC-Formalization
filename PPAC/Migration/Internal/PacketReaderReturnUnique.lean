import PPAC.Migration.Internal.PacketReaderReturnExistence

/-! Actual EOF-return payloads and option codes are unique; original success/rejection guards exclude mixed branches. -/
namespace PPAC.Migration.Internal.PacketReaderReturnUnique
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem success_rejection_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketReaderInputSyntax.eofSuccess w z o L v s a))
    (hr : Derives Γ (rejection w B z o L v s a)) : Derives Γ .bot := by
  apply Derives.disjE hr
  · exact PacketReaderTerminalRaw.success_failure_disjoint _ _ _ _ _ _ _ (add he _) (.hyp (Or.inl rfl))
  · exact PacketReaderTerminalRaw.success_reject_disjoint (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add he _) (.conjR (.hyp (Or.inl rfl)))

theorem success_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z o L v s a p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (success w z o L v s a p)) (hq : Derives Γ (success w z o L v s a q)) : Derives Γ (.equal p q) := by
  let R := (StructuralListReverseSyntax.reverses w.castSucc a.castSucc (Fin.last m)).conj (some w.castSucc (Fin.last m) p.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR hp)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hq1 := of_eq (success_rename w z o L v s a q Fin.castSucc) (under hq R)
  let T := (StructuralListReverseSyntax.reverses w.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))).conj (some w.castSucc.castSucc (Fin.last (m+1)) q.castSucc.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) (.conjR hq1)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
  have hOldRev := of_eq (StructuralListReverseSyntax.reverses_rename w.castSucc a.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) T)
  have hOldSome := of_eq (some_rename w.castSucc (Fin.last m) p.castSucc Fin.castSucc) (under (.conjR hR) T)
  have he := StructuralListReverseUnique.unique hZ2 _ _ _ _ hw2 hOldRev (.conjL hT)
  have hc := PacketReaderReturnPayload.payload_subst _ _ _ _ he hOldSome
  exact PacketReaderReturnPayload.some_unique hZ2 _ _ _ _ hw2 hc (.conjR hT)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (result w B z o L v s a p)) (hq : Derives Γ (result w B z o L v s a q)) : Derives Γ (.equal p q) := by
  apply Derives.disjE hp
  · let P := success w z o L v s a p
    apply Derives.disjE (add hq P)
    · exact success_unique (ZFContext.add (ZFContext.add hZ P) _) w z o L v s a p q (add (add hw P) _) (add (.hyp (Or.inl rfl)) _) (.hyp (Or.inl rfl))
    · exact .botE (success_rejection_disjoint (ZFContext.add (ZFContext.add hZ P) _) w B z o L v s a (add (add hw P) _) (add (.conjL (.hyp (Or.inl rfl) : Derives (Context.add P Γ) P)) _) (.conjL (.hyp (Or.inl rfl))))
  · let P := failure w B z o L v s a p
    apply Derives.disjE (add hq P)
    · exact .botE (success_rejection_disjoint (ZFContext.add (ZFContext.add hZ P) _) w B z o L v s a (add (add hw P) _) (.conjL (.hyp (Or.inl rfl))) (add (.conjL (.hyp (Or.inl rfl) : Derives (Context.add P Γ) P)) _))
    · exact PacketReaderReturnPayload.none_unique (ZFContext.add (ZFContext.add hZ P) _) w p q (add (add hw P) _) (add (.conjR (.hyp (Or.inl rfl) : Derives (Context.add P Γ) P)) _) (.conjR (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketReaderReturnUnique
