import PPAC.Migration.Internal.OriginalHeadDisjoint

/-! 任意内部tag0行上完整原规则表精确分派到两个原lookup规则，不遗留外部规则假设。 -/
namespace PPAC.Migration.Internal.OriginalLookupDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornStepSyntax HornApplicationSyntax
open OriginalRuleTags
open YesMetaZFC.Automation.ObjectSyntaxTransform (lookupHead lookupTail)

theorem remaining_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w row trace : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor k 0 w xs row))
    (he : Derives Γ (step remaining w row trace)) : Derives Γ .bot := by
  apply step_elim remaining w row trace .bot he
  intro rule hr
  apply Derives.impI
  exact OriginalHeadDisjoint.application_contradiction (ZFContext.add hZ _) rule (remaining_nonzero rule hr) k w row trace xs
    (add hw _) (add hc _) (.hyp (Or.inl rfl))

theorem dispatch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w row trace : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor k 0 w xs row)) :
    Derives Γ ((originalStep w row trace).iff (lookupStep w row trace)) := by
  change Derives Γ (((application lookupHead w row trace).disj ((application lookupTail w row trace).disj (step remaining w row trace))).iff
    ((application lookupHead w row trace).disj (application lookupTail w row trace)))
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .disjR (.hyp (Or.inl rfl))
      · exact .botE (remaining_rejected (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) k w row trace xs
          (add (add (add hw _) _) _) (add (add (add hc _) _) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.hyp (Or.inl rfl))
    · exact .disjR (.disjL (.hyp (Or.inl rfl)))

theorem lookup_intro {m} {Γ : Context m} (w row trace : Fin m) (he : Derives Γ (lookupStep w row trace)) :
    Derives Γ (originalStep w row trace) := by
  change Derives Γ ((application lookupHead w row trace).disj ((application lookupTail w row trace).disj (step remaining w row trace)))
  apply Derives.disjE he
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (.disjL (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.OriginalLookupDispatch
