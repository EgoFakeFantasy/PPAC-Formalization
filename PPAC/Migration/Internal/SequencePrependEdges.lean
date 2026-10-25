import PPAC.Migration.Internal.SequencePrependGraph

/-! Every zero and successor edge of the actual prepended graph has the exact original source value, including all nonstandard indices. -/
namespace PPAC.Migration.Internal.SequencePrependEdges
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequencePrependSyntax

theorem zero_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n e g z : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (successor e d))
    (hg : Derives Γ (graph f d n e g)) (hz : Derives Γ (empty z)) : Derives Γ (edge g z n) := by
  have hzE := SyntaxIndexLiftOrder.zero_member hZ w d e z hw hd he hz
  have hv : Derives Γ (value f d n z n) := .disjL (.conjI hz (.eqRefl n))
  exact .impE (.conjR (law_at _ _ _ _ _ _ _ hg)) (.conjI hzE hv)

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n e g i j y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (successor e d))
    (hg : Derives Γ (graph f d n e g)) (hj : Derives Γ (.mem j d)) (hs : Derives Γ (successor i j)) :
    Derives Γ ((edge g i y).iff (edge f j y)) := by
  have hjN := StructuralListTraceOrder.member_member hZ w j d hw hd hj
  have hiE := SyntaxIndexLiftOrder.successor_member hZ w j d i e hw hjN hd hj hs he
  have hLaw := law_at f d n e g i y hg
  have hNorm := SequencePrependValues.at_successor hZ w f d n i j y hw hd hs
  apply Derives.conjI
  · apply Derives.impI
    have hVal := Derives.conjR (.impE (add (.conjL hLaw) _) (.hyp (Or.inl rfl)))
    exact .conjR (.impE (add (.conjL hNorm) _) hVal)
  · apply Derives.impI
    have hv := Derives.impE (add (.conjR hNorm) _) (.conjI (add hj _) (.hyp (Or.inl rfl)))
    exact .impE (add (.conjR hLaw) _) (.conjI (add hiE _) hv)

theorem forward_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n e g i j y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (successor e d))
    (hg : Derives Γ (graph f d n e g)) (hj : Derives Γ (.mem j d)) (hs : Derives Γ (successor i j))
    (hf : Derives Γ (edge f j y)) : Derives Γ (edge g i y) :=
  .impE (.conjR (successor_iff hZ w f d n e g i j y hw hd he hg hj hs)) hf

end PPAC.Migration.Internal.SequencePrependEdges
