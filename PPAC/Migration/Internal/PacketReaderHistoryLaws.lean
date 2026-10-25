import PPAC.Migration.Internal.PacketReaderHistorySyntax

/-! Concrete history projections, all-index adjacent steps, and the exact zero-step endpoint law. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryLaws
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PacketReaderHistorySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem source_at {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (PacketReaderStateSyntax.carrier w n) := (.conjL hh)

theorem zero_at {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (empty z) := (.conjL (.conjR hh))

theorem length_at {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (Formula.mem l w) := (.conjL (.conjR (.conjR hh)))

theorem successor_at {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (successor d l) := (.conjL (.conjR (.conjR (.conjR hh))))

theorem sequence_at {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (SequenceSyntax.sequence f d w) := (.conjL (.conjR (.conjR (.conjR (.conjR hh)))))

theorem seed_at {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (edge f z n) := (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hh))))))

theorem last_at {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (edge f l r) := (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hh)))))))

theorem links_at_history {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (links w B z o l f) := (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hh)))))))

theorem row_at {m} {Γ : Context m} (w B z o n r l d f i : Fin m) (hh : Derives Γ (history w B z o n r l d f))
    (hi : Derives Γ (.mem i l)) : Derives Γ (row w B z o f i) := links_at _ _ _ _ _ _ _ (links_at_history _ _ _ _ _ _ _ _ _ hh) hi

theorem endpoint_range {m} {Γ : Context m} (w B z o n r l d f : Fin m) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ ((Formula.mem n w).conj (.mem r w)) := by
  have hs := sequence_at _ _ _ _ _ _ _ _ _ hh
  exact .conjI (.impE (SequenceSyntax.bounded_at f w z n (.conjR hs)) (seed_at _ _ _ _ _ _ _ _ _ hh))
    (.impE (SequenceSyntax.bounded_at f w l r (.conjR hs)) (last_at _ _ _ _ _ _ _ _ _ hh))

theorem zero_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f : Fin m)
    (hh : Derives Γ (history w B z o n r l d f)) (hl : Derives Γ (empty l)) : Derives Γ (.equal n r) := by
  have he := OmegaUniversal.empty_unique z l (ZFContext.arithmetic hZ).base.extensionality (zero_at _ _ _ _ _ _ _ _ _ hh) hl
  have hn := StructuralListTraceOrder.edge_input_subst f z l n he (seed_at _ _ _ _ _ _ _ _ _ hh)
  exact GraphProperties.single_valued f d l n r (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ _ _ hh)) hn (last_at _ _ _ _ _ _ _ _ _ hh)

end PPAC.Migration.Internal.PacketReaderHistoryLaws
