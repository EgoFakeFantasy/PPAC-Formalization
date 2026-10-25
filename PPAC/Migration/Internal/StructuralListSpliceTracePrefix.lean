import PPAC.Migration.Internal.StructuralListSpliceRowRestrict

/-! Original Separation constructs both exact prefix graphs; all restricted old rows are proved. -/
namespace PPAC.Migration.Internal.StructuralListSpliceTracePrefix
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax StructuralListSpliceSyntax StructuralListSpliceTraceProperties
open SyntaxRenameQuerySyntax (of_eq)

theorem from_prefixes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a z e l d f g p x u F G : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (ht : Derives Γ (trace w n t a z e l d f g)) (hx : Derives Γ (edge f p x)) (hu : Derives Γ (edge g p u))
    (hF : Derives Γ (SequencePrefix.witness F f l w)) (hG : Derives Γ (SequencePrefix.witness G g l w)) :
    Derives Γ (trace w x t u z e p l F G) := by
  have hlist := list_trace _ _ _ _ _ _ _ _ _ _ ht
  have hFr := Derives.conjL (Derives.conjR hF)
  have hGr := Derives.conjL (Derives.conjR hG)
  have hzp := GodelUnpairArithmetic.zero_below hZ w z p hw (StructuralListTraceProperties.zero_at _ _ _ _ _ _ _ hlist) hp
  have hzl := NaturalOrderBasic.below_successor _ _ _ hs hzp
  have hpl := InsertLogic.new_member l p p hs
  have hseedF := RestrictionEdges.restricted_edge _ _ _ _ _ hFr (StructuralListTraceProperties.seed_at _ _ _ _ _ _ _ hlist) hzl
  have hlastF := RestrictionEdges.restricted_edge _ _ _ _ _ hFr hx hpl
  have hseedG := RestrictionEdges.restricted_edge _ _ _ _ _ hGr (seed_edge _ _ _ _ _ _ _ _ _ _ ht) hzl
  have hlastG := RestrictionEdges.restricted_edge _ _ _ _ _ hGr hu hpl
  have hlinksF := StructuralListTracePrefix.links_restrict hZ w p l f F hw hp hs (StructuralListTraceProperties.links_at_trace _ _ _ _ _ _ _ hlist) hFr
  have hnewF := StructuralListTraceSyntax.intro_trace w z e p l F x (StructuralListTraceProperties.zero_at _ _ _ _ _ _ _ hlist)
    (StructuralListTraceProperties.nil_at _ _ _ _ _ _ _ hlist) hp hs (.conjL hF) hseedF hlinksF hlastF
  have hlinks := StructuralListSpliceRowRestrict.links_restrict hZ w p l f g F G hw hp hs (splice_links _ _ _ _ _ _ _ _ _ _ ht) hFr hGr
  exact intro_trace _ _ _ _ _ _ _ _ _ _ hnewF (.conjL hG) hseedG hlastG hlinks

theorem exists_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a z e l d f g p x u : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (ht : Derives Γ (trace w n t a z e l d f g)) (hx : Derives Γ (edge f p x)) (hu : Derives Γ (edge g p u)) :
    Derives Γ (raw w x t u) := by
  have hsub := StructuralListTraceOrder.old_subset l d (StructuralListTraceProperties.successor_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ ht))
  have hF := SequencePrefix.exists_prefix f d l w (ZFContext.separation hZ RestrictionSyntax.matrix) (ZFContext.arithmetic hZ).base.extensionality
    (StructuralListTraceProperties.sequence_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ ht)) hsub
  let F := SequencePrefix.witness (Fin.last m) f.castSucc l.castSucc w.castSucc
  let ΓF := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) hF
  have hZ1 := ZFContext.under hZ F
  have ht1 := of_eq (trace_rename w n t a z e l d f g Fin.castSucc) (under ht F)
  have hsub1 := of_eq (RestrictionSyntax.subset_rename l d Fin.castSucc) (under hsub F)
  have hG := SequencePrefix.exists_prefix g.castSucc d.castSucc l.castSucc w.castSucc
    (ZFContext.separation hZ1 RestrictionSyntax.matrix) (ZFContext.arithmetic hZ1).base.extensionality (value_sequence _ _ _ _ _ _ _ _ _ _ ht1) hsub1
  let G := SequencePrefix.witness (Fin.last (m+1)) g.castSucc.castSucc l.castSucc.castSucc w.castSucc.castSucc
  let Δ := Context.add G (Context.image Formula.raise ΓF)
  apply Derives.exE (p := G) hG
  have hZ2 := ZFContext.under hZ1 G
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using under (under hw F) G
  have hp2 : Derives Δ (.mem p.castSucc.castSucc w.castSucc.castSucc) := under (under hp F) G
  have hs2 : Derives Δ (successor l.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise,successor_rename] using under (under hs F) G
  have ht2 := of_eq (trace_rename w.castSucc n.castSucc t.castSucc a.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc g.castSucc Fin.castSucc) (under ht1 G)
  have hx2 : Derives Δ (edge f.castSucc.castSucc p.castSucc.castSucc x.castSucc.castSucc) := by simpa only [Formula.raise,edge_rename] using under (under hx F) G
  have hu2 : Derives Δ (edge g.castSucc.castSucc p.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise,edge_rename] using under (under hu F) G
  have hFold : Derives ΓF F := .hyp (Or.inl rfl)
  have hF2 := of_eq (SequencePrefix.witness_rename (Fin.last m) f.castSucc l.castSucc w.castSucc Fin.castSucc) (under hFold G)
  have hG2 : Derives Δ G := .hyp (Or.inl rfl)
  have hnew := from_prefixes hZ2 w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc
    z.castSucc.castSucc e.castSucc.castSucc l.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc
    p.castSucc.castSucc x.castSucc.castSucc u.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hp2 hs2 ht2 hx2 hu2 hF2 hG2
  simpa only [Formula.raise,raw_rename] using intro_raw _ _ _ _ _ _ _ _ _ _ hnew

end PPAC.Migration.Internal.StructuralListSpliceTracePrefix
