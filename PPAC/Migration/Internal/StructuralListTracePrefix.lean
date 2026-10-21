import PPAC.Migration.Internal.StructuralListTraceOrder

/-! 实际限制图保留所有前缀相邻步；前驱长度上的完整轨迹实际存在。 -/
namespace PPAC.Migration.Internal.StructuralListTracePrefix
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListTraceOrder
open StructuralListTraceProperties
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem row_restrict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p l f g i : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (hres : Derives Γ (RestrictionSyntax.restrict g f l)) (hi : Derives Γ (.mem i p))
    (hr : Derives Γ (row w f i)) : Derives Γ (row w g i) := by
  have hiW := member_member hZ w i p hw hp hi
  let R := rowWitness w f i
  let Δ := Context.add R (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_row w f i _ hr
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) R
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise.raise := GraphInsertElimination.under_three hq R
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs3 : Derives Δ (successor l.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hres3 : Derives Δ (RestrictionSyntax.restrict g.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, RestrictionSyntax.restrict_rename] using lift hres
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hil := InsertLogic.old_member _ _ _ _ hs3 (lift hi)
  have hjp := GodelPairArithmetic.successor_below hZ3 _ _ _ _ hw3 (lift hiW) (lift hp) (.conjL hR) (lift hi)
  have hjl := NaturalOrderBasic.below_successor _ _ _ hs3 hjp
  have ha := RestrictionEdges.restricted_edge _ _ _ _ _ hres3 (.conjL (.conjR hR)) hil
  have hb := RestrictionEdges.restricted_edge _ _ _ _ _ hres3 (.conjL (.conjR (.conjR hR))) hjl
  have hout := intro_row _ _ _ _ _ _ (.conjL hR) ha hb (.conjR (.conjR (.conjR hR)))
  simpa only [Formula.raise, row_rename] using hout

theorem links_restrict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p l f g : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (hl : Derives Γ (links w l f)) (hr : Derives Γ (RestrictionSyntax.restrict g f l)) : Derives Γ (links w p g) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) p.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ M
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw M
  have hs1 : Derives Δ (successor l.castSucc p.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs M
  have hl1 : Derives Δ (links w.castSucc l.castSucc f.castSucc) := by simpa only [Formula.raise, links_rename] using under hl M
  have hr1 : Derives Δ (RestrictionSyntax.restrict g.castSucc f.castSucc l.castSucc) := by simpa only [Formula.raise, RestrictionSyntax.restrict_rename] using under hr M
  have hi : Derives Δ (.mem (Fin.last m) p.castSucc) := .hyp (Or.inl rfl)
  have hil := InsertLogic.old_member _ _ _ _ hs1 hi
  exact row_restrict hZ1 _ _ _ _ _ _ hw1 (under hp M) hs1 hr1 hi (StructuralListTraceSyntax.links_at _ _ _ _ hl1 hil)

theorem valid_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n p a : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (ht : Derives Γ (trace w z e l d f n)) (ha : Derives Γ (edge f p a)) : Derives Γ (valid w a) := by
  have hsub := old_subset l d (successor_at _ _ _ _ _ _ _ ht)
  have hg := SequencePrefix.exists_prefix f d l w (ZFContext.separation hZ RestrictionSyntax.matrix)
    (ZFContext.arithmetic hZ).base.extensionality (sequence_at _ _ _ _ _ _ _ ht) hsub
  let G := SequencePrefix.witness (Fin.last m) f.castSucc l.castSucc w.castSucc
  let Δ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ G
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw G
  have hs1 : Derives Δ (successor l.castSucc p.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs G
  have ht1 : Derives Δ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, trace_rename] using under ht G
  have ha1 : Derives Δ (edge f.castSucc p.castSucc a.castSucc) := by simpa only [Formula.raise, edge_rename] using under ha G
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hres := Derives.conjL (Derives.conjR hG)
  have hzp := GodelUnpairArithmetic.zero_below hZ1 _ _ _ hw1 (zero_at _ _ _ _ _ _ _ ht1) (under hp G)
  have hzl := NaturalOrderBasic.below_successor _ _ _ hs1 hzp
  have hseed := RestrictionEdges.restricted_edge _ _ _ _ _ hres (seed_at _ _ _ _ _ _ _ ht1) hzl
  have hlast := RestrictionEdges.restricted_edge _ _ _ _ _ hres ha1 (InsertLogic.new_member _ _ _ hs1)
  have hlinks := links_restrict hZ1 _ _ _ _ _ hw1 (under hp G) hs1 (links_at_trace _ _ _ _ _ _ _ ht1) hres
  have hnew := intro_trace _ _ _ _ _ _ _ (zero_at _ _ _ _ _ _ _ ht1) (nil_at _ _ _ _ _ _ _ ht1)
    (under hp G) hs1 (.conjL hG) hseed hlinks hlast
  have hout := intro_valid _ _ _ _ _ _ _ hnew
  simpa only [Formula.raise, valid_rename] using hout
end PPAC.Migration.Internal.StructuralListTracePrefix
