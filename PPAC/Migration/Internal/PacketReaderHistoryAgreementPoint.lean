import PPAC.Migration.Internal.PacketReaderHistoryAgreementRows

/-! Empty-index and successor-index comparison points retain actual history rows and exact graph domains. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryAgreementPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws PacketReaderHistoryAgreementSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem zero_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g i a b : Fin m)
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (hi : Derives Γ (empty i)) (ha : Derives Γ (edge f i a)) (hb : Derives Γ (edge g i b)) : Derives Γ (.equal a b) := by
  have he := OmegaUniversal.empty_unique i z (ZFContext.arithmetic hZ).base.extensionality hi (zero_at _ _ _ _ _ _ _ _ _ hf)
  have ha' := StructuralListTraceOrder.edge_input_subst f i z a he ha
  have hb' := StructuralListTraceOrder.edge_input_subst g i z b he hb
  have hA := GraphProperties.single_valued f d z a n (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ _ _ hf)) ha' (seed_at _ _ _ _ _ _ _ _ _ hf)
  have hB := GraphProperties.single_valued g e z b n (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ _ _ hg)) hb' (seed_at _ _ _ _ _ _ _ _ _ hg)
  exact eq_trans hA (eq_symm hB)

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g i : Fin m)
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (hi : Derives Γ (empty i)) : Derives Γ (agree f g i) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let F := edge (old 2 f) (old 2 i) (slot 2 0)
  let G := edge (old 2 g) (old 2 i) (slot 2 1)
  let Δ := Context.add G (Context.add F (raisedContext 2 Γ))
  have lift2 {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := add (add (HornBinderRules.under_many 2 hp) F) G
  have hZ2 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) F) G
  have hf2 := of_eq (history_rename w B z o n r l d f (old 2)) (lift2 hf)
  have hg2 := of_eq (history_rename w B z o n t k e g (old 2)) (lift2 hg)
  have hi2 := of_eq (empty_rename i (old 2)) (lift2 hi)
  exact zero_values hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf2 hg2 hi2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g i j a b : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (hi : Derives Γ (agree f g i)) (hs : Derives Γ (successor j i))
    (ha : Derives Γ (edge f j a)) (hb : Derives Γ (edge g j b)) : Derives Γ (.equal a b) := by
  have hF := sequence_at _ _ _ _ _ _ _ _ _ hf
  have hG := sequence_at _ _ _ _ _ _ _ _ _ hg
  have hjD := GraphProperties.domain_of_edge f d j a (ZFContext.arithmetic hZ).base.extensionality (.conjL hF) ha
  have hjE := GraphProperties.domain_of_edge g e j b (ZFContext.arithmetic hZ).base.extensionality (.conjL hG) hb
  have hiL := SyntaxIndexLiftOrder.predecessor_member hZ w l d j i hw (length_at _ _ _ _ _ _ _ _ _ hf) (successor_at _ _ _ _ _ _ _ _ _ hf) hjD hs
  have hiK := SyntaxIndexLiftOrder.predecessor_member hZ w k e j i hw (length_at _ _ _ _ _ _ _ _ _ hg) (successor_at _ _ _ _ _ _ _ _ _ hg) hjE hs
  have hrowF := row_at _ _ _ _ _ _ _ _ _ _ hf hiL
  have hrowG := row_at _ _ _ _ _ _ _ _ _ _ hg hiK
  exact PacketReaderHistoryAgreementRows.outputs_unique hZ w B z o f g d e i j a b hw hB hF hG hi hs hrowF hrowG ha hb

theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g i j : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (hi : Derives Γ (agree f g i)) (hs : Derives Γ (successor j i)) : Derives Γ (agree f g j) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let F := edge (old 2 f) (old 2 j) (slot 2 0)
  let G := edge (old 2 g) (old 2 j) (slot 2 1)
  let Δ := Context.add G (Context.add F (raisedContext 2 Γ))
  have lift2 {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := add (add (HornBinderRules.under_many 2 hp) F) G
  have hZ2 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) F) G
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := lift2 hB
  have hf2 := of_eq (history_rename w B z o n r l d f (old 2)) (lift2 hf)
  have hg2 := of_eq (history_rename w B z o n t k e g (old 2)) (lift2 hg)
  have hi2 := of_eq (agree_rename f g i (old 2)) (lift2 hi)
  have hs2 := of_eq (successor_rename j i (old 2)) (lift2 hs)
  exact step_values hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 hB2 hf2 hg2 hi2 hs2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderHistoryAgreementPoint
