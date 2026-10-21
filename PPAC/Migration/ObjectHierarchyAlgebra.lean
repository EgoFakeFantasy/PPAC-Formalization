import PPAC.Migration.HierarchySuccessor

/-! 历史与层成员公式、层代数及后继幂集等式的全对象闭句和原核证书。 -/
namespace PPAC.Migration.ObjectHierarchyAlgebra
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax HierarchyLayerSyntax HierarchyMemberSyntax

def historySentence : Source.Sentence := ((ordinal (0 : Fin 4)).imp ((graph 1 0).imp
  ((Formula.mem 2 0).imp ((edge 1 2 3).iff (layer 2 3))))).close

def operationSentence : Source.Sentence := ((PowerUnionSyntax.operation (0 : Fin 4) 1 2).imp
  ((Formula.mem 3 2).iff (graphMember 0 1 3))).close

def membershipSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp ((layer 0 1).imp (membership 0 1))).close

def monotoneSentence : Source.Sentence := ((ordinal (0 : Fin 4)).imp ((ordinal 1).imp
  ((layer 0 2).imp ((layer 1 3).imp ((subset 1 0).imp (subset 3 2)))))).close

def memberSentence : Source.Sentence := ((ordinal (0 : Fin 4)).imp ((layer 0 2).imp
  ((Formula.mem 1 0).imp ((layer 1 3).imp (.mem 3 2))))).close

def transitiveSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp ((layer 0 1).imp (transitiveSet 1))).close

def successorSentence : Source.Sentence := ((ordinal (0 : Fin 4)).imp ((OmegaSyntax.successor 1 0).imp
  ((layer 0 2).imp ((layer 1 3).imp (PowerSetSyntax.powerOf 3 2))))).close

theorem separation_at (m : Nat) : Derives (Source.SetLanguage.ZF.at m)
    ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) :=
  .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation RestrictionSyntax.matrix, rfl⟩

theorem power_at (m : Nat) : Derives (Source.SetLanguage.ZF.at m) (Source.SetLanguage.powerSet.rename Fin.elim0) :=
  .hyp ⟨_, Source.SetLanguage.IsZFAxiom.powerSet, rfl⟩

theorem deterministic_at (m : Nat) : Derives (Source.SetLanguage.ZF.at m)
    (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) :=
  HierarchyLayerUnique.deterministic_at (ObjectTransitiveCover.closed_at ObjectPowerUnion.source_ZF_deterministic m)

theorem source_history : Derives (Source.SetLanguage.ZF.at 0) historySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (Formula.mem 2 0) (Context.add (graph 1 0) (Context.add (ordinal 0) (Source.SetLanguage.ZF.at 4))))
  have hA : OrdinalRecursionContext.Evidence Δ := (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 4) _) _) _)
  have hsep : Derives Δ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := (add (add (add (separation_at 4) _) _) _)
  have hd : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := (add (add (add (deterministic_at 4) _) _) _)
  exact HierarchyHistory.edge_iff_layer hA hsep 1 0 2 3 hd
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_operation : Derives (Source.SetLanguage.ZF.at 0) operationSentence := by
  apply close_derives
  apply Derives.impI
  exact PowerUnionMembership.operation_iff 0 1 2 3 (add (power_at 4) _) (.hyp (Or.inl rfl))

theorem source_membership : Derives (Source.SetLanguage.ZF.at 0) membershipSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (layer 0 1) (Context.add (ordinal 0) (Source.SetLanguage.ZF.at 2)))
  have hA : OrdinalRecursionContext.Evidence Δ := (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 2) _) _)
  have hsep : Derives Δ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := (add (add (separation_at 2) _) _)
  have hp : Derives Δ (Source.SetLanguage.powerSet.rename Fin.elim0) := (add (add (power_at 2) _) _)
  have hd : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := (add (add (deterministic_at 2) _) _)
  exact HierarchyMembership.layer_membership hA hsep hp 0 1 hd
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_monotone : Derives (Source.SetLanguage.ZF.at 0) monotoneSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (subset 1 0) (Context.add (layer 1 3) (Context.add (layer 0 2) (Context.add (ordinal 1) (Context.add (ordinal 0) (Source.SetLanguage.ZF.at 4))))))
  have hA : OrdinalRecursionContext.Evidence Δ := (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 4) _) _) _) _) _)
  have hsep : Derives Δ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := (add (add (add (add (add (separation_at 4) _) _) _) _) _)
  have hp : Derives Δ (Source.SetLanguage.powerSet.rename Fin.elim0) := (add (add (add (add (add (power_at 4) _) _) _) _) _)
  have hd : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := (add (add (add (add (add (deterministic_at 4) _) _) _) _) _)
  have ha : Derives Δ (ordinal 0) := Derives.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hb : Derives Δ (ordinal 1) := Derives.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hu := HierarchyMembership.layer_membership hA hsep hp 0 2 hd ha (.hyp (Or.inr (Or.inr (Or.inl rfl))))
  have hv := HierarchyMembership.layer_membership hA hsep hp 1 3 hd hb (.hyp (Or.inr (Or.inl rfl)))
  exact HierarchyAlgebra.monotone 0 1 2 3 (.hyp (Or.inl rfl)) hu hv

theorem source_member : Derives (Source.SetLanguage.ZF.at 0) memberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (layer 1 3) (Context.add (Formula.mem 1 0) (Context.add (layer 0 2) (Context.add (ordinal 0) (Source.SetLanguage.ZF.at 4)))))
  have hA : OrdinalRecursionContext.Evidence Δ := (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 4) _) _) _) _)
  have hsep : Derives Δ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := (add (add (add (add (separation_at 4) _) _) _) _)
  have hp : Derives Δ (Source.SetLanguage.powerSet.rename Fin.elim0) := (add (add (add (add (power_at 4) _) _) _) _)
  have hd : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := (add (add (add (add (deterministic_at 4) _) _) _) _)
  have hu := HierarchyMembership.layer_membership hA hsep hp 0 2 hd
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
  exact HierarchyAlgebra.value_member 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)) hu

theorem source_transitive : Derives (Source.SetLanguage.ZF.at 0) transitiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (layer 0 1) (Context.add (ordinal 0) (Source.SetLanguage.ZF.at 2)))
  have hA : OrdinalRecursionContext.Evidence Δ := (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 2) _) _)
  have hsep : Derives Δ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := (add (add (separation_at 2) _) _)
  have hp : Derives Δ (Source.SetLanguage.powerSet.rename Fin.elim0) := (add (add (power_at 2) _) _)
  have hd : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := (add (add (deterministic_at 2) _) _)
  have ha : Derives Δ (ordinal 0) := Derives.hyp (Or.inr (Or.inl rfl))
  have hu := HierarchyMembership.layer_membership hA hsep hp 0 1 hd ha (.hyp (Or.inl rfl))
  exact HierarchyAlgebra.transitive hA hsep hp 0 1 hd ha hu

theorem source_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (layer 1 3) (Context.add (layer 0 2) (Context.add (OmegaSyntax.successor 1 0) (Context.add (ordinal 0) (Source.SetLanguage.ZF.at 4)))))
  have hA : OrdinalRecursionContext.Evidence Δ := (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 4) _) _) _) _)
  have hsep : Derives Δ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := (add (add (add (add (separation_at 4) _) _) _) _)
  have hp : Derives Δ (Source.SetLanguage.powerSet.rename Fin.elim0) := (add (add (add (add (power_at 4) _) _) _) _)
  have hd : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := (add (add (add (add (deterministic_at 4) _) _) _) _)
  have ha : Derives Δ (ordinal 0) := Derives.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hs : Derives Δ (OmegaSyntax.successor 1 0) := Derives.hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hl : Derives Δ (layer 0 2) := Derives.hyp (Or.inr (Or.inl rfl))
  have hu := HierarchyMembership.layer_membership hA hsep hp 0 2 hd ha hl
  have hOrdS := OrdinalSuccessor.ordinal 1 0 hA.foundation hs ha
  have hv := HierarchyMembership.layer_membership hA hsep hp 1 3 hd hOrdS (.hyp (Or.inl rfl))
  exact HierarchySuccessor.power hA hsep hp 0 2 1 3 hd ha hl hu hs hv

theorem history_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence historySentence) := TheoryTransport.sentence source_history

theorem native_history : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence historySentence) :=
  ZFReplay.replay history_kernel_certificate

theorem operation_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence operationSentence) := TheoryTransport.sentence source_operation

theorem native_operation : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence operationSentence) :=
  ZFReplay.replay operation_kernel_certificate

theorem membership_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence membershipSentence) := TheoryTransport.sentence source_membership

theorem native_membership : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence membershipSentence) :=
  ZFReplay.replay membership_kernel_certificate

theorem monotone_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence monotoneSentence) := TheoryTransport.sentence source_monotone

theorem native_monotone : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence monotoneSentence) :=
  ZFReplay.replay monotone_kernel_certificate

theorem member_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence memberSentence) := TheoryTransport.sentence source_member

theorem native_member : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence memberSentence) :=
  ZFReplay.replay member_kernel_certificate

theorem transitive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence transitiveSentence) := TheoryTransport.sentence source_transitive

theorem native_transitive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence transitiveSentence) :=
  ZFReplay.replay transitive_kernel_certificate

theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor

theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence successorSentence) :=
  ZFReplay.replay successor_kernel_certificate
end PPAC.Migration.ObjectHierarchyAlgebra
