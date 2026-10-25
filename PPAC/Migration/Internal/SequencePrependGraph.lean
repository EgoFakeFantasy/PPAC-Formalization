import PPAC.Migration.Internal.SequencePrependValues

/-! Original Replacement builds the exact actual prepend graph; no external iteration or chosen graph is used. -/
namespace PPAC.Migration.Internal.SequencePrependGraph
open Source SourceAlgebra SourceLogic OmegaSyntax SequencePrependSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 3 → Fin m) (w e : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem (ρ 1) w)) (he : Derives Γ (successor e (ρ 1)))
    (hf : Derives Γ (SequenceSyntax.sequence (ρ 0) (ρ 1) w)) : Derives Γ (ReplacementPredicates.total matrix ρ e) := by
  simp only [ReplacementPredicates.total,matrix_fiber,paramsUp]
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (Fin.last m) e.castSucc
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have he1 := of_eq (successor_rename e (ρ 1) Fin.castSucc) (under he H)
  have hf1 := of_eq (SequenceSyntax.sequence_rename (ρ 0) (ρ 1) w Fin.castSucc) (under hf H)
  exact SequencePrependValues.exists_unique hZ1 w.castSucc (ρ 0).castSucc (ρ 1).castSucc (ρ 2).castSucc e.castSucc (Fin.last m) hw1 (under hd H) he1 hf1 (.hyp (Or.inl rfl))

theorem outputs {m} {Γ : Context m} (ρ : Fin 3 → Fin m) (w e : Fin m)
    (hf : Derives Γ (SequenceSyntax.sequence (ρ 0) (ρ 1) w)) (hn : Derives Γ (.mem (ρ 2) w)) :
    Derives Γ (RelationGraph.outputsInto matrix ρ e w) := by
  simp only [RelationGraph.outputsInto,matrix_rel,paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := (Formula.mem (Fin.last m).castSucc e.castSucc.castSucc).conj (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  have hf2 := of_eq (SequenceSyntax.sequence_rename (ρ 0) (ρ 1) w (HornBinderSyntax.old 2)) (add (HornBinderRules.under_many 2 hf) H)
  exact SequencePrependValues.range _ _ _ _ _ _ hf2 (add (HornBinderRules.under_many 2 hn) H) (.conjR (.hyp (Or.inl rfl)))

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n e : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (successor e d))
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) : Derives Γ (existsGraph f d n e) := by
  let ρ := NaturalAdditionTransport.params3 f d n
  have ht := total hZ ρ w e hw hd he hf
  have hex := RelationGraphFunction.exists_graph hZ matrix ρ e ht
  simpa only [ρ,RelationGraphSyntax.existsGraph,matrix_graph,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2,existsGraph] using hex

theorem sequence {m} {Γ : Context m} (w f d n e g : Fin m)
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph f d n e g)) :
    Derives Γ (SequenceSyntax.sequence g e w) := by
  let ρ := NaturalAdditionTransport.params3 f d n
  have hg0 : Derives Γ (RelationGraphSyntax.functionGraph matrix ρ e g) :=
    of_eq (by simp only [matrix_graph,ρ,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2]) hg
  exact RelationGraph.sequence matrix ρ e w g hg0 (outputs ρ w e hf hn)

theorem unique_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f d n e g h : Fin m)
    (hg : Derives Γ (graph f d n e g)) (hh : Derives Γ (graph f d n e h)) : Derives Γ (.equal g h) := by
  let ρ := NaturalAdditionTransport.params3 f d n
  have hg0 : Derives Γ (RelationGraphSyntax.functionGraph matrix ρ e g) :=
    of_eq (by simp only [matrix_graph,ρ,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2]) hg
  have hh0 : Derives Γ (RelationGraphSyntax.functionGraph matrix ρ e h) :=
    of_eq (by simp only [matrix_graph,ρ,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2]) hh
  exact RelationGraph.unique_graph hZ matrix ρ e g h hg0 hh0

end PPAC.Migration.Internal.SequencePrependGraph
