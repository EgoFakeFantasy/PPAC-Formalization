import PPAC.Migration.Internal.StructuralReverseFieldValues

/-! Original Replacement constructs the actual exact reverse-field graph, with omega-valued full sequence and unique graph set. -/
namespace PPAC.Migration.Internal.StructuralReverseFieldGraph
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralReverseFieldSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 3 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hl : Derives Γ (.mem (ρ 2) (ρ 0))) :
    Derives Γ (ReplacementPredicates.total matrix ρ (ρ 2)) := by
  simp only [ReplacementPredicates.total,matrix_fiber,paramsUp]
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (Fin.last m) (ρ 2).castSucc
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename (ρ 0) Fin.castSucc) (under hw H)
  exact StructuralReverseFieldValues.exists_unique hZ1 (ρ 0).castSucc (ρ 1).castSucc (ρ 2).castSucc (Fin.last m) hw1 (under hl H) (.hyp (Or.inl rfl))

theorem outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 3 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (RelationGraph.outputsInto matrix ρ (ρ 2) (ρ 0)) := by
  simp only [RelationGraph.outputsInto,matrix_rel,paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := (Formula.mem (Fin.last m).castSucc (ρ 2).castSucc.castSucc).conj (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  have hZ2 := ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) H
  have hw2 : Derives (Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))) (omega (ρ 0).castSucc.castSucc) := of_eq (by simp only [omega_rename]) (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)) H)
  exact StructuralReverseFieldValues.range hZ2 _ _ _ _ _ hw2 (.conjR (.hyp (Or.inl rfl)))

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) : Derives Γ (existsGraph w n l) := by
  let ρ := NaturalAdditionTransport.params3 w n l
  have ht := total hZ ρ hw hl
  have he := RelationGraphFunction.exists_graph hZ matrix ρ l ht
  simpa only [ρ,RelationGraphSyntax.existsGraph,RelationGraphSyntax.functionGraph,RelationGraphSyntax.edgeLaw,matrix_rel,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2,existsGraph,graph,edgeLaw] using he

theorem sequence {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (graph w n l g)) : Derives Γ (SequenceSyntax.sequence g l w) := by
  let ρ := NaturalAdditionTransport.params3 w n l
  have hg0 : Derives Γ (RelationGraphSyntax.functionGraph matrix ρ l g) :=
    of_eq (by simp only [ρ,RelationGraphSyntax.functionGraph,RelationGraphSyntax.edgeLaw,matrix_rel,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2,graph,edgeLaw]) hg
  exact RelationGraph.sequence matrix ρ l w g hg0 (outputs hZ ρ hw)

theorem unique_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g h : Fin m)
    (hg : Derives Γ (graph w n l g)) (hh : Derives Γ (graph w n l h)) : Derives Γ (.equal g h) := by
  let ρ := NaturalAdditionTransport.params3 w n l
  have hg0 : Derives Γ (RelationGraphSyntax.functionGraph matrix ρ l g) :=
    of_eq (by simp only [ρ,RelationGraphSyntax.functionGraph,RelationGraphSyntax.edgeLaw,matrix_rel,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2,graph,edgeLaw]) hg
  have hh0 : Derives Γ (RelationGraphSyntax.functionGraph matrix ρ l h) :=
    of_eq (by simp only [ρ,RelationGraphSyntax.functionGraph,RelationGraphSyntax.edgeLaw,matrix_rel,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2,graph,edgeLaw]) hh
  exact RelationGraph.unique_graph hZ matrix ρ l g h hg0 hh0

end PPAC.Migration.Internal.StructuralReverseFieldGraph
