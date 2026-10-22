import PPAC.Migration.Internal.SyntaxIndexLiftSystem

/-! 任意对象函数关系实际图与完整量词binder提升及项兼容性的原nativeZF闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxIndexLift
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates RelationGraphSyntax
open SyntaxIndexMapSyntax SyntaxVariableSyntax SyntaxIndexLiftSyntax

def relationUniqueSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d x y z : Fin m) : Source.Sentence := ((total P ρ d).imp ((Formula.mem x d).imp ((rel P ρ x y).imp ((rel P ρ x z).imp ((Formula.equal y z)))))).close

theorem source_relationUnique {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d x y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (relationUniqueSentence P ρ d x y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (rel P ρ x z) (Context.add (rel P ρ x y) (Context.add (Formula.mem x d) (Context.add (total P ρ d) ((Source.SetLanguage.ZF.at m)))))
  have h0 : Derives Δ (total P ρ d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem x d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (rel P ρ x y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (rel P ρ x z) := .hyp (Or.inl rfl)
  exact RelationGraphSyntax.relation_unique P ρ d x y z h0 h1 h2 h3

theorem relationUnique_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (relationUniqueSentence P ρ d x y z)) := TheoryTransport.sentence (source_relationUnique P ρ d x y z)

theorem native_relationUnique {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (relationUniqueSentence P ρ d x y z)) := ZFReplay.replay (relationUnique_kernel_certificate P ρ d x y z)

def pairTotalSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Source.Sentence := ((total P ρ d).imp ((total (entryMatrix P) ρ d))).close

theorem source_pairTotal {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairTotalSentence P ρ d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (total P ρ d) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (total P ρ d) := .hyp (Or.inl rfl)
  exact RelationGraphPairs.pair_total hZ P ρ d h0

theorem pairTotal_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairTotalSentence P ρ d)) := TheoryTransport.sentence (source_pairTotal P ρ d)

theorem native_pairTotal {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairTotalSentence P ρ d)) := ZFReplay.replay (pairTotal_kernel_certificate P ρ d)

def pairGraphSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Source.Sentence := ((total P ρ d).imp ((Source.Formula.ex (pairGraph P (paramsUp ρ) d.castSucc (Fin.last m))))).close

theorem source_pairGraph {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairGraphSentence P ρ d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (total P ρ d) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (total P ρ d) := .hyp (Or.inl rfl)
  exact RelationGraphPairs.exists_pair_graph hZ P ρ d h0

theorem pairGraph_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairGraphSentence P ρ d)) := TheoryTransport.sentence (source_pairGraph P ρ d)

theorem native_pairGraph {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairGraphSentence P ρ d)) := ZFReplay.replay (pairGraph_kernel_certificate P ρ d)

def pairEdgeSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g x y : Fin m) : Source.Sentence := ((pairGraph P ρ d g).imp (((edge g x y).iff ((Formula.mem x d).conj (rel P ρ x y))))).close

theorem source_pairEdge {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairEdgeSentence P ρ d g x y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (pairGraph P ρ d g) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (pairGraph P ρ d g) := .hyp (Or.inl rfl)
  exact RelationGraphEdges.edge_iff hZ P ρ d g x y h0

theorem pairEdge_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairEdgeSentence P ρ d g x y)) := TheoryTransport.sentence (source_pairEdge P ρ d g x y)

theorem native_pairEdge {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairEdgeSentence P ρ d g x y)) := ZFReplay.replay (pairEdge_kernel_certificate P ρ d g x y)

def pairCompleteSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : Source.Sentence := ((total P ρ d).imp ((pairGraph P ρ d g).imp ((functionGraph P ρ d g)))).close

theorem source_pairComplete {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairCompleteSentence P ρ d g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (pairGraph P ρ d g) (Context.add (total P ρ d) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (total P ρ d) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (pairGraph P ρ d g) := .hyp (Or.inl rfl)
  exact RelationGraphFunction.complete hZ P ρ d g h0 h1

theorem pairComplete_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairCompleteSentence P ρ d g)) := TheoryTransport.sentence (source_pairComplete P ρ d g)

theorem native_pairComplete {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairCompleteSentence P ρ d g)) := ZFReplay.replay (pairComplete_kernel_certificate P ρ d g)

def graphExistsSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Source.Sentence := ((total P ρ d).imp ((RelationGraphSyntax.existsGraph P ρ d))).close

theorem source_graphExists {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphExistsSentence P ρ d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (total P ρ d) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (total P ρ d) := .hyp (Or.inl rfl)
  exact RelationGraphFunction.exists_graph hZ P ρ d h0

theorem graphExists_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphExistsSentence P ρ d)) := TheoryTransport.sentence (source_graphExists P ρ d)

theorem native_graphExists {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphExistsSentence P ρ d)) := ZFReplay.replay (graphExists_kernel_certificate P ρ d)

def graphFiberSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Source.Sentence := ((total P ρ d).imp ((graphFiber P ρ d))).close

theorem source_graphFiber {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphFiberSentence P ρ d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (total P ρ d) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (total P ρ d) := .hyp (Or.inl rfl)
  exact RelationGraph.actual_fiber hZ P ρ d h0

theorem graphFiber_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphFiberSentence P ρ d)) := TheoryTransport.sentence (source_graphFiber P ρ d)

theorem native_graphFiber {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphFiberSentence P ρ d)) := ZFReplay.replay (graphFiber_kernel_certificate P ρ d)

def graphUniqueSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g h : Fin m) : Source.Sentence := ((functionGraph P ρ d g).imp ((functionGraph P ρ d h).imp ((Formula.equal g h)))).close

theorem source_graphUnique {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphUniqueSentence P ρ d g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (functionGraph P ρ d h) (Context.add (functionGraph P ρ d g) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (functionGraph P ρ d g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (functionGraph P ρ d h) := .hyp (Or.inl rfl)
  exact RelationGraph.unique_graph hZ P ρ d g h h0 h1

theorem graphUnique_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphUniqueSentence P ρ d g h)) := TheoryTransport.sentence (source_graphUnique P ρ d g h)

theorem native_graphUnique {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphUniqueSentence P ρ d g h)) := ZFReplay.replay (graphUnique_kernel_certificate P ρ d g h)

def graphSequenceSentence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d c g : Fin m) : Source.Sentence := ((functionGraph P ρ d g).imp ((RelationGraph.outputsInto P ρ d c).imp ((SequenceSyntax.sequence g d c)))).close

theorem source_graphSequence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d c g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphSequenceSentence P ρ d c g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RelationGraph.outputsInto P ρ d c) (Context.add (functionGraph P ρ d g) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (functionGraph P ρ d g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (RelationGraph.outputsInto P ρ d c) := .hyp (Or.inl rfl)
  exact RelationGraph.sequence P ρ d c g h0 h1

theorem graphSequence_kernel_certificate {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d c g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphSequenceSentence P ρ d c g)) := TheoryTransport.sentence (source_graphSequence P ρ d c g)

theorem native_graphSequence {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d c g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphSequenceSentence P ρ d c g)) := ZFReplay.replay (graphSequence_kernel_certificate P ρ d c g)

def zeroMemberSentence {m} (w a u z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((successor u a).imp ((empty z).imp ((Formula.mem z u)))))).close

theorem source_zeroMember {m} (w a u z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroMemberSentence w a u z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (successor u a) (Context.add (Formula.mem a w) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftOrder.zero_member hZ w a u z h0 h1 h2 h3

theorem zeroMember_kernel_certificate {m} (w a u z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroMemberSentence w a u z)) := TheoryTransport.sentence (source_zeroMember w a u z)

theorem native_zeroMember {m} (w a u z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroMemberSentence w a u z)) := ZFReplay.replay (zeroMember_kernel_certificate w a u z)

def successorMemberSentence {m} (w a b u v : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem b w).imp ((Formula.mem a b).imp ((successor u a).imp ((successor v b).imp ((Formula.mem u v)))))))).close

theorem source_successorMember {m} (w a b u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorMemberSentence w a b u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor v b) (Context.add (successor u a) (Context.add (Formula.mem a b) (Context.add (Formula.mem b w) (Context.add (Formula.mem a w) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor v b) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftOrder.successor_member hZ w a b u v h0 h1 h2 h3 h4 h5

theorem successorMember_kernel_certificate {m} (w a b u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorMemberSentence w a b u v)) := TheoryTransport.sentence (source_successorMember w a b u v)

theorem native_successorMember {m} (w a b u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorMemberSentence w a b u v)) := ZFReplay.replay (successorMember_kernel_certificate w a b u v)

def predecessorMemberSentence {m} (w a u i k : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((successor u a).imp ((Formula.mem i u).imp ((successor i k).imp ((Formula.mem k a))))))).close

theorem source_predecessorMember {m} (w a u i k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (predecessorMemberSentence w a u i k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i k) (Context.add (Formula.mem i u) (Context.add (successor u a) (Context.add (Formula.mem a w) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem i u) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor i k) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftOrder.predecessor_member hZ w a u i k h0 h1 h2 h3 h4

theorem predecessorMember_kernel_certificate {m} (w a u i k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (predecessorMemberSentence w a u i k)) := TheoryTransport.sentence (source_predecessorMember w a u i k)

theorem native_predecessorMember {m} (w a u i k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (predecessorMemberSentence w a u i k)) := ZFReplay.replay (predecessorMember_kernel_certificate w a u i k)

def successorInjectiveSentence {m} (w i k l : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem k w).imp ((successor i k).imp ((successor i l).imp ((Formula.equal k l)))))).close

theorem source_successorInjective {m} (w i k l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorInjectiveSentence w i k l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i l) (Context.add (successor i k) (Context.add (Formula.mem k w) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem k w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor i k) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor i l) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftOrder.successor_injective hZ w i k l h0 h1 h2 h3

theorem successorInjective_kernel_certificate {m} (w i k l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorInjectiveSentence w i k l)) := TheoryTransport.sentence (source_successorInjective w i k l)

theorem native_successorInjective {m} (w i k l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorInjectiveSentence w i k l)) := ZFReplay.replay (successorInjective_kernel_certificate w i k l)

def zeroOutputSentence {m} (r a x y : Fin m) : Source.Sentence := ((empty x).imp ((value r a x y).imp ((empty y)))).close

theorem source_zeroOutput {m} (r a x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroOutputSentence r a x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (value r a x y) (Context.add (empty x) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (empty x) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (value r a x y) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftPoint.zero_output r a x y h0 h1

theorem zeroOutput_kernel_certificate {m} (r a x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroOutputSentence r a x y)) := TheoryTransport.sentence (source_zeroOutput r a x y)

theorem native_zeroOutput {m} (r a x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroOutputSentence r a x y)) := ZFReplay.replay (zeroOutput_kernel_certificate r a x y)

def successorOutputSentence {m} (w r a x y k : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem k w).imp ((successor x k).imp ((value r a x y).imp (((Formula.mem k a).conj (SyntaxIndexLiftPoint.output r k y))))))).close

theorem source_successorOutput {m} (w r a x y k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorOutputSentence w r a x y k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (value r a x y) (Context.add (successor x k) (Context.add (Formula.mem k w) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem k w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor x k) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (value r a x y) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftPoint.at_successor hZ w r a x y k h0 h1 h2 h3

theorem successorOutput_kernel_certificate {m} (w r a x y k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorOutputSentence w r a x y k)) := TheoryTransport.sentence (source_successorOutput w r a x y k)

theorem native_successorOutput {m} (w r a x y k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorOutputSentence w r a x y k)) := ZFReplay.replay (successorOutput_kernel_certificate w r a x y k)

def sourceMemberSentence {m} (w r a u x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((successor u a).imp ((value r a x y).imp ((Formula.mem x u)))))).close

theorem source_sourceMember {m} (w r a u x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceMemberSentence w r a u x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (value r a x y) (Context.add (successor u a) (Context.add (Formula.mem a w) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (value r a x y) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftPoint.source_member hZ w r a u x y h0 h1 h2 h3

theorem sourceMember_kernel_certificate {m} (w r a u x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceMemberSentence w r a u x y)) := TheoryTransport.sentence (source_sourceMember w r a u x y)

theorem native_sourceMember {m} (w r a u x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceMemberSentence w r a u x y)) := ZFReplay.replay (sourceMember_kernel_certificate w r a u x y)

def targetMemberSentence {m} (w r a c v x y : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w r a c).imp ((successor v c).imp ((value r a x y).imp ((Formula.mem y v)))))).close

theorem source_targetMember {m} (w r a c v x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetMemberSentence w r a c v x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (value r a x y) (Context.add (successor v c) (Context.add (indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor v c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (value r a x y) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftPoint.target_member hZ w r a c v x y h0 h1 h2 h3

theorem targetMember_kernel_certificate {m} (w r a c v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetMemberSentence w r a c v x y)) := TheoryTransport.sentence (source_targetMember w r a c v x y)

theorem native_targetMember {m} (w r a c v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetMemberSentence w r a c v x y)) := ZFReplay.replay (targetMember_kernel_certificate w r a c v x y)

def valueUniqueSentence {m} (w r a c x y z : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w r a c).imp ((value r a x y).imp ((value r a x z).imp ((Formula.equal y z)))))).close

theorem source_valueUnique {m} (w r a c x y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueUniqueSentence w r a c x y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (value r a x z) (Context.add (value r a x y) (Context.add (indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (value r a x y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (value r a x z) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftUnique.unique hZ w r a c x y z h0 h1 h2 h3

theorem valueUnique_kernel_certificate {m} (w r a c x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueUniqueSentence w r a c x y z)) := TheoryTransport.sentence (source_valueUnique w r a c x y z)

theorem native_valueUnique {m} (w r a c x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueUniqueSentence w r a c x y z)) := ZFReplay.replay (valueUnique_kernel_certificate w r a c x y z)

def pointExistsSentence {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w (ρ 0) (ρ 1) c).imp ((successor u (ρ 1)).imp ((Formula.mem x u).imp ((hasValue SyntaxIndexLiftSyntax.matrix ρ x)))))).close

theorem source_pointExists {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pointExistsSentence ρ w c u x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x u) (Context.add (successor u (ρ 1)) (Context.add (indexMap w (ρ 0) (ρ 1) c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (indexMap w (ρ 0) (ρ 1) c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u (ρ 1)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem x u) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftExistence.point_exists hZ ρ w c u x h0 h1 h2 h3

theorem pointExists_kernel_certificate {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pointExistsSentence ρ w c u x)) := TheoryTransport.sentence (source_pointExists ρ w c u x)

theorem native_pointExists {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pointExistsSentence ρ w c u x)) := ZFReplay.replay (pointExists_kernel_certificate ρ w c u x)

def pointFiberSentence {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w (ρ 0) (ρ 1) c).imp ((successor u (ρ 1)).imp ((Formula.mem x u).imp ((fiber SyntaxIndexLiftSyntax.matrix ρ x)))))).close

theorem source_pointFiber {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pointFiberSentence ρ w c u x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x u) (Context.add (successor u (ρ 1)) (Context.add (indexMap w (ρ 0) (ρ 1) c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (indexMap w (ρ 0) (ρ 1) c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u (ρ 1)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem x u) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftExistence.point_fiber hZ ρ w c u x h0 h1 h2 h3

theorem pointFiber_kernel_certificate {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pointFiberSentence ρ w c u x)) := TheoryTransport.sentence (source_pointFiber ρ w c u x)

theorem native_pointFiber {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pointFiberSentence ρ w c u x)) := ZFReplay.replay (pointFiber_kernel_certificate ρ w c u x)

def liftTotalSentence {m} (ρ : Fin 2 → Fin m) (w c u : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w (ρ 0) (ρ 1) c).imp ((successor u (ρ 1)).imp ((total SyntaxIndexLiftSyntax.matrix ρ u))))).close

theorem source_liftTotal {m} (ρ : Fin 2 → Fin m) (w c u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftTotalSentence ρ w c u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor u (ρ 1)) (Context.add (indexMap w (ρ 0) (ρ 1) c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (indexMap w (ρ 0) (ρ 1) c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor u (ρ 1)) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftExistence.total hZ ρ w c u h0 h1 h2

theorem liftTotal_kernel_certificate {m} (ρ : Fin 2 → Fin m) (w c u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftTotalSentence ρ w c u)) := TheoryTransport.sentence (source_liftTotal ρ w c u)

theorem native_liftTotal {m} (ρ : Fin 2 → Fin m) (w c u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftTotalSentence ρ w c u)) := ZFReplay.replay (liftTotal_kernel_certificate ρ w c u)

def liftOutputsSentence {m} (ρ : Fin 2 → Fin m) (w c u v : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w (ρ 0) (ρ 1) c).imp ((successor v c).imp ((RelationGraph.outputsInto SyntaxIndexLiftSyntax.matrix ρ u v))))).close

theorem source_liftOutputs {m} (ρ : Fin 2 → Fin m) (w c u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftOutputsSentence ρ w c u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor v c) (Context.add (indexMap w (ρ 0) (ρ 1) c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (indexMap w (ρ 0) (ρ 1) c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor v c) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftExistence.outputs hZ ρ w c u v h0 h1 h2

theorem liftOutputs_kernel_certificate {m} (ρ : Fin 2 → Fin m) (w c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftOutputsSentence ρ w c u v)) := TheoryTransport.sentence (source_liftOutputs ρ w c u v)

theorem native_liftOutputs {m} (ρ : Fin 2 → Fin m) (w c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftOutputsSentence ρ w c u v)) := ZFReplay.replay (liftOutputs_kernel_certificate ρ w c u v)

def targetMapSentence {m} (w r a c u v g : Fin m) : Source.Sentence := ((lifted w r a c u v g).imp ((indexMap w g u v))).close

theorem source_targetMap {m} (w r a c u v g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetMapSentence w r a c u v g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (lifted w r a c u v g) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inl rfl)
  exact SyntaxIndexLift.target_map w r a c u v g h0

theorem targetMap_kernel_certificate {m} (w r a c u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetMapSentence w r a c u v g)) := TheoryTransport.sentence (source_targetMap w r a c u v g)

theorem native_targetMap {m} (w r a c u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetMapSentence w r a c u v g)) := ZFReplay.replay (targetMap_kernel_certificate w r a c u v g)

def liftExistsSentence {m} (w r a c u v : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w r a c).imp ((successor u a).imp ((successor v c).imp ((existsLift w r a c u v)))))).close

theorem source_liftExists {m} (w r a c u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftExistsSentence w r a c u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor v c) (Context.add (successor u a) (Context.add (indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor v c) := .hyp (Or.inl rfl)
  exact SyntaxIndexLift.exists_lift hZ w r a c u v h0 h1 h2 h3

theorem liftExists_kernel_certificate {m} (w r a c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftExistsSentence w r a c u v)) := TheoryTransport.sentence (source_liftExists w r a c u v)

theorem native_liftExists {m} (w r a c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftExistsSentence w r a c u v)) := ZFReplay.replay (liftExists_kernel_certificate w r a c u v)

def liftFiberSentence {m} (w r a c u v : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w r a c).imp ((successor u a).imp ((successor v c).imp ((liftFiber w r a c u v)))))).close

theorem source_liftFiber {m} (w r a c u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftFiberSentence w r a c u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor v c) (Context.add (successor u a) (Context.add (indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor v c) := .hyp (Or.inl rfl)
  exact SyntaxIndexLift.actual_fiber hZ w r a c u v h0 h1 h2 h3

theorem liftFiber_kernel_certificate {m} (w r a c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftFiberSentence w r a c u v)) := TheoryTransport.sentence (source_liftFiber w r a c u v)

theorem native_liftFiber {m} (w r a c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftFiberSentence w r a c u v)) := ZFReplay.replay (liftFiber_kernel_certificate w r a c u v)

def liftUniqueSentence {m} (w r a c u v g h : Fin m) : Source.Sentence := ((lifted w r a c u v g).imp ((lifted w r a c u v h).imp ((Formula.equal g h)))).close

theorem source_liftUnique {m} (w r a c u v g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftUniqueSentence w r a c u v g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (lifted w r a c u v h) (Context.add (lifted w r a c u v g) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (lifted w r a c u v h) := .hyp (Or.inl rfl)
  exact SyntaxIndexLift.unique hZ w r a c u v g h h0 h1

theorem liftUnique_kernel_certificate {m} (w r a c u v g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftUniqueSentence w r a c u v g h)) := TheoryTransport.sentence (source_liftUnique w r a c u v g h)

theorem native_liftUnique {m} (w r a c u v g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftUniqueSentence w r a c u v g h)) := ZFReplay.replay (liftUnique_kernel_certificate w r a c u v g h)

def liftEdgeSentence {m} (w r a c u v g i j : Fin m) : Source.Sentence := ((omega w).imp ((lifted w r a c u v g).imp (((edge g i j).iff (value r a i j))))).close

theorem source_liftEdge {m} (w r a c u v g i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftEdgeSentence w r a c u v g i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (lifted w r a c u v g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inl rfl)
  exact SyntaxIndexLift.edge_iff hZ w r a c u v g i j h0 h1

theorem liftEdge_kernel_certificate {m} (w r a c u v g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftEdgeSentence w r a c u v g i j)) := TheoryTransport.sentence (source_liftEdge w r a c u v g i j)

theorem native_liftEdge {m} (w r a c u v g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftEdgeSentence w r a c u v g i j)) := ZFReplay.replay (liftEdge_kernel_certificate w r a c u v g i j)

def liftAllSentence {m} (w r a c u v g : Fin m) : Source.Sentence := ((omega w).imp ((lifted w r a c u v g).imp ((SyntaxIndexLiftEdges.valueLaw r a g)))).close

theorem source_liftAll {m} (w r a c u v g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftAllSentence w r a c u v g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (lifted w r a c u v g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftEdges.all_edges hZ w r a c u v g h0 h1

theorem liftAll_kernel_certificate {m} (w r a c u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftAllSentence w r a c u v g)) := TheoryTransport.sentence (source_liftAll w r a c u v g)

theorem native_liftAll {m} (w r a c u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftAllSentence w r a c u v g)) := ZFReplay.replay (liftAll_kernel_certificate w r a c u v g)

def liftZeroSentence {m} (w r a c u v g z y : Fin m) : Source.Sentence := ((omega w).imp ((lifted w r a c u v g).imp ((empty z).imp (((edge g z y).iff (empty y)))))).close

theorem source_liftZero {m} (w r a c u v g z y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftZeroSentence w r a c u v g z y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (lifted w r a c u v g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftEdges.zero_iff hZ w r a c u v g z y h0 h1 h2

theorem liftZero_kernel_certificate {m} (w r a c u v g z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftZeroSentence w r a c u v g z y)) := TheoryTransport.sentence (source_liftZero w r a c u v g z y)

theorem native_liftZero {m} (w r a c u v g z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftZeroSentence w r a c u v g z y)) := ZFReplay.replay (liftZero_kernel_certificate w r a c u v g z y)

def liftSuccessorSentence {m} (w r a c u v g i j k l : Fin m) : Source.Sentence := ((omega w).imp ((lifted w r a c u v g).imp ((Formula.mem k a).imp ((successor i k).imp ((successor j l).imp (((edge g i j).iff (edge r k l)))))))).close

theorem source_liftSuccessor {m} (w r a c u v g i j k l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftSuccessorSentence w r a c u v g i j k l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j l) (Context.add (successor i k) (Context.add (Formula.mem k a) (Context.add (lifted w r a c u v g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem k a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor i k) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor j l) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftEdges.successor_iff hZ w r a c u v g i j k l h0 h1 h2 h3 h4

theorem liftSuccessor_kernel_certificate {m} (w r a c u v g i j k l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftSuccessorSentence w r a c u v g i j k l)) := TheoryTransport.sentence (source_liftSuccessor w r a c u v g i j k l)

theorem native_liftSuccessor {m} (w r a c u v g i j k l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftSuccessorSentence w r a c u v g i j k l)) := ZFReplay.replay (liftSuccessor_kernel_certificate w r a c u v g i j k l)

def mapsLiftedSentence {m} (w r s a b c d u v g : Fin m) : Source.Sentence := ((maps w r s a b c d).imp ((lifted w r a c u v g).imp ((maps w g s u b v d)))).close

theorem source_mapsLifted {m} (w r s a b c d u v g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapsLiftedSentence w r s a b c d u v g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (lifted w r a c u v g) (Context.add (maps w r s a b c d) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftTerms.maps_lifted w r s a b c d u v g h0 h1

theorem mapsLifted_kernel_certificate {m} (w r s a b c d u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapsLiftedSentence w r s a b c d u v g)) := TheoryTransport.sentence (source_mapsLifted w r s a b c d u v g)

theorem native_mapsLifted {m} (w r s a b c d u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapsLiftedSentence w r s a b c d u v g)) := ZFReplay.replay (mapsLifted_kernel_certificate w r s a b c d u v g)

def newBoundFixedSentence {m} (w r s a b c d u v g z n : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp ((lifted w r a c u v g).imp ((empty z).imp ((code true w z n).imp ((SyntaxRenameTermSyntax.renamed w g s u b v d n n))))))).close

theorem source_newBoundFixed {m} (w r s a b c d u v g z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (newBoundFixedSentence w r s a b c d u v g z n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code true w z n) (Context.add (empty z) (Context.add (lifted w r a c u v g) (Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (code true w z n) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftTerms.new_bound_fixed hZ w r s a b c d u v g z n h0 h1 h2 h3 h4

theorem newBoundFixed_kernel_certificate {m} (w r s a b c d u v g z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (newBoundFixedSentence w r s a b c d u v g z n)) := TheoryTransport.sentence (source_newBoundFixed w r s a b c d u v g z n)

theorem native_newBoundFixed {m} (w r s a b c d u v g z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (newBoundFixedSentence w r s a b c d u v g z n)) := ZFReplay.replay (newBoundFixed_kernel_certificate w r s a b c d u v g z n)

def oldBoundShiftedSentence {m} (w r s a b c d u v g i j k l n q : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp ((lifted w r a c u v g).imp ((Formula.mem k a).imp ((edge r k l).imp ((successor i k).imp ((successor j l).imp ((code true w i n).imp ((code true w j q).imp ((SyntaxRenameTermSyntax.renamed w g s u b v d n q))))))))))).close

theorem source_oldBoundShifted {m} (w r s a b c d u v g i j k l n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (oldBoundShiftedSentence w r s a b c d u v g i j k l n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code true w j q) (Context.add (code true w i n) (Context.add (successor j l) (Context.add (successor i k) (Context.add (edge r k l) (Context.add (Formula.mem k a) (Context.add (lifted w r a c u v g) (Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem k a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (edge r k l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (successor i k) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (successor j l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (code true w i n) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (code true w j q) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftTerms.old_bound_shifted hZ w r s a b c d u v g i j k l n q h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem oldBoundShifted_kernel_certificate {m} (w r s a b c d u v g i j k l n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (oldBoundShiftedSentence w r s a b c d u v g i j k l n q)) := TheoryTransport.sentence (source_oldBoundShifted w r s a b c d u v g i j k l n q)

theorem native_oldBoundShifted {m} (w r s a b c d u v g i j k l n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (oldBoundShiftedSentence w r s a b c d u v g i j k l n q)) := ZFReplay.replay (oldBoundShifted_kernel_certificate w r s a b c d u v g i j k l n q)

def freePreservedSentence {m} (w r s a b c d u v g i j n q : Fin m) : Source.Sentence := ((maps w r s a b c d).imp ((lifted w r a c u v g).imp ((Formula.mem i b).imp ((edge s i j).imp ((code false w i n).imp ((code false w j q).imp ((SyntaxRenameTermSyntax.renamed w g s u b v d n q)))))))).close

theorem source_freePreserved {m} (w r s a b c d u v g i j n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freePreservedSentence w r s a b c d u v g i j n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code false w j q) (Context.add (code false w i n) (Context.add (edge s i j) (Context.add (Formula.mem i b) (Context.add (lifted w r a c u v g) (Context.add (maps w r s a b c d) ((Source.SetLanguage.ZF.at m)))))))
  have h0 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (lifted w r a c u v g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem i b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (edge s i j) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (code false w i n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (code false w j q) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftTerms.free_preserved w r s a b c d u v g i j n q h0 h1 h2 h3 h4 h5

theorem freePreserved_kernel_certificate {m} (w r s a b c d u v g i j n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freePreservedSentence w r s a b c d u v g i j n q)) := TheoryTransport.sentence (source_freePreserved w r s a b c d u v g i j n q)

theorem native_freePreserved {m} (w r s a b c d u v g i j n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freePreservedSentence w r s a b c d u v g i j n q)) := ZFReplay.replay (freePreserved_kernel_certificate w r s a b c d u v g i j n q)

def liftSystemSentence {m} (w r a c : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w r a c).imp ((SyntaxIndexLiftSystem.system w r a c)))).close

theorem source_liftSystem {m} (w r a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftSystemSentence w r a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (indexMap w r a c) := .hyp (Or.inl rfl)
  exact SyntaxIndexLiftSystem.actual_system hZ w r a c h0 h1

theorem liftSystem_kernel_certificate {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftSystemSentence w r a c)) := TheoryTransport.sentence (source_liftSystem w r a c)

theorem native_liftSystem {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftSystemSentence w r a c)) := ZFReplay.replay (liftSystem_kernel_certificate w r a c)

end PPAC.Migration.Internal.ObjectSyntaxIndexLift
