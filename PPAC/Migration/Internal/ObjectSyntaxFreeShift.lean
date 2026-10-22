import PPAC.Migration.Internal.SyntaxFreeShiftFiber

/-! 原 free 头槽位移的全部内部图/码、实际唯一纤维和零槽排除的 YesMetaZFC 原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxFreeShift
open Source SourceAlgebra SourceLogic OmegaSyntax

def graphExistsSentence {m} (b : Fin m) : Source.Sentence := (Formula.ex (SyntaxFreeShiftSyntax.graph b.castSucc (Fin.last m))).close

theorem source_graphExists {m} (b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphExistsSentence b) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxFreeShiftGraph.exists_graph hZ b

theorem graphExists_kernel_certificate {m} (b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphExistsSentence b)) := TheoryTransport.sentence (source_graphExists b)

theorem native_graphExists {m} (b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphExistsSentence b)) := ZFReplay.replay (graphExists_kernel_certificate b)

def graphEdgesSentence {m} (b r i j : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.graph b r).imp ((GraphSyntax.edge r i j).iff ((Formula.mem i b).conj (successor j i)))).close

theorem source_graphEdges {m} (b r i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphEdgesSentence b r i j) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.graph b r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.graph b r) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftGraph.edge_iff b r i j h0

theorem graphEdges_kernel_certificate {m} (b r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphEdgesSentence b r i j)) := TheoryTransport.sentence (source_graphEdges b r i j)

theorem native_graphEdges {m} (b r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphEdgesSentence b r i j)) := ZFReplay.replay (graphEdges_kernel_certificate b r i j)

def graphUniqueSentence {m} (b r s : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.graph b r).imp ((SyntaxFreeShiftSyntax.graph b s).imp (Formula.equal r s))).close

theorem source_graphUnique {m} (b r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphUniqueSentence b r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.graph b s) (Context.add (SyntaxFreeShiftSyntax.graph b r) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.graph b r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.graph b s) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftGraph.unique_graph hZ b r s h0 h1

theorem graphUnique_kernel_certificate {m} (b r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphUniqueSentence b r s)) := TheoryTransport.sentence (source_graphUnique b r s)

theorem native_graphUnique {m} (b r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphUniqueSentence b r s)) := ZFReplay.replay (graphUnique_kernel_certificate b r s)

def mapExistsSentence {m} (w b B : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((successor B b).imp (SyntaxFreeShiftSyntax.existsMap w b B)))).close

theorem source_mapExists {m} (w b B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapExistsSentence w b B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftGraph.exists_map hZ w b B h0 h1 h2

theorem mapExists_kernel_certificate {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapExistsSentence w b B)) := TheoryTransport.sentence (source_mapExists w b B)

theorem native_mapExists {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapExistsSentence w b B)) := ZFReplay.replay (mapExists_kernel_certificate w b B)

def mapFiberSentence {m} (w b B : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((successor B b).imp (SyntaxFreeShiftSyntax.mapFiber w b B)))).close

theorem source_mapFiber {m} (w b B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapFiberSentence w b B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.actual_map_fiber hZ w b B h0 h1 h2

theorem mapFiber_kernel_certificate {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapFiberSentence w b B)) := TheoryTransport.sentence (source_mapFiber w b B)

theorem native_mapFiber {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapFiberSentence w b B)) := ZFReplay.replay (mapFiber_kernel_certificate w b B)

def mapUniqueSentence {m} (w b B r s : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftMap w b B r).imp ((SyntaxFreeShiftSyntax.shiftMap w b B s).imp (Formula.equal r s))).close

theorem source_mapUnique {m} (w b B r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapUniqueSentence w b B r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftMap w b B s) (Context.add (SyntaxFreeShiftSyntax.shiftMap w b B r) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w b B r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w b B s) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftGraph.unique_map hZ w b B r s h0 h1

theorem mapUnique_kernel_certificate {m} (w b B r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapUniqueSentence w b B r s)) := TheoryTransport.sentence (source_mapUnique w b B r s)

theorem native_mapUnique {m} (w b B r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapUniqueSentence w b B r s)) := ZFReplay.replay (mapUnique_kernel_certificate w b B r s)

def mapEdgesSentence {m} (w b B r i j : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftMap w b B r).imp ((GraphSyntax.edge r i j).iff ((Formula.mem i b).conj (successor j i)))).close

theorem source_mapEdges {m} (w b B r i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapEdgesSentence w b B r i j) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftMap w b B r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w b B r) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.map_edges w b B r i j h0

theorem mapEdges_kernel_certificate {m} (w b B r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapEdgesSentence w b B r i j)) := TheoryTransport.sentence (source_mapEdges w b B r i j)

theorem native_mapEdges {m} (w b B r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapEdgesSentence w b B r i j)) := ZFReplay.replay (mapEdges_kernel_certificate w b B r i j)

def codeExistsSentence {m} (w b B : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((successor B b).imp (SyntaxFreeShiftSyntax.existsCode w b B)))).close

theorem source_codeExists {m} (w b B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeExistsSentence w b B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftCode.exists_code hZ w b B h0 h1 h2

theorem codeExists_kernel_certificate {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeExistsSentence w b B)) := TheoryTransport.sentence (source_codeExists w b B)

theorem native_codeExists {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeExistsSentence w b B)) := ZFReplay.replay (codeExists_kernel_certificate w b B)

def codeMapSentence {m} (w b B S : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp (SyntaxMapCodeSyntax.mapCode w b B S)).close

theorem source_codeMap {m} (w b B S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeMapSentence w b B S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftCode.map_code w b B S h0

theorem codeMap_kernel_certificate {m} (w b B S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeMapSentence w b B S)) := TheoryTransport.sentence (source_codeMap w b B S)

theorem native_codeMap {m} (w b B S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeMapSentence w b B S)) := ZFReplay.replay (codeMap_kernel_certificate w b B S)

def codeNaturalSentence {m} (w b B S : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp (Formula.mem S w)).close

theorem source_codeNatural {m} (w b B S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeNaturalSentence w b B S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftCode.natural w b B S h0

theorem codeNatural_kernel_certificate {m} (w b B S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeNaturalSentence w b B S)) := TheoryTransport.sentence (source_codeNatural w b B S)

theorem native_codeNatural {m} (w b B S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeNaturalSentence w b B S)) := ZFReplay.replay (codeNatural_kernel_certificate w b B S)

def codeInputSentence {m} (w b B S : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((Formula.mem b w).conj (successor B b))).close

theorem source_codeInput {m} (w b B S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeInputSentence w b B S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftCode.input w b B S h0

theorem codeInput_kernel_certificate {m} (w b B S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeInputSentence w b B S)) := TheoryTransport.sentence (source_codeInput w b B S)

theorem native_codeInput {m} (w b B S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeInputSentence w b B S)) := ZFReplay.replay (codeInput_kernel_certificate w b B S)

def codeAtGraphSentence {m} (w b B S r : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r b B S).imp (SyntaxFreeShiftSyntax.shiftMap w b B r))).close

theorem source_codeAtGraph {m} (w b B S r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeAtGraphSentence w b B S r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w r b B S) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b B S) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftCode.at_graph hZ w b B S r h0 h1

theorem codeAtGraph_kernel_certificate {m} (w b B S r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeAtGraphSentence w b B S r)) := TheoryTransport.sentence (source_codeAtGraph w b B S r)

theorem native_codeAtGraph {m} (w b B S r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeAtGraphSentence w b B S r)) := ZFReplay.replay (codeAtGraph_kernel_certificate w b B S r)

def codeEncodedIffSentence {m} (w b B S r : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r b B S).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).iff (SyntaxFreeShiftSyntax.shiftMap w b B r))).close

theorem source_codeEncodedIff {m} (w b B S r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeEncodedIffSentence w b B S r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w r b B S) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b B S) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftCode.encoded_iff hZ w b B S r h0

theorem codeEncodedIff_kernel_certificate {m} (w b B S r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeEncodedIffSentence w b B S r)) := TheoryTransport.sentence (source_codeEncodedIff w b B S r)

theorem native_codeEncodedIff {m} (w b B S r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeEncodedIffSentence w b B S r)) := ZFReplay.replay (codeEncodedIff_kernel_certificate w b B S r)

def codeUniqueSentence {m} (w b B S T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxFreeShiftSyntax.shiftCode w b B T).imp (Formula.equal S T)))).close

theorem source_codeUnique {m} (w b B S T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeUniqueSentence w b B S T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftCode w b B T) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B T) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftCode.unique hZ w b B S T h0 h1 h2

theorem codeUnique_kernel_certificate {m} (w b B S T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeUniqueSentence w b B S T)) := TheoryTransport.sentence (source_codeUnique w b B S T)

theorem native_codeUnique {m} (w b B S T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeUniqueSentence w b B S T)) := ZFReplay.replay (codeUnique_kernel_certificate w b B S T)

def codeFiberSentence {m} (w b B : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((successor B b).imp (SyntaxFreeShiftSyntax.codeFiber w b B)))).close

theorem source_codeFiber {m} (w b B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeFiberSentence w b B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.actual_code_fiber hZ w b B h0 h1 h2

theorem codeFiber_kernel_certificate {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFiberSentence w b B)) := TheoryTransport.sentence (source_codeFiber w b B)

theorem native_codeFiber {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFiberSentence w b B)) := ZFReplay.replay (codeFiber_kernel_certificate w b B)

def codeInputIffSentence {m} (w b B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.existsCode w b B).iff ((Formula.mem b w).conj (successor B b)))).close

theorem source_codeInputIff {m} (w b B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeInputIffSentence w b B) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.exists_iff_input hZ w b B h0

theorem codeInputIff_kernel_certificate {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeInputIffSentence w b B)) := TheoryTransport.sentence (source_codeInputIff w b B)

theorem native_codeInputIff {m} (w b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeInputIffSentence w b B)) := ZFReplay.replay (codeInputIff_kernel_certificate w b B)

def actualStateSentence {m} (w b : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp (SyntaxFreeShiftSyntax.actualState w b))).close

theorem source_actualState {m} (w b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualStateSentence w b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.actual_state hZ w b h0 h1

theorem actualState_kernel_certificate {m} (w b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualStateSentence w b)) := TheoryTransport.sentence (source_actualState w b)

theorem native_actualState {m} (w b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualStateSentence w b)) := ZFReplay.replay (actualState_kernel_certificate w b)

def zeroStateSentence {m} (w z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (SyntaxFreeShiftSyntax.actualState w z))).close

theorem source_zeroState {m} (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroStateSentence w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.zero_state hZ w z h0 h1

theorem zeroState_kernel_certificate {m} (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroStateSentence w z)) := TheoryTransport.sentence (source_zeroState w z)

theorem native_zeroState {m} (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroStateSentence w z)) := ZFReplay.replay (zeroState_kernel_certificate w z)

def codedEdgesSentence {m} (w b B S r i j : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r b B S).imp ((GraphSyntax.edge r i j).iff ((Formula.mem i b).conj (successor j i))))).close

theorem source_codedEdges {m} (w b B S r i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codedEdgesSentence w b B S r i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w r b B S) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b B S) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.coded_edges hZ w b B S r i j h0 h1

theorem codedEdges_kernel_certificate {m} (w b B S r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codedEdgesSentence w b B S r i j)) := TheoryTransport.sentence (source_codedEdges w b B S r i j)

theorem native_codedEdges {m} (w b B S r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codedEdgesSentence w b B S r i j)) := ZFReplay.replay (codedEdges_kernel_certificate w b B S r i j)

def freshAbsentSentence {m} (w b B r i z : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftMap w b B r).imp ((empty z).imp ((GraphSyntax.edge r i z).neg))).close

theorem source_freshAbsent {m} (w b B r i z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freshAbsentSentence w b B r i z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (SyntaxFreeShiftSyntax.shiftMap w b B r) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w b B r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.fresh_absent w b B r i z h0 h1

theorem freshAbsent_kernel_certificate {m} (w b B r i z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freshAbsentSentence w b B r i z)) := TheoryTransport.sentence (source_freshAbsent w b B r i z)

theorem native_freshAbsent {m} (w b B r i z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freshAbsentSentence w b B r i z)) := ZFReplay.replay (freshAbsent_kernel_certificate w b B r i z)

def emptySourceSentence {m} (w b B r i j : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftMap w b B r).imp ((empty b).imp ((GraphSyntax.edge r i j).neg))).close

theorem source_emptySource {m} (w b B r i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (emptySourceSentence w b B r i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty b) (Context.add (SyntaxFreeShiftSyntax.shiftMap w b B r) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w b B r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty b) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.empty_source w b B r i j h0 h1

theorem emptySource_kernel_certificate {m} (w b B r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (emptySourceSentence w b B r i j)) := TheoryTransport.sentence (source_emptySource w b B r i j)

theorem native_emptySource {m} (w b B r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (emptySourceSentence w b B r i j)) := ZFReplay.replay (emptySource_kernel_certificate w b B r i j)

def emptyGraphSentence {m} (w b B r : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftMap w b B r).imp ((empty b).imp (empty r))).close

theorem source_emptyGraph {m} (w b B r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (emptyGraphSentence w b B r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty b) (Context.add (SyntaxFreeShiftSyntax.shiftMap w b B r) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w b B r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty b) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.empty_graph w b B r h0 h1

theorem emptyGraph_kernel_certificate {m} (w b B r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (emptyGraphSentence w b B r)) := TheoryTransport.sentence (source_emptyGraph w b B r)

theorem native_emptyGraph {m} (w b B r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (emptyGraphSentence w b B r)) := ZFReplay.replay (emptyGraph_kernel_certificate w b B r)

def rangeUniqueSentence {m} (w b B C S T : Fin m) : Source.Sentence := ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxFreeShiftSyntax.shiftCode w b C T).imp (Formula.equal B C))).close

theorem source_rangeUnique {m} (w b B C S T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rangeUniqueSentence w b B C S T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftCode w b C T) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b C T) := .hyp (Or.inl rfl)
  exact SyntaxFreeShiftFiber.range_unique hZ w b B C S T h0 h1

theorem rangeUnique_kernel_certificate {m} (w b B C S T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rangeUniqueSentence w b B C S T)) := TheoryTransport.sentence (source_rangeUnique w b B C S T)

theorem native_rangeUnique {m} (w b B C S T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rangeUniqueSentence w b B C S T)) := ZFReplay.replay (rangeUnique_kernel_certificate w b B C S T)

end PPAC.Migration.Internal.ObjectSyntaxFreeShift
