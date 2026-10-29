/- Pinned CodeLinks.tailGroup/root_le_tailGroup/tailGroup_supported and
ConcreteSystem.Chain.tailFixer/fixes_mem_stabilizer. The full internal set of
coordinate permutations is separated; root and component conditions are proved. -/
import PPAC.Migration.ForcingTailCovariance
import PPAC.Migration.ForcingCohenRankConsumers

namespace PPAC.Migration.ForcingTailGroup
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection Small)
open ForcingConditionGraphs (Permutation CompositionGraph InverseGraph)
open ForcingLabelPermutations (Fixes Fixing)
open ForcingSupportedNames (Range)
open ForcingTailCovariance (TailFixes)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedCommon)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def TailGroup (w D G chain group : M.Carrier .set) : Prop :=
  ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi group ↔
    (Project.FirstOrderSemantics.reduct M).mem pi G ∧ TailFixes w D pi chain

def tailGroup {m : Nat} (w D G chain group : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound group.succ))
    (.conj (.mem (.bound 0) (.bound G.succ)) (ForcingTailCovariance.tailFixes w.succ D.succ 0 chain.succ)))

theorem tailGroup_freeClosed {m : Nat} (w D G chain group : Fin m) :
    (tailGroup w D G chain group).FreeClosed := by
  simp -implicitDefEqProofs [tailGroup,Definitional.Formula.FreeClosed,ForcingTailCovariance.tailFixes_freeClosed]

theorem tailGroup_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D G chain group : Fin m) :
    Project.Formula.satisfies env (tailGroup w D G chain group) ↔
      TailGroup (env.bound w) (env.bound D) (env.bound G) (env.bound chain) (env.bound group) := by
  simp only [tailGroup,TailGroup,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ForcingTailCovariance.tailFixes_semantics hM]
  rfl

theorem exists_tailGroup (hM : FirstOrder.Theory.Models M nativeZF) (w D G chain : M.Carrier .set) :
    ∃ group, TailGroup (M := M) w D G chain group := by
  let schema : Project.UnarySchema 3 := {
    body := ForcingTailCovariance.tailFixes 1 2 0 3
    freeClosed := ForcingTailCovariance.tailFixes_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases w (Fin.cases D (fun _ => chain)), free := fun _ => D }
  have he pi : schema.denote env pi ↔ TailFixes w D pi chain :=
    ForcingTailCovariance.tailFixes_semantics hM (env.push pi) 1 2 0 3
  obtain ⟨group,hgroup⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env G
  exact ⟨group,fun pi => (hgroup pi).trans (and_congr Iff.rfl (he pi))⟩

theorem range_subset {D I r A : M.Carrier .set} (hr : Injection D I r) (hA : Range D r A) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset A I := by
  intro x hx
  obtain ⟨a,_,hax⟩ := (hA x).mp hx
  exact hr.1.2 a x hax

theorem root_vertex {w D I mul q zero root vertices chain r a U : M.Carrier .set}
    (hChain : Chain w D I mul q zero root vertices chain) (hCode : Code root r a U) :
    ConstructionComponentVertices.Vertex D I mul q r a U := by
  obtain ⟨r',a',U',s,b,V,hRoot,_,hr,_⟩ := hChain.2.2.2.1 zero root hChain.2.1
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hCode
  exact hr

theorem fixes_later {w D I mul q zero root vertices chain pi N i vN v rN aN UN r a U AN A : M.Carrier .set}
    (hChain : Chain w D I mul q zero root vertices chain) (hNi : NatLe N i)
    (hN : PureKuratowski.PairMember M N vN chain) (hi : PureKuratowski.PairMember M i v chain)
    (hCodeN : Code vN rN aN UN) (hCode : Code v r a U)
    (hAN : Range D rN AN) (hA : Range D r A) (hFix : Fixes AN pi) : Fixes A pi := by
  obtain ⟨n,rN',aN',UN',r',a',U',hCodeN',hCode',hrN,_,hArrow⟩ := hChain.2.2.1 N i vN v hNi hN hi
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCodeN' hCodeN
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode' hCode
  exact fun x hx => hFix x ((hAN x).mpr (ConstructionDescentPlacement.range_antitone
    ⟨n,hrN.2.2.1 n hArrow.1,hArrow.2.1⟩ ((hA x).mp hx)))

theorem tail_inverse {w D pi inv chain : M.Carrier .set}
    (hi : InverseGraph pi inv) (h : TailFixes w D pi chain) : TailFixes w D inv chain := by
  obtain ⟨N,v,r,a,U,A,hN,hv,hCode,hA,hFix⟩ := h
  exact ⟨N,v,r,a,U,A,hN,hv,hCode,hA,ForcingLabelPermutations.fixes_inverse hi hFix⟩

theorem tail_composition (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi sigma product : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w D I mul q zero root vertices chain) (hsigma : Permutation I sigma)
    (hc : CompositionGraph I pi sigma product) (hp : TailFixes w D pi chain) (hs : TailFixes w D sigma chain) :
    TailFixes w D product chain := by
  obtain ⟨N,vN,rN,aN,UN,AN,hN,hvN,hCodeN,hAN,hpi⟩ := hp
  obtain ⟨i,v,r,a,U,A,hi,hv,hCode,hA,hs⟩ := hs
  rcases ConstructionFractionOrder.nat_compare hM hw hN hi with hEq | hNi | hiN
  · exact ⟨i,v,r,a,U,A,hi,hv,hCode,hA,ForcingLabelPermutations.fixes_composition hsigma.1.1 hc
      (fixes_later hChain (Or.inl hEq) hvN hv hCodeN hCode hAN hA hpi) hs⟩
  · exact ⟨i,v,r,a,U,A,hi,hv,hCode,hA,ForcingLabelPermutations.fixes_composition hsigma.1.1 hc
      (fixes_later hChain (Or.inr hNi) hvN hv hCodeN hCode hAN hA hpi) hs⟩
  · exact ⟨N,vN,rN,aN,UN,AN,hN,hvN,hCodeN,hAN,ForcingLabelPermutations.fixes_composition hsigma.1.1 hc
      hpi (fixes_later hChain (Or.inr hiN) hv hvN hCode hCodeN hA hAN hs)⟩

theorem root_le_tailGroup {w D I mul q zero root vertices chain G group r a U A fixing : M.Carrier .set}
    (hChain : Chain w D I mul q zero root vertices chain) (hCode : Code root r a U)
    (hA : Range D r A) (hFixing : Fixing G A fixing) (hGroup : TailGroup w D G chain group) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset fixing group := by
  intro pi hpi
  obtain ⟨hpiG,hFix⟩ := (hFixing pi).mp hpi
  exact (hGroup pi).mpr ⟨hpiG,zero,root,r,a,U,A,
    ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1,hChain.2.1,hCode,hA,hFix⟩

theorem subgroup (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain G group r a U A : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w D I mul q zero root vertices chain) (hCode : Code root r a U)
    (hA : Range D r A) (hG : ForcingLabelPermutations.Carrier I G)
    (hGroup : TailGroup w D G chain group) : ForcingConjugationGraph.Subgroup I G group := by
  have hAI := range_subset (root_vertex hChain hCode).1 hA
  refine ⟨fun pi hpi => ((hGroup pi).mp hpi).1,?_,?_,?_⟩
  · obtain ⟨one,hone,hid⟩ := ForcingLabelPermutations.identity_mem hM hG
    exact ⟨one,(hGroup one).mpr ⟨hone,zero,root,r,a,U,A,
      ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1,hChain.2.1,hCode,hA,
      ForcingLabelPermutations.fixes_identity hAI hid⟩,hid⟩
  · intro pi hpi
    obtain ⟨hpiG,hTail⟩ := (hGroup pi).mp hpi
    obtain ⟨inv,hinv,hInv⟩ := ForcingLabelPermutations.inverse_mem hM hG hpiG
    exact ⟨inv,(hGroup inv).mpr ⟨hinv,tail_inverse hInv hTail⟩,hInv⟩
  · intro pi sigma hpi hsigma
    obtain ⟨hpiG,hpi⟩ := (hGroup pi).mp hpi
    obtain ⟨hsigmaG,hsigma⟩ := (hGroup sigma).mp hsigma
    obtain ⟨product,hproduct,hcomp⟩ := ForcingLabelPermutations.composition_mem hM hG hpiG hsigmaG
    exact ⟨product,(hGroup product).mpr ⟨hproduct,tail_composition hM hw hChain ((hG sigma).mp hsigmaG) hcomp hpi hsigma⟩,hcomp⟩

/-- Discharge the root-group and component-stabilizer fields of the source map. -/
theorem fixes_mem_stabilizer (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain pi J : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hq : Injection D I q) (hJ : Range D q J) (hp : Permutation I pi)
    (hChain : Chain w D I mul q zero root vertices chain) (hTail : TailFixes w D pi chain) :
    CompositionGraph D pi q q ∧ ∃ rootT, ForcingComponentMove.Move D I mul q pi root rootT ∧
      EncodedCommon D I mul q root rootT := by
  obtain ⟨N,v,r,a,U,A,_,hNv,hCode,hA,hFix⟩ := hTail
  have hCommon := hChain.2.2.2.1 N v hNv
  obtain ⟨r0,a0,U0,r',a',U',hRoot,hCode',hr0,hr,_⟩ := hChain.2.2.2.1 N v hNv
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode' hCode
  have hFixQ : Fixes J pi := fun x hx => hFix x ((hA x).mpr
    (ConstructionDescentPlacement.range_antitone ⟨a',hr.2.2.2.1,hr.2.1⟩ ((hJ x).mp hx)))
  have hqFixed := ForcingComponentMove.root_fixed hp hq hJ hFixQ
  obtain ⟨rootT,hMove⟩ := ForcingComponentMove.exists_move hM hp hqFixed ⟨r0,a0,U0,hRoot,hr0⟩
  have hSelf : ForcingComponentMove.Move D I mul q pi v v :=
    ⟨r',a',U',r',hCode',hCode',hr,hr,ForcingComponentMove.root_fixed hp hr.1 hA hFix⟩
  have hMoved := ForcingComponentMove.move_common hM hp hqFixed hMove hSelf hCommon
  exact ⟨hqFixed,rootT,hMove,(ForcingComponentRebase.common_iff hM hm hJoins hCommon).mpr
    (ForcingComponentRebase.common_symm hMoved)⟩

theorem tailGroup_mem (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain G group J pi : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hq : Injection D I q) (hJ : Range D q J) (hG : ForcingLabelPermutations.Carrier I G)
    (hChain : Chain w D I mul q zero root vertices chain) (hGroup : TailGroup w D G chain group) :
    (Project.FirstOrderSemantics.reduct M).mem pi group ↔
      (Project.FirstOrderSemantics.reduct M).mem pi G ∧ CompositionGraph D pi q q ∧
        (∃ rootT, ForcingComponentMove.Move D I mul q pi root rootT ∧ EncodedCommon D I mul q root rootT) ∧
          TailFixes w D pi chain := by
  constructor
  · intro hpi
    obtain ⟨hpiG,hTail⟩ := (hGroup pi).mp hpi
    have h := fixes_mem_stabilizer hM hm hJoins hq hJ ((hG pi).mp hpiG) hChain hTail
    exact ⟨hpiG,h.1,h.2,hTail⟩
  · exact fun ⟨hpiG,_,_,hTail⟩ => (hGroup pi).mpr ⟨hpiG,hTail⟩


theorem tailGroup_supported (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain G F mu r a U : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsOrdinal mu) (hD : Small D mu)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hChain : Chain w D I mul q zero root vertices chain) (hCode : Code root r a U)
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingSupportFilter.Filter I G mu F) :
    ∃ group A fixing, TailGroup w D G chain group ∧ Range D r A ∧ Fixing G A fixing ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset fixing group ∧
      ForcingConjugationGraph.Subgroup I G group ∧ (Project.FirstOrderSemantics.reduct M).mem group F ∧
      ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi group → CompositionGraph D pi q q ∧
        ∃ rootT, ForcingComponentMove.Move D I mul q pi root rootT ∧ EncodedCommon D I mul q root rootT := by
  obtain ⟨A,hA,hAI,hSmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu (root_vertex hChain hCode).1 hD
  obtain ⟨J,hJ,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu hq hD
  obtain ⟨fixing,hfixing⟩ := ForcingLabelPermutations.exists_fixing hM G A
  obtain ⟨group,hGroup⟩ := exists_tailGroup hM w D G chain
  have hSub := root_le_tailGroup hChain hCode hA hfixing hGroup
  have hSubgroup := subgroup hM hw hChain hCode hA hG hGroup
  refine ⟨group,A,fixing,hGroup,hA,hfixing,hSub,hSubgroup,
    (hF group).mpr ⟨hSubgroup,A,fixing,hAI,hSmall,hfixing,hSub⟩,?_⟩
  intro pi hpi
  have h := (tailGroup_mem hM hm hJoins hq hJ hG hChain hGroup).mp hpi
  exact ⟨h.2.1,h.2.2.1⟩

def stabilizes {m : Nat} (D I mul q root group : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound group.succ)) (.conj
    (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ 0 q.succ q.succ))
    (.existsE (.conj (ForcingComponentMove.move D.succ.succ I.succ.succ mul.succ.succ q.succ.succ 1 root.succ.succ 0)
      (ConstructionComponentCofinal.encodedCommon D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ 0)))))

theorem stabilizes_freeClosed {m : Nat} (D I mul q root group : Fin m) :
    (stabilizes D I mul q root group).FreeClosed := by
  simp -implicitDefEqProofs [stabilizes,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem stabilizes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q root group : Fin m) :
    Project.Formula.satisfies env (stabilizes D I mul q root group) ↔
      ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi (env.bound group) →
        CompositionGraph (env.bound D) pi (env.bound q) (env.bound q) ∧
          ∃ rootT, ForcingComponentMove.Move (env.bound D) (env.bound I) (env.bound mul) (env.bound q) pi (env.bound root) rootT ∧
            EncodedCommon (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) rootT := by
  simp only [stabilizes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,Project.Term.eval_bound]
  rfl

def constructionSentence {m : Nat} (w D I mul unit q zero root vertices chain G F mu r a U : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isOrdinal (.bound mu)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small D mu))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I))
    (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r a U)
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.existsE (.existsE (.existsE (.conj
      (tailGroup w.succ.succ.succ D.succ.succ.succ G.succ.succ.succ chain.succ.succ.succ 2) (.conj
      (ProjectSyntax.encode id (ForcingSupportedNames.range D.succ.succ.succ r.succ.succ.succ 1)) (.conj
      (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G.succ.succ.succ 1 0)) (.conj
      (ProjectSyntax.encode id (Source.SetLanguage.subset 0 2)) (.conj
      (ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I.succ.succ.succ G.succ.succ.succ 2)) (.conj
      (.mem (.bound 2) (.bound F.succ.succ.succ))
      (stabilizes D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ root.succ.succ.succ 2))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isOrdinal,
      ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      tailGroup_freeClosed,stabilizes_freeClosed]

theorem construction_models {m : Nat} (w D I mul unit q zero root vertices chain G F mu r a U : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w D I mul unit q zero root vertices chain G F mu r a U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ConstructionComponentCarrier.code_semantics hM,ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),tailGroup_semantics hM,ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingConjugationGraph.subgroup_semantics (M := M),stabilizes_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hD hm hJoins hq hChain hCode hG hF =>
    tailGroup_supported hM hw hMu hD hm hJoins hq hChain hCode hG hF

theorem construction_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain G F mu r a U : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w D I mul unit q zero root vertices chain G F mu r a U)) :=
  ModelTransfer.derives (fun _ hM => construction_models w D I mul unit q zero root vertices chain G F mu r a U hM)

end PPAC.Migration.ForcingTailGroup
