/- Pinned ConcreteSystem.Vertex.permute/Arrow.move/Common.move:285-325.
Use existing diagram permutation/Sub and the entire existing vertex carrier.
Root index and ideal are literally retained; no second geometry backend. -/
import PPAC.Migration.ForcingComponentGluing

namespace PPAC.Migration.ForcingComponentMove
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (CompositionGraph Permutation InverseGraph)
open ConstructionComponentCarrier (Code EncodedVertex)
open ConstructionComponentCofinal (EncodedArrow EncodedCommon)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Move (D I mul q pi v V : M.Carrier .set) : Prop := ∃ r a U R,
  Code v r a U ∧ Code V R a U ∧ ConstructionComponentVertices.Vertex D I mul q r a U ∧
    ConstructionComponentVertices.Vertex D I mul q R a U ∧ CompositionGraph D pi r R

theorem root_fixed {D I q A pi : M.Carrier .set} (hp : Permutation I pi)
    (hq : Injection D I q) (hA : ForcingSupportedNames.Range D q A)
    (hFix : ForcingLabelPermutations.Fixes A pi) : CompositionGraph D pi q q := by
  intro k x
  constructor
  · intro hkx
    have hk := ForcingConditionGraphs.function_input hq.1.1 hkx
    exact ⟨hk,x,hkx,hFix x ((hA x).mpr ⟨k,hk,hkx⟩)⟩
  · rintro ⟨hk,y,hky,hyx⟩
    have hyy := hFix y ((hA y).mpr ⟨k,hk,hky⟩)
    exact (ForcingConditionGraphs.function_unique hp.1.1 hyx hyy).symm ▸ hky

theorem exists_move (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q pi v : M.Carrier .set} (hp : Permutation I pi)
    (hFix : CompositionGraph D pi q q) (hv : EncodedVertex D I mul q v) :
    ∃ V, Move D I mul q pi v V := by
  obtain ⟨r,a,U,hv,hr⟩ := hv
  obtain ⟨R,hR,hComp⟩ := ForcingDiagramAction.exists_permute hM hp hr.1
  obtain ⟨V,hV⟩ := ConstructionComponentCarrier.code_total hM R a U
  exact ⟨V,r,a,U,R,hv,hV,hr,⟨hR,ForcingDiagramOrder.permute_sub hComp hFix hr.2.1,hr.2.2⟩,hComp⟩

theorem target_vertex {D I mul q pi v V : M.Carrier .set} (h : Move D I mul q pi v V) :
    EncodedVertex D I mul q V := by
  obtain ⟨_,a,U,R,_,hV,_,hR,_⟩ := h
  exact ⟨R,a,U,hV,hR⟩

theorem source_vertex {D I mul q pi v V : M.Carrier .set} (h : Move D I mul q pi v V) :
    EncodedVertex D I mul q v := by
  obtain ⟨r,a,U,_,hv,_,hr,_,_⟩ := h
  exact ⟨r,a,U,hv,hr⟩

theorem move_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q pi v V W : M.Carrier .set} (h : Move D I mul q pi v V) (k : Move D I mul q pi v W) : V = W := by
  obtain ⟨r,a,U,R,hv,hV,_,hR,hComp⟩ := h
  obtain ⟨s,b,T,S,hv',hW,_,hS,hComp'⟩ := k
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  have he := ForcingDiagramAction.unique hM hR.1 hS.1 hComp hComp'
  subst S
  exact ConstructionComponentCarrier.code_unique hM hV hW

theorem move_inverse {D I mul q pi inv v V : M.Carrier .set}
    (hp : Permutation I pi) (hi : InverseGraph pi inv) (h : Move D I mul q pi v V) :
    Move D I mul q inv V v := by
  obtain ⟨r,a,U,R,hv,hV,hr,hR,hComp⟩ := h
  exact ⟨R,a,U,r,hV,hv,hR,hr,ForcingDiagramCarrier.reverse hp hr.1 hi hComp⟩

theorem move_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q pi v w V : M.Carrier .set} (hp : Permutation I pi)
    (h : Move D I mul q pi v V) (k : Move D I mul q pi w V) : v = w := by
  obtain ⟨inv,_,hi⟩ := ForcingConditionGraphs.exists_inverse hM hp
  exact move_unique hM (move_inverse hp hi h) (move_inverse hp hi k)

theorem move_arrow {D I mul q pi v V w W n : M.Carrier .set}
    (hv : Move D I mul q pi v V) (hw : Move D I mul q pi w W)
    (h : EncodedArrow D I mul q v w n) : EncodedArrow D I mul q V W n := by
  obtain ⟨r,a,U,R,hv,hV,_,hR,hpR⟩ := hv
  obtain ⟨s,b,T,S,hw,hW,_,hS,hpS⟩ := hw
  obtain ⟨r',a',U',s',b',T',hv',hw',_,_,hArrow⟩ := h
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hw hw'
  exact ⟨R,a,U,S,b,T,hV,hW,hR,hS,hArrow.1,ForcingDiagramOrder.permute_sub hpR hpS hArrow.2.1,hArrow.2.2⟩

theorem move_common (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q pi v V w W : M.Carrier .set} (hp : Permutation I pi)
    (hFix : CompositionGraph D pi q q) (hv : Move D I mul q pi v V) (hw : Move D I mul q pi w W)
    (h : EncodedCommon D I mul q v w) : EncodedCommon D I mul q V W := by
  obtain ⟨r,a,U,s,b,T,hvC,hwC,hr,hs,t,c,Z,n,m,ht,hn,hm⟩ := h
  obtain ⟨z,hz⟩ := ConstructionComponentCarrier.code_total hM t c Z
  obtain ⟨z',hz'⟩ := exists_move hM hp hFix ⟨t,c,Z,hz,ht⟩
  exact ForcingComponentMatches.arrow_common
    (move_arrow hv hz' ⟨r,a,U,t,c,Z,hvC,hz,hr,ht,hn⟩)
    (move_arrow hw hz' ⟨s,b,T,t,c,Z,hwC,hz,hs,ht,hm⟩)

def Graph (D I mul q pi vertices graph : M.Carrier .set) : Prop := ∀ v V,
  PureKuratowski.PairMember M v V graph ↔ (Project.FirstOrderSemantics.reduct M).mem v vertices ∧ Move D I mul q pi v V


def move {m : Nat} (D I mul q pi v V : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionComponentCarrier.code v.succ.succ.succ.succ 3 2 1) (.conj (ConstructionComponentCarrier.code V.succ.succ.succ.succ 0 2 1) (.conj (ConstructionComponentVertices.vertex D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ 3 2 1) (.conj (ConstructionComponentVertices.vertex D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ 0 2 1) (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ pi.succ.succ.succ.succ 3 0))))))))))

theorem move_freeClosed {m : Nat} (D I mul q pi v V : Fin m) : (move D I mul q pi v V).FreeClosed := by
  simp -implicitDefEqProofs [move,Definitional.Formula.FreeClosed,ConstructionComponentCarrier.code_freeClosed,
    ConstructionComponentVertices.vertex_freeClosed,ProjectSyntax.freeClosed]

theorem move_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q pi v V : Fin m) :
    Project.Formula.satisfies env (move D I mul q pi v V) ↔
      Move (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound pi) (env.bound v) (env.bound V) := by
  simp only [move,Move,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionComponentCarrier.code_semantics hM,ConstructionComponentVertices.vertex_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.compositionGraph_semantics (M := M)]
  rfl

def graph {m : Nat} (D I mul q pi vertices g : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound vertices.succ.succ))
      (move D.succ.succ I.succ.succ mul.succ.succ q.succ.succ pi.succ.succ 1 0))))

theorem graph_freeClosed {m : Nat} (D I mul q pi vertices g : Fin m) : (graph D I mul q pi vertices g).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,move_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q pi vertices g : Fin m) :
    Project.Formula.satisfies env (graph D I mul q pi vertices g) ↔
      Graph (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound pi) (env.bound vertices) (env.bound g) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,move_semantics hM]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q pi vertices : M.Carrier .set} (hp : Permutation I pi) (hq : Injection D I q)
    (hFix : CompositionGraph D pi q q) (hVertices : ConstructionComponentCarrier.Carrier D I mul q vertices) :
    ∃ g, Permutation vertices g ∧ Graph D I mul q pi vertices g := by
  let schema : Project.BinarySchema 5 := { body := move 2 3 4 5 6 1 0, freeClosed := move_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (fun _ => pi)))), free := fun _ => vertices }
  have he v V : schema.denote env v V ↔ Move D I mul q pi v V := move_semantics hM ((env.push v).push V) 2 3 4 5 6 1 0
  have ht : ∀ v, (Project.FirstOrderSemantics.reduct M).mem v vertices → ∃ V, schema.denote env v V := by
    intro v hv
    obtain ⟨V,hV⟩ := exists_move hM hp hFix ((hVertices v).mp hv)
    exact ⟨V,(he v V).mpr hV⟩
  have hu : ∀ v V W, schema.denote env v V → schema.denote env v W → V = W :=
    fun v V W hV hW => move_unique hM ((he v V).mp hV) ((he v W).mp hW)
  obtain ⟨g,hg,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun v _ V W hV hW => hu v V W hV hW)
    (fun v V _ hV => (hVertices V).mpr (target_vertex ((he v V).mp hV)))
  have hGraph : Graph D I mul q pi vertices g := fun v V => (hEdge v V).trans (and_congr Iff.rfl (he v V))
  refine ⟨g,⟨(ForcingSupportSize.native_mapsTo hM vertices vertices g).mpr hg,?_,?_⟩,hGraph⟩
  · intro v w V hv hw
    exact move_injective hM hp ((hGraph v V).mp hv).2 ((hGraph w V).mp hw).2
  · intro V hV
    obtain ⟨inv,hInv,hi⟩ := ForcingConditionGraphs.exists_inverse hM hp
    have hInvFix := ForcingDiagramCarrier.reverse hp hq hi hFix
    obtain ⟨v,hv⟩ := exists_move hM hInv hInvFix ((hVertices V).mp hV)
    have hMove := move_inverse hInv (fun x y => (hi y x).symm) hv
    have hvMem := (hVertices v).mpr (source_vertex hMove)
    exact ⟨v,hvMem,(hGraph v V).mpr ⟨hvMem,hMove⟩⟩

def Laws (D I mul q pi : M.Carrier .set) : Prop := ∀ v V w W,
  Move D I mul q pi v V → Move D I mul q pi w W →
    (∀ n, EncodedArrow D I mul q v w n → EncodedArrow D I mul q V W n) ∧
    (EncodedCommon D I mul q v w → EncodedCommon D I mul q V W)

def laws {m : Nat} (D I mul q pi : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (move D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ pi.succ.succ.succ.succ 3 2) (.imp (move D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ pi.succ.succ.succ.succ 1 0) (.conj (.forallE (.imp (ConstructionComponentCofinal.encodedArrow D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 4 2 0) (ConstructionComponentCofinal.encodedArrow D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 3 1 0))) (.imp (ConstructionComponentCofinal.encodedCommon D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ 3 1) (ConstructionComponentCofinal.encodedCommon D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ 2 0)))))))))

theorem laws_freeClosed {m : Nat} (D I mul q pi : Fin m) : (laws D I mul q pi).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,move_freeClosed,
    ConstructionComponentCofinal.encodedArrow_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q pi : Fin m) :
    Project.Formula.satisfies env (laws D I mul q pi) ↔ Laws (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound pi) := by
  simp only [laws,Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    move_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM]
  rfl

def constructionSentence {k : Nat} (D I mul q A pi : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixes A pi))
      (.conj (laws D I mul q pi) (.existsE (.existsE
        (.conj (ConstructionComponentCarrier.carrier D.succ.succ I.succ.succ mul.succ.succ q.succ.succ 1)
          (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation 1 0))
            (graph D.succ.succ I.succ.succ mul.succ.succ q.succ.succ pi.succ.succ 1 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,laws_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,graph_freeClosed]

theorem construction_models {k : Nat} (D I mul q A pi : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul q A pi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence D I mul q A pi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixes_semantics (M := M),
    laws_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,graph_semantics hM]
  intro hp hq hA hFix
  have hf := root_fixed hp hq hA hFix
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM (bound D) (bound I) (bound mul) (bound q)
  obtain ⟨g,hg,hGraph⟩ := exists_graph hM hp hq hf hVertices
  exact ⟨fun _ _ _ _ hv hw => ⟨fun _ h => move_arrow hv hw h,fun h => move_common hM hp hf hv hw h⟩,
    vertices,g,hVertices,hg,hGraph⟩

theorem construction_kernel_certificate {k : Nat} (D I mul q A pi : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul q A pi)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul q A pi hM)

end PPAC.Migration.ForcingComponentMove
