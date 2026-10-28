/- Pinned ComponentGluing.Vertex.component_cofinal_chain:181-201.
Reuse the actual internal ideal cofinal sequence, unique contraction vertices,
and native definable function graphs. The final cofinality quantifies the
ENTIRE original component, including vertices not reached from the root. -/
import PPAC.Migration.ConstructionComponentCarrier
import PPAC.Migration.ConstructionProbeMappedPath
import PPAC.Migration.ConstructionRoundStepSyntax

namespace PPAC.Migration.ConstructionComponentCofinal
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionComponentVertices (Vertex Arrow Common)
open ConstructionComponentCarrier (Code Carrier)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- An actual contraction target, with its complete encoded vertex data. -/
def Step (D I mul q r U n v : M.Carrier .set) : Prop :=
  ∃ s b V, Code v s b V ∧ Vertex D I mul q s b V ∧ Arrow D mul r U s V n

def EncodedArrow (D I mul q v w n : M.Carrier .set) : Prop :=
  ∃ r a U s b V, Code v r a U ∧ Code w s b V ∧
    Vertex D I mul q r a U ∧ Vertex D I mul q s b V ∧ Arrow D mul r U s V n

def EncodedCommon (D I mul q v w : M.Carrier .set) : Prop :=
  ∃ r a U s b V, Code v r a U ∧ Code w s b V ∧
    Vertex D I mul q r a U ∧ Vertex D I mul q s b V ∧ Common D I mul q r U s V

def Contractions (D I mul q r U G : M.Carrier .set) : Prop := ∀ n v,
  PureKuratowski.PairMember M n v G ↔ (Project.FirstOrderSemantics.reduct M).mem n U ∧
    Step D I mul q r U n v

/-- No representative choice is hidden here: the diagram, right factor,
ideal and final triple code are all uniquely determined by n. -/
theorem step_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U n v w : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (h : Step D I mul q r U n v) (k : Step D I mul q r U n w) : v = w := by
  obtain ⟨s,b,V,hCode,hS,hA⟩ := h
  obtain ⟨t,c,W,hCode',hT,hB⟩ := k
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentVertices.contraction_unique hM hm hv hS hT hA hB
  exact ConstructionComponentCarrier.code_unique hM hCode hCode'

def step {m : Nat} (D I mul q r U n v : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ConstructionComponentCarrier.code v.succ.succ.succ (2 : Fin
  (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3))) (.conj (ConstructionComponentVertices.vertex
  D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ (2 : Fin (m+3)) (1 : Fin
  (m+3)) (0 : Fin (m+3))) (ConstructionComponentVertices.arrow D.succ.succ.succ mul.succ.succ.succ
  r.succ.succ.succ U.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3)) n.succ.succ.succ))))))

theorem step_freeClosed {m : Nat} (D I mul q r U n v : Fin m) :
    (step D I mul q r U n v).FreeClosed := by
  simp -implicitDefEqProofs [step,Definitional.Formula.FreeClosed,ConstructionComponentCarrier.code_freeClosed,ConstructionComponentVertices.vertex_freeClosed,ConstructionComponentVertices.arrow_freeClosed]

theorem step_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q r U n v : Fin m) :
    Project.Formula.satisfies env (step D I mul q r U n v) ↔ Step (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound r) (env.bound U) (env.bound n) (env.bound v) := by
  simp only [step,Step,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionComponentCarrier.code_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ConstructionComponentVertices.arrow_semantics hM]
  rfl

def encodedArrow {m : Nat} (D I mul q v w n : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionComponentCarrier.code v.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6))
  (3 : Fin (m+6))) (.conj (ConstructionComponentCarrier.code w.succ.succ.succ.succ.succ.succ (2 : Fin
  (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))) (.conj (ConstructionComponentVertices.vertex
  D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  q.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)) (3 : Fin (m+6))) (.conj
  (ConstructionComponentVertices.vertex D.succ.succ.succ.succ.succ.succ
  I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ (2
  : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))) (ConstructionComponentVertices.arrow
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin (m+6)) (2
  : Fin (m+6)) (0 : Fin (m+6)) n.succ.succ.succ.succ.succ.succ)))))))))))

theorem encodedArrow_freeClosed {m : Nat} (D I mul q v w n : Fin m) :
    (encodedArrow D I mul q v w n).FreeClosed := by
  simp -implicitDefEqProofs [encodedArrow,Definitional.Formula.FreeClosed,ConstructionComponentCarrier.code_freeClosed,ConstructionComponentVertices.vertex_freeClosed,ConstructionComponentVertices.arrow_freeClosed]

theorem encodedArrow_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q v w n : Fin m) :
    Project.Formula.satisfies env (encodedArrow D I mul q v w n) ↔ EncodedArrow (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound v) (env.bound w) (env.bound n) := by
  simp only [encodedArrow,EncodedArrow,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionComponentCarrier.code_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ConstructionComponentVertices.arrow_semantics hM]
  rfl

def encodedCommon {m : Nat} (D I mul q v w : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionComponentCarrier.code v.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6))
  (3 : Fin (m+6))) (.conj (ConstructionComponentCarrier.code w.succ.succ.succ.succ.succ.succ (2 : Fin
  (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))) (.conj (ConstructionComponentVertices.vertex
  D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  q.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)) (3 : Fin (m+6))) (.conj
  (ConstructionComponentVertices.vertex D.succ.succ.succ.succ.succ.succ
  I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ (2
  : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6))) (ConstructionComponentVertices.common
  D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  q.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin (m+6)) (2 : Fin (m+6)) (0 : Fin
  (m+6)))))))))))))

theorem encodedCommon_freeClosed {m : Nat} (D I mul q v w : Fin m) :
    (encodedCommon D I mul q v w).FreeClosed := by
  simp -implicitDefEqProofs [encodedCommon,Definitional.Formula.FreeClosed,ConstructionComponentCarrier.code_freeClosed,ConstructionComponentVertices.vertex_freeClosed,ConstructionComponentVertices.common_freeClosed]

theorem encodedCommon_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q v w : Fin m) :
    Project.Formula.satisfies env (encodedCommon D I mul q v w) ↔ EncodedCommon (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound v) (env.bound w) := by
  simp only [encodedCommon,EncodedCommon,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionComponentCarrier.code_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ConstructionComponentVertices.common_semantics hM]
  rfl


/-- Replacement constructs the unique contraction map on the full ideal. -/
theorem exists_contractions (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U X : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hX : Carrier D I mul q X) :
    ∃ G, MapsTo U X G ∧ Contractions D I mul q r U G := by
  let schema : Project.BinarySchema 6 := {
    body := step 2 3 4 5 6 7 1 0
    freeClosed := step_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases r (fun _ => U))))),
    free := fun _ => D }
  have he n v : schema.denote env n v ↔ Step D I mul q r U n v :=
    step_semantics hM ((env.push n).push v) 2 3 4 5 6 7 1 0
  obtain ⟨G,hG,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    schema env (source := U) (target := X) (by
      intro n hn
      obtain ⟨s,b,V,hS,hA⟩ := ConstructionComponentVertices.exists_contraction hM hm hv hn
      obtain ⟨v,hvcode⟩ := ConstructionComponentCarrier.code_total hM s b V
      exact ⟨v,(he n v).mpr ⟨s,b,V,hvcode,hS,hA⟩⟩) (by
      intro n _ v z hV hZ
      exact step_unique hM hm hv ((he n v).mp hV) ((he n z).mp hZ)) (by
      intro n v _ hV
      obtain ⟨s,b,V,hCode,hS,_⟩ := (he n v).mp hV
      exact (hX v).mpr ⟨s,b,V,hCode,hS⟩)
  exact ⟨G,(ForcingSupportSize.native_mapsTo hM U X G).mpr hG,
    fun n v => (hGraph n v).trans (and_congr_right (fun _ => he n v))⟩

/-- A chain is a function on every internal natural, with cofinality over
ALL vertices in the component of its first vertex. -/
def Chain (w D I mul q zero v X f : M.Carrier .set) : Prop :=
  MapsTo w X f ∧ PureKuratowski.PairMember M zero v f ∧
    (∀ i j x y, NatLe i j → PureKuratowski.PairMember M i x f →
      PureKuratowski.PairMember M j y f → ∃ n, EncodedArrow D I mul q x y n) ∧
    (∀ i x, PureKuratowski.PairMember M i x f → EncodedCommon D I mul q v x) ∧
    (∀ z, (Project.FirstOrderSemantics.reduct M).mem z X → EncodedCommon D I mul q v z →
      ∃ i x n, (Project.FirstOrderSemantics.reduct M).mem i w ∧
        PureKuratowski.PairMember M i x f ∧ EncodedArrow D I mul q z x n)

/-- Pinned source component_cofinal_chain. The sequence of ideal indices
comes from the existing internal cofinal-sequence proof. Its unique contraction
map is composed with it as an actual native set function. -/
theorem component_cofinal_chain (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D I mul e mark H C q r a U zero v X : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hTop : ConstructionRealCuts.Cut hM w Q top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hv : Vertex D I mul q r a U) (hCode : Code v r a U)
    (hX : Carrier D I mul q X)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) :
    ∃ f, Chain w D I mul q zero v X f := by
  have hm := hObj.1
  have heU := (ConstructionComponentVertices.identity hm hv).1
  obtain ⟨node,hNode,hZero,hMono,hCof⟩ := ConstructionIdealCofinal.directed_cofinal_sequence
    hM hChoice hw hQ hR hTop hObj
      (ConstructionIdealProbes.directed hm hObj.2.2.1 hv.2.2) hz heU
  obtain ⟨G,hG,hGraph⟩ := exists_contractions hM hm hv hX
  obtain ⟨f,hf,hMap⟩ := ConstructionProbeMappedPath.exists_node_map hM hNode hG
  have hEntry i x (hix : PureKuratowski.PairMember M i x f) :
      ∃ n, PureKuratowski.PairMember M i n node ∧ Step D I mul q r U n x := by
    obtain ⟨n,hin,hnx⟩ := (hMap i x).mp hix
    exact ⟨n,hin,((hGraph n x).mp hnx).2⟩
  refine ⟨f,hf,?_,?_,?_,?_⟩
  · exact (hMap zero v).mpr ⟨e,hZero,(hGraph e v).mpr
      ⟨heU,r,a,U,hCode,hv,ConstructionComponentVertices.identity hm hv⟩⟩
  · intro i j x y hij hix hjy
    obtain ⟨ni,hni,s,b,V,hx,hS,hA⟩ := hEntry i x hix
    obtain ⟨nj,hnj,t,c,W,hy,hT,hB⟩ := hEntry j y hjy
    have hle := hMono j (ForcingConditionGraphs.function_input hNode.1 hnj) i ni nj hij hni hnj
    obtain ⟨n,_,hArrow⟩ := ConstructionComponentVertices.between hM hm hv hS hT hA hB hle
    exact ⟨n,s,b,V,t,c,W,hx,hy,hS,hT,hArrow⟩
  · intro i x hix
    obtain ⟨n,_,s,b,V,hx,hS,hA⟩ := hEntry i x hix
    exact ⟨r,a,U,s,b,V,hCode,hx,hv,hS,ConstructionComponentVertices.common_of_arrow hm hS hA⟩
  · intro z _ hzCommon
    obtain ⟨r',a',U',s,b,V,hCode',hzCode,hv',hzVertex,hCommon⟩ := hzCommon
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode'
    obtain ⟨t,c,W,n,m,hT,hRoot,hZ⟩ := hCommon
    obtain ⟨i,ni,hi,hni,hle⟩ := hCof n hRoot.1
    obtain ⟨x,hnix,_⟩ := hG.1.2 ni (hNode.2 i ni hni)
    obtain ⟨p,d,P,hx,hP,hTarget⟩ := ((hGraph ni x).mp hnix).2
    obtain ⟨k,_,hTail⟩ := ConstructionComponentVertices.between hM hm hv hT hP hRoot hTarget hle
    obtain ⟨mk,_,hProduct⟩ :=
      (hm.2.1 m (hzVertex.2.2.1 m hZ.1)).1 k (hT.2.2.1 k hTail.1)
    exact ⟨i,x,mk,hi,(hMap i x).mpr ⟨ni,hni,hnix⟩,
      s,b,V,p,d,P,hzCode,hx,hzVertex,hP,
      ConstructionComponentVertices.compose hm hzVertex hT hZ hTail hProduct⟩

def chain {m : Nat} (w D I mul q zero v X f : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f w X)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f zero v)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp
  (ConstructionBaseCostBound.natLeF (3 : Fin (m+4)) (2 : Fin (m+4))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4))))
  (.existsE (encodedArrow D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ
  q.succ.succ.succ.succ.succ (2 : Fin (m+5)) (1 : Fin (m+5)) (0 : Fin (m+5))))))))))) (.conj (.forallE
  (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ (1 : Fin (m+2)) (0 : Fin
  (m+2)))) (encodedCommon D.succ.succ I.succ.succ mul.succ.succ q.succ.succ v.succ.succ (0 : Fin (m+2))))))
  (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound X.succ)) (.imp (encodedCommon D.succ I.succ
  mul.succ q.succ v.succ (0 : Fin (m+1))) (.existsE (.existsE (.existsE (.conj (.mem (.bound (2 : Fin
  (m+4))) (.bound w.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ (2 : Fin (m+4)) (1 : Fin (m+4)))) (encodedArrow D.succ.succ.succ.succ
  I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)) (0 :
  Fin (m+4)))))))))))))))

theorem chain_freeClosed {m : Nat} (w D I mul q zero v X f : Fin m) :
    (chain w D I mul q zero v X f).FreeClosed := by
  simp -implicitDefEqProofs [chain,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionBaseCostBound.natLeF_freeClosed,encodedArrow_freeClosed,encodedCommon_freeClosed]

theorem chain_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I mul q zero v X f : Fin m) :
    Project.Formula.satisfies env (chain w D I mul q zero v X f) ↔
      Chain (env.bound w) (env.bound D) (env.bound I) (env.bound mul) (env.bound q)
        (env.bound zero) (env.bound v) (env.bound X) (env.bound f) := by
  simp only [chain,Chain,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionBaseCostBound.natLeF_semantics hM,
    encodedArrow_semantics hM,encodedCommon_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula :=
    (Project.Formula.forallClosure 18 (.imp (Project.Formula.isOmega (.bound (0 : Fin 18))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 18) (1 : Fin 18)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 18) (1 : Fin 18) (2 : Fin 18)) (.imp (ConstructionRealCuts.cut (0 : Fin 18) (1 : Fin 18) (3 : Fin
    18)) (.imp (ConstructionRoundStepSyntax.objectFields (0 : Fin 18) (1 : Fin 18) (2 : Fin 18) (3 : Fin 18)
    (4 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (10 : Fin 18)) (.imp
    (ConstructionComponentVertices.vertex (4 : Fin 18) (5 : Fin 18) (6 : Fin 18) (11 : Fin 18) (12 : Fin 18)
    (13 : Fin 18) (14 : Fin 18)) (.imp (ConstructionComponentCarrier.code (16 : Fin 18) (12 : Fin 18) (13 :
    Fin 18) (14 : Fin 18)) (.imp (ConstructionComponentCarrier.carrier (4 : Fin 18) (5 : Fin 18) (6 : Fin
    18) (11 : Fin 18) (17 : Fin 18)) (.imp (Project.Formula.isEmpty (.bound (15 : Fin 18))) (.existsE (chain
    (0 : Fin 18).succ (4 : Fin 18).succ (5 : Fin 18).succ (6 : Fin 18).succ (11 : Fin 18).succ (15 : Fin
    18).succ (16 : Fin 18).succ (17 : Fin 18).succ (0 : Fin 19)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isEmpty,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionComponentVertices.vertex_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,
      chain_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionRealCuts.cut_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionComponentVertices.vertex_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,chain_semantics hM]
  exact fun hw hQ hR hTop hObj hv hCode hX hz =>
    component_cofinal_chain hM hChoice hw hQ hR hTop hObj hv hCode hX hz

/-- Choice is obtained inside the SAME L using the existing native-ZF
interpretation; the ambient background remains nativeZF. -/
theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

end PPAC.Migration.ConstructionComponentCofinal
