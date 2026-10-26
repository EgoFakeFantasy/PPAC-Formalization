/- Pinned ProbeWords.Path.target/target_letter/target_act, on actual quotient letters. -/
import PPAC.Migration.ConstructionProbeAction

namespace PPAC.Migration.ConstructionProbeTarget
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionProbePath
open ConstructionProbeTransitions (Transition transition_closed product_closed)
open ConstructionProbeLetters
open ConstructionProbeAction (Act ActionTable representative projected_indices)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem transport_terminal {w D mul e zero a node F T i j x y ti tj z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hT : MapsTo w D T) (hTable : TableLaws w mul e zero a node F T)
    (hxy : Transition D mul F i j x y)
    (hti : PureKuratowski.PairMember M i ti T) (htj : PureKuratowski.PairMember M j tj T)
    (hz : Product mul x ti z) : Product mul y tj z := by
  obtain ⟨hx,f,hf,hxf⟩ := hxy
  obtain ⟨_,_,_,ni,nj,_,_,hfD,_⟩ := (hF i j f).mp hf
  have htjD := hT.2 j tj htj
  obtain ⟨v,_,hft⟩ := (hm.2.1 f hfD).1 tj htjD
  have hiv := hTable.2.2.2.2 i j f tj v hf htj hft
  have he := ForcingConditionGraphs.function_unique hT.1 hiv hti
  subst v
  exact (hm.2.2 x f tj y ti z hx hfD htjD hxf hft).mpr hz

def Target (D mul projection T c z : M.Carrier .set) : Prop := ∃ i x t,
  (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x c ∧
    PureKuratowski.PairMember M i t T ∧ Product mul x t z

theorem target_total {w D mul e F C L projection T c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives w D C)
    (hL : Letters w D mul F C L) (hp : Projection w D mul F C projection)
    (hT : MapsTo w D T) (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z D ∧ Target D mul projection T c z := by
  obtain ⟨i,x,hi,hx,hxc⟩ := representative hC hL hp hc
  obtain ⟨t,hit,_⟩ := hT.1.2 i hi
  obtain ⟨z,hz,hxt⟩ := (hm.2.1 x hx).1 t (hT.2 i t hit)
  exact ⟨z,hz,i,x,t,hx,hxc,hit,hxt⟩

theorem target_unique {w D mul e zero a node F projection T c z v : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hE : EqualityLaw w D mul F projection) (hT : MapsTo w D T)
    (hTable : TableLaws w mul e zero a node F T)
    (hz : Target D mul projection T c z) (hv : Target D mul projection T c v) : z = v := by
  obtain ⟨i,x,ti,_,hxc,hti,hxt⟩ := hz
  obtain ⟨j,y,tj,_,hyc,htj,hyt⟩ := hv
  obtain ⟨k,u,hk,hxu,hyu⟩ := (letter_eq_iff hE hxc hyc).mp rfl
  obtain ⟨tk,htk,_⟩ := hT.1.2 k hk
  have hutz := transport_terminal hm hF hT hTable hxu hti htk hxt
  have hutv := transport_terminal hm hF hT hTable hyu htj htk hyt
  exact (hm.2.1 u (transition_closed hm hF hxu)).2.1 tk z v (hT.2 k tk htk) hutz hutv

theorem target_letter_iff {w D mul e zero a node F C L projection T i x t c z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hp : MapsTo C L projection) (hE : EqualityLaw w D mul F projection)
    (hT : MapsTo w D T) (hTable : TableLaws w mul e zero a node F T)
    (hc : Product projection i x c) (ht : PureKuratowski.PairMember M i t T) :
    Target D mul projection T c z ↔ Product mul x t z := by
  have hx := (projected_indices hC hp hc).2
  constructor
  · intro hz
    obtain ⟨v,_,hxt⟩ := (hm.2.1 x hx).1 t (hT.2 i t ht)
    have he := target_unique hm hF hE hT hTable hz ⟨i,x,t,hx,hc,ht,hxt⟩
    exact he.symm ▸ hxt
  · exact fun hxt => ⟨i,x,t,hx,hc,ht,hxt⟩

theorem target_act {w D mul e zero a node F C L projection T b c d z bz : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hp : MapsTo C L projection) (hE : EqualityLaw w D mul F projection)
    (hT : MapsTo w D T) (hTable : TableLaws w mul e zero a node F T)
    (hact : Act D mul projection b c d) (hz : Target D mul projection T c z)
    (hbz : Product mul b z bz) : Target D mul projection T d bz := by
  obtain ⟨hb,i,x,bx,hx,hxc,hbx,hbxd⟩ := hact
  have hi := (projected_indices hC hp hxc).1
  obtain ⟨t,ht,_⟩ := hT.1.2 i hi
  have hxt := (target_letter_iff hm hF hC hp hE hT hTable hxc ht).mp hz
  exact ⟨i,bx,t,product_closed hm hb hx hbx,hbxd,ht,
    (hm.2.2 b x t bx z bz hb hx (hT.2 i t ht) hbx hxt).mpr hbz⟩

def target {m : Nat} (D mul projection T c z : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 1) (.bound D.succ.succ.succ))
    (.conj (ProjectSyntax.encode id (product projection.succ.succ.succ 2 1 c.succ.succ.succ))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge T.succ.succ.succ 2 0))
        (ProjectSyntax.encode id (product mul.succ.succ.succ 1 0 z.succ.succ.succ)))))))

theorem target_freeClosed {m : Nat} (D mul projection T c z : Fin m) : (target D mul projection T c z).FreeClosed := by
  simp -implicitDefEqProofs [target,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem target_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul projection T c z : Fin m) :
    Project.Formula.satisfies env (target D mul projection T c z) ↔
      Target (env.bound D) (env.bound mul) (env.bound projection) (env.bound T) (env.bound c) (env.bound z) := by
  simp only [target,Target,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def TargetGraph (D mul projection T K : M.Carrier .set) : Prop := ∀ c z,
  PureKuratowski.PairMember M c z K ↔ Target D mul projection T c z

theorem exists_target (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F C L projection T : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : MapsTo C L projection) (hProjection : Projection w D mul F C projection)
    (hE : EqualityLaw w D mul F projection) (hT : MapsTo w D T)
    (hTable : TableLaws w mul e zero a node F T) :
    ∃ K, MapsTo L D K ∧ TargetGraph D mul projection T K := by
  let schema : Project.BinarySchema 4 := { body := target 2 3 4 5 1 0, freeClosed := target_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 :=
    { bound := Fin.cases D (Fin.cases mul (Fin.cases projection (fun _ => T))), free := fun _ => D }
  have he : ∀ c z, schema.denote env c z ↔ Target D mul projection T c z :=
    fun c z => target_semantics hM ((env.push c).push z) 2 3 4 5 1 0
  obtain ⟨K,hK,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := L) (target := D) (by
      intro c hc
      obtain ⟨z,_,hz⟩ := target_total hm hC hL hProjection hT hc
      exact ⟨z,(he c z).mpr hz⟩) (by
      intro c _ z v hz hv
      exact target_unique hm hF hE hT hTable ((he c z).mp hz) ((he c v).mp hv)) (by
      intro c z _ hz
      obtain ⟨i,x,t,hx,_,ht,hxt⟩ := (he c z).mp hz
      exact product_closed hm hx (hT.2 i t ht) hxt)
  refine ⟨K,(ForcingSupportSize.native_mapsTo hM L D K).mpr hK,fun c z => ?_⟩
  refine (hgraph c z).trans ⟨fun h => (he c z).mp h.2,fun h => ?_⟩
  have hcopy := h
  obtain ⟨i,x,_,_,hxc,_,_⟩ := hcopy
  exact ⟨ConstructionProbeAction.projected_range hp hxc,(he c z).mpr h⟩

def TargetLaws (mul projection T A K : M.Carrier .set) : Prop :=
  (∀ i x t c z, Product projection i x c → PureKuratowski.PairMember M i t T →
    (PureKuratowski.PairMember M c z K ↔ Product mul x t z)) ∧
  (∀ b c d z bz, Product A b c d → PureKuratowski.PairMember M c z K →
    Product mul b z bz → PureKuratowski.PairMember M d bz K)

theorem target_laws {w D mul e zero a node F C L projection T A K : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hp : MapsTo C L projection) (hE : EqualityLaw w D mul F projection)
    (hT : MapsTo w D T) (hTable : TableLaws w mul e zero a node F T)
    (hA : ActionTable D mul projection A) (hK : TargetGraph D mul projection T K) : TargetLaws mul projection T A K := by
  exact ⟨fun i x t c z hc ht => (hK c z).trans (target_letter_iff hm hF hC hp hE hT hTable hc ht),
    fun b c d z bz hact hz hbz => (hK d bz).mpr
      (target_act hm hF hC hp hE hT hTable ((hA b c d).mp hact) ((hK c z).mp hz) hbz)⟩

def targetGraph {m : Nat} (D mul projection T K : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ 1 0)) (target
    D.succ.succ mul.succ.succ projection.succ.succ T.succ.succ 1 0))))

theorem targetGraph_freeClosed {m : Nat} (D mul projection T K : Fin m) : (targetGraph D mul projection T K).FreeClosed := by
  simp -implicitDefEqProofs [targetGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,target_freeClosed]

theorem targetGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul projection T K : Fin m) :
    Project.Formula.satisfies env (targetGraph D mul projection T K) ↔
      TargetGraph (env.bound D) (env.bound mul) (env.bound projection) (env.bound T) (env.bound K) := by
  simp only [targetGraph, TargetGraph, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    target_semantics hM]
  rfl

def targetLaws {m : Nat} (mul projection T A K : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (product
    projection.succ.succ.succ.succ.succ 4 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    T.succ.succ.succ.succ.succ 4 2)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
    K.succ.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id (product mul.succ.succ.succ.succ.succ 3 2
    0)))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (product
    A.succ.succ.succ.succ.succ 4 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    K.succ.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (product mul.succ.succ.succ.succ.succ 4 1
    0)) (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ.succ.succ 2 0)))))))))))

theorem targetLaws_freeClosed {m : Nat} (mul projection T A K : Fin m) : (targetLaws mul projection T A K).FreeClosed := by
  simp -implicitDefEqProofs [targetLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem targetLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (mul projection T A K : Fin m) :
    Project.Formula.satisfies env (targetLaws mul projection T A K) ↔
      TargetLaws (env.bound mul) (env.bound projection) (env.bound T) (env.bound A) (env.bound K) := by
  simp only [targetLaws, TargetLaws, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff, product_semantics (M := M)]
  rfl

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound 0)) (.imp (.forallE (.neg
    (.mem (.bound 0) (.bound 5)))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin
    7) 2 3)) (.imp (path (0 : Fin 7) 1 2 3 4 5 6) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.conj (factorTable (8 : Fin 15) 9 10 14 7) (.conj (terminalTable (8 : Fin 15) 9 10 14
    13 6) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 15) 8 9)) (.conj (representatives
    (8 : Fin 15) 9 5) (.conj (letters (8 : Fin 15) 9 10 7 5 4) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (3 : Fin 15) 5 4)) (.conj (projectionGraph (8 : Fin 15) 9 10 7 5 3) (.conj
    (equalityLaw (8 : Fin 15) 9 10 7 3) (.conj (representatives (9 : Fin 15) 4 2) (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (1 : Fin 15) 2 4)) (.conj (ConstructionProbeAction.actionTable (9 : Fin 15) 10
    3 1) (.conj (ConstructionProbeAction.actionLaws (10 : Fin 15) 11 4 1) (.conj
    (ConstructionProbeAction.letterActionLaw (9 : Fin 15) 10 3 1) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 15) 4 9)) (.conj (targetGraph (9 : Fin 15) 10 3 6 0) (targetLaws (10 :
    Fin 15) 3 6 1 0)))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    path_freeClosed,factorTable_freeClosed,terminalTable_freeClosed,representatives_freeClosed,letters_freeClosed,
    projectionGraph_freeClosed,equalityLaw_freeClosed,ConstructionProbeAction.actionTable_freeClosed,
    ConstructionProbeAction.actionLaws_freeClosed,ConstructionProbeAction.letterActionLaw_freeClosed,
    targetGraph_freeClosed,targetLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),path_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,factorTable_semantics hM,
    terminalTable_semantics hM,representatives_semantics hM,letters_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),projectionGraph_semantics hM,equalityLaw_semantics hM,
    ConstructionProbeAction.actionTable_semantics hM,ConstructionProbeAction.actionLaws_semantics hM,
    ConstructionProbeAction.letterActionLaw_semantics hM,targetGraph_semantics hM,targetLaws_semantics hM]
  intro hw hz hm hp
  obtain ⟨pairs,hpairs⟩ := exists_ordered_pairs hM (bound 0)
  obtain ⟨F,_,hF⟩ := exists_factor_table hM hm hp hpairs
  obtain ⟨T,hTm,hT⟩ := exists_terminal_table hM hm hp
  have hTable := table_laws hM hw hz hm hp hF hT
  have hLaws := ConstructionProbeTransitions.meets_laws hM hw hm hp hF hTable
  obtain ⟨C,hC⟩ := exists_representatives hM (bound 0) (bound 1)
  obtain ⟨L,hL⟩ := exists_letters hM (bound 0) (bound 1) (bound 2) F C
  obtain ⟨projection,hp,hProjection⟩ := exists_projection hM hL
  have hE := equality_law hM hC hLaws hProjection
  obtain ⟨I,A,hI,hA,hAction⟩ := ConstructionProbeAction.exists_action hM hm hF hC hL hp hProjection hE
  obtain ⟨K,hK,hTarget⟩ := exists_target hM hm hF hC hL hp hProjection hE hTm hTable
  exact ⟨F,T,C,L,projection,I,A,K,hF,hT,hTm,hC,hL,hp,hProjection,hE,hI,hA,hAction,
    ConstructionProbeAction.action_laws hM hm hF hC hL hp hProjection hE hAction,
    ConstructionProbeAction.letter_action_law hM hm hF hC hp hE hAction,hK,hTarget,
    target_laws hm hF hC hp hE hTm hTable hAction hTarget⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeTarget
