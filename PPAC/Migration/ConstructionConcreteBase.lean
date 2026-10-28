/- Pinned Base.object / Models.ConcreteSystem.T.
Retain the exact EXISTING Base graph producer's actual function certificate;
reuse all completed Base mathematics and canonical_uniform. No new arithmetic,
choice, graph or recursion backend. -/
import PPAC.Migration.ConstructionConcreteTower
import PPAC.Migration.ConstructionBaseUniformMarginSyntax

namespace PPAC.Migration.ConstructionConcreteBase
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBaseMonoid (AdditionGraph sumPair sumPair_semantics addition_unique)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

-- Exact existing producer body; only its returned function certificate is retained.
theorem addition_with_graph (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) : ∃ mul pairs, AdditionGraph hM w mul ∧
      (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) pairs w w ∧
      (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) mul pairs w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨pairs,hpairs⟩ := ZF.exists_cartesianProduct hZF I w w
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 :=
    { bound := fun _ => w, free := fun _ => w }
  obtain ⟨mul,hNative,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I sumPair env
    (source := pairs) (target := w) (by
      intro p hp
      obtain ⟨x,hx,y,hy,hp⟩ := (hpairs p).mp hp
      obtain ⟨z,hz,_⟩ := ZF.ordinalAddition_existsUnique hZF I x (hw.members_areOrdinals hZF y hy)
      exact ⟨z,(sumPair_semantics hM env p z).mpr ⟨x,hx,y,hy,hp,hz⟩⟩) (by
      intro p _ a b ha hb
      obtain ⟨x,hx,y,hy,hp,ha⟩ := (sumPair_semantics hM env p a).mp ha
      obtain ⟨x',_,y',_,hp',hb⟩ := (sumPair_semantics hM env p b).mp hb
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact addition_unique hM hw hy ha hb) (by
      intro p z _ hz
      obtain ⟨x,hx,y,hy,_,hz⟩ := (sumPair_semantics hM env p z).mp hz
      exact ZF.ordinalAddition_mem_omega hZF I hw hx hy hz)
  refine ⟨mul,pairs,?_,hpairs,hNative⟩
  intro x y z
  constructor
  · rintro ⟨p,hp,hpz⟩
    obtain ⟨x',hx,y',hy,hp',hz⟩ := (sumPair_semantics hM env p z).mp ((he p z).mp hpz).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    exact ⟨hx,hy,hz⟩
  · rintro ⟨hx,hy,hz⟩
    obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM x y
    exact ⟨p,hp,(he p z).mpr ⟨(hpairs p).mpr ⟨x,hx,y,hy,hp⟩,
      (sumPair_semantics hM env p z).mpr ⟨x,hx,y,hy,hp,hz⟩⟩⟩


def Base (hM : FirstOrder.Theory.Models M nativeZF)
    (w mul zero one two three Q R H C u top : M.Carrier .set) : Prop :=
  ConstructionBaseUniformMargin.Data hM w mul zero one two three Q R H C u top ∧
    ConstructionRoundFields.ObjectFields hM w Q R top w mul zero one H C

theorem exists_base (hM : FirstOrder.Theory.Models M nativeZF)
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ mul zero one two three Q R H C u top, Base hM w mul zero one two three Q R H C u top := by
  obtain ⟨oldMul,zero,one,two,three,Q,R,H,C,u,top,hData⟩ := ConstructionBaseUniformMargin.exists_base hM hw
  obtain ⟨_,hz,_,_,hne,_,hd,hQ,hR,hHG,hCG,hHM,hCM,hCoords,hPrincipal,hTopR,hHB,hCB,_,_,hMargin,_⟩ := hData
  obtain ⟨mul,pairs,hAdd,hPairs,hNative⟩ := addition_with_graph hM hw
  have hZeroW : (Project.FirstOrderSemantics.reduct M).mem zero w := by
    obtain ⟨z,hz',hzw⟩ := hw.1.1
    have he := (ModelTransfer.extensionality hM).eq_of_same_members z zero
      (fun x => iff_of_false (hz' x) (hz x))
    exact he ▸ hzw
  have hm := ConstructionBaseMonoid.leftCancelMonoid hM hw hAdd hz hZeroW
  have hc := ConstructionBaseMonoid.conical hM hw hAdd hz
  have hj := ConstructionBaseMonoid.joins hM hw hAdd
  have hUniform := ConstructionBaseUniformMargin.base_uniform hM hw hd hQ hR hAdd hHG hCG hHM
  have hBase : ConstructionBaseUniformMargin.Data hM w mul zero one two three Q R H C u top :=
    ⟨hAdd,hz,hm,hc,hne,hj,hd,hQ,hR,hHG,hCG,hHM,hCM,hCoords,hPrincipal,hTopR,hHB,hCB,
      ConstructionBaseUniformMargin.base_height_order hM hw hd hQ hAdd hHG hHM hHB,
      ConstructionBasePointBound.base_point_bound hM hw hd hQ hAdd hHG hCG,hMargin,hUniform⟩
  have hRep : ConstructionProbeLetters.Representatives w w pairs := by
    intro p
    exact ⟨fun h => by obtain ⟨x,hx,y,hy,hp⟩ := (hPairs p).mp h; exact ⟨x,y,hx,hy,hp⟩,
      fun ⟨x,y,hx,hy,hp⟩ => (hPairs p).mpr ⟨x,hx,y,hy,hp⟩⟩
  have hMaps := (ForcingSupportSize.native_mapsTo hM pairs w mul).mpr hNative
  refine ⟨mul,zero,one,two,three,Q,R,H,C,u,top,hBase,hm,hc,
    ConstructionProbeSharedIntersections.conditionalJoins_of_joins hj,hd.1,hne,hHM,hHB,hCM,
    (fun x cost hxc => ⟨(hCB x cost hxc).1,(hCB x cost hxc).2.1⟩),hUniform,?_,pairs,hRep,hMaps⟩
  intro x y hx hy hxh hyh hxy hnot
  exact ConstructionProbeCostSupremum.canonical_uniform hM hw hQ hR hCM
    ((hR hx).mp (hHM.2 x hx hxh)) (hUniform x y hx hy hxh hyh hxy hnot)

def TowerData (hM : FirstOrder.Theory.Models M nativeZF)
    (w mul zero one two three Q R H C u top P c mu kappa B : M.Carrier .set) : Prop :=
  Base hM w mul zero one two three Q R H C u top ∧
    ConstructionConcreteTower.Tower hM w Q R top w mul zero one H C zero one u P c mu kappa B

theorem exists_tower_data (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ mul zero one two three Q R H C u top P c mu kappa B,
      TowerData hM w mul zero one two three Q R H C u top P c mu kappa B := by
  obtain ⟨mul,zero,one,two,three,Q,R,H,C,u,top,hBase,hObj⟩ := exists_base hM hw
  have hCopy := hBase
  obtain ⟨_,hz,_,_,_,_,hd,hQ,hR,_,_,_,_,hCoordinates,hTop,_,_,_,_,_,_,_⟩ := hCopy
  have hZeroW : (Project.FirstOrderSemantics.reduct M).mem zero w := by
    obtain ⟨z,hz',hzw⟩ := hw.1.1
    have he := (ModelTransfer.extensionality hM).eq_of_same_members z zero
      (fun x => iff_of_false (hz' x) (hz x))
    exact he ▸ hzw
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) w
  have hCountable := (ForcingSupportSize.native_small hM w w).mpr ⟨id,hId.1⟩
  obtain ⟨P,c,mu,kappa,B,hTower⟩ := ConstructionConcreteTower.exists_tower hM hOrder hChoice
    hw hQ hR hCoordinates hd.2.2.2.1 hTop hObj hz hZeroW hCountable
  exact ⟨mul,zero,one,two,three,Q,R,H,C,u,top,P,c,mu,kappa,B,⟨hBase,hObj⟩,hTower⟩

def Target (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero mu history kappa N mul unit mark H C incoming base : M.Carrier .set) : Prop :=
  ConstructionTowerHistory.Row history kappa N mul unit mark H C incoming base kappa ∧
  ConstructionRoundFields.ObjectFields hM w Q R top N mul unit mark H C ∧
  ConstructionSaturationProbes.AllProbes w mu zero history kappa ∧
  ConstructionSaturationMergers.AllMergers w history kappa ∧
  ConstructionIdealProbes.AllIdeals mu history kappa ∧
  ConstructionSaturationComplement.Complement mu N mul mark ∧
  ConstructionSaturationCardinals.Cardinals hM N mul mark mu

theorem target_of_tower_data (hM : FirstOrder.Theory.Models M nativeZF)
    {w mul zero one two three Q R H C u top P c mu kappa B : M.Carrier .set}
    (hData : TowerData hM w mul zero one two three Q R H C u top P c mu kappa B) :
    ∃ history N mulN unit mark HN CN incoming base,
      Target hM w Q R top zero mu history kappa N mulN unit mark HN CN incoming base := by
  have hIdeal := hData.2.2
  have hCard := hIdeal.1
  have hComp := hCard.1
  have hMerger := hComp.1
  have hProbe := hMerger.1
  have hIndex := hProbe.1.1
  obtain ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,Pairs,F,
    hRec,hValid,_,_,_,_,hMatrix,_,_⟩ := hIndex.2.2
  have hi := hIndex.1.2.2.2.1.predecessor_mem
  obtain ⟨N,m,v,a,W,V,L,f,hRow⟩ := hValid.1.2 kappa hi
  have hObj := (hValid.2.1 kappa hi N m v a W V L f hRow).1
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) mu
  exact ⟨history,N,m,v,a,W,V,L,f,hRow,hObj,
    hProbe.2 history Pairs F hRec hMatrix,
    hMerger.2 history Pairs F hRec hMatrix,
    hIdeal.2 history Pairs F hRec hMatrix,
    hComp.2 history Pairs F hRec hMatrix N m v a W V L f hRow,
    hCard.2 ⟨id,hId⟩ history Pairs F hRec hMatrix N m v a W V L f hRow⟩

def System (hM : FirstOrder.Theory.Models M nativeZF)
    (w mul zero one two three Q R H C u top P c mu kappa B : M.Carrier .set) : Prop :=
  TowerData hM w mul zero one two three Q R H C u top P c mu kappa B ∧
  ∃ history N mulN unit mark HN CN incoming base,
    Target hM w Q R top zero mu history kappa N mulN unit mark HN CN incoming base

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ mul zero one two three Q R H C u top P c mu kappa B,
      System hM w mul zero one two three Q R H C u top P c mu kappa B := by
  obtain ⟨mul,zero,one,two,three,Q,R,H,C,u,top,P,c,mu,kappa,B,hData⟩ :=
    exists_tower_data hM hOrder hChoice hw
  exact ⟨mul,zero,one,two,three,Q,R,H,C,u,top,P,c,mu,kappa,B,hData,target_of_tower_data hM hData⟩


def baseF {m : Nat} (w mul zero one two three Q R H C u top : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionBaseUniformMarginSyntax.data w mul zero one two three Q R H C u top)
  (ConstructionRoundStepSyntax.objectFields w Q R top w mul zero one H C))

theorem baseF_freeClosed {m : Nat} (w mul zero one two three Q R H C u top : Fin m) :
    (baseF w mul zero one two three Q R H C u top).FreeClosed := by
  simp -implicitDefEqProofs [baseF,Definitional.Formula.FreeClosed,ConstructionBaseUniformMarginSyntax.data_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed]

theorem baseF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mul zero one two three Q R H C u top : Fin m) :
    Project.Formula.satisfies env (baseF w mul zero one two three Q R H C u top) ↔ Base hM (env.bound w) (env.bound mul) (env.bound zero) (env.bound one) (env.bound two) (env.bound three) (env.bound Q) (env.bound R) (env.bound H) (env.bound C) (env.bound u) (env.bound top) := by
  simp only [baseF,Base,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionBaseUniformMarginSyntax.data_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM]


def towerData {m : Nat} (w mul zero one two three Q R H C u top P c mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (baseF w mul zero one two three Q R H C u top) (ConstructionConcreteTower.tower w Q R top w mul zero
  one H C zero one u P c mu kappa B))

theorem towerData_freeClosed {m : Nat} (w mul zero one two three Q R H C u top P c mu kappa B : Fin m) :
    (towerData w mul zero one two three Q R H C u top P c mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [towerData,Definitional.Formula.FreeClosed,baseF_freeClosed,ConstructionConcreteTower.tower_freeClosed]

theorem towerData_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mul zero one two three Q R H C u top P c mu kappa B : Fin m) :
    Project.Formula.satisfies env (towerData w mul zero one two three Q R H C u top P c mu kappa B) ↔ TowerData hM (env.bound w) (env.bound mul) (env.bound zero) (env.bound one) (env.bound two) (env.bound three) (env.bound Q) (env.bound R) (env.bound H) (env.bound C) (env.bound u) (env.bound top) (env.bound P) (env.bound c) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [towerData,TowerData,
    Project.Formula.satisfies_conj_iff,
    
    baseF_semantics hM,ConstructionConcreteTower.tower_semantics hM]


def target {m : Nat} (w Q R top zero mu history kappa N mul unit mark H C incoming base : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionTowerHistory.row history kappa N mul unit mark H C incoming base kappa) (.conj
  (ConstructionRoundStepSyntax.objectFields w Q R top N mul unit mark H C) (.conj
  (ConstructionSaturationProbes.allProbes w mu zero history kappa) (.conj
  (ConstructionSaturationMergers.allMergers w history kappa) (.conj (ConstructionIdealProbes.allIdeals mu
  history kappa) (.conj (ConstructionSaturationComplement.complement mu N mul mark)
  (ConstructionSaturationCardinals.cardinalsF N mul mark mu)))))))

theorem target_freeClosed {m : Nat} (w Q R top zero mu history kappa N mul unit mark H C incoming base : Fin m) :
    (target w Q R top zero mu history kappa N mul unit mark H C incoming base).FreeClosed := by
  simp -implicitDefEqProofs [target,Definitional.Formula.FreeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionSaturationProbes.allProbes_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,ConstructionIdealProbes.allIdeals_freeClosed,ConstructionSaturationComplement.complement_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed]

theorem target_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero mu history kappa N mul unit mark H C incoming base : Fin m) :
    Project.Formula.satisfies env (target w Q R top zero mu history kappa N mul unit mark H C incoming base) ↔ Target hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound mu) (env.bound history) (env.bound kappa) (env.bound N) (env.bound mul) (env.bound unit) (env.bound mark) (env.bound H) (env.bound C) (env.bound incoming) (env.bound base) := by
  simp only [target,Target,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionTowerHistory.row_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionSaturationProbes.allProbes_semantics hM,ConstructionSaturationMergers.allMergers_semantics hM,ConstructionIdealProbes.allIdeals_semantics hM,ConstructionSaturationComplement.complement_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM]


def system {m : Nat} (w mul zero one two three Q R H C u top P c mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (towerData w mul zero one two three Q R H C u top P c mu kappa B) (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (target
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ mu.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
  (m+9)) kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+9)) (6 : Fin (m+9)) (5 : Fin (m+9))
  (4 : Fin (m+9)) (3 : Fin (m+9)) (2 : Fin (m+9)) (1 : Fin (m+9)) (0 : Fin (m+9)))))))))))))

theorem system_freeClosed {m : Nat} (w mul zero one two three Q R H C u top P c mu kappa B : Fin m) :
    (system w mul zero one two three Q R H C u top P c mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [system,Definitional.Formula.FreeClosed,towerData_freeClosed,target_freeClosed]

theorem system_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mul zero one two three Q R H C u top P c mu kappa B : Fin m) :
    Project.Formula.satisfies env (system w mul zero one two three Q R H C u top P c mu kappa B) ↔ System hM (env.bound w) (env.bound mul) (env.bound zero) (env.bound one) (env.bound two) (env.bound three) (env.bound Q) (env.bound R) (env.bound H) (env.bound C) (env.bound u) (env.bound top) (env.bound P) (env.bound c) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [system,System,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    towerData_semantics hM,target_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 1)))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (system (0 : Fin
      1).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (15 : Fin (1+16))
      (14 : Fin (1+16)) (13 : Fin (1+16)) (12 : Fin (1+16)) (11 : Fin (1+16)) (10 : Fin (1+16)) (9 : Fin
      (1+16)) (8 : Fin (1+16)) (7 : Fin (1+16)) (6 : Fin (1+16)) (5 : Fin (1+16)) (4 : Fin (1+16)) (3 : Fin
      (1+16)) (2 : Fin (1+16)) (1 : Fin (1+16)) (0 : Fin (1+16))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,system_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_exists_iff,system_semantics hM,Project.Term.eval_bound]
  exact exists_system hM hOrder hChoice

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
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ConstructionConcreteBase
