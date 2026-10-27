/- Pinned CompleteRounds.CompleteRound.probe (438), probe_profile (441),
probe_injective (446), probes_independent (456), realizes_merger (466).
Consume the SAME ordinal Place/last and actual recursive tower. No new
schedule, selector, recursion, or object Choice principle. -/
import PPAC.Migration.ConstructionTowerProbeIndependence
import PPAC.Migration.ConstructionTowerCardinality
import PPAC.Migration.ConstructionOrdinalScheduleSyntax
import PPAC.Migration.ConstructionScheduleCardinality

namespace PPAC.Migration.ConstructionCompleteRound
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerExecution (StepSet)
open ConstructionTowerTransitions (Before Matrix)
open ConstructionTowerHistory (Row Chart)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ConstructionTowerProbeFamily (Positions ProbeAt)
open ConstructionTowerProbeIndependence (Independent)
open ConstructionProbeMappedPath (NodeMap)
open ForcingSupportSize (MapsTo Injection Small)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- An actual Place strictly before last has its successor in the SAME tower.
Only existing internal successor and ordinal comparison are used. -/
theorem successor_before_last (hM : FirstOrder.Theory.Models M nativeZF)
    {J last i : M.Carrier .set}
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hLast : (Project.FirstOrderSemantics.reduct M).mem last J)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i last) :
    ∃ s, (Project.FirstOrderSemantics.reduct M).mem s J ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf s i ∧ Before s last := by
  have hKP := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  have hiJ := hJ.transitive last hLast i hi
  obtain ⟨s,hs⟩ := KP.exists_successor hKP i
  have hSO := KP.successor_isOrdinal hKP (hJ.mem hiJ) hs
  rcases Structure.IsOrdinal.trichotomy (ModelTransfer.extensionality hM) hSO (hJ.mem hLast)
      (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP s last) with he | hlt | hgt
  · have eq := (ModelTransfer.extensionality hM).eq_of_same_members s last he
    subst s
    exact ⟨last,hLast,hs,Or.inr rfl⟩
  · exact ⟨s,hJ.transitive last hLast s hlt,hs,Or.inl hlt⟩
  · rcases (hs last).mp hgt with hli | he
    · exact False.elim (hJ.wellOrder.linear.irrefl i hiJ
        (hJ.wellOrder.linear.trans i hiJ last hLast i hiJ hi hli))
    · have eq := (ModelTransfer.extensionality hM).eq_of_same_members last i he
      subst i
      exact False.elim (hJ.wellOrder.linear.irrefl last hLast hi)

/-- Restrict the actual product Place(q,k) to K and collect its graph by the
native set-function constructor. Its range is exactly eligible positions. -/
theorem exists_placement (hM : FirstOrder.Theory.Models M nativeZF)
    {J last Steps Schedule Place A K request Inputs : M.Carrier .set}
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hLast : (Project.FirstOrderSemantics.reduct M).mem last J)
    (hSteps : StepSet J Steps) (hInputs : Positions J Steps Schedule request last Inputs)
    (hPlace : ForcingConditionGraphs.FunctionOn A Place)
    (hEvery : ∀ k, (Project.FirstOrderSemantics.reduct M).mem k K →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i last ∧ Product Place request k i ∧
        PureKuratowski.PairMember M i request Schedule)
    (hFibers : ∀ k l i, Product Place request k i → Product Place request l i → k = l) :
    ∃ position, Injection K Inputs position ∧
      ∀ k i, PureKuratowski.PairMember M k i position ↔
        (Project.FirstOrderSemantics.reduct M).mem k K ∧ Product Place request k i := by
  have unique (k i j) (hi : Product Place request k i) (hj : Product Place request k j) : i = j := by
    obtain ⟨p,hp,hpi⟩ := hi
    obtain ⟨p',hp',hpj⟩ := hj
    have eq := KuratowskiZF.code_unique hM hp hp'
    subst p'
    exact ForcingConditionGraphs.function_unique hPlace hpi hpj
  have eligible (k i) (hk : (Project.FirstOrderSemantics.reduct M).mem k K)
      (hi : Product Place request k i) :
      (Project.FirstOrderSemantics.reduct M).mem i Inputs := by
    obtain ⟨j,hjl,hj,hSchedule⟩ := hEvery k hk
    have eq := unique k j i hj hi
    subst j
    obtain ⟨s,hs,hSucc,hBefore⟩ := successor_before_last hM hJ hLast hjl
    have hiJ := hJ.transitive last hLast i hjl
    exact (hInputs i).mpr ⟨(hSteps i).mpr ⟨hiJ,s,hs,hSucc⟩,hSchedule,s,hs,hSucc,hBefore⟩
  let schema : Project.BinarySchema 2 := {
    body := ProjectSyntax.encode id (ForcingDiagramOrder.product 2 3 1 0)
    freeClosed := ProjectSyntax.freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := fun i => if i.val = 0 then Place else request, free := fun _ => J }
  have he (k i) : schema.denote env k i ↔ Product Place request k i := by
    change Project.Formula.satisfies ((env.push k).push i) schema.body ↔ _
    simp only [schema,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      ForcingDiagramOrder.product_semantics (M := M)]
    rfl
  obtain ⟨position,hPosition,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env
    (fun k hk => by obtain ⟨i,_,hi,_⟩ := hEvery k hk; exact ⟨i,(he k i).mpr hi⟩)
    (fun k _ i j hi hj => unique k i j ((he k i).mp hi) ((he k j).mp hj))
    (fun k i hk hi => eligible k i hk ((he k i).mp hi))
  have hMap : MapsTo K Inputs position := (ForcingSupportSize.native_mapsTo hM K Inputs position).mpr hPosition
  have hGraph' : ∀ k i, PureKuratowski.PairMember M k i position ↔
      (Project.FirstOrderSemantics.reduct M).mem k K ∧ Product Place request k i :=
    fun k i => (hGraph k i).trans (and_congr_right (fun _ => he k i))
  exact ⟨position,⟨hMap,fun k l i hk hl => hFibers k l i ((hGraph' k i).mp hk).2
    ((hGraph' l i).mp hl).2⟩,hGraph'⟩

/-- Faithful K-indexed CompleteRound probe. The actual ordinal schedule Data,
actual tower, actual root table and target last-row produce the family.
No injection, profile or independence is an input. -/
theorem exists_probe (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F Steps Events Roots
      Requests K A I indexTop default oldSchedule oldPlace r order collapse inverse Place last
      request a b node V GV unitV markV HV CV KV baseV : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hF : Matrix J history zero P F) (hSteps : StepSet J Steps)
    (hEvents : ConstructionTowerExecution.Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events)
    (hRoots : Chart 8 Steps Events Roots)
    (hData : ConstructionOrdinalSchedule.Data hM Requests K A I indexTop default oldSchedule oldPlace r order
      J collapse inverse Schedule Place last)
    (hRequest : (Project.FirstOrderSemantics.reduct M).mem request Requests)
    (hCode : ConstructionRequestSchedule.ProbeCode zero a b node request)
    (hCut : Row history last V GV unitV markV HV CV KV baseV last) :
    ∃ Family, Independent K V GV Family baseV a markV ∧
      (∀ k p, PureKuratowski.PairMember M k p Family ↔
        (Project.FirstOrderSemantics.reduct M).mem k K ∧
        ∃ i, Product Place request k i ∧ ProbeAt J F Roots i last p) ∧
      ∀ k p, PureKuratowski.PairMember M k p Family →
        ConstructionRoundFresh.ProbeWitness w V GV markV baseV a b node p := by
  obtain ⟨_,_,_,_,_,_,_,_,hPlace,_,hLast,_,_,_,_,hEvery,hFibers,_⟩ := hData
  obtain ⟨Inputs,actual,hInputs,hMap,hGraph,hProfiles,hIndependent⟩ :=
    ConstructionTowerProbeIndependence.exists_independent_family hM hCtx hRec hF hSteps hEvents hRoots hCode hLast hCut
  obtain ⟨_,_,_,_,_,_,_,_,_,hJ,_,_⟩ := hCtx
  obtain ⟨position,hPosition,hPositionGraph⟩ := exists_placement hM hJ hLast hSteps hInputs hPlace.1.1
    (fun k hk => hEvery request k hRequest hk) (fun k l i => hFibers request k l i)
  obtain ⟨Family,hFamily,hComposition⟩ := ConstructionProbeMappedPath.exists_node_map hM hPosition.1 hMap
  have hFamilyGraph : ∀ k p, PureKuratowski.PairMember M k p Family ↔
      (Project.FirstOrderSemantics.reduct M).mem k K ∧
      ∃ i, Product Place request k i ∧ ProbeAt J F Roots i last p := by
    intro k p
    constructor
    · intro hp
      obtain ⟨i,hki,hip⟩ := (hComposition k p).mp hp
      exact ⟨((hPositionGraph k i).mp hki).1,i,((hPositionGraph k i).mp hki).2,((hGraph i p).mp hip).2⟩
    · rintro ⟨hk,i,hPlaceI,hProbe⟩
      have hki := (hPositionGraph k i).mpr ⟨hk,hPlaceI⟩
      exact (hComposition k p).mpr ⟨i,hki,(hGraph i p).mpr ⟨hPosition.1.2 k i hki,hProbe⟩⟩
  refine ⟨Family,⟨⟨hFamily,?_⟩,?_⟩,hFamilyGraph,?_⟩
  · intro k l p hkp hlp
    obtain ⟨i,hki,hip⟩ := (hComposition k p).mp hkp
    obtain ⟨j,hlj,hjp⟩ := (hComposition l p).mp hlp
    have eq := hIndependent.1.2 i j p hip hjp
    subst j
    exact hPosition.2 k l i hki hlj
  · intro k l pk pl hkp hlp hne
    obtain ⟨i,hki,hip⟩ := (hComposition k pk).mp hkp
    obtain ⟨j,hlj,hjp⟩ := (hComposition l pl).mp hlp
    have hij : i ≠ j := by
      intro eq
      subst j
      exact hne (hPosition.2 k l i hki hlj)
    exact hIndependent.2 i j pk pl hip hjp hij
  · intro k p hkp
    obtain ⟨i,_,hip⟩ := (hComposition k p).mp hkp
    exact hProfiles i p hip

/-- Original realizes_merger: use ONE member of K, not a choice function;
read the scheduled execution and transport to the SAME last target. -/
theorem realizes_merger (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F
      Requests K A I indexTop default oldSchedule oldPlace r order collapse inverse Place last
      request n prescription V GV unitV markV HV CV KV baseV : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hF : Matrix J history zero P F)
    (hData : ConstructionOrdinalSchedule.Data hM Requests K A I indexTop default oldSchedule oldPlace r order
      J collapse inverse Schedule Place last)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hRequest : (Project.FirstOrderSemantics.reduct M).mem request Requests)
    (hCode : ConstructionRequestSchedule.MergerCode one n prescription request)
    (hCut : Row history last V GV unitV markV HV CV KV baseV last) :
    ∃ roots, MapsTo n V roots ∧ ConstructionMergerRootSystem.RootSystem n prescription V GV baseV roots := by
  have hV := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hLast,_,_,_,_,hEvery,_⟩ := hData
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,hJ,hSchedule,_⟩ := hCtxCopy
  obtain ⟨k,hk⟩ := hK
  obtain ⟨i,hi,hPlace,hReq⟩ := hEvery request k hRequest hk
  obtain ⟨j,hj,hs,hBefore⟩ := successor_before_last hM hJ hLast hi
  have hiJ := hJ.transitive last hLast i hi
  obtain ⟨raw,req,N,mulN,eN,markN,HN,CN,L,f,W,G,unitW,markW,HL,LC,NewOut,base,O,root,
    V',GV',unitV',markV',HV',CV',KV',baseV',leg,
    hReq',hRowI,hRowJ,hRowK,_,_,_,_,_,_,_,_,hMerger⟩ :=
    ConstructionTowerRequestCones.at_later hM hCtx hRec hF hiJ hj hLast hs hBefore
  have eqReq := ForcingConditionGraphs.function_unique hSchedule hReq' hReq
  subst req
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := ConstructionTowerHistory.row_unique hV.1.1 hCut hRowK
  obtain ⟨roots,hMap,_,hRootSystem⟩ := hMerger n prescription hCode
  exact ⟨roots,hMap,hRootSystem⟩

/-- Source target/inclusion/preservesProfiles/cardinal_le on the actual last
row, with no target object or inclusion supplied separately. -/
theorem target (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history last mu : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hLast : (Project.FirstOrderSemantics.reduct M).mem last J)
    (hSmall : ConstructionTowerCardinality.AllSmall J history mu) :
    ∃ V GV unitV markV HV CV KV baseV, Row history last V GV unitV markV HV CV KV baseV last ∧
      ConstructionRoundFields.ObjectFields hM w Q R top V GV unitV markV HV CV ∧
      ConstructionRoundFields.MapFields hM w Q D V mul GV e unitV mark markV H C HV CV baseV ∧
      ConstructionRoundFields.Profiles w D V mul GV baseV ∧ ForcingSupportSize.Small V mu := by
  have hV := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  obtain ⟨V,GV,unitV,markV,HV,CV,KV,baseV,hRow⟩ := hV.1.2 last hLast
  obtain ⟨hObj,hMap,hProfiles,_⟩ := hV.2.1 last hLast V GV unitV markV HV CV KV baseV hRow
  exact ⟨V,GV,unitV,markV,HV,CV,KV,baseV,hRow,hObj,hMap,hProfiles,
    hSmall last hLast V (ConstructionTowerValidity.row_field 0 hRow)⟩

def ProbeFamilies (w K V GV markV baseV zero Requests : M.Carrier .set) : Prop :=
  ∀ request a b node, (Project.FirstOrderSemantics.reduct M).mem request Requests →
    ConstructionRequestSchedule.ProbeCode zero a b node request →
    ∃ Family, Independent K V GV Family baseV a markV ∧
      ∀ k p, PureKuratowski.PairMember M k p Family →
        ConstructionRoundFresh.ProbeWitness w V GV markV baseV a b node p

def MergerFamilies (V GV baseV one Requests : M.Carrier .set) : Prop :=
  ∀ request n prescription, (Project.FirstOrderSemantics.reduct M).mem request Requests →
    ConstructionRequestSchedule.MergerCode one n prescription request →
    ∃ roots, MapsTo n V roots ∧ ConstructionMergerRootSystem.RootSystem n prescription V GV baseV roots

/- Actual bounded CompleteRound, from the original parent/context and actual
ordinal schedule only. The tower, execution/root tables, target, inclusion,
all K-indexed probe families and every merger are constructed here. -/

/-- The SAME actual complete-round construction trace, retained for the outer
successor selector. A merely property-equivalent arbitrary target does not
satisfy this contract without its actual schedule, recursion and last row. -/
def Built (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O : M.Carrier .set) : Prop :=
  ∃ u A I indexTop default oldSchedule oldPlace r order J collapse inverse Schedule Place last
      history P F Steps Events Roots L,
    Context hM w Q R top D mul e mark H C zero one u J Schedule ∧
    ConstructionOrdinalSchedule.Data hM Requests K A I indexTop default oldSchedule oldPlace r order
      J collapse inverse Schedule Place last ∧ Small J mu ∧
    Recursive hM w Q R top D mul e mark H C zero one J Schedule J history ∧
    Matrix J history zero P F ∧ StepSet J Steps ∧
    ConstructionTowerExecution.Graph hM w Q R top D mul e mark H C zero one Schedule history F J Steps Events ∧
    Chart 8 Steps Events Roots ∧ Row history last W G unitW markW HW CW L O last ∧
    ConstructionTowerCardinality.AllSmall J history mu


def built {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.conj (ConstructionTowerIterationCases.context
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (21 : Fin (m+22)) (12 : Fin (m+22)) (9 : Fin (m+22))) (.conj (ConstructionOrdinalScheduleSyntax.data
  Requests.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (20 : Fin (m+22)) (19 : Fin (m+22)) (18 : Fin (m+22)) (17 : Fin (m+22)) (16 : Fin (m+22)) (15 : Fin
  (m+22)) (14 : Fin (m+22)) (13 : Fin (m+22)) (12 : Fin (m+22)) (11 : Fin (m+22)) (10 : Fin (m+22)) (9 : Fin
  (m+22)) (8 : Fin (m+22)) (7 : Fin (m+22))) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (12 :
  Fin (m+22))
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionTowerIteration.recursive
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (12 : Fin (m+22)) (9 : Fin (m+22)) (12 : Fin (m+22)) (6 : Fin (m+22))) (.conj
  (ConstructionTowerTransitions.matrix (12 : Fin (m+22)) (6 : Fin (m+22))
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (5 : Fin (m+22)) (4 : Fin (m+22))) (.conj (ConstructionTowerExecution.stepSet (12 : Fin (m+22)) (3 : Fin
  (m+22))) (.conj (ConstructionTowerExecution.graph
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (9 : Fin (m+22)) (6 : Fin (m+22)) (4 : Fin (m+22)) (12 : Fin (m+22)) (3 : Fin (m+22)) (2 : Fin (m+22)))
  (.conj (ConstructionTowerHistory.chart 8 (3 : Fin (m+22)) (2 : Fin (m+22)) (1 : Fin (m+22))) (.conj
  (ConstructionTowerHistory.row (6 : Fin (m+22)) (7 : Fin (m+22))
  W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  markW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  HW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  CW.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (0 : Fin (m+22))
  O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (7 : Fin (m+22))) (ConstructionTowerCardinality.allSmall (12 : Fin (m+22)) (6 : Fin (m+22))
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))))))

theorem built_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O : Fin m) :
    (built w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O).FreeClosed := by
  simp -implicitDefEqProofs [built,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerIterationCases.context_freeClosed,ConstructionOrdinalScheduleSyntax.data_freeClosed,ConstructionTowerIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerExecution.stepSet_freeClosed,ConstructionTowerExecution.graph_freeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionTowerCardinality.allSmall_freeClosed]

theorem built_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O : Fin m) :
    Project.Formula.satisfies env (built w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O) ↔ Built hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound Requests) (env.bound W) (env.bound G) (env.bound unitW) (env.bound markW) (env.bound HW) (env.bound CW) (env.bound O) := by
  simp only [built,Built,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,

    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerIterationCases.context_semantics hM,ConstructionOrdinalScheduleSyntax.data_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionTowerIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerExecution.stepSet_semantics,ConstructionTowerExecution.graph_semantics hM,ConstructionTowerHistory.chart_semantics hM 8,ConstructionTowerHistory.row_semantics hM,ConstructionTowerCardinality.allSmall_semantics hM]
  rfl


theorem exists_complete_round_built (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u J Schedule
      Requests K A I indexTop default oldSchedule oldPlace r order collapse inverse Place last mu : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hData : ConstructionOrdinalSchedule.Data hM Requests K A I indexTop default oldSchedule oldPlace r order
      J collapse inverse Schedule Place last)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : ForcingSupportSize.Small D mu) (hLength : ForcingSupportSize.Small J mu) :
    ∃ V GV unitV markV HV CV baseV,
      ConstructionRoundFields.ObjectFields hM w Q R top V GV unitV markV HV CV ∧
      ConstructionRoundFields.MapFields hM w Q D V mul GV e unitV mark markV H C HV CV baseV ∧
      ConstructionRoundFields.Profiles w D V mul GV baseV ∧ ForcingSupportSize.Small V mu ∧
      ProbeFamilies w K V GV markV baseV zero Requests ∧
      MergerFamilies V GV baseV one Requests ∧
      Built hM w Q R top D mul e mark H C zero one K mu Requests V GV unitV markV HV CV baseV := by
  obtain ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hRec,_,_,_,_,hF,_,_,hSmall,_⟩ :=
    ConstructionTowerCardinality.exists_tower hM hOrder hChoice hCtx hmu hD hLength
  obtain ⟨Steps,Outputs,Events,RootValues,Roots,hSteps,_,hEvents,_,hRoots⟩ :=
    ConstructionTowerExecution.exists_execution hM hOrder hCtx hRec hF
  have hDataCopy := hData
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hLast,_⟩ := hDataCopy
  obtain ⟨V,GV,unitV,markV,HV,CV,KV,baseV,hRow,hObj,hMap,hProfiles,hBound⟩ :=
    target hM hCtx hRec hLast hSmall
  refine ⟨V,GV,unitV,markV,HV,CV,baseV,hObj,hMap,hProfiles,hBound,?_,?_,?_⟩
  · intro request a b node hRequest hCode
    obtain ⟨Family,hIndependent,_,hProfile⟩ :=
      exists_probe hM hCtx hRec hF hSteps hEvents hRoots hData hRequest hCode hRow
    exact ⟨Family,hIndependent,hProfile⟩
  · intro request n prescription hRequest hCode
    exact realizes_merger hM hCtx hRec hF hData hK hRequest hCode hRow

  · exact ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,
      history,P,F,Steps,Events,Roots,KV,hCtx,hData,hLength,hRec,hF,hSteps,hEvents,hRoots,hRow,hSmall⟩

theorem exists_complete_round (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u J Schedule
      Requests K A I indexTop default oldSchedule oldPlace r order collapse inverse Place last mu : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hData : ConstructionOrdinalSchedule.Data hM Requests K A I indexTop default oldSchedule oldPlace r order
      J collapse inverse Schedule Place last)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : ForcingSupportSize.Small D mu) (hLength : ForcingSupportSize.Small J mu) :
    ∃ V GV unitV markV HV CV baseV,
      ConstructionRoundFields.ObjectFields hM w Q R top V GV unitV markV HV CV ∧
      ConstructionRoundFields.MapFields hM w Q D V mul GV e unitV mark markV H C HV CV baseV ∧
      ConstructionRoundFields.Profiles w D V mul GV baseV ∧ ForcingSupportSize.Small V mu ∧
      ProbeFamilies w K V GV markV baseV zero Requests ∧
      MergerFamilies V GV baseV one Requests := by
  obtain ⟨V,GV,unitV,markV,HV,CV,baseV,hObj,hMap,hProfiles,hBound,hProbes,hMergers,_⟩ :=
    exists_complete_round_built hM hOrder hChoice hCtx hData hK hmu hD hLength
  exact ⟨V,GV,unitV,markV,HV,CV,baseV,hObj,hMap,hProfiles,hBound,hProbes,hMergers⟩

/-- Discharge even the request carrier, schedule, ordinal index and its size
from the ORIGINAL CompleteRound parent. The existing bounded schedule and
complete-round constructors are consumed, rather than assumed as output. -/
theorem exists_from_parent_built (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : ForcingSupportSize.Small D mu) (hKSmall : ForcingSupportSize.Small K mu) :
    ∃ Requests V GV unitV markV HV CV baseV,
      ConstructionRequestCarrier.Carrier w D mul e zero one Requests ∧
      ConstructionRoundFields.ObjectFields hM w Q R top V GV unitV markV HV CV ∧
      ConstructionRoundFields.MapFields hM w Q D V mul GV e unitV mark markV H C HV CV baseV ∧
      ConstructionRoundFields.Profiles w D V mul GV baseV ∧ ForcingSupportSize.Small V mu ∧
      ProbeFamilies w K V GV markV baseV zero Requests ∧
      MergerFamilies V GV baseV one Requests ∧
      Built hM w Q R top D mul e mark H C zero one K mu Requests V GV unitV markV HV CV baseV := by
  obtain ⟨Requests,node,default,hCarrier,_,_,_,_,hDefault,h01,hLegacy,_⟩ :=
    ConstructionRequestCarrier.exists_system hM hw hz hzw hone hObj.1 hObj.2.2.2.1 hObj.2.2.2.2.1
  obtain ⟨one',hSucc,hOne⟩ := hw.1.2 zero hzw
  obtain ⟨z,hz',hSucc'⟩ := hone
  have eqZero := (ModelTransfer.extensionality hM).eq_of_same_members z zero
    (fun x => ⟨fun h => False.elim (hz' x h),fun h => False.elim (hz x h)⟩)
  subst z
  have eqOne := (ModelTransfer.extensionality hM).eq_of_same_members one' one
    (fun x => (hSucc x).trans (hSucc' x).symm)
  have how : (Project.FirstOrderSemantics.reduct M).mem one w := eqOne ▸ hOne
  obtain ⟨A,I,indexTop,oldSchedule,oldPlace,r,order,J,collapse,inverse,Schedule,Place,last,
    hData,_,_,_,hJSmall,_⟩ := ConstructionScheduleCardinality.exists_bounded_system hM hChoice hw hmu hpow
      hD hKSmall hzw how h01 hCarrier hDefault hK
  have hDataCopy := hData
  obtain ⟨hOrdered,_,_,_,_,_,hSchedule,_⟩ := hDataCopy
  obtain ⟨_,_,_,_,_,_,_,_,hJ,_⟩ := hOrdered
  have hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule :=
    ⟨hw,hQ,hR,hCoordinates,⟨zero,hz,hSucc'⟩,hTop,hObj,hz,hzw,hJ,hSchedule.1,
      fun i q hq => hLegacy q (hSchedule.2 i q hq)⟩
  obtain ⟨V,GV,unitV,markV,HV,CV,baseV,hTarget,hMap,hProfiles,hBound,hProbes,hMergers,hBuilt⟩ :=
    exists_complete_round_built hM hOrder hChoice hCtx hData hK hmu hD hJSmall
  exact ⟨Requests,V,GV,unitV,markV,HV,CV,baseV,hCarrier,hTarget,hMap,hProfiles,hBound,hProbes,hMergers,hBuilt⟩
theorem exists_from_parent (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : ForcingSupportSize.Small D mu) (hKSmall : ForcingSupportSize.Small K mu) :
    ∃ Requests V GV unitV markV HV CV baseV,
      ConstructionRequestCarrier.Carrier w D mul e zero one Requests ∧
      ConstructionRoundFields.ObjectFields hM w Q R top V GV unitV markV HV CV ∧
      ConstructionRoundFields.MapFields hM w Q D V mul GV e unitV mark markV H C HV CV baseV ∧
      ConstructionRoundFields.Profiles w D V mul GV baseV ∧ ForcingSupportSize.Small V mu ∧
      ProbeFamilies w K V GV markV baseV zero Requests ∧
      MergerFamilies V GV baseV one Requests := by
  obtain ⟨Requests,V,GV,unitV,markV,HV,CV,baseV,hCarrier,hObj',hMap,hProfiles,hBound,hProbes,hMergers,_⟩ :=
    exists_from_parent_built hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall
  exact ⟨Requests,V,GV,unitV,markV,HV,CV,baseV,hCarrier,hObj',hMap,hProfiles,hBound,hProbes,hMergers⟩


def probeFamilies {m : Nat} (w K V GV markV baseV zero Requests : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound
  Requests.succ.succ.succ.succ)) (.imp (ConstructionRequestSchedule.probeCode zero.succ.succ.succ.succ (2 :
  Fin (m+4)) (1 : Fin (m+4)) (0 : Fin (m+4)) (3 : Fin (m+4))) (.existsE (.conj
  (ConstructionTowerProbeIndependence.independentFamily K.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ (0 : Fin (m+5)) baseV.succ.succ.succ.succ.succ (3 :
  Fin (m+5)) markV.succ.succ.succ.succ.succ) (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (0 : Fin (m+5)).succ.succ (1 : Fin (m+7)) (0 : Fin (m+7))))
  (ConstructionRoundFresh.probeWitness w.succ.succ.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ
  markV.succ.succ.succ.succ.succ.succ.succ baseV.succ.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+5)).succ.succ (2 : Fin (m+5)).succ.succ (1 : Fin (m+5)).succ.succ (0 : Fin (m+7))))))))))))))

theorem probeFamilies_freeClosed {m : Nat} (w K V GV markV baseV zero Requests : Fin m) :
    (probeFamilies w K V GV markV baseV zero Requests).FreeClosed := by
  simp -implicitDefEqProofs [probeFamilies,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerProbeIndependence.independentFamily_freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionRoundFresh.probeWitness_freeClosed]

theorem probeFamilies_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w K V GV markV baseV zero Requests : Fin m) :
    Project.Formula.satisfies env (probeFamilies w K V GV markV baseV zero Requests) ↔ ProbeFamilies (env.bound w) (env.bound K) (env.bound V) (env.bound GV) (env.bound markV) (env.bound baseV) (env.bound zero) (env.bound Requests) := by
  simp only [probeFamilies,ProbeFamilies,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerProbeIndependence.independentFamily_semantics hM,ConstructionRequestSchedule.probeCode_semantics hM,ConstructionRoundFresh.probeWitness_semantics hM]
  rfl


def mergerFamilies {m : Nat} (V GV baseV one Requests : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin (m+3))) (.bound Requests.succ.succ.succ)) (.imp
  (ConstructionRequestSchedule.mergerCode one.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)) (2 : Fin
  (m+3))) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+4)) (2 : Fin
  (m+4)) V.succ.succ.succ.succ)) (ConstructionMergerRootSystem.rootSystem (2 : Fin (m+4)) (1 : Fin (m+4))
  V.succ.succ.succ.succ GV.succ.succ.succ.succ baseV.succ.succ.succ.succ (0 : Fin (m+4))))))))))

theorem mergerFamilies_freeClosed {m : Nat} (V GV baseV one Requests : Fin m) :
    (mergerFamilies V GV baseV one Requests).FreeClosed := by
  simp -implicitDefEqProofs [mergerFamilies,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionMergerRootSystem.rootSystem_freeClosed]

theorem mergerFamilies_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V GV baseV one Requests : Fin m) :
    Project.Formula.satisfies env (mergerFamilies V GV baseV one Requests) ↔ MergerFamilies (env.bound V) (env.bound GV) (env.bound baseV) (env.bound one) (env.bound Requests) := by
  simp only [mergerFamilies,MergerFamilies,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionRequestSchedule.mergerCode_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ConstructionMergerRootSystem.rootSystem_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 15) (1 : Fin 15)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 15) (1 : Fin 15) (2 : Fin 15)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 15) (12 : Fin
    15) (11 : Fin 15) (11 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 15))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 15) (1 : Fin 15) (12 : Fin 15) (3 : Fin 15)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 15) (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (4 : Fin
    15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15) (8 : Fin 15) (9 : Fin 15)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 15))) (.imp (.mem (.bound (10 : Fin 15)) (.bound (0 : Fin 15))) (.imp (.existsE (.mem
    (.bound (0 : Fin 16)) (.bound (13 : Fin 15).succ))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 15)) (.bound (14 : Fin 15))) (.imp
    (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (14 : Fin 15))
    (.bound (14 : Fin 15)) (.bound (0 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small
    (4 : Fin 15) (14 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 15) (14
    : Fin 15))) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionRequestCarrier.carrier (0 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (6 :
    Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ
    (11 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin 23)) (.conj
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (3 :
    Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin 23) (5 : Fin 23) (4 : Fin 23) (3 : Fin 23) (2 :
    Fin 23) (1 : Fin 23)) (.conj (ConstructionRoundStepSyntax.mapFields (0 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (4 :
    Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin 23) (5 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin 23) (6 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin 23) (7 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 23) (8 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (2 :
    Fin 23) (1 : Fin 23) (0 : Fin 23)) (.conj (ConstructionRoundStepSyntax.profiles (0 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (6 :
    Fin 23) (5 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin 23) (0 : Fin 23)) (.conj
    (ProjectSyntax.encode id (ForcingSupportSize.small (6 : Fin 23) (14 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (probeFamilies (0 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (6 :
    Fin 23) (5 : Fin 23) (3 : Fin 23) (0 : Fin 23) (10 : Fin 15).succ.succ.succ.succ.succ.succ.succ.succ (7
    : Fin 23)) (mergerFamilies (6 : Fin 23) (5 : Fin 23) (0 : Fin 23) (11 : Fin
    15).succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin 23)))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,
      Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      ConstructionRequestCarrier.carrier_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,
      ConstructionRoundStepSyntax.profiles_freeClosed,probeFamilies_freeClosed,mergerFamilies_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,
    ConstructionRoundStepSyntax.profiles_semantics hM,ConstructionRequestCarrier.carrier_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),probeFamilies_semantics hM,mergerFamilies_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall =>
    exists_from_parent hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall

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


end PPAC.Migration.ConstructionCompleteRound
