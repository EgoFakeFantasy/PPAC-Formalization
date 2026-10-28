/- Pinned LocalRecords.System.Available/available_one/available_lower/
available_join/availability:549-598, consumed by AvailableRecords.classAvailability.
Availability is the literal preimage of the SAME internal restriction family.
Reuse native Separation, existing Sub algebra, range intersections and ConeIdeal. -/
import PPAC.Migration.ForcingEligibleSystem
import PPAC.Migration.ConstructionComponentVertices

namespace PPAC.Migration.ForcingSystemAvailability
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Sub Le)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeCones (JoinProperty)
open ConstructionIdealProbes (ConeIdeal)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Available (D mul objects maps r x n : M.Carrier .set) : Prop :=
  ∃ s Os z f y, Sub D mul r n s ∧ PureKuratowski.PairMember M s Os objects ∧
    PureKuratowski.Code M z s r ∧ PureKuratowski.PairMember M z f maps ∧
    (Project.FirstOrderSemantics.reduct M).mem y Os ∧ PureKuratowski.PairMember M y x f

theorem exists_map (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul diagrams objImage objects S mapImage maps r s Or Os : M.Carrier .set}
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hrs : Le D mul r s) :
    ∃ z f, PureKuratowski.Code M z s r ∧ PureKuratowski.PairMember M z f maps ∧ MapsTo Os Or f := by
  obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM s r
  have hzS := (hS z).mpr ⟨s,r,ForcingConditionGraphs.function_input hObj.1 hs,
    ForcingConditionGraphs.function_input hObj.1 hr,hrs,hz⟩
  obtain ⟨f,hf,_⟩ := hMaps.1.2 z hzS
  exact ⟨z,f,hz,hf,hSys.1 s r Os Or z f hs hr hz hf⟩

/-- Source sub_mono, using existing sub construction, sub_sub and sub_eq. -/
theorem sub_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e r s t n m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hs : Injection D I s) (ht : Injection D I t)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n D)
    (hnm : Divides D mul n m) (hS : Sub D mul r n s) (hT : Sub D mul r m t) :
    Le D mul s t := by
  obtain ⟨b,hb,hprod⟩ := hnm
  obtain ⟨t',ht',hSub⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 b hb) hs
  have he := ConstructionComponentVertices.sub_eq hM ht' ht
    (ForcingDiagramPoset.sub_sub hm hn hb hprod hS hSub) hT
  exact ⟨b,hb,he ▸ hSub⟩

theorem available_one (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r Or x : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hrI : Injection D I r)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x Or) :
    Available D mul objects maps r x e := by
  obtain ⟨z,f,hz,hf,_⟩ := exists_map hM hObj hS hMaps hSys hr hr (ForcingDiagramPoset.le_refl hm hrI)
  exact ⟨r,Or,z,f,x,ForcingDiagramPoset.sub_one hm hrI,hr,hz,hf,hx,
    (hSys.2.1 r Or z f hr hz hf x x).mpr ⟨hx,rfl⟩⟩

theorem available_lower (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r Or x n m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n D)
    (hnm : Divides D mul n m) (hAvailable : Available D mul objects maps r x m) :
    Available D mul objects maps r x n := by
  have hrI := (hDiagrams r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  obtain ⟨sm,Om,zm,fm,ym,hSubm,hOm,hzm,hfm,hym,heym⟩ := hAvailable
  have hsmI := (hDiagrams sm).mp (ForcingConditionGraphs.function_input hObj.1 hOm)
  obtain ⟨sn,hsnI,hSubn⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 n hn) hrI
  obtain ⟨On,hOn,_⟩ := hObj.1.2 sn ((hDiagrams sn).mpr hsnI)
  have hnmLe := sub_mono hM hm hsnI hsmI hn hnm hSubn hSubm
  obtain ⟨zmn,fmn,hzmn,hfmn,hMN⟩ := exists_map hM hObj hS hMaps hSys hOn hOm hnmLe
  obtain ⟨zn,fn,hzn,hfn,_⟩ := exists_map hM hObj hS hMaps hSys hr hOn ⟨n,hn,hSubn⟩
  have hcomp := hSys.2.2.1 sm sn r Om On Or zmn zn zm fmn fn fm hOm hOn hr hzmn hzn hzm hfmn hfn hfm
  obtain ⟨_,yn,heMN,heNR⟩ := (hcomp ym x).mp heym
  exact ⟨sn,On,zn,fn,yn,hSubn,hOn,hzn,hfn,hMN.2 ym yn heMN,heNR⟩

theorem available_join (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r Or x n m k : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n D)
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m D)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k D) (hJoin : JoinProperty D mul n m k)
    (hnAvail : Available D mul objects maps r x n) (hmAvail : Available D mul objects maps r x m) :
    Available D mul objects maps r x k := by
  have hrI := (hDiagrams r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  obtain ⟨sn,On,zn,fn,yn,hSubn,hOn,hzn,hfn,hyn,heyn⟩ := hnAvail
  obtain ⟨sm,Om,zm,fm,ym,hSubm,hOm,hzm,hfm,hym,heym⟩ := hmAvail
  have hsnI := (hDiagrams sn).mp (ForcingConditionGraphs.function_input hObj.1 hOn)
  have hsmI := (hDiagrams sm).mp (ForcingConditionGraphs.function_input hObj.1 hOm)
  obtain ⟨sk,hskI,hSubk⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 k hk) hrI
  obtain ⟨Ok,hOk,_⟩ := hObj.1.2 sk ((hDiagrams sk).mpr hskI)
  have hkk : Divides D mul k k := ⟨e,hm.1.1,(hm.1.2 k hk k).2.mpr rfl⟩
  obtain ⟨hnk,hmk⟩ := (hJoin k hk).mpr hkk
  have hnkLe := sub_mono hM hm hsnI hskI hn hnk hSubn hSubk
  have hmkLe := sub_mono hM hm hsmI hskI hmD hmk hSubm hSubk
  obtain ⟨zkn,fkn,hzkn,hfkn,_⟩ := exists_map hM hObj hS hMaps hSys hOn hOk hnkLe
  obtain ⟨zkm,fkm,hzkm,hfkm,_⟩ := exists_map hM hObj hS hMaps hSys hOm hOk hmkLe
  obtain ⟨zk,fk,hzk,hfk,_⟩ := exists_map hM hObj hS hMaps hSys hr hOk ⟨k,hk,hSubk⟩
  have hInter := ConstructionDiagramPlacements.range_inter_sub hrI hSubn hSubm hSubk hJoin
  obtain ⟨yk,hyk,hekn,_⟩ := hSys.2.2.2.2 sk sn sm r Ok On Om Or zn zm zkn zkm fn fm fkn fkm yn ym x
    hOk hOn hOm hr hzn hzm hzkn hzkm hfn hfm hfkn hfkm hInter heyn heym
  have hcomp := hSys.2.2.1 sk sn r Ok On Or zkn zn zk fkn fn fk hOk hOn hr hzkn hzn hzk hfkn hfn hfk
  exact ⟨sk,Ok,zk,fk,yk,hSubk,hOk,hzk,hfk,hyk,(hcomp yk x).mpr ⟨hyk,yn,hekn,heyn⟩⟩

def Carrier (D mul objects maps r x a U : M.Carrier .set) : Prop :=
  ∀ n, (Project.FirstOrderSemantics.reduct M).mem n U ↔
    (Project.FirstOrderSemantics.reduct M).mem n D ∧ Divides D mul n a ∧ Available D mul objects maps r x n

theorem carrier_ideal (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r Or x a U : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x Or)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hU : Carrier D mul objects maps r x a U) : ConeIdeal D mul a U := by
  have hrI := (hDiagrams r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  refine ⟨fun n hn => ((hU n).mp hn).1,ha,?_,?_,?_,?_⟩
  · exact ⟨e,(hU e).mpr ⟨hm.1.1,⟨a,ha,(hm.1.2 a ha a).1.mpr rfl⟩,
      available_one hM hm hrI hObj hS hMaps hSys hr hx⟩⟩
  · exact fun n hn => ((hU n).mp hn).2.1
  · intro n m hn hmU hnm
    obtain ⟨_,hma,hmAvail⟩ := (hU m).mp hmU
    exact (hU n).mpr ⟨hn,ConstructionProbeGates.divides_trans hm hn hnm hma,
      available_lower hM hm hDiagrams hObj hS hMaps hSys hr hn hnm hmAvail⟩
  · intro n m k hnU hmU hk hJoin
    obtain ⟨hn,hna,hnAvail⟩ := (hU n).mp hnU
    obtain ⟨hmD,hma,hmAvail⟩ := (hU m).mp hmU
    exact (hU k).mpr ⟨hk,(hJoin a ha).mp ⟨hna,hma⟩,
      available_join hM hm hDiagrams hObj hS hMaps hSys hr hn hmD hk hJoin hnAvail hmAvail⟩

def available {m : Nat} (D mul objects maps r x n : Fin m) : Formula m :=
  let up : Fin m → Fin (m+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let s := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let Os := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let z := (Fin.last (m+2)).castSucc.castSucc
  let f := (Fin.last (m+3)).castSucc
  let y := (Fin.last (m+4))
  .ex (.ex (.ex (.ex (.ex (((ForcingDiagramOrder.sub (up D) (up mul) (up r) (up n) s).conj ((Source.SetLanguage.edge (up objects) s Os).conj ((PairSyntax.ordered z s (up r)).conj ((Source.SetLanguage.edge (up maps) z f).conj ((Formula.mem y Os).conj (Source.SetLanguage.edge f y (up x))))))))))))

theorem available_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul objects maps r x n : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (available D mul objects maps r x n) ↔
      Available (env D) (env mul) (env objects) (env maps) (env r) (env x) (env n) := by
  simp only [available,Available,Formula.Realize,ForcingDiagramOrder.sub_semantics (M := M),
    KuratowskiZF.source_edge,KuratowskiZF.source_code,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def carrier {m : Nat} (D mul objects maps r x a U : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) U.castSucc).iff ((Formula.mem (Fin.last m) D.castSucc).conj
    ((ConstructionBaseMonoid.divides D.castSucc mul.castSucc (Fin.last m) a.castSucc).conj
      (available D.castSucc mul.castSucc objects.castSucc maps.castSucc r.castSucc x.castSucc (Fin.last m)))))

theorem carrier_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul objects maps r x a U : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (carrier D mul objects maps r x a U) ↔
      Carrier (env D) (env mul) (env objects) (env maps) (env r) (env x) (env a) (env U) := by
  simp only [carrier,Carrier,Source.Formula.iff,Formula.Realize,ConstructionBaseMonoid.divides_semantics (M := M),
    available_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h n => ⟨(h n).1,(h n).2⟩,fun h n => ⟨(h n).mp,(h n).mpr⟩⟩

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF)
    (D mul objects maps r x a : M.Carrier .set) : ∃ U, Carrier D mul objects maps r x a U := by
  let schema : Project.UnarySchema 7 := {
    body := ProjectSyntax.encode id ((ConstructionBaseMonoid.divides (1 : Fin 8) 2 0 7).conj
      (available 1 2 3 4 5 6 0))
    freeClosed := ProjectSyntax.freeClosed _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases D (Fin.cases mul (Fin.cases objects (Fin.cases maps (Fin.cases r (Fin.cases x (fun _ => a)))))),
    free := fun _ => D }
  obtain ⟨U,hU⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env D
  refine ⟨U,fun n => ?_⟩
  simpa only [schema,env,Project.UnarySchema.denote,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    Formula.Realize,ConstructionBaseMonoid.divides_semantics (M := M),available_semantics (M := M)] using! hU n

def AllIdeals (D mul objects maps : M.Carrier .set) : Prop :=
  ∀ r Or a x, PureKuratowski.PairMember M r Or objects →
    (Project.FirstOrderSemantics.reduct M).mem x Or →
    (Project.FirstOrderSemantics.reduct M).mem a D →
    ∃ U, Carrier D mul objects maps r x a U ∧ ConeIdeal D mul a U

theorem all_ideals (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps) :
    AllIdeals D mul objects maps := by
  intro r Or a x hr hx ha
  obtain ⟨U,hU⟩ := exists_carrier hM D mul objects maps r x a
  exact ⟨U,hU,carrier_ideal hM hm hDiagrams hObj hS hMaps hSys hr hx ha hU⟩

def allIdeals {m : Nat} (D mul objects maps : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+4) := fun i => i.succ.succ.succ.succ
  let r : Fin (m+4) := 3
  let Or : Fin (m+4) := 2
  let a : Fin (m+4) := 1
  let x : Fin (m+4) := 0
  .forallE (.forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) r Or))
      (.imp (.mem (.bound x) (.bound Or))
        (.imp (.mem (.bound a) (.bound (up D)))
          (.existsE (.conj (ProjectSyntax.encode id (carrier (up D).succ (up mul).succ
            (up objects).succ (up maps).succ r.succ x.succ a.succ 0))
            (ConstructionIdealProbes.coneIdeal (up D).succ (up mul).succ a.succ 0)))))))))

theorem allIdeals_freeClosed {m : Nat} (D mul objects maps : Fin m) :
    (allIdeals D mul objects maps).FreeClosed := by
  simp -implicitDefEqProofs [allIdeals,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionIdealProbes.coneIdeal_freeClosed]

theorem allIdeals_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul objects maps : Fin m) :
    Project.Formula.satisfies env (allIdeals D mul objects maps) ↔
      AllIdeals (env.bound D) (env.bound mul) (env.bound objects) (env.bound maps) := by
  simp only [allIdeals,AllIdeals,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    carrier_semantics (M := M),ConstructionIdealProbes.coneIdeal_semantics hM,Project.Term.eval_bound]
  rfl

def systemSentence {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage)) (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.imp (ForcingEligibleSystem.system D objects maps) (allIdeals D mul objects maps)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingEligibleSystem.system_freeClosed,allIdeals_freeClosed]

theorem system_models {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (systemSentence D I mul e diagrams objImage objects S mapImage maps)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (systemSentence D I mul e diagrams objImage objects S mapImage maps)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingEligibleSystem.system_semantics hM,allIdeals_semantics hM]
  exact fun hm hDiagrams hObj hS hMaps hSys => all_ideals hM hm hDiagrams hObj hS hMaps hSys

theorem system_kernel_certificate {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (systemSentence D I mul e diagrams objImage objects S mapImage maps)) :=
  ModelTransfer.derives (fun _ hM => system_models D I mul e diagrams objImage objects S mapImage maps hM)

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
    let objImage : Fin (k+5) := 4
    let objects : Fin (k+5) := 3
    let S : Fin (k+5) := 2
    let mapImage : Fin (k+5) := 1
    let maps : Fin (k+5) := 0
    Project.Formula.forallClosure k
      (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu)) (.imp (ConstructionSaturationIndex.hartogs mu I) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu)) (.imp (ConstructionSaturationMergers.allMergers w history kappa) (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e)) (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6))) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G)) (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K)) (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t)) (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels)) (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c t b nameBound)) (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I)) (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq)) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq fixingQ)) (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixingQ E)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (up (rho 4)) objImage)) (.conj (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun i => up (rho i)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) (up (rho 4)) objects)) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (up (rho 0)) (up mul) (up (rho 4)) S)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun i => up (rho i)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) S maps)) (.conj (ForcingEligibleSystem.system (up (rho 0)) objects maps) (allIdeals (up (rho 0)) (up mul) objects maps)))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ForcingEligibleSystem.system_freeClosed,allIdeals_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleFamily.family_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingEligibleMapFamily.family_semantics (M := M),
    ForcingEligibleSystem.system_semantics hM,allIdeals_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hp hG hFilter hc ht hLabels hBound hg hq hRangeQ hFixQ hE
  obtain ⟨objImage,objects,hObjMap,hObj⟩ := ForcingEligibleFamily.exists_family hM
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) bound rho G F mul g q nameBound labels E I (rho 4)
    hp.2.2.2.1
  obtain ⟨S,hS⟩ := ForcingEligibleMapFamily.exists_arrows hM bound (rho 0) mul (rho 4)
  obtain ⟨mapImage,maps,hMap,hMaps⟩ := ForcingEligibleMapFamily.exists_family hM bound rho G F mul
    I K B w e g q nameBound labels E S hm hp hg hS
  have hSys := ForcingEligibleSystem.system_of_families hM hChoice bound rho G F mul
    hw hMu hI hD hMergers hRow hm hp hG hFilter hc ht hLabels hBound hg hq hRangeQ hFixQ hE hObj hS hMaps
  exact ⟨objImage,objects,S,mapImage,maps,hObjMap,hObj,hS,hMap,hMaps,hSys,
    all_ideals hM hm hp.2.2.2.1 hObjMap hS hMap hSys⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let zero := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => zero }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E hL hChoice)


end PPAC.Migration.ForcingSystemAvailability
