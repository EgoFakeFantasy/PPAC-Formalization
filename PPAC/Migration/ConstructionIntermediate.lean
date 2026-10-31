/- Pinned CellCuts.Square.intermediate and apex_eq_sup; consumed by
CellReorder.future_cut's selected successor. Reuse the actual Cell.map,
full pushout pasting/comparison, ordinary comap and exact range object. -/
import PPAC.Migration.ConstructionCellBaseChange

namespace PPAC.Migration.ConstructionIntermediate
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCellRestriction (Cell Attachment)
open ConstructionProbePushout (Hom IsPushout composition_value)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionPushoutPasting (exists_hom_comp nodeMap_assoc)
open ConstructionPushoutIdentification (right_identity)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (IdentityGraph InverseGraph function_input function_unique)
open ConstructionAttachmentCoefficients (OldFixed)
open ForcingSupportedNames (Range)
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square base_inclusion)
open ConstructionRealCuts (Subset)
open ConstructionCellGeneration (Submonoid Generated)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The existing RoundFields.map_comp conservative proof, with unrelated
height/profile fields removed from the interface. Its proof body is retained. -/
theorem conservative_comp
    {D N R mul mulN mulR eN eR f g h : M.Carrier .set}
    (hmN : LeftCancelMonoid N mulN eN) (hmR : LeftCancelMonoid R mulR eR)
    (hfCons : Conservative D N mul mulN f) (hgCons : Conservative N R mulN mulR g)
    (hgProd : ConstructionProbeLiftHom.PreservesProducts mulN mulR g)
    (hh : MapsTo D R h) (hComp : NodeMap f g h) : Conservative D R mul mulR h := by
  have hCon : Conservative D R mul mulR h := by
    refine ⟨⟨hh,?_⟩,?_,?_,?_⟩
    · intro x y z hx hy
      obtain ⟨a,hxa,haz⟩ := (hComp x z).mp hx
      obtain ⟨b,hyb,hbz⟩ := (hComp y z).mp hy
      have hab := hgCons.1.2 a b z haz hbz
      exact hfCons.1.2 x y a hxa (hab.symm ▸ hyb)
    · intro x y z fx fy hx hy hz hprod
      obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
      obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
      obtain ⟨t,ht,hat⟩ := ConstructionProbeAlphabetMap.factor_eq hmN hmR hgCons.1 hgProd hgCons.2.1 haf hbf hz hprod
      obtain ⟨u,hu⟩ := hfCons.2.1 x y t a b hxa hyb (ForcingConditionGraphs.function_input hgCons.1.1.1 ht) hat
      exact ⟨u,(hComp u z).mpr ⟨t,hu,ht⟩⟩
    · intro x y j fx fy fj hx hy hj hJoin
      obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
      obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
      obtain ⟨c,hjc,hcf⟩ := (hComp j fj).mp hj
      exact hgCons.2.2.1 a b c fx fy fj haf hbf hcf (hfCons.2.2.1 x y j a b c hxa hyb hjc hJoin)
    · intro x y fx fy hx hy hCommon
      obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
      obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
      exact hfCons.2.2.2 x y a b hxa hyb (hgCons.2.2.2 a b fx fy haf hbf hCommon)
  exact hCon

/-- Source ofMulEquiv: the actual inverse graph supplies every target preimage. -/
theorem iso_conservative {D N mul mulN e eN f g : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hf : Hom D N mul mulN e eN f) (hg : Hom N D mulN mul eN e g)
    (hInv : InverseGraph f g) : Conservative D N mul mulN f := by
  have hInj : Injection D N f := ⟨hf.1,fun x y z hx hy =>
    function_unique hg.1.1 ((hInv x z).mp hx) ((hInv y z).mp hy)⟩
  have hFactors : ConstructionProbeAlphabetMap.FactorConservation N mulN f := by
    intro _ _ z _ _ _ _ hz _
    obtain ⟨a,hza,_⟩ := hg.1.1.2 z hz
    exact ⟨a,(hInv a z).mpr hza⟩
  have hDiv := ConstructionProbeAlphabetMap.division_reflection hm hmN hInj hf.2.2 hFactors
  refine ⟨hInj,hFactors,?_,?_⟩
  · intro x y j fx fy fj hx hy hj hJoin z hz
    obtain ⟨a,hza,_⟩ := hg.1.1.2 z hz
    have haz := (hInv a z).mpr hza
    exact ((and_congr (hDiv x a fx z hx haz) (hDiv y a fy z hy haz)).trans
      (hJoin a (hg.1.2 z a hza))).trans (hDiv j a fj z hj haz).symm
  · intro x y fx fy hx hy hCommon
    obtain ⟨z,hz,hxz,hyz⟩ := hCommon
    obtain ⟨a,hza,_⟩ := hg.1.1.2 z hz
    have haz := (hInv a z).mpr hza
    exact ⟨a,hg.1.2 z a hza,(hDiv x a fx z hx haz).mp hxz,(hDiv y a fy z hy haz).mp hyz⟩

/-- Existing old-fixed law as the exact composite inclusion graph. -/
theorem old_node {A W V O f ia : M.Carrier .set}
    (hO : MapsTo A W O) (hf : MapsTo W V f)
    (hFixed : OldFixed O f) (hId : IdentityGraph A ia) : NodeMap O f ia := by
  intro a b
  constructor
  · intro hab
    obtain ⟨ha,rfl⟩ := (hId a b).mp hab
    obtain ⟨u,hau,_⟩ := hO.1.2 a ha
    exact ⟨u,hau,hFixed a u hau⟩
  · rintro ⟨u,hau,hub⟩
    have he := function_unique hf.1 hub (hFixed a u hau)
    exact (hId a b).mpr ⟨function_input hO.1 hau,he.symm⟩

/-- Source IsPushout.generated, using only an ordinary submonoid target. -/
theorem pushout_generated (hM : FirstOrder.Theory.Models M nativeZF)
    {B C D PB mulB mulC mulD eB eC eD ab ac bd cd : M.Carrier .set}
    (hPD : ConstructionProbeLetters.Representatives D D PB) (hMulD : MapsTo PB D mulD)
    (hmD : LeftCancelMonoid D mulD eD)
    (hbd : Hom B D mulB mulD eB eD bd) (hcd : Hom C D mulC mulD eC eD cd)
    (hPush : IsPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) :
    Generated B C D mulD eD bd cd := by
  intro S hS hBS hCS
  obtain ⟨PS,GS,hPS,hGS,hGraph⟩ := ConstructionCellGeneration.exists_product hM
    (fun _ _ hx hy => ConstructionProbeAction.projected hM hPD hMulD hx hy)
    (fun _ _ _ _ _ _ hp hq => ConstructionProbeHomEvaluation.product_unique hM hMulD hp hq) hS
  have hU := ConstructionCellGeneration.unit_restrict hmD.1 hS hGraph
  have hAssoc := ConstructionCellGeneration.associative_restrict hmD.2.2 hS hGraph
  have hbS := ConstructionCellGeneration.hom_restrict hbd hBS hGraph
  have hcS := ConstructionCellGeneration.hom_restrict hcd hCS hGraph
  obtain ⟨f,hf,hfb,hfc,_⟩ := hPush.2 S PS GS eD bd cd hPS hGS hU hAssoc hbS hcS hPush.1
  have hfD := ConstructionCellGeneration.hom_include hf hS.1 hGraph
  obtain ⟨ident,hId,hIdentity⟩ := ConstructionPushoutIdentification.exists_hom_identity (mul := mulD) hM hmD.1.1
  obtain ⟨lift,_,_,_,hu⟩ := hPush.2 D PB mulD eD bd cd hPD hMulD hmD.1 hmD.2.2 hbd hcd hPush.1
  have he := (hu f hfD hfb hfc).trans
    (hu ident hId (right_identity hbd.1 hIdentity) (right_identity hcd.1 hIdentity)).symm
  apply (ModelTransfer.extensionality hM).eq_of_same_members S D
  intro x
  constructor
  · exact hS.1 x
  · intro hx
    exact hf.1.2 x x (he ▸ (hIdentity x x).mpr ⟨hx,rfl⟩)

/-- Literal supremum among ALL ordinary internal submonoids, not conservative hulls. -/
def Sup (V GV e B E F : M.Carrier .set) : Prop :=
  Submonoid V GV e F ∧ Subset B F ∧ Subset E F ∧
    ∀ S, Submonoid V GV e S → Subset B S → Subset E S → Subset F S

/-- Source apex_eq_sup, via the already constructed ordinary comap. -/
theorem apex_sup (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF : M.Carrier .set}
    (hBaseB : Base V GV e B PB GB ib)
    (hBaseE : Base V GV e E PE GE ie) (hBaseF : Base V GV e F PF GF iF)
    (hSquare : Square A B E F GA GB GE GF e ia ib ie) : Sup V GV e B E F := by
  obtain ⟨hClosedF,hPF,hMulF,_,hmF,_,hIdF,hFV,_,_⟩ := hBaseF
  obtain ⟨_,_,hBF,hEF,_,_,_,_,hBHom,_,hEHom,_,hPush⟩ := hSquare
  have hGenerated := pushout_generated hM hPF hMulF hmF hBHom hEHom hPush
  have hWhole : Submonoid F GF e F := by
    refine ⟨fun _ h => h,hmF.1.1,?_⟩
    intro x y z hx hy hp
    obtain ⟨t,ht,hpt⟩ := (hmF.2.1 x hx).1 y hy
    exact ((hmF.2.1 x hx).2.1 y t z hy hpt hp) ▸ ht
  refine ⟨⟨hClosedF.1,hClosedF.2.1,hClosedF.2.2.1⟩,hBF,hEF,?_⟩
  intro S hS hBS hES
  obtain ⟨Q,hQ,hq⟩ := ConstructionAttachmentCoefficients.exists_comap hM hWhole hFV hS
  have hBMap : MapsTo B Q ib := by
    refine ⟨hBHom.1.1,?_⟩
    intro x y hxy
    obtain ⟨hx,rfl⟩ := (hBaseB.2.2.2.2.2.2.1 x y).mp hxy
    exact (hq x).mpr ⟨hBF x hx,fun z hxz => ((hIdF x z).mp hxz).2 ▸ hBS x hx⟩
  have hEMap : MapsTo E Q ie := by
    refine ⟨hEHom.1.1,?_⟩
    intro x y hxy
    obtain ⟨hx,rfl⟩ := (hBaseE.2.2.2.2.2.2.1 x y).mp hxy
    exact (hq x).mpr ⟨hEF x hx,fun z hxz => ((hIdF x z).mp hxz).2 ▸ hES x hx⟩
  have hEq := hGenerated Q hQ hBMap hEMap
  intro x hx
  exact ((hq x).mp (hEq.symm ▸ hx)).2 x ((hIdF x x).mpr ⟨hx,rfl⟩)

/-- Exact source intermediate: SAME ambient terminal object, the actual
range inside the original successor, full Attachment and Square, and the
ordinary generated supremum. Two mapped cells are compared by their full
pushout; this is the source map_comp/cast identification via uniqueness. -/
theorem intermediate (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJV : ConditionalJoins V GV)
    (hBaseA : Base V GV e A PA GA ia) (hBaseB : Base V GV e B PB GB ib)
    (hBaseC : Base V GV e C PC GC ic) (hBaseD : Base V GV e D PD GD idD)
    (hBaseE : Base V GV e E PE GE ie)
    (hSquare : Square A B C D GA GB GC GD e ia ib ic)
    (hAttach : Attachment hM w zero A GA e B GB) (hAE : Subset A E) (hEC : Subset E C) :
    ∃ F PF GF iF, Base V GV e F PF GF iF ∧ Sup V GV e B E F ∧ Subset F D ∧
      Attachment hM w zero E GE e F GF ∧ Square A B E F GA GB GE GF e ia ib ie := by
  obtain ⟨hAEHom,hAECons⟩ := base_inclusion hv hc hJV hBaseA hBaseE hAE
  obtain ⟨hECHom,hECCons⟩ := base_inclusion hv hc hJV hBaseE hBaseC hEC
  have bases : Base V GV e B PB GB ib ∧ Base V GV e E PE GE ie := ⟨hBaseB,hBaseE⟩
  obtain ⟨_,_,_,_,_,_,hIa,_,_,hJA⟩ := hBaseA
  obtain ⟨_,_,_,_,_,_,hIb,_,_,_⟩ := hBaseB
  obtain ⟨_,_,_,_,hmC,hcC,hIc,_,_,hJC⟩ := hBaseC
  obtain ⟨_,hPD,hMulD,hGD,hmD,_,hIdD,hDV,hDVCons,_⟩ := hBaseD
  obtain ⟨_,_,_,_,hmE,hcE,hIe,_,_,hJE⟩ := hBaseE
  obtain ⟨hAB,_,hBD,_,hABHom,hABCons,_,_,hBDHom,_,hCDHom,_,hPush⟩ := hSquare
  obtain ⟨W,G,unit,O,embed,inv,hCell,_,_,hOld,hEmbed,hInv,hInverse,hFixed,_⟩ := hAttach
  obtain ⟨W1,G1,u1,O1,H1,hMap1⟩ := ConstructionCellBaseChange.exists_mapped hM hw hz hzw hCell hOld hJA hmE hcE hJE hAEHom hAECons
  obtain ⟨hOH,_,_,_,hCell1,hm1,_,hJ1,hO1,hO1Cons,hH1,_,hPush1,_⟩ := hMap1
  obtain ⟨W2,G2,u2,O2,H2,hMap2⟩ := ConstructionCellBaseChange.exists_mapped hM hw hz hzw hCell1 hO1Cons hJE hmC hcC hJC hECHom hECCons
  obtain ⟨_,_,_,_,_,hm2,_,_,hO2,_,hH2,hH2Cons,hPush2,P2,hP2,hMul2⟩ := hMap2
  obtain ⟨H12,hH12,hH12Graph⟩ := exists_hom_comp hM hH1 hH2
  have hOuter := ConstructionPushoutPasting.flip
    (ConstructionPushoutPasting.paste hM hAEHom.1 hO1 hH1 hECHom hH2
      (right_identity hAEHom.1 hIe) hH12Graph (ConstructionPushoutPasting.flip hPush1) (ConstructionPushoutPasting.flip hPush2))
  have hEmbedD : Hom W D G GD unit e embed :=
    ⟨⟨hEmbed.1.1,fun x y hxy => hBD y (hEmbed.1.2 x y hxy)⟩,hEmbed.2.1,
      ConstructionProbePushout.composition_preserves (right_identity hEmbed.1 hIb) hEmbed.2.2 hBDHom.2.2⟩
  have hPresentation := ConstructionPushoutIdentification.change_left hM hABHom.1 hBDHom hInv hEmbed
    (fun x y => (hInverse y x).symm) (ConstructionCellBaseChange.inverse_old hOH.1 hInv.1 hInverse hFixed hIa)
    (right_identity hEmbed.1 hIb) hPush
  obtain ⟨r,ri,hr,hri,hRInv,hNew,hOldEquation,_,_⟩ := ConstructionPushoutIdentification.exists_comparison hM
    hP2 hMul2 hm2.1 hm2.2.2 hPD hMulD hmD.1 hmD.2.2 hH12 hO2 hEmbedD hCDHom hOuter hPresentation
  obtain ⟨m,hmDMap,hmGraph⟩ := exists_hom_comp hM hH2 hr
  have hConsD := conservative_comp hm2 hmD hH2Cons (iso_conservative hm2 hmD hr hri hRInv) hr.2.2 hmDMap.1 hmGraph
  have hmV : Hom W1 V G1 GV u1 e m :=
    ⟨⟨hmDMap.1.1,fun x y hxy => hDV.1.2 y y ((hIdD y y).mpr ⟨hmDMap.1.2 x y hxy,rfl⟩)⟩,
      hmDMap.2.1,ConstructionProbePushout.composition_preserves (right_identity hmDMap.1 hIdD) hmDMap.2.2 hDV.2.2⟩
  have hConsV := conservative_comp hmD hv hConsD hDVCons hDV.2.2 hmV.1 (right_identity hmDMap.1 hIdD)
  have hmOld : OldFixed O1 m := by
    intro a u hau
    obtain ⟨v,huv,_⟩ := hH2.1.1.2 u (hO1.1.2 a u hau)
    have hav := (hPush2.1 a u a v hau ((hIe a a).mpr ⟨function_input hO1.1.1 hau,rfl⟩)).mp huv
    have hra := (composition_value hO2.1 hOldEquation hav).mp
      ((hIc a a).mpr ⟨function_input hO2.1.1 hav,rfl⟩)
    exact (hmGraph u a).mpr ⟨v,huv,hra⟩
  have hmNew : NodeMap H1 m embed := (nodeMap_assoc hH12Graph hmGraph).mp hNew
  have hmOldNode := old_node hO1.1 hmV.1 hmOld hIe
  obtain ⟨F,hRange⟩ := ConstructionBlockStages.range_exists hM hmV.1
  obtain ⟨PF,GF,iF,mi,hRangeData⟩ := ConstructionRangeObject.construction (w := w) (zero := zero) hM hm1 hJ1 hv hc hJV hmV hConsV hRange
  obtain ⟨hClosedF,hPF,hMulF,hGF,hmF,hcF,hJF,hIdF,hFV,hFVCons,hmFMap,_,_,hmi,hMI,_,_⟩ := hRangeData
  have hBaseF : Base V GV e F PF GF iF := ⟨hClosedF,hPF,hMulF,hGF,hmF,hcF,hIdF,hFV,hFVCons,hJF⟩
  have hFD : Subset F D := by
    intro x hx
    obtain ⟨y,_,hyx⟩ := (hRange x).mp hx
    exact hmDMap.1.2 y x hyx
  have hEF : Subset E F := by
    intro x hx
    obtain ⟨u,hxu,_⟩ := hO1.1.1.2 x hx
    exact (hRange x).mpr ⟨u,hO1.1.2 x u hxu,hmOld x u hxu⟩
  have hBF : Subset B F := by
    intro x hx
    obtain ⟨u,hxu,_⟩ := hInv.1.1.2 x hx
    obtain ⟨v,huv,_⟩ := hH1.1.1.2 u (hInv.1.2 x u hxu)
    exact (hRange x).mpr ⟨v,hH1.1.2 u v huv,(composition_value hH1.1 hmNew huv).mp ((hInverse u x).mpr hxu)⟩
  have hMappedPush := ConstructionPushoutIdentification.map_apex hM hmFMap hmi hMI hmNew hmOldNode hPush1
  have hInvEmbed : NodeMap inv embed ib := by
    intro x y
    constructor
    · intro hxy
      obtain ⟨hx,rfl⟩ := (hIb x y).mp hxy
      obtain ⟨u,hxu,_⟩ := hInv.1.1.2 x hx
      exact ⟨u,hxu,(hInverse u x).mpr hxu⟩
    · rintro ⟨u,hxu,huy⟩
      have he := function_unique hEmbed.1.1 huy ((hInverse u x).mpr hxu)
      exact (hIb x y).mpr ⟨function_input hInv.1.1 hxu,he.symm⟩
  have hHomWF := ConstructionCellGeneration.hom_restrict hEmbedD
    ⟨hEmbed.1.1,fun x y hxy => hBF y (hEmbed.1.2 x y hxy)⟩
    (ConstructionCellRestriction.product_factor hGF hGD hFD)
  have hFinalPush := ConstructionPushoutIdentification.change_left hM hOH.1 hHomWF hEmbed hInv hInverse
    (old_node hOH.1 hEmbed.1 hFixed hIa) hInvEmbed hMappedPush
  obtain ⟨hBFHom,hBFCons⟩ := base_inclusion hv hc hJV bases.1 hBaseF hBF
  obtain ⟨hEFHom,hEFCons⟩ := base_inclusion hv hc hJV bases.2 hBaseF hEF
  have hFinalSquare : Square A B E F GA GB GE GF e ia ib ie :=
    ⟨hAB,hAE,hBF,hEF,hABHom,hABCons,hAEHom,hAECons,hBFHom,hBFCons,hEFHom,hEFCons,hFinalPush⟩
  exact ⟨F,PF,GF,iF,hBaseF,apex_sup hM bases.1 bases.2 hBaseF hFinalSquare,hFD,
    ⟨W1,G1,u1,O1,m,mi,hCell1,hm1,hO1,hO1Cons,hmFMap,hmi,hMI,hmOld,hRange⟩,hFinalSquare⟩

/-- Pure membership formula for the exact ordinary generated supremum. -/
def sup {m : Nat} (V GV e B E F : Fin m) : Project.Formula 1 m :=
  .conj (ConstructionCellGeneration.submonoid V GV e F)
    (.conj (Project.Formula.subset (.bound B) (.bound F))
      (.conj (Project.Formula.subset (.bound E) (.bound F))
        (.forallE (.imp (ConstructionCellGeneration.submonoid V.succ GV.succ e.succ 0)
          (.imp (Project.Formula.subset (.bound B.succ) (.bound 0))
            (.imp (Project.Formula.subset (.bound E.succ) (.bound 0))
              (Project.Formula.subset (.bound F.succ) (.bound 0))))))))

theorem sup_freeClosed {m : Nat} (V GV e B E F : Fin m) : (sup V GV e B E F).FreeClosed := by
  simp -implicitDefEqProofs [sup,Definitional.Formula.FreeClosed,ConstructionCellGeneration.submonoid_freeClosed,Project.Formula.subset]

theorem sup_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V GV e B E F : Fin m) :
    Project.Formula.satisfies env (sup V GV e B E F) ↔
      Sup (env.bound V) (env.bound GV) (env.bound e) (env.bound B) (env.bound E) (env.bound F) := by
  simp only [sup,Sup,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    ConstructionCellGeneration.submonoid_semantics hM]
  rfl

def apexSupSentence {m : Nat} (V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e E PE GE ie) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e F PF GF iF) (.imp (ConstructionUnionPushout.square A B E F GA GB GE GF e ia ib ie) (sup V GV e B E F)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,sup_freeClosed]

theorem apexSup_models {m : Nat} (V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (apexSupSentence V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (apexSupSentence V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,sup_semantics hM]
  exact apex_sup hM

theorem apexSup_kernel_certificate {m : Nat} (V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (apexSupSentence V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF)) :=
  ModelTransfer.derives (fun _ hM => apexSup_models V GV e A B E F PB PE PF GA GB GE GF ia ib ie iF hM)

def intermediateSentence {m : Nat} (w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e D PD GD idD) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e E PE GE ie) (.imp (ConstructionUnionPushout.square A B C D GA GB GC GD e ia ib ic) (.imp (ConstructionCellRestriction.attachmentFormula w zero A GA e B GB) (.imp (Project.Formula.subset (.bound A) (.bound E)) (.imp (Project.Formula.subset (.bound E) (.bound C)) (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ 3 2 1 0) (.conj (sup V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ B.succ.succ.succ.succ E.succ.succ.succ.succ 3) (.conj (Project.Formula.subset (.bound 3) (.bound D.succ.succ.succ.succ)) (.conj (ConstructionCellRestriction.attachmentFormula w.succ.succ.succ.succ zero.succ.succ.succ.succ E.succ.succ.succ.succ GE.succ.succ.succ.succ e.succ.succ.succ.succ 3 1) (ConstructionUnionPushout.square A.succ.succ.succ.succ B.succ.succ.succ.succ E.succ.succ.succ.succ 3 GA.succ.succ.succ.succ GB.succ.succ.succ.succ GE.succ.succ.succ.succ 1 e.succ.succ.succ.succ ia.succ.succ.succ.succ ib.succ.succ.succ.succ ie.succ.succ.succ.succ))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.subset,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionCellRestriction.attachmentFormula_freeClosed,sup_freeClosed]

theorem intermediate_models {m : Nat} (w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (intermediateSentence w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (intermediateSentence w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,ConstructionCellRestriction.attachmentFormula_semantics hM,sup_semantics hM]
  exact intermediate hM

theorem intermediate_kernel_certificate {m : Nat} (w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (intermediateSentence w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie)) :=
  ModelTransfer.derives (fun _ hM => intermediate_models w zero V GV e A B C D E PA PB PC PD PE GA GB GC GD GE ia ib ic idD ie hM)

end PPAC.Migration.ConstructionIntermediate
