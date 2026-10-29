/- Pinned CohenSelection fixed-root ordinal consumers (OrdinalCodes:352-412).
Reuse the SAME lifted predicate, actual rank graph, collected type and support.
The extraction step decodes an actual stronger non-top condition. -/
import PPAC.Migration.ForcingCohenSelection

namespace PPAC.Migration.ForcingCohenRankConsumers
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingSupportSize (Injection Small)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingCohenConditions (Condition)
open ForcingSupportingRoot (Code code code_mem code_le exists_code)
open ForcingCheckName (Checked checkName)
open ForcingRawRank (Rank Ordinal)
open ForcingCohenSelection (liftRelation mapRel_lift)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Monotone {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (S w X : M.Carrier .set) : Prop :=
  ∀ a d e, (Project.FirstOrderSemantics.reduct M).mem a X → Condition S w d → Condition S w e →
    (Project.FirstOrderSemantics.reduct M).MemberSubset d e → MapRel R env a d → MapRel R env a e

section Root
variable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul I w : Fin k)
    (R : Formula (n+2)) (rp : Fin n → Fin k)
    {mu tower kappa unit mark H C incoming base K B root A fixing support X order ranks selection top : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers (env w) tower kappa)
    (hRow : ConstructionTowerHistory.Row tower kappa (env (rho 0)) (env mul) unit mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) unit)
    (hpres : Presentation (env (rho 0)) (env I) K B (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) mu (env F))
    (hroot : Injection (env (rho 0)) (env I) root)
    (hRange : ForcingStabilizerTransport.Image root (env (rho 0)) A)
    (hFix : ForcingLabelPermutations.Fixing (env G) A fixing)
variable (ht : ForcingWithTopCarrier.Empty top)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order X)
    (hRanks : ForcingOrdinalRanks.Ranks (liftRelation R rp (rho 0) I (rho 2) w) env X order (env (rho 6)) ranks)
    (hselection : ForcingCollectedName.Collected (liftRelation R rp (rho 0) I (rho 2) w) env X ranks (env (rho 6)) selection)
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun i => env (rho i)) (env G) (env F) support X ranks)
    (hType : ForcingOrdinalFixed.Fixed (fun i => env (rho i)) (env G) (env F) support selection)
    (hsub : (Project.FirstOrderSemantics.reduct M).MemberSubset fixing support)
include hM hChoice hw hMu hI hD hMergers hRow hm hpres hG hF hroot hRange hFix ht hselection hsub

include hType hOrder hRanks in
theorem orderType_decide {d z : M.Carrier .set}
    (hd : Condition (env (rho 2)) (env w) d) (hz : Code z d root) :
    ∃ rank, Rank selection rank ∧ ForcingOrdinalRoot.RootDecision (orderFormula (rho 0) mul) env (env (rho 6)) (env (rho 2)) (env w) top selection root d rank := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  obtain ⟨rank,hrank⟩ := ForcingRawRank.exists_rank hM selection
  exact ⟨rank,hrank,ForcingOrdinalRoot.ordinal_decide_at_root hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hF hroot hRange hFix hd hz ht hType.1
      (fun pi hpi act hact => hType.2 pi (hsub pi hpi) act hact) hrank
      (ForcingOrdinalTransitivity.ordF_selectionType hM hpre hOrder hRanks hselection)⟩

include hFamily hOrder hRanks in
theorem rank_decide {d z a name theta ntheta : M.Carrier .set}
    (hd : Condition (env (rho 2)) (env w) d) (hz : Code z d root)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X) (han : PureKuratowski.PairMember M a name ranks)
    (hRa : MapRel R (fun j => env (rp j)) a d) (hntheta : Checked top theta ntheta)
    (htheta : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) selection ntheta z) :
    ∃ de zr beta nb, Condition (env (rho 2)) (env w) de ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset d de ∧ Code zr de root ∧ Ordinal beta ∧
      (Project.FirstOrderSemantics.reduct M).mem beta theta ∧ Checked top beta nb ∧ Forces true (orderFormula (rho 0) mul) env (env (rho 6)) name nb zr := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hfixed := hFamily a ha name han
  obtain ⟨rank,hrank⟩ := ForcingRawRank.exists_rank hM name
  obtain ⟨de,zr,beta,nb,hde,hdd,hzr,hbeta,_,hnb,he⟩ :=
    ForcingOrdinalRoot.ordinal_decide_at_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm
      hpres hG hF hroot hRange hFix hd hz ht hfixed.1
      (fun pi hpi act hact => hfixed.2 pi (hsub pi hpi) act hact) hrank
      (ForcingOrdinalTransitivity.ordF_selectedRank hM hpre hOrder hRanks ha han)
  have hzrP := code_mem hpres hde hroot hzr
  have hle := (orderFormula_semantics env (rho 0) mul zr z).mpr
    ((code_le hzr hz).mpr ⟨hdd,ForcingDiagramPoset.le_refl hm hroot⟩)
  have hLift := (mapRel_lift R rp env (rho 0) I (rho 2) w a z).mpr
    ((ForcingCohenSelection.lift_coe hd hroot hz).mpr hRa)
  have hm := ForcingAtomicBasic.mem_mono hM hpre hzrP hle
    (ForcingOrdinalMembership.selectedRank_mem_selectionType hM hpre hselection ha han (code_mem hpres hd hroot hz) hLift)
  have hm' := (ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hzrP hle htheta)).mp
    ((ForcingAtomicLaws.mem_congr_left hM hpre he).mp hm)
  have htP := (hpres.2.2.2.2.2 top).mpr (Or.inl ht)
  have htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q top :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q top).mpr (Or.inl ht)
  exact ⟨de,zr,beta,nb,hde,hdd,hzr,hbeta,(ForcingCheckReflection.mem_check_check hM hpre htP htop hzrP hnb hntheta).mp hm',hnb,he⟩

include hFamily in
theorem member_rank (hmono : Monotone R (fun j => env (rp j)) (env (rho 2)) (env w) X)
    {d z theta ntheta beta nb : M.Carrier .set}
    (hd : Condition (env (rho 2)) (env w) d) (hz : Code z d root)
    (hntheta : Checked top theta ntheta) (hnb : Checked top beta nb)
    (hbeta : (Project.FirstOrderSemantics.reduct M).mem beta theta)
    (htheta : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) selection ntheta z) :
    ∃ de zr a name, Condition (env (rho 2)) (env w) de ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset d de ∧ Code zr de root ∧
      (Project.FirstOrderSemantics.reduct M).mem a X ∧ PureKuratowski.PairMember M a name ranks ∧
      MapRel R (fun j => env (rp j)) a de ∧ Forces true (orderFormula (rho 0) mul) env (env (rho 6)) name nb zr := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hzP := code_mem hpres hd hroot hz
  have htP := (hpres.2.2.2.2.2 top).mpr (Or.inl ht)
  have htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q top :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q top).mpr (Or.inl ht)
  have hmem := (ForcingAtomicLaws.mem_congr_right hM hpre htheta).mpr
    ((ForcingCheckReflection.mem_check_check hM hpre htP htop hzP hnb hntheta).mpr hbeta)
  obtain ⟨q,a,c,name,hq,hqz,ha,_,hc,han,hRc,hqc,he⟩ :=
    (ForcingOrdinalMembership.mem_selectionType hM (orderFormula (rho 0) mul) env (liftRelation R rp (rho 0) I (rho 2) w) env (order := X) (a := X) hselection hzP).mp
      hmem z hzP (hpre.1 z hzP)
  obtain ⟨cz,hcz,hzs⟩ := hz
  rcases (orderFormula_semantics env (rho 0) mul q z).mp hqz with hzEmpty | ⟨cq,cz',hqs,hzs',hqprod⟩
  · exact False.elim (ForcingWithTopCarrier.single_nonempty hzs hzEmpty)
  · have hczEq := ForcingWithTopCarrier.single_injective hzs' hzs
    subst cz'
    have hcq := ForcingProductPoset.coe_mem hpres.2.2.2.2.2 hq hqs
    obtain ⟨de,hdeX,s,hsY,hcqs⟩ := (hpres.2.2.2.2.1 cq).mp hcq
    have hde := (hpres.2.2.1 de).mp hdeX
    have hs := (hpres.2.2.2.1 s).mp hsY
    have hqCode : Code q de s := ⟨cq,hcqs,hqs⟩
    have hqroot := (code_le hqCode ⟨cz,hcz,hzs⟩).mp (Or.inr ⟨cq,cz,hqs,hzs,hqprod⟩)
    obtain ⟨df,sf,hdf,_,hcf,hRdf⟩ := (mapRel_lift R rp env (rho 0) I (rho 2) w a c).mp hRc
    have hqcf := (code_le hqCode hcf).mp ((orderFormula_semantics env (rho 0) mul q c).mp hqc)
    obtain ⟨zr,hzr⟩ := exists_code hM de root
    have hfixed := hFamily a ha name han
    exact ⟨de,zr,a,name,hde,hqroot.1,hzr,ha,han,hmono a df de ha hdf hde hqcf.1 hRdf,
      ForcingOrdinalRoot.eq_at_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hF
        hroot hRange hFix hs hqroot.2 hde hqCode hzr
        (fun pi hpi act hact => hfixed.2 pi (hsub pi hpi) act hact)
        (ForcingOrdinalRoot.check_supported hM (fun i => env (rho i)) hpres ht hnb)
        (ForcingAtomicBasic.eq_symm hM he)⟩
end Root


def monotone {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (S w X : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let a := (Fin.last m).castSucc.castSucc
  let d := (Fin.last (m+1)).castSucc
  let e := Fin.last (m+2)
  .all (.all (.all ((Formula.mem a (up X)).imp
    ((ForcingCohenConditions.condition (up S) (up w) d).imp
      ((ForcingCohenConditions.condition (up S) (up w) e).imp
        ((Source.SetLanguage.subset d e).imp ((rel R (fun j => up (rp j)) a d).imp
          (rel R (fun j => up (rp j)) a e))))))))

theorem monotone_semantics {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (env : Fin m → M.Carrier .set) (S w X : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (monotone R rp S w X) ↔
      Monotone R (fun j => env (rp j)) (env S) (env w) (env X) := by
  simp only [monotone,Monotone,Formula.Realize,ForcingCohenConditions.condition_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def typeDecision {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P S w top selection root d : Fin m) : Formula m :=
  .ex ((LayerRankSyntax.rank selection.castSucc (Fin.last m)).conj
    (ForcingOrdinalRoot.rootDecision L (paramsUp lp) P.castSucc S.castSucc w.castSucc top.castSucc
      selection.castSucc root.castSucc d.castSucc (Fin.last m)))

theorem typeDecision_semantics {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (env : Fin m → M.Carrier .set) (P S w top selection root d : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (typeDecision L lp P S w top selection root d) ↔
      ∃ rank, Rank (env selection) rank ∧ ForcingOrdinalRoot.RootDecision L (fun j => env (lp j))
        (env P) (env S) (env w) (env top) (env selection) (env root) (env d) rank := by
  simp only [typeDecision,Formula.Realize,ForcingRawRank.rank_semantics (M := M),
    ForcingOrdinalRoot.rootDecision_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def lowerDecision {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P S w top name root d theta : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let e := (Fin.last m).castSucc.castSucc.castSucc
  let z := (Fin.last (m+1)).castSucc.castSucc
  let beta := (Fin.last (m+2)).castSucc
  let nb := Fin.last (m+3)
  .ex (.ex (.ex (.ex ((ForcingCohenConditions.condition (up S) (up w) e).conj
    ((Source.SetLanguage.subset (up d) e).conj ((code z e (up root)).conj
      ((OrdinalSyntax.ordinal beta).conj ((Formula.mem beta (up theta)).conj
        ((checkName (up top) beta nb).conj (forces true L (fun i => up (lp i)) (up P) (up name) nb z))))))))))

theorem lowerDecision_semantics {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (env : Fin m → M.Carrier .set) (P S w top name root d theta : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (lowerDecision L lp P S w top name root d theta) ↔
      ∃ e z beta nb, Condition (env S) (env w) e ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset (env d) e ∧
        Code z e (env root) ∧ Ordinal beta ∧ (Project.FirstOrderSemantics.reduct M).mem beta (env theta) ∧
          Checked (env top) beta nb ∧ Forces true L (fun j => env (lp j)) (env P) (env name) nb z := by
  simp only [lowerDecision,Formula.Realize,ForcingCohenConditions.condition_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingRawRank.ordinal_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def memberDecision {k n m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P S w X ranks root d nb : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let e := (Fin.last m).castSucc.castSucc.castSucc
  let z := (Fin.last (m+1)).castSucc.castSucc
  let a := (Fin.last (m+2)).castSucc
  let name := Fin.last (m+3)
  .ex (.ex (.ex (.ex ((ForcingCohenConditions.condition (up S) (up w) e).conj
    ((Source.SetLanguage.subset (up d) e).conj ((code z e (up root)).conj
      ((Formula.mem a (up X)).conj ((Source.SetLanguage.edge (up ranks) a name).conj
        ((rel R (fun j => up (rp j)) a e).conj (forces true L (fun i => up (lp i)) (up P) name (up nb) z))))))))))

theorem memberDecision_semantics {k n m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (env : Fin m → M.Carrier .set)
    (P S w X ranks root d nb : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (memberDecision L lp R rp P S w X ranks root d nb) ↔
      ∃ e z a name, Condition (env S) (env w) e ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset (env d) e ∧
        Code z e (env root) ∧ (Project.FirstOrderSemantics.reduct M).mem a (env X) ∧ PureKuratowski.PairMember M a name (env ranks) ∧
          MapRel R (fun j => env (rp j)) a e ∧ Forces true L (fun j => env (lp j)) (env P) name (env nb) z := by
  simp only [memberDecision,Formula.Realize,ForcingCohenConditions.condition_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    KuratowskiZF.source_edge,ForcingMapConditions.rel_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def consumerBody {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (I G F mul w root d fixing support X order ranks selection top z a b na nb theta ntheta beta nbeta : Fin k) : Formula k :=
  let Q := liftRelation R rp (rho 0) I (rho 2) w
  let L := orderFormula (rho 0) mul
  let sa := ForcingOrdinalCoding.selectedInput R rp X ranks a na d
  let sb := ForcingOrdinalCoding.selectedInput R rp X ranks b nb d
  let result := (typeDecision L id (rho 6) (rho 2) w top selection root d).conj
    ((sa.imp ((forces false L id (rho 6) na selection z).conj
      (sb.imp ((forces true L id (rho 6) na nb z).iff (.equal a b))))).conj
    ((checkName top theta ntheta).imp ((forces true L id (rho 6) selection ntheta z).imp
      ((sa.imp (lowerDecision L id (rho 6) (rho 2) w top na root d theta)).conj
        ((monotone R rp (rho 2) w X).imp ((checkName top beta nbeta).imp ((Formula.mem beta theta).imp
          (memberDecision L id R rp (rho 6) (rho 2) w X ranks root d nbeta))))))))
  ((ForcingConjugationGraph.subgroup I G support).conj ((Formula.mem support F).conj
    ((Source.SetLanguage.subset fixing support).conj ((ForcingWithTopCarrier.empty top).conj
      ((ForcingCohenConditions.condition (rho 2) w d).conj ((code z d root).conj
        ((ForcingOrdinalRanks.ranks Q id X order (rho 6) ranks).conj
          (ForcingCollectedName.collected Q id X ranks (rho 6) selection)))))))).imp result

def constructionSentence {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (w mu tower kappa unit mark H C incoming base I K B G F mul root d A fixing support X order ranks selection top z
      a b na nb theta ntheta beta nbeta : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp
    (ForcingOrdinalRoot.rootContext rho w mu tower kappa unit mark H C incoming base I K B G F mul root A fixing)
    (.imp (ForcingCohenSelection.covariant R rp (rho 2) w support X) (.imp
      (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound X))
      (ProjectSyntax.encode id (consumerBody R rp rho I G F mul w root d fixing support X order ranks selection top z
        a b na nb theta ntheta beta nbeta)))))
  freeClosed := by
    simp -implicitDefEqProofs [ForcingOrdinalRoot.rootContext,Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingCohenSelection.covariant_freeClosed]

theorem construction_models {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (w mu tower kappa unit mark H C incoming base I K B G F mul root d A fixing support X order ranks selection top z
      a b na nb theta ntheta beta nbeta : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence R rp rho w mu tower kappa unit mark H C incoming base I K B G F mul
      root d A fixing support X order ranks selection top z a b na nb theta ntheta beta nbeta)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [ForcingOrdinalRoot.rootContext,consumerBody,ForcingOrdinalCoding.selectedInput,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ConstructionSaturationIndex.hartogs_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingStabilizerTransport.image_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingCohenSelection.covariant_semantics hM,
    Source.Formula.iff,Formula.Realize,ForcingSupportSize.injection_semantics (M := M),
    ForcingConjugationGraph.subgroup_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),typeDecision_semantics (M := M),
    lowerDecision_semantics (M := M),memberDecision_semantics (M := M),monotone_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),KuratowskiZF.source_edge,Project.Term.eval_bound]
  rintro ⟨hw,hMu,hI,hD,hMergers,hRow,hm,hpres,hG,hF,hroot,hRange,hFix⟩ hCov hOrder
    ⟨hSupport,hSF,hsub,ht,hd,hz,hRanks,hselection⟩
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hInv := ForcingCohenSelection.lift_invariant hM R rp env rho I w hpres hCov
  have hFamily := ForcingOrdinalFixed.ranks_fixed hM (liftRelation R rp (rho 0) I (rho 2) w) env
    (fun i => env (rho i)) hpres hG hNormal hSupport hSF hInv hOrder hRanks
  have hType := ForcingOrdinalFixed.collected_fixed hM (liftRelation R rp (rho 0) I (rho 2) w) env
    (fun i => env (rho i)) hpres hG hNormal hSupport hSF hFamily hInv hselection
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hzP := code_mem hpres hd hroot hz
  have htP := (hpres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hdomain := fun name => ForcingPairUnion.domain_semantics env rho G F name
  have hcheck : ∀ x nx, Checked (env top) x nx → ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env nx := by
    intro x nx hn
    exact (hdomain nx).mpr (ForcingInfinity.check_hs hM (fun i => env (rho i)) hpres hG hNormal ht hn)
  have hlift : ∀ i, MapRel R (fun j => env (rp j)) i (env d) →
      MapRel (liftRelation R rp (rho 0) I (rho 2) w) env i (env z) := by
    intro i hi
    exact (mapRel_lift R rp env (rho 0) I (rho 2) w i (env z)).mpr ((ForcingCohenSelection.lift_coe hd hroot hz).mpr hi)
  refine ⟨orderType_decide hM hChoice env rho G F mul I w R rp hw hMu hI hD hMergers hRow hm hpres hG hF
    hroot hRange hFix ht hOrder hRanks hselection hType hsub hd hz,?_,?_⟩
  · rintro ⟨ha,han,hRa⟩
    refine ⟨ForcingOrdinalMembership.selectedRank_mem_selectionType hM hpre hselection ha han hzP (hlift (env a) hRa),?_⟩
    rintro ⟨hb,hbn,hRb⟩
    have he := ForcingOrdinalCoding.selectedRank_eq_iff hM hpre htP htop hdomain hcheck hOrder hRanks ha hb han hbn
      ((hdomain (env na)).mpr (hFamily (env a) ha (env na) han).1)
      ((hdomain (env nb)).mpr (hFamily (env b) hb (env nb) hbn).1) hzP (hlift (env a) hRa) (hlift (env b) hRb)
    exact ⟨he.mp,he.mpr⟩
  · intro hntheta htheta
    constructor
    · rintro ⟨ha,han,hRa⟩
      exact rank_decide hM hChoice env rho G F mul I w R rp hw hMu hI hD hMergers hRow hm hpres hG hF
        hroot hRange hFix ht hOrder hRanks hselection hFamily hsub hd hz ha han hRa hntheta htheta
    · intro hmono hnbeta hbeta
      exact member_rank hM hChoice env rho G F mul I w R rp hw hMu hI hD hMergers hRow hm hpres hG hF
        hroot hRange hFix ht hselection hFamily hsub hmono hd hz hntheta hnbeta hbeta htheta

theorem construction_kernel_certificate {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (w mu tower kappa unit mark H C incoming base I K B G F mul root d A fixing support X order ranks selection top z
      a b na nb theta ntheta beta nbeta : Fin k) : FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence R rp rho w mu tower kappa unit mark H C incoming base
        I K B G F mul root d A fixing support X order ranks selection top z a b na nb theta ntheta beta nbeta))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence R rp rho w mu tower kappa unit mark H C incoming base
    I K B G F mul root d A fixing support X order ranks selection top z a b na nb theta ntheta beta nbeta)
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL)
    (constructionSentence R rp rho w mu tower kappa unit mark H C incoming base I K B G F mul root d A fixing support X order
      ranks selection top z a b na nb theta ntheta beta nbeta)).mp
    (construction_models R rp rho w mu tower kappa unit mark H C incoming base I K B G F mul root d A fixing support X order
      ranks selection top z a b na nb theta ntheta beta nbeta hL hChoice)

end PPAC.Migration.ForcingCohenRankConsumers
