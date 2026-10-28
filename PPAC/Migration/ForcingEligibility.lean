/- Pinned LocalRecords.classOfFormula/isClassFormula:336-347 and
AvailableRecords.EligibleName/eligibleName_congr/Eligible/eligible_ofName/
eligible_restrict. Use the unchanged pure-member graph formula and the existing
forcing tuple congruence; no semantic or preselected eligibility substitute. -/
import PPAC.Migration.ForcingLocalIntersection

namespace PPAC.Migration.ForcingEligibility
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingLocalAtomic (EqG)
open ForcingLocalQuotient (Projection)
open ForcingLocalRestriction (Restriction)
open ForcingSupportingRoot (Code exists_code code_mem code_le)
open ForcingFormula (Force)
open ForcingProductSymmetry (orderFormula_semantics)
open ForcingSupportSize (MapsTo)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}


def classOfFormula : Formula 4 :=
  .all ((Formula.mem 4 0).iff ((Formula.mem 4 1).conj (Source.SetLanguage.edge 2 3 4)))

def classOf {n : Nat} (tau A E x : Fin n) : Formula n :=
  Formula.rename (Fin.cases tau (args3 A E x)) classOfFormula

def isClassFormula : Formula 3 :=
  .ex ((Formula.mem 3 1).conj (classOf 0 1 2 3))

def isClass {n : Nat} (tau A E : Fin n) : Formula n :=
  Formula.rename (args3 tau A E) isClassFormula

def EligibleName {k : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (W g r labels E sigma : M.Carrier .set) : Prop :=
  ∃ d z, (Project.FirstOrderSemantics.reduct M).mem d g ∧ Code z d r ∧
    Force R H env (args3 sigma labels E) W z (isClass 0 1 2)

def eligibleName {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (W g r labels E sigma : Fin m) : Formula m :=
  .ex (.ex ((Formula.mem (Fin.last m).castSucc g.castSucc.castSucc).conj
    ((ForcingSupportingRoot.code (Fin.last (m+1)) (Fin.last m).castSucc r.castSucc.castSucc).conj
      (ForcingFormula.formula R H (paramsUp (paramsUp rho))
        (args3 sigma.castSucc.castSucc labels.castSucc.castSucc E.castSucc.castSucc)
        W.castSucc.castSucc (Fin.last (m+1)) (isClass 0 1 2)))))

theorem eligibleName_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (W g r labels E sigma : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (eligibleName R H rho W g r labels E sigma) ↔
      EligibleName R H (fun j => env (rho j)) (env W) (env g) (env r) (env labels) (env E) (env sigma) := by
  have ht (d z : M.Carrier .set) :
      (fun i => Fin.lastCases z (Fin.lastCases d env)
        (args3 sigma.castSucc.castSucc labels.castSucc.castSucc E.castSucc.castSucc i)) =
        args3 (env sigma) (env labels) (env E) := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i) i
    all_goals simp only [args3,args2,args1,Fin.cases_zero,Fin.cases_succ,Fin.lastCases_castSucc]
  simp only [eligibleName,EligibleName,Formula.Realize,ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  simp only [ht]
  rfl

theorem eligibleName_transport (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e g r labels E sigma tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (he : EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau)
    (hn : EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env (env (rho 6)) g r labels E sigma) :
    EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env (env (rho 6)) g r labels E tau := by
  obtain ⟨d,z,hd,hz,hforce⟩ := hn
  obtain ⟨a,t,ha,ht,heq⟩ := he
  obtain ⟨b,hb,hdb,hab⟩ := hg.2.2.2 d a hd ha
  obtain ⟨q,hq⟩ := exists_code hM b r
  have hzW := code_mem hp ((hp.2.2.1 d).mp (hg.1 d hd)) hr hz
  have hqW := code_mem hp ((hp.2.2.1 b).mp (hg.1 b hb)) hr hq
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hrr := ForcingDiagramPoset.le_refl hm hr
  have hqz := (orderFormula_semantics env (rho 0) mul q z).mpr ((code_le hq hz).mpr ⟨hdb,hrr⟩)
  have hqt := (orderFormula_semantics env (rho 0) mul q t).mpr ((code_le hq ht).mpr ⟨hab,hrr⟩)
  have heq' := ForcingAtomicBasic.eq_mono hM hpre hqW hqt heq
  have htuple : ∀ i : Fin 3, ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env
      (env (rho 6)) (args3 sigma labels E i) (args3 tau labels E i) q := by
    intro i
    exact Fin.cases heq' (fun i => Fin.cases (ForcingAtomicBasic.eq_refl hM hpre labels q hqW)
      (fun i => Fin.cases (ForcingAtomicBasic.eq_refl hM hpre E q hqW) (fun i => Fin.elim0 i) i) i) i
  exact ⟨b,q,hb,hq,(ForcingFormula.tuple_congr hM hpre (isClass 0 1 2)
    (args3 sigma labels E) (args3 tau labels E) q hqW htuple).mp
      (ForcingFormula.mono hM hpre (isClass 0 1 2) (args3 sigma labels E) hzW hqW hqz hforce)⟩

theorem eligibleName_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e g r labels E sigma tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (he : EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau) :
    EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E sigma ↔
      EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E tau :=
  ⟨eligibleName_transport hM env rho G F mul hm hp hg hr he,
    eligibleName_transport hM env rho G F mul hm hp hg hr (ForcingLocalAtomic.eqG_symm hM he)⟩

theorem eligibleName_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e g r s labels E sigma : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (hs : ForcingSupportSize.Injection (env (rho 0)) I s)
    (hsr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r)
    (hn : EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E sigma) :
    EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g s labels E sigma := by
  obtain ⟨d,z,hd,hz,hforce⟩ := hn
  have hdC := (hp.2.2.1 d).mp (hg.1 d hd)
  obtain ⟨q,hq⟩ := exists_code hM d s
  have hzW := code_mem hp hdC hr hz
  have hqW := code_mem hp hdC hs hq
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact ⟨d,q,hd,hq,ForcingFormula.mono hM hpre (isClass 0 1 2) (args3 sigma labels E) hzW hqW
    ((orderFormula_semantics env (rho 0) mul q z).mpr ((code_le hq hz).mpr ⟨fun _ h => h,hsr⟩)) hforce⟩

def Eligible {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (W g r labels E pr cls : M.Carrier .set) : Prop :=
  ∃ sigma, PureKuratowski.PairMember M sigma cls pr ∧ EligibleName R H env W g r labels E sigma

def eligible {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (W g r labels E pr cls : Fin m) : Formula m :=
  .ex ((Source.SetLanguage.edge pr.castSucc (Fin.last m) cls.castSucc).conj
    (eligibleName R H (paramsUp rho) W.castSucc g.castSucc r.castSucc labels.castSucc E.castSucc (Fin.last m)))

theorem eligible_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (W g r labels E pr cls : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (eligible R H rho W g r labels E pr cls) ↔
      Eligible R H (fun j => env (rho j)) (env W) (env g) (env r) (env labels) (env E) (env pr) (env cls) := by
  simp only [eligible,Eligible,Formula.Realize,KuratowskiZF.source_edge,eligibleName_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem eligible_ofName (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e g r labels E X pr sigma cls : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (hPr : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X pr)
    (hsc : PureKuratowski.PairMember M sigma cls pr) :
    Eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E pr cls ↔
      EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E sigma := by
  constructor
  · rintro ⟨tau,htc,ht⟩
    exact eligibleName_transport hM env rho G F mul hm hp hg hr
      ((ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hr hPr tau sigma cls cls htc hsc).mp rfl) ht
  · exact fun h => ⟨sigma,hsc,h⟩

theorem eligible_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e g r s labels E X pr ps f x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (hs : ForcingSupportSize.Injection (env (rho 0)) I s)
    (hsr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r)
    (hPr : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X pr)
    (hRestr : Restriction pr ps f) (hxy : PureKuratowski.PairMember M x y f)
    (hx : Eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g r labels E pr x) :
    Eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) g s labels E ps y := by
  obtain ⟨sigma,hsx,hsy⟩ := (hRestr x y).mp hxy
  have hn := (eligible_ofName hM env rho G F mul hm hp hg hr hPr hsx).mp hx
  exact ⟨sigma,hsy,eligibleName_restrict hM env rho G F mul hm hp hg hr hs hsr hn⟩


def representativeSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r labels E X pr sigma cls : Fin k) : Source.Sentence :=
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e).imp ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp ((Source.SetLanguage.injection r (rho 0) I).imp ((ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g r X pr).imp ((Source.SetLanguage.edge pr sigma cls).imp (((eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E pr cls).iff (eligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E sigma))))))))).close

theorem representative_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r labels E X pr sigma cls : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (representativeSentence rho I K B w e G F mul g r labels E X pr sigma cls)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hg hr hPr hsc
  have h := eligible_ofName hM env rho G F mul (labels := env labels) (E := env E)
    ((ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul e).mp hm)
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg)
    ((ForcingSupportSize.injection_semantics (M := M) env r (rho 0) I).mp hr)
    ((ForcingLocalQuotient.projection_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6) g r X pr).mp hPr)
    ((KuratowskiZF.source_edge (M := M) env pr sigma cls).mp hsc)
  have hl := eligible_semantics (M := M) env (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E pr cls
  have hr' := eligibleName_semantics (M := M) env (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E sigma
  exact ⟨fun he => hr'.mpr (h.mp (hl.mp he)),fun he => hl.mpr (h.mpr (hr'.mp he))⟩

theorem representative_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r labels E X pr sigma cls : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (representativeSentence rho I K B w e G F mul g r labels E X pr sigma cls)) :=
  ModelTransfer.derives (fun _ hM => representative_models rho I K B w e G F mul g r labels E X pr sigma cls hM)

def restrictionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s labels E X pr ps f x y : Fin k) : Source.Sentence :=
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e).imp ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp ((Source.SetLanguage.injection r (rho 0) I).imp ((Source.SetLanguage.injection s (rho 0) I).imp ((ForcingDiagramOrder.le (rho 0) mul s r).imp ((ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g r X pr).imp ((ForcingLocalRestriction.restriction pr ps f).imp ((Source.SetLanguage.edge f x y).imp ((eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E pr x).imp ((eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g s labels E ps y)))))))))))).close

theorem restriction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s labels E X pr ps f x y : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (restrictionSentence rho I K B w e G F mul g r s labels E X pr ps f x y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hg hr hs hsr hPr hRestr hxy hx
  have h := eligible_restrict hM env rho G F mul
    ((ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul e).mp hm)
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg)
    ((ForcingSupportSize.injection_semantics (M := M) env r (rho 0) I).mp hr)
    ((ForcingSupportSize.injection_semantics (M := M) env s (rho 0) I).mp hs)
    ((ForcingDiagramOrder.le_semantics (M := M) env (rho 0) mul s r).mp hsr)
    ((ForcingLocalQuotient.projection_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6) g r X pr).mp hPr)
    ((ForcingLocalRestriction.restriction_semantics (M := M) env pr ps f).mp hRestr)
    ((KuratowskiZF.source_edge (M := M) env f x y).mp hxy)
    ((eligible_semantics (M := M) env (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g r labels E pr x).mp hx)
  exact (eligible_semantics (M := M) env (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) g s labels E ps y).mpr h

theorem restriction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s labels E X pr ps f x y : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (restrictionSentence rho I K B w e G F mul g r s labels E X pr ps f x y)) :=
  ModelTransfer.derives (fun _ hM => restriction_models rho I K B w e G F mul g r s labels E X pr ps f x y hM)

end PPAC.Migration.ForcingEligibility
