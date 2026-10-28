/- Pinned QuotientTransport.LocalQuotient.transportEquiv and transport_restrict.
Descend the actual name action through the existing native class projections.
The target uses the moved Cohen filter and moved supporting diagram. -/
import PPAC.Migration.ForcingLocalNameTransport
import PPAC.Migration.ForcingLocalRestriction

namespace PPAC.Migration.ForcingLocalQuotientTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingStabilizer (Action)
open ForcingLocalQuotient (Classes Projection EqualityLaw)
open ForcingLocalAtomic (EqG)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ImageClass (W a pr ps c d : M.Carrier .set) : Prop :=
  ∃ sigma tau, PureKuratowski.PairMember M sigma c pr ∧ Action W a sigma tau ∧ PureKuratowski.PairMember M tau d ps

def imageClass {k : Nat} (W a pr ps c d : Fin k) : Formula k :=
  .ex (.ex ((Source.SetLanguage.edge pr.castSucc.castSucc (Fin.last k).castSucc c.castSucc.castSucc).conj
    ((ForcingStabilizer.action W.castSucc.castSucc a.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))).conj
      (Source.SetLanguage.edge ps.castSucc.castSucc (Fin.last (k+1)) d.castSucc.castSucc))))

theorem imageClass_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W a pr ps c d : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (imageClass W a pr ps c d) ↔
      ImageClass (env W) (env a) (env pr) (env ps) (env c) (env d) := by
  simp only [imageClass,ImageClass,Formula.Realize,KuratowskiZF.source_edge,ForcingStabilizer.action_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Graph (W a pr ps f : M.Carrier .set) : Prop :=
  ∀ c d, PureKuratowski.PairMember M c d f ↔ ImageClass W a pr ps c d

def graph {k : Nat} (W a pr ps f : Fin k) : Formula k :=
  .all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))).iff
    (imageClass W.castSucc.castSucc a.castSucc.castSucc pr.castSucc.castSucc ps.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1)))))

theorem graph_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W a pr ps f : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (graph W a pr ps f) ↔
      Graph (env W) (env a) (env pr) (env ps) (env f) := by
  simp only [graph,Graph,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,imageClass_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h c d => ⟨(h c d).1,(h c d).2⟩,fun h c d => ⟨(h c d).mp,(h c d).mpr⟩⟩

/-- Reuse the native function constructor and existing exact projections.
The relation quantifies over all representatives and never selects one. -/
theorem exists_transport (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {W a g gT r s X Y Q T pr ps nf : M.Carrier .set}
    (hnf : MapsTo X Y nf) (hnGraph : ForcingLocalNameTransport.Graph W a X nf)
    (hnOnto : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y Y →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x y nf)
    (hpr : MapsTo X Q pr) (hps : MapsTo Y T ps)
    (hQ : Classes R env W g r X Q) (hT : Classes R env W gT s Y T)
    (hPr : Projection R env W g r X pr) (hPs : Projection R env W gT s Y ps)
    (hEr : EqualityLaw R env W g r pr) (hEs : EqualityLaw R env W gT s ps)
    (hEq : ∀ sigma tau sigmaT tauT, Action W a sigma sigmaT → Action W a tau tauT →
      (EqG R env W gT s sigmaT tauT ↔ EqG R env W g r sigma tau)) :
    ∃ f, Injection Q T f ∧ Graph W a pr ps f ∧
      ∀ d, (Project.FirstOrderSemantics.reduct M).mem d T →
        ∃ c, (Project.FirstOrderSemantics.reduct M).mem c Q ∧ PureKuratowski.PairMember M c d f := by
  let params : Fin 4 → M.Carrier .set := Fin.cases W (Fin.cases a (Source.SetLanguage.args2 pr ps))
  let query := imageClass (0 : Fin 6) 1 2 3 4 5
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 :=
    { bound := fun i => params i.rev, free := fun _ => Q }
  have hRel : ∀ c d, (ProjectSyntax.binary query).denote penv c d ↔ ImageClass W a pr ps c d := by
    intro c d
    rw [ForcingMapConditions.binary_semantics hM query params Q c d]
    simp only [ForcingMapConditions.MapRel,query,imageClass_semantics (M := M),params]
    rfl
  have ht : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c Q →
      ∃ d, (ProjectSyntax.binary query).denote penv c d := by
    intro c hc
    obtain ⟨sigma,hs,hsc⟩ := ForcingLocalQuotient.projection_onto hQ hPr hc
    obtain ⟨tau,hst,_⟩ := hnf.1.2 sigma hs
    obtain ⟨d,htd,_⟩ := hps.1.2 tau (hnf.2 sigma tau hst)
    exact ⟨d,(hRel c d).mpr ⟨sigma,tau,hsc,((hnGraph sigma tau).mp hst).2,htd⟩⟩
  have hu : ∀ c d e, (ProjectSyntax.binary query).denote penv c d →
      (ProjectSyntax.binary query).denote penv c e → d = e := by
    intro c d e hd he
    obtain ⟨sigma,sigmaT,hsc,hs,hsd⟩ := (hRel c d).mp hd
    obtain ⟨tau,tauT,htc,ht,hte⟩ := (hRel c e).mp he
    exact (hEs sigmaT tauT d e hsd hte).mpr
      ((hEq sigma tau sigmaT tauT hs ht).mpr ((hEr sigma tau c c hsc htc).mp rfl))
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) penv (source := Q) (target := T)
    ht (fun c _ d e hd he => hu c d e hd he) (by
      intro c d _ hd
      obtain ⟨_,tau,_,_,htd⟩ := (hRel c d).mp hd
      exact hps.2 tau d htd)
  have hGraph : Graph W a pr ps f := by
    intro c d
    exact (he c d).trans ⟨fun h => (hRel c d).mp h.2,fun h => by
      obtain ⟨sigma,tau,hsc,hs,htd⟩ := h
      exact ⟨hpr.2 sigma c hsc,(hRel c d).mpr ⟨sigma,tau,hsc,hs,htd⟩⟩⟩
  refine ⟨f,⟨(ForcingSupportSize.native_mapsTo hM Q T f).mpr hf,?_⟩,hGraph,?_⟩
  · intro c d e hce hde
    obtain ⟨sigma,sigmaT,hsc,hs,hse⟩ := (hGraph c e).mp hce
    obtain ⟨tau,tauT,htd,ht,hte⟩ := (hGraph d e).mp hde
    exact (hEr sigma tau c d hsc htd).mpr
      ((hEq sigma tau sigmaT tauT hs ht).mp ((hEs sigmaT tauT e e hse hte).mp rfl))
  · intro d hd
    obtain ⟨tau,ht,htd⟩ := ForcingLocalQuotient.projection_onto hT hPs hd
    obtain ⟨sigma,hs,hst⟩ := hnOnto tau ht
    obtain ⟨c,hsc,_⟩ := hpr.1.2 sigma hs
    exact ⟨c,hpr.2 sigma c hsc,(hGraph c d).mpr ⟨sigma,tau,hsc,((hnGraph sigma tau).mp hst).2,htd⟩⟩

theorem transport_ofName {W a pr ps f sigma tau c d : M.Carrier .set}
    (hf : Graph W a pr ps f) (hc : PureKuratowski.PairMember M sigma c pr)
    (hAct : Action W a sigma tau) (hd : PureKuratowski.PairMember M tau d ps) : PureKuratowski.PairMember M c d f :=
  (hf c d).mpr ⟨sigma,tau,hc,hAct,hd⟩

/-- Literal naturality: the witness name is unchanged by restriction and
has the same coordinate image on both sides of the square. -/
theorem transport_restrict {W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e : M.Carrier .set}
    (hnf : MapsTo X Y nf) (hnGraph : ForcingLocalNameTransport.Graph W a X nf)
    (hYY : ForcingPowerName.Subset Y YS)
    (hpr : MapsTo X Q pr) (hprT : MapsTo Y T prT) (hpsT : MapsTo YS TS psT)
    (hfr : MapsTo Q T fr) (hfs : MapsTo QS TS fs)
    (hFr : Graph W a pr prT fr) (hFs : Graph W a ps psT fs)
    (hSr : ForcingLocalRestriction.Restriction pr ps sr) (hSt : ForcingLocalRestriction.Restriction prT psT st)
    (hcd : PureKuratowski.PairMember M c d sr) (hcb : PureKuratowski.PairMember M c b fr)
    (hde : PureKuratowski.PairMember M d e fs) : PureKuratowski.PairMember M b e st := by
  obtain ⟨sigma,hsc,hsd⟩ := (hSr c d).mp hcd
  have hs := ForcingConditionGraphs.function_input hpr.1 hsc
  obtain ⟨tau,hst,_⟩ := hnf.1.2 sigma hs
  have ht := hnf.2 sigma tau hst
  have hAct := ((hnGraph sigma tau).mp hst).2
  obtain ⟨b',htb,_⟩ := hprT.1.2 tau ht
  obtain ⟨e',hte,_⟩ := hpsT.1.2 tau (hYY tau ht)
  have hb : b' = b := ForcingConditionGraphs.function_unique hfr.1 (transport_ofName hFr hsc hAct htb) hcb
  have he : e' = e := ForcingConditionGraphs.function_unique hfs.1 (transport_ofName hFs hsd hAct hte) hde
  subst b'
  subst e'
  exact (hSt b e).mpr ⟨tau,htb,hte⟩


def QuotientResult {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W a g gT r rT X Y : M.Carrier .set) : Prop :=
  ∃ Q T pr ps f, MapsTo X Q pr ∧ MapsTo Y T ps ∧ Classes R env W g r X Q ∧ Classes R env W gT rT Y T ∧
    Projection R env W g r X pr ∧ Projection R env W gT rT Y ps ∧ Injection Q T f ∧ Graph W a pr ps f ∧
    ∀ d, (Project.FirstOrderSemantics.reduct M).mem d T →
      ∃ c, (Project.FirstOrderSemantics.reduct M).mem c Q ∧ PureKuratowski.PairMember M c d f

def Result {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a : Fin k)
    (pi g r rT X Y : M.Carrier .set) : Prop := ∃ ac gT,
  ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac ∧
    ForcingStabilizerTransport.Image ac g gT ∧ ForcingLocalAtomic.CohenFilter (env (rho 3)) gT ∧
    QuotientResult (orderFormula (rho 0) mul) env (env (rho 6)) (env a) g gT r rT X Y

/-- Actual product forcing supplies name transport and EqG symmetry; the
previously constructed native classes supply both quotients and projections. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a : Fin k)
    {I K B w e G F mu pi inv c ai bound J JT H HT X Y g r rT : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w G F mu pi inv c (env a) ai)
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) G bound)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : Injection (env (rho 0)) I r) (hrT : Injection (env (rho 0)) I rT)
    (hComp : ForcingConditionGraphs.CompositionGraph (env (rho 0)) pi r rT)
    (hJ : ForcingSupportedNames.Range (env (rho 0)) r J) (hImage : ForcingStabilizerTransport.Image pi J JT)
    (hH : ForcingLabelPermutations.Fixing G J H) (hHT : ForcingLabelPermutations.Fixing G JT HT)
    (hX : ForcingLocalNames.Carrier (fun j => env (rho j)) G F bound H X)
    (hY : ForcingLocalNames.Carrier (fun j => env (rho j)) G F bound HT Y) : Result env rho mul a pi g r rT X Y := by
  have hJI : ForcingPowerName.Subset J I := by
    intro y hy
    obtain ⟨x,_,hxy⟩ := (hJ y).mp hy
    exact hr.1.2 x y hxy
  obtain ⟨nf,hnf,hnGraph,hnOnto⟩ := ForcingLocalNameTransport.exists_graph hM hData hBound hJI hImage hH hHT hX hY
  obtain ⟨ac,gT,hac,hgImage,hgT,hLaw⟩ := ForcingLocalTransport.construct hM env rho mul a hData.1 hData.2.2.1 hData.2.2.2.2.2.2.2.1 hg
  obtain ⟨Q,pr,hpr,hQ,hPr⟩ := ForcingLocalQuotient.exists_quotient hM (orderFormula (rho 0) mul) env (env (rho 6)) g r X
  obtain ⟨T,ps,hps,hT,hPs⟩ := ForcingLocalQuotient.exists_quotient hM (orderFormula (rho 0) mul) env (env (rho 6)) gT rT Y
  obtain ⟨f,hf,hGraph,hOnto⟩ := exists_transport hM hnf.1 hnGraph hnOnto hpr hps hQ hT hPr hPs
    (ForcingLocalQuotient.equality_law hM env rho mul hm hData.1 hg hr hPr)
    (ForcingLocalQuotient.equality_law hM env rho mul hm hData.1 hgT hrT hPs)
    (fun sigma tau sigmaT tauT hs ht => hLaw r rT sigma tau sigmaT tauT hr hrT hComp
      ((ForcingNameConjugacy.action_iff env (rho 6) a sigma sigmaT).mpr hs)
      ((ForcingNameConjugacy.action_iff env (rho 6) a tau tauT).mpr ht))
  exact ⟨ac,gT,hac,hgImage,hgT,Q,T,pr,ps,f,hpr,hps,hQ,hT,hPr,hPs,hf,hGraph,hOnto⟩

def quotientResult {k m : Nat} (R : Formula (k+2)) (rho : Fin k → Fin m)
    (W a g gT r rT X Y : Fin m) : Formula m :=
  let up := fun j : Fin m => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr := fun j => up (rho j)
  let Q := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let T := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let pr := (Fin.last (m+2)).castSucc.castSucc
  let ps := (Fin.last (m+3)).castSucc
  let f := Fin.last (m+4)
  let onto : Formula (m+5) := .all ((Formula.mem (Fin.last (m+5)) T.castSucc).imp
    (.ex ((Formula.mem (Fin.last (m+6)) Q.castSucc.castSucc).conj
      (Source.SetLanguage.edge f.castSucc.castSucc (Fin.last (m+6)) ((Fin.last (m+5)).castSucc)))))
  let body := (Source.SetLanguage.mapsTo pr (up X) Q).conj
    ((Source.SetLanguage.mapsTo ps (up Y) T).conj
      ((ForcingLocalQuotient.classes R rr (up W) (up g) (up r) (up X) Q).conj
        ((ForcingLocalQuotient.classes R rr (up W) (up gT) (up rT) (up Y) T).conj
          ((ForcingLocalQuotient.projection R rr (up W) (up g) (up r) (up X) pr).conj
            ((ForcingLocalQuotient.projection R rr (up W) (up gT) (up rT) (up Y) ps).conj
              ((Source.SetLanguage.injection f Q T).conj ((graph (up W) (up a) pr ps f).conj onto)))))))
  .ex (.ex (.ex (.ex (.ex body))))

theorem quotientResult_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (k+2)) (rho : Fin k → Fin m)
    (W a g gT r rT X Y : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (quotientResult R rho W a g gT r rT X Y) ↔
      QuotientResult R (fun j => env (rho j)) (env W) (env a) (env g) (env gT) (env r) (env rT) (env X) (env Y) := by
  simp only [quotientResult,QuotientResult,Formula.Realize,ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingLocalQuotient.classes_semantics (M := M),
    ForcingLocalQuotient.projection_semantics (M := M),graph_semantics (M := M),KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def result {k : Nat} (rho : Fin 7 → Fin k) (mul a pi g r rT X Y : Fin k) : Formula k :=
  let up := fun j : Fin k => j.castSucc.castSucc
  let ac := (Fin.last k).castSucc
  let gT := Fin.last (k+1)
  .ex (.ex ((ForcingLocalTransport.cohenPart (up (rho 1)) (up (rho 2)) (up (rho 3)) (up pi) ac).conj
    ((ForcingStabilizerTransport.image ac (up g) gT).conj
      ((ForcingLocalAtomic.cohenFilter (up (rho 3)) gT).conj
        (quotientResult (orderFormula (rho 0) mul) up (up (rho 6)) (up a) (up g) gT (up r) (up rT) (up X) (up Y))))))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (mul a pi g r rT X Y : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (result rho mul a pi g r rT X Y) ↔
      Result env rho mul a (env pi) (env g) (env r) (env rT) (env X) (env Y) := by
  simp only [result,Result,Formula.Realize,ForcingLocalTransport.cohenPart_semantics (M := M),
    ForcingStabilizerTransport.image_semantics (M := M),ForcingLocalAtomic.cohenFilter_semantics (M := M),
    quotientResult_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT : Fin k) : Source.Sentence :=
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e).imp ((ForcingProductCovariance.systemData rho I K B w G F mu pi inv c a ai).imp ((ForcingEquivariantMix.fixedAll rho G bound).imp ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp ((Source.SetLanguage.injection r (rho 0) I).imp ((Source.SetLanguage.injection rT (rho 0) I).imp ((ForcingConditionGraphs.compositionGraph (rho 0) pi r rT).imp ((ForcingSupportedNames.range (rho 0) r J).imp ((ForcingStabilizerTransport.image pi J JT).imp ((ForcingLabelPermutations.fixing G J H).imp ((ForcingLabelPermutations.fixing G JT HT).imp ((ForcingLocalNames.carrier rho G F bound H X).imp ((ForcingLocalNames.carrier rho G F bound HT Y).imp (result rho mul a pi g r rT X Y)))))))))))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hData hBound hg hr hrT hComp hJ hImage hH hHT hX hY
  exact (result_semantics env rho mul a pi g r rT X Y).mpr (construct hM env rho mul a
    ((ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul e).mp hm)
    ((ForcingProductCovariance.systemData_semantics (M := M) env rho I K B w G F mu pi inv c a ai).mp hData)
    ((ForcingSupportedNames.supported_semantics (M := M) env rho G bound).mp hBound)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg)
    ((ForcingSupportSize.injection_semantics (M := M) env r (rho 0) I).mp hr)
    ((ForcingSupportSize.injection_semantics (M := M) env rT (rho 0) I).mp hrT)
    ((ForcingConditionGraphs.compositionGraph_semantics (M := M) env (rho 0) pi r rT).mp hComp)
    ((ForcingSupportedNames.range_semantics (M := M) env (rho 0) r J).mp hJ)
    ((ForcingStabilizerTransport.image_semantics (M := M) env pi J JT).mp hImage)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env G J H).mp hH)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env G JT HT).mp hHT)
    ((ForcingLocalNames.carrier_semantics (M := M) env rho G F bound H X).mp hX)
    ((ForcingLocalNames.carrier_semantics (M := M) env rho G F bound HT Y).mp hY))

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT hM)

def naturalitySentence {k : Nat} (W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e : Fin k) : Source.Sentence :=
  ((Source.SetLanguage.mapsTo nf X Y).imp ((ForcingLocalNameTransport.graph W a X nf).imp ((Source.SetLanguage.subset Y YS).imp ((Source.SetLanguage.mapsTo pr X Q).imp ((Source.SetLanguage.mapsTo prT Y T).imp ((Source.SetLanguage.mapsTo psT YS TS).imp ((Source.SetLanguage.mapsTo fr Q T).imp ((Source.SetLanguage.mapsTo fs QS TS).imp ((graph W a pr prT fr).imp ((graph W a ps psT fs).imp ((ForcingLocalRestriction.restriction pr ps sr).imp ((ForcingLocalRestriction.restriction prT psT st).imp ((Source.SetLanguage.edge sr c d).imp ((Source.SetLanguage.edge fr c b).imp ((Source.SetLanguage.edge fs d e).imp (Source.SetLanguage.edge st b e)))))))))))))))).close

theorem naturality_models {k : Nat} (W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e : Fin k)
    (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (naturalitySentence W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hnf hnGraph hYY hpr hprT hpsT hfr hfs hFr hFs hSr hSt hcd hcb hde
  exact (KuratowskiZF.source_edge (M := M) env st b e).mpr (transport_restrict
    ((ForcingSupportSize.mapsTo_semantics (M := M) env nf X Y).mp hnf)
    ((ForcingLocalNameTransport.graph_semantics (M := M) env W a X nf).mp hnGraph)
    ((ForcingLabelPermutations.subset_semantics (M := M) env Y YS).mp hYY)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env pr X Q).mp hpr)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env prT Y T).mp hprT)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env psT YS TS).mp hpsT)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env fr Q T).mp hfr)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env fs QS TS).mp hfs)
    ((graph_semantics (M := M) env W a pr prT fr).mp hFr)
    ((graph_semantics (M := M) env W a ps psT fs).mp hFs)
    ((ForcingLocalRestriction.restriction_semantics (M := M) env pr ps sr).mp hSr)
    ((ForcingLocalRestriction.restriction_semantics (M := M) env prT psT st).mp hSt)
    ((KuratowskiZF.source_edge (M := M) env sr c d).mp hcd)
    ((KuratowskiZF.source_edge (M := M) env fr c b).mp hcb)
    ((KuratowskiZF.source_edge (M := M) env fs d e).mp hde))

theorem naturality_kernel_certificate {k : Nat} (W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (naturalitySentence W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e)) :=
  ModelTransfer.derives (fun _ hM => naturality_models W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e hM)

end PPAC.Migration.ForcingLocalQuotientTransport
