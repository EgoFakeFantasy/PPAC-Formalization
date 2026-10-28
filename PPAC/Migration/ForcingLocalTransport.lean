/- Pinned QuotientTransport.local_eq_transport_iff:65-88.
Move the actual Cohen filter by its existing condition permutation. Reuse
actual Product action, moved_code and full atomic symmetry; no fixed-filter
substitute or new name/forcing recursion. -/
import PPAC.Migration.ForcingLocalQuotient

namespace PPAC.Migration.ForcingLocalTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingSupportSize (Injection)
open ForcingStabilizerTransport (Image)
open ForcingLocalAtomic (CohenFilter EqG)
open ForcingProductFamily (Presentation Action)
open ForcingProductSymmetry (orderFormula)
open ForcingMapConditions (Mapped)
open ForcingSupportingRoot (Code)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The literal Cohen part of the same coordinate permutation. -/
def CohenPart (C S X pi ac : M.Carrier .set) : Prop :=
  ∃ f t, Permutation C f ∧ ForcingCohenCoordinates.Graph C pi f ∧
    Permutation S t ∧ ForcingCohenCoordinates.Graph S f t ∧
    Permutation X ac ∧ ForcingCohenOrderAction.ActionGraph X t ac

theorem part_of_action {D C S X Y P W pi a : M.Carrier .set}
    (h : Action D C S X Y P W pi a) : ∃ ac, CohenPart C S X pi ac := by
  obtain ⟨f,t,ac,_,_,hf,hfg,ht,htg,hac,hacg,_⟩ := h
  exact ⟨ac,f,t,hf,hfg,ht,htg,hac,hacg⟩

theorem part_permutation {C S X pi ac : M.Carrier .set} (h : CohenPart C S X pi ac) : Permutation X ac := by
  obtain ⟨_,_,_,_,_,_,h,_⟩ := h
  exact h

theorem image_mem_iff {X ac g g' d d' : M.Carrier .set} (hac : Permutation X ac)
    (hIm : Image ac g g') (hd : PureKuratowski.PairMember M d d' ac) :
    (Project.FirstOrderSemantics.reduct M).mem d' g' ↔ (Project.FirstOrderSemantics.reduct M).mem d g := by
  constructor
  · intro h
    obtain ⟨e,he,hed⟩ := (hIm d').mp h
    exact hac.2.1 e d d' hed hd ▸ he
  · intro h
    exact (hIm d').mpr ⟨d,h,hd⟩

theorem filter_image {X ac g g' : M.Carrier .set} (hac : Permutation X ac)
    (ho : ForcingCohenOrderAction.OrderPreserving ac) (hg : CohenFilter X g) (hIm : Image ac g g') :
    CohenFilter X g' := by
  refine ⟨?_,?_,?_,?_⟩
  · intro d' hd'
    obtain ⟨d,_,hdd⟩ := (hIm d').mp hd'
    exact hac.1.2 d d' hdd
  · obtain ⟨d,hd⟩ := hg.2.1
    obtain ⟨d',hdd,_⟩ := hac.1.1.2 d (hg.1 d hd)
    exact ⟨d',(hIm d').mpr ⟨d,hd,hdd⟩⟩
  · intro d' q' hd' hq' hsub
    obtain ⟨d,hd,hdd⟩ := (hIm d').mp hd'
    obtain ⟨q,hq,hqq⟩ := hac.2.2 q' hq'
    exact (hIm q').mpr ⟨q,hg.2.2.1 d q hd hq ((ho d q d' q' hdd hqq).mp hsub),hqq⟩
  · intro d' e' hd' he'
    obtain ⟨d,hd,hdd⟩ := (hIm d').mp hd'
    obtain ⟨e,he,hee⟩ := (hIm e').mp he'
    obtain ⟨f,hf,hdf,hef⟩ := hg.2.2.2 d e hd he
    obtain ⟨f',hff,_⟩ := hac.1.1.2 f (hg.1 f hf)
    exact ⟨f',(hIm f').mpr ⟨f,hf,hff⟩,(ho f d f' d' hff hdd).mpr hdf,(ho f e f' e' hff hee).mpr hef⟩

theorem moved_code (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi a ac d d' r R z z' : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (ha : Action D C S X Y P W pi a)
    (hc : CohenPart C S X pi ac) (hdd : PureKuratowski.PairMember M d d' ac)
    (hr : Injection D I r) (hR : Injection D I R) (hComp : CompositionGraph D pi r R)
    (hz : Code z d r) (hz' : Code z' d' R) : PureKuratowski.PairMember M z z' a := by
  obtain ⟨f,t,hf,hfg,ht,htg,_,hacg⟩ := hc
  obtain ⟨hd,hd',him⟩ := (hacg d d').mp hdd
  have hdC := (hp.2.2.1 d).mp hd
  have hMoved : ConstructionDescentPlacement.ActualMoved C S w pi d d' :=
    ⟨f,t,hf,hfg,ht,htg,(hp.2.2.1 d').mp hd',him,
      ConstructionCohenCompatibility.moved_of_image hM hp.1 hp.2.1 hfg htg hdC him⟩
  exact ForcingSupportingRoot.moved_code hM hp ha hdC hr hR hMoved hComp hz hz'

/-- The two filters and diagrams both move; all internal names are covered. -/
theorem local_eq_transport_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a : Fin k)
    {I K B w pi ac g g' r R sigma tau sigma' tau' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hpi : Permutation I pi)
    (ha : Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) pi (env a))
    (hc : CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hg : CohenFilter (env (rho 3)) g) (hIm : Image ac g g')
    (hr : Injection (env (rho 0)) I r) (hR : Injection (env (rho 0)) I R)
    (hComp : CompositionGraph (env (rho 0)) pi r R)
    (hs : Mapped (ForcingConditionAction.actFormula (rho 6) a) env sigma sigma')
    (ht : Mapped (ForcingConditionAction.actFormula (rho 6) a) env tau tau') :
    EqG (orderFormula (rho 0) mul) env (env (rho 6)) g' R sigma' tau' ↔
      EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau := by
  have hac := part_permutation hc
  have haPerm := ForcingProductFamily.action_permutation ha
  have ho := ForcingProductFamily.order hM (env mul) hp hpi ha
  have hOrder : ForcingAtomicSymmetry.OrderOn (orderFormula (rho 0) mul) env (env (rho 6)) (env a) := by
    intro x y x' y' hx hy hxx hyy
    rw [ForcingProductSymmetry.orderFormula_semantics,ForcingProductSymmetry.orderFormula_semantics]
    exact (ho x y x' y' ((ForcingConditionAction.act_inside hx).mp hxx) ((ForcingConditionAction.act_inside hy).mp hyy)).symm
  have hSym := ForcingAtomicSymmetry.atomic_symmetry hM (ForcingConditionAction.actFormula (rho 6) a)
    (orderFormula (rho 0) mul) env (env (rho 6)) (ForcingAtomicSymmetry.action_transport _ env (rho 6) a haPerm hOrder) sigma tau
  have hAt : ∀ d d' z z', (Project.FirstOrderSemantics.reduct M).mem d g →
      PureKuratowski.PairMember M d d' ac → Code z d r → Code z' d' R →
      (ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma tau z ↔
        ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma' tau' z') := by
    intro d d' z z' hd hdd hz hz'
    have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp (hg.1 d hd)) hr hz
    have hzz := moved_code hM hp ha hc hdd hr hR hComp hz hz'
    exact (hSym sigma' tau' z z' hs ht hzW
      ((ForcingConditionAction.relation_semantics env (rho 6) a z z').mpr ((ForcingConditionAction.act_inside hzW).mpr hzz))).2
  constructor
  · rintro ⟨d',z',hd',hz',he⟩
    obtain ⟨d,hd,hdd⟩ := (hIm d').mp hd'
    obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM d r
    exact ⟨d,z,hd,hz,(hAt d d' z z' hd hdd hz hz').mpr he⟩
  · rintro ⟨d,z,hd,hz,he⟩
    obtain ⟨d',hdd,_⟩ := hac.1.1.2 d (hg.1 d hd)
    obtain ⟨z',hz'⟩ := ForcingSupportingRoot.exists_code hM d' R
    exact ⟨d',z',(hIm d').mpr ⟨d,hd,hdd⟩,hz',(hAt d d' z z' hd hdd hz hz').mp he⟩


def Law {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a : Fin k)
    (I pi g g' : M.Carrier .set) : Prop := ∀ r R sigma tau sigma' tau',
  Injection (env (rho 0)) I r → Injection (env (rho 0)) I R → CompositionGraph (env (rho 0)) pi r R →
  Mapped (ForcingConditionAction.actFormula (rho 6) a) env sigma sigma' →
  Mapped (ForcingConditionAction.actFormula (rho 6) a) env tau tau' →
  (EqG (orderFormula (rho 0) mul) env (env (rho 6)) g' R sigma' tau' ↔
    EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau)

def Result {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a : Fin k)
    (I pi g : M.Carrier .set) : Prop := ∃ ac g',
  CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac ∧ Image ac g g' ∧
    CohenFilter (env (rho 3)) g' ∧ Law env rho mul a I pi g g'

theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a : Fin k)
    {I K B w pi g : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hpi : Permutation I pi)
    (ha : Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) pi (env a))
    (hg : CohenFilter (env (rho 3)) g) : Result env rho mul a I pi g := by
  obtain ⟨ac,hc⟩ := part_of_action ha
  have hac := part_permutation hc
  obtain ⟨g',hIm,_⟩ := ForcingLabelConjugacy.exists_image hM hac.1 (J := g)
  have ho : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨_,t,_,_,ht,_,_,hacg⟩ := hc
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hacg
  refine ⟨ac,g',hc,hIm,filter_image hac ho hg hIm,?_⟩
  intro r R sigma tau sigma' tau' hr hR hComp hs ht
  exact local_eq_transport_iff hM env rho mul a hp hpi ha hc hg hIm hr hR hComp hs ht

def cohenPart {m : Nat} (C S X pi ac : Fin m) : Formula m :=
  let up := fun i : Fin m => i.castSucc.castSucc
  let f := (Fin.last m).castSucc
  let t := Fin.last (m+1)
  .ex (.ex ((ForcingConditionGraphs.permutation (up C) f).conj
    ((ForcingCohenCoordinates.graph (up C) (up pi) f).conj
      ((ForcingConditionGraphs.permutation (up S) t).conj
        ((ForcingCohenCoordinates.graph (up S) f t).conj
          ((ForcingConditionGraphs.permutation (up X) (up ac)).conj
            (ForcingCohenOrderAction.actionGraph (up X) t (up ac))))))))

theorem cohenPart_semantics {m : Nat} (env : Fin m → M.Carrier .set) (C S X pi ac : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (cohenPart C S X pi ac) ↔
      CohenPart (env C) (env S) (env X) (env pi) (env ac) := by
  simp only [cohenPart,CohenPart,Formula.Realize,ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingCohenCoordinates.graph_semantics (M := M),ForcingCohenOrderAction.actionGraph_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def law {k m : Nat} (rho : Fin 7 → Fin k) (mul a : Fin k) (rr : Fin k → Fin m)
    (I pi g g' : Fin m) : Formula m :=
  let up := fun i : Fin m => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let ur := fun j => up (rr j)
  let r := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc
  let R := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc
  let sigma := (Fin.last (m+2)).castSucc.castSucc.castSucc
  let tau := (Fin.last (m+3)).castSucc.castSucc
  let sigma' := (Fin.last (m+4)).castSucc
  let tau' := Fin.last (m+5)
  .all (.all (.all (.all (.all (.all
    ((Source.SetLanguage.injection r (ur (rho 0)) (up I)).imp
      ((Source.SetLanguage.injection R (ur (rho 0)) (up I)).imp
        ((ForcingConditionGraphs.compositionGraph (ur (rho 0)) (up pi) r R).imp
          ((ForcingMapConditions.mapping (ForcingConditionAction.actFormula (rho 6) a) ur sigma sigma').imp
            ((ForcingMapConditions.mapping (ForcingConditionAction.actFormula (rho 6) a) ur tau tau').imp
              ((ForcingLocalAtomic.eqG (orderFormula (rho 0) mul) ur (ur (rho 6)) (up g') R sigma' tau').iff
                (ForcingLocalAtomic.eqG (orderFormula (rho 0) mul) ur (ur (rho 6)) (up g) r sigma tau))))))))))))

theorem law_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a : Fin k)
    (rr : Fin k → Fin m) (I pi g g' : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (law rho mul a rr I pi g g') ↔
      Law (fun j => env (rr j)) rho mul a (env I) (env pi) (env g) (env g') := by
  simp only [law,Law,Source.Formula.iff,Formula.Realize,ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingMapConditions.mapping_semantics (M := M),
    ForcingLocalAtomic.eqG_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h r R sigma tau sigma' tau' hr hR hc hs ht
    exact ⟨(h r R sigma tau sigma' tau' hr hR hc hs ht).1,(h r R sigma tau sigma' tau' hr hR hc hs ht).2⟩
  · intro h r R sigma tau sigma' tau' hr hR hc hs ht
    exact ⟨(h r R sigma tau sigma' tau' hr hR hc hs ht).mp,(h r R sigma tau sigma' tau' hr hR hc hs ht).mpr⟩

def result {k : Nat} (rho : Fin 7 → Fin k) (mul a I pi g : Fin k) : Formula k :=
  let up := fun i : Fin k => i.castSucc.castSucc
  let ac := (Fin.last k).castSucc
  let g' := Fin.last (k+1)
  .ex (.ex ((cohenPart (up (rho 1)) (up (rho 2)) (up (rho 3)) (up pi) ac).conj
    ((ForcingStabilizerTransport.image ac (up g) g').conj
      ((ForcingLocalAtomic.cohenFilter (up (rho 3)) g').conj (law rho mul a up (up I) (up pi) (up g) g')))))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul a I pi g : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (result rho mul a I pi g) ↔
      Result env rho mul a (env I) (env pi) (env g) := by
  simp only [result,Result,Formula.Realize,cohenPart_semantics (M := M),ForcingStabilizerTransport.image_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),law_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (mul a I K B w pi g : Fin k) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingConditionGraphs.permutation I pi).imp
      ((ForcingProductFamily.action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) pi a).imp
        ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp (result rho mul a I pi g))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (mul a I K B w pi g : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho mul a I K B w pi g)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hpi ha hg
  exact (result_semantics env rho mul a I pi g).mpr (construct hM env rho mul a
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingConditionGraphs.permutation_semantics (M := M) env I pi).mp hpi)
    ((ForcingProductFamily.action_semantics (M := M) env (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) pi a).mp ha)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg))

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (mul a I K B w pi g : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho mul a I K B w pi g)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho mul a I K B w pi g hM)


/-- Consume the existing actual action constructor; no action graph is postulated. -/
def assemblySentence {k : Nat} (rho : Fin 7 → Fin k) (mul I K B w pi g : Fin k) : Source.Sentence :=
  let up : Fin k → Fin (k+1) := Fin.castSucc
  let rr := fun j => up (rho j)
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingConditionGraphs.permutation I pi).imp ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp
      (.ex ((ForcingProductFamily.action (rr 0) (rr 1) (rr 2) (rr 3) (rr 4) (rr 5) (rr 6) (up pi) (Fin.last k)).conj
        (result rr (up mul) (Fin.last k) (up I) (up pi) (up g))))))).close

theorem assembly_models {k : Nat} (rho : Fin 7 → Fin k) (mul I K B w pi g : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (assemblySentence rho mul I K B w pi g)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hpi hg
  have hpres := (ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp
  have hperm := (ForcingConditionGraphs.permutation_semantics (M := M) env I pi).mp hpi
  have hfilter := (ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg
  obtain ⟨a,ha⟩ := ForcingProductFamily.exists_action hM hpres hperm
  refine ⟨a,?_,?_⟩
  · apply (ForcingProductFamily.action_semantics (M := M) (Fin.lastCases a env)
      (rho 0).castSucc (rho 1).castSucc (rho 2).castSucc (rho 3).castSucc (rho 4).castSucc (rho 5).castSucc (rho 6).castSucc pi.castSucc (Fin.last k)).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using ha
  · apply (result_semantics (Fin.lastCases a env) (fun j => (rho j).castSucc) mul.castSucc (Fin.last k) I.castSucc pi.castSucc g.castSucc).mpr
    simp only [Fin.lastCases_castSucc]
    refine construct hM (Fin.lastCases a env) (fun j => (rho j).castSucc) mul.castSucc (Fin.last k)
      (I := env I) (K := env K) (B := env B) (w := env w) (pi := env pi) (g := env g) ?_ hperm ?_ ?_
    · simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hpres
    · simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using ha
    · simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hfilter

theorem assembly_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (mul I K B w pi g : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (assemblySentence rho mul I K B w pi g)) :=
  ModelTransfer.derives (fun _ hM => assembly_models rho mul I K B w pi g hM)

end PPAC.Migration.ForcingLocalTransport
