/- Pinned rawCost update, evaluated by the existing Raw fold on internal
(word,cost) states. The cap is indexed by the CURRENT new word, not its
letter or suffix. A total extension handles unused algebra inputs. -/
import PPAC.Migration.ConstructionProbeGateCap
import PPAC.Migration.ConstructionProbeHeightFold
import PPAC.Migration.ConstructionCutMinimum

namespace PPAC.Migration.ConstructionProbeCostOperation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionProbeRaw (Cons)
open ConstructionProbeLetters (Representatives)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Update (hM : FirstOrder.Theory.Models M nativeZF) (w Q Cap V q s v c : M.Carrier .set) : Prop :=
  ∃ d p cap, PureKuratowski.PairMember M s d V ∧ ConstructionCutProduct.Value hM w Q d v p ∧
    PureKuratowski.PairMember M q cap Cap ∧ ConstructionCutMinimum.Value p cap c

theorem update_total (hM : FirstOrder.Theory.Models M nativeZF) {w Q R W S Cap V q s v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hv : (Project.FirstOrderSemantics.reduct M).mem v R) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c R ∧ Update hM w Q Cap V q s v c := by
  obtain ⟨d,hd,_⟩ := hV.1.2 s hs
  obtain ⟨cap,hcap,_⟩ := hCap.1.2 q hq
  obtain ⟨p,hp,hprod⟩ := ConstructionCutProduct.exists_product hM hw hQ ((hR d).mp (hV.2 s d hd)) ((hR v).mp hv)
  obtain ⟨c,hc,hmin⟩ := ConstructionCutMinimum.exists_minimum hM hw hQ hp ((hR cap).mp (hCap.2 q cap hcap))
  exact ⟨c,(hR c).mpr hc,d,p,cap,hd,hprod,hcap,hmin⟩

theorem update_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q R W S Cap V q s v c c' : M.Carrier .set}
    (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (hc : Update hM w Q Cap V q s v c) (hc' : Update hM w Q Cap V q s v c') : c = c' := by
  obtain ⟨d,p,cap,hd,hp,hcap,hmin⟩ := hc
  obtain ⟨d',p',cap',hd',hp',hcap',hmin'⟩ := hc'
  have he := ForcingConditionGraphs.function_unique hV.1 hd hd'
  subst d'
  have he := ConstructionCutProduct.value_unique hM hp hp'
  subst p'
  have he := ForcingConditionGraphs.function_unique hCap.1 hcap hcap'
  subst cap'
  exact ConstructionCutMinimum.value_unique hM hmin hmin'

theorem update_range (hM : FirstOrder.Theory.Models M nativeZF) {w Q R W S Cap V q s v c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hv : (Project.FirstOrderSemantics.reduct M).mem v R) (hc : Update hM w Q Cap V q s v c) :
    (Project.FirstOrderSemantics.reduct M).mem c R := by
  obtain ⟨c',hcR,hc'⟩ := update_total hM hw hQ hR hCap hV hq hs hv
  exact (update_unique hM hCap hV hc' hc) ▸ hcR

def Initial (O C x z : M.Carrier .set) : Prop :=
  ∃ q c, PureKuratowski.PairMember M x q O ∧ PureKuratowski.PairMember M x c C ∧ PureKuratowski.Code M z q c

def Active (w D S W R s z : M.Carrier .set) : Prop :=
  ∃ t v q, (Project.FirstOrderSemantics.reduct M).mem t W ∧ (Project.FirstOrderSemantics.reduct M).mem v R ∧
    PureKuratowski.Code M z t v ∧ Cons w D S s t q ∧ (Project.FirstOrderSemantics.reduct M).mem q W

def StateValue (hM : FirstOrder.Theory.Models M nativeZF)
    (w D S W Q R Cap V default s z out : M.Carrier .set) : Prop :=
  (∃ t v q c, (Project.FirstOrderSemantics.reduct M).mem t W ∧ (Project.FirstOrderSemantics.reduct M).mem v R ∧
    PureKuratowski.Code M z t v ∧ Cons w D S s t q ∧ (Project.FirstOrderSemantics.reduct M).mem q W ∧
    Update hM w Q Cap V q s v c ∧ PureKuratowski.Code M out q c) ∨
  (¬ Active w D S W R s z ∧ out = default)

theorem state_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S W Q R Cap V default T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (hT : Representatives W R T) (hd : (Project.FirstOrderSemantics.reduct M).mem default T) (s z : M.Carrier .set) :
    ∃ out, (Project.FirstOrderSemantics.reduct M).mem out T ∧ StateValue hM w D S W Q R Cap V default s z out := by
  classical
  by_cases ha : Active w D S W R s z
  · obtain ⟨t,v,q,ht,hv,hz,hcons,hq⟩ := ha
    obtain ⟨c,hc,hup⟩ := update_total hM hw hQ hR hCap hV hq (ConstructionProbeRawAction.cons_letter hcons) hv
    obtain ⟨out,hout⟩ := KuratowskiZF.exists_code hM q c
    exact ⟨out,(hT out).mpr ⟨q,c,hq,hc,hout⟩,Or.inl ⟨t,v,q,c,ht,hv,hz,hcons,hq,hup,hout⟩⟩
  · exact ⟨default,hd,Or.inr ⟨ha,rfl⟩⟩

theorem state_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S W Q R Cap V default s z out out' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (ho : StateValue hM w D S W Q R Cap V default s z out)
    (ho' : StateValue hM w D S W Q R Cap V default s z out') : out = out' := by
  rcases ho with ⟨t,v,q,c,ht,hv,hz,hcons,hq,hup,hout⟩ | ⟨hn,he⟩
  · rcases ho' with ⟨t',v',q',c',ht',hv',hz',hcons',hq',hup',hout'⟩ | ⟨hn,_⟩
    · obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
      have he := ConstructionProbeRaw.cons_unique hM hw hcons hcons'
      subst q'
      have he := update_unique hM hCap hV hup hup'
      subst c'
      exact KuratowskiZF.code_unique hM hout hout'
    · exact (hn ⟨t,v,q,ht,hv,hz,hcons,hq⟩).elim
  · rcases ho' with ⟨t,v,q,c,ht,hv,hz,hcons,hq,hup,hout⟩ | ⟨_,he'⟩
    · exact (hn ⟨t,v,q,ht,hv,hz,hcons,hq⟩).elim
    · exact he.trans he'.symm

theorem state_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S W Q R Cap V default T s z out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (hT : Representatives W R T) (hd : (Project.FirstOrderSemantics.reduct M).mem default T)
    (ho : StateValue hM w D S W Q R Cap V default s z out) : (Project.FirstOrderSemantics.reduct M).mem out T := by
  obtain ⟨o,hoT,hv⟩ := state_total hM hw hQ hR hCap hV hT hd s z
  exact (state_unique hM hw hCap hV hv ho) ▸ hoT

def Graph (hM : FirstOrder.Theory.Models M nativeZF)
    (w D S W Q R Cap V default N G : M.Carrier .set) : Prop := ∀ s z out,
  ForcingDiagramOrder.Product G s z out ↔ (Project.FirstOrderSemantics.reduct M).mem s N ∧
    (Project.FirstOrderSemantics.reduct M).mem z N ∧ StateValue hM w D S W Q R Cap V default s z out

def update {m : Nat} (w Q Cap V q s v c : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge V.succ.succ.succ
s.succ.succ.succ (2 : Fin (m+3)))) (.conj (ConstructionCutProduct.value w.succ.succ.succ Q.succ.succ.succ (2 :
Fin (m+3)) v.succ.succ.succ (1 : Fin (m+3))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
Cap.succ.succ.succ q.succ.succ.succ (0 : Fin (m+3)))) (ConstructionCutMinimum.value (1 : Fin (m+3)) (0 : Fin
(m+3)) c.succ.succ.succ)))))))

theorem update_freeClosed {m : Nat} (w Q Cap V q s v c : Fin m) : (update w Q Cap V q s v c).FreeClosed := by
  simp -implicitDefEqProofs [update,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionCutProduct.value_freeClosed,ConstructionCutMinimum.value_freeClosed]

theorem update_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q Cap V q s v c : Fin m) :
    Project.Formula.satisfies env (update w Q Cap V q s v c) ↔ Update hM (env.bound w) (env.bound Q) (env.bound Cap) (env.bound V) (env.bound q) (env.bound s) (env.bound v) (env.bound c) := by
  simp only
    [update,Update,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionCutProduct.value_semantics
    hM,ConstructionCutMinimum.value_semantics]
  rfl

def initial {m : Nat} (O C x z : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ x.succ.succ (1 : Fin
(m+2)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ x.succ.succ (0 : Fin (m+2))))
(PureKuratowskiProject.code (.bound z.succ.succ) (.bound (1 : Fin (m+2))) (.bound (0 : Fin (m+2))))))))

theorem initial_freeClosed {m : Nat} (O C x z : Fin m) : (initial O C x z).FreeClosed := by
  simp -implicitDefEqProofs [initial,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem initial_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (O C x z : Fin m) :
    Project.Formula.satisfies env (initial O C x z) ↔ Initial (env.bound O) (env.bound C) (env.bound x) (env.bound z) := by
  simp only
    [initial,Initial,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.code_correct hM,Project.Term.eval_bound]
  rfl

def active {m : Nat} (w D S W R s z : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (.mem (.bound (2 : Fin (m+3))) (.bound W.succ.succ.succ)) (.conj (.mem
(.bound (1 : Fin (m+3))) (.bound R.succ.succ.succ)) (.conj (PureKuratowskiProject.code (.bound z.succ.succ.succ)
(.bound (2 : Fin (m+3))) (.bound (1 : Fin (m+3)))) (.conj (ConstructionProbeRaw.cons w.succ.succ.succ
D.succ.succ.succ S.succ.succ.succ s.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))) (.mem (.bound (0 : Fin
(m+3))) (.bound W.succ.succ.succ)))))))))

theorem active_freeClosed {m : Nat} (w D S W R s z : Fin m) : (active w D S W R s z).FreeClosed := by
  simp -implicitDefEqProofs [active,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ConstructionProbeRaw.cons_freeClosed]

theorem active_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S W R s z : Fin m) :
    Project.Formula.satisfies env (active w D S W R s z) ↔ Active (env.bound w) (env.bound D) (env.bound S) (env.bound W) (env.bound R) (env.bound s) (env.bound z) := by
  simp only
    [active,Active,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,KuratowskiZF.code_correct
    hM,ConstructionProbeRaw.cons_semantics hM]
  rfl

def stateValue {m : Nat} (w D S W Q R Cap V default s z out : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound (3 : Fin (m+4))) (.bound
W.succ.succ.succ.succ)) (.conj (.mem (.bound (2 : Fin (m+4))) (.bound R.succ.succ.succ.succ)) (.conj
(PureKuratowskiProject.code (.bound z.succ.succ.succ.succ) (.bound (3 : Fin (m+4))) (.bound (2 : Fin (m+4))))
(.conj (ConstructionProbeRaw.cons w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ
s.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4))) (.conj (.mem (.bound (1 : Fin (m+4))) (.bound
W.succ.succ.succ.succ)) (.conj (update w.succ.succ.succ.succ Q.succ.succ.succ.succ Cap.succ.succ.succ.succ
V.succ.succ.succ.succ (1 : Fin (m+4)) s.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4)))
(PureKuratowskiProject.code (.bound out.succ.succ.succ.succ) (.bound (1 : Fin (m+4))) (.bound (0 : Fin
(m+4)))))))))))))) (.conj (.neg (active w D S W R s z)) (Project.Formula.extensionalEq (.bound out) (.bound
default))))

theorem stateValue_freeClosed {m : Nat} (w D S W Q R Cap V default s z out : Fin m) : (stateValue w D S W Q R Cap V default s z out).FreeClosed := by
  simp -implicitDefEqProofs [stateValue,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ConstructionProbeRaw.cons_freeClosed,update_freeClosed,active_freeClosed]

theorem stateValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S W Q R Cap V default s z out : Fin m) :
    Project.Formula.satisfies env (stateValue w D S W Q R Cap V default s z out) ↔ StateValue hM (env.bound w) (env.bound D) (env.bound S) (env.bound W) (env.bound Q) (env.bound R) (env.bound Cap) (env.bound V) (env.bound default) (env.bound s) (env.bound z) (env.bound out) := by
  simp only
    [stateValue,StateValue,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq
    (ModelTransfer.extensionality hM),Project.Term.eval_bound,KuratowskiZF.code_correct
    hM,ConstructionProbeRaw.cons_semantics hM,update_semantics hM,active_semantics hM]
  rfl

def pairState {m : Nat} (w D S W Q R Cap V default p out : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound (1 : Fin (m+2))) (.bound (0
: Fin (m+2)))) (stateValue w.succ.succ D.succ.succ S.succ.succ W.succ.succ Q.succ.succ R.succ.succ Cap.succ.succ
V.succ.succ default.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)) out.succ.succ))))

theorem pairState_freeClosed {m : Nat} (w D S W Q R Cap V default p out : Fin m) : (pairState w D S W Q R Cap V default p out).FreeClosed := by
  simp -implicitDefEqProofs [pairState,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,stateValue_freeClosed]

theorem pairState_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S W Q R Cap V default p out : Fin m) :
    Project.Formula.satisfies env (pairState w D S W Q R Cap V default p out) ↔ ∃ s z, PureKuratowski.Code M (env.bound p) s z ∧ StateValue hM (env.bound w) (env.bound D) (env.bound S) (env.bound W) (env.bound Q) (env.bound R) (env.bound Cap) (env.bound V) (env.bound default) s z (env.bound out) := by
  simp only
    [pairState,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,KuratowskiZF.code_correct
    hM,stateValue_semantics hM]
  rfl

theorem exists_initial (hM : FirstOrder.Theory.Models M nativeZF) {D W R O C T : M.Carrier .set}
    (hO : MapsTo D W O) (hC : MapsTo D R C) (hT : Representatives W R T) :
    ∃ F, MapsTo D T F ∧ ∀ x z, PureKuratowski.PairMember M x z F ↔
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ Initial O C x z := by
  let schema : Project.BinarySchema 2 := { body := initial 2 3 1 0, freeClosed := initial_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases O (fun _ => C), free := fun _ => D }
  have he (x z : M.Carrier .set) : schema.denote env x z ↔ Initial O C x z :=
    initial_semantics hM ((env.push x).push z) 2 3 1 0
  obtain ⟨F,hF,hf⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := D) (target := T) (by
      intro x hx
      obtain ⟨q,hq,_⟩ := hO.1.2 x hx
      obtain ⟨c,hc,_⟩ := hC.1.2 x hx
      obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM q c
      exact ⟨z,(he x z).mpr ⟨q,c,hq,hc,hz⟩⟩) (by
      intro x _ z z' hz hz'
      obtain ⟨q,c,hq,hc,hz⟩ := (he x z).mp hz
      obtain ⟨q',c',hq',hc',hz'⟩ := (he x z').mp hz'
      have he := ForcingConditionGraphs.function_unique hO.1 hq hq'
      subst q'
      have he := ForcingConditionGraphs.function_unique hC.1 hc hc'
      subst c'
      exact KuratowskiZF.code_unique hM hz hz') (by
      intro x z _ hz
      obtain ⟨q,c,hq,hc,hz⟩ := (he x z).mp hz
      exact (hT z).mpr ⟨q,c,hO.2 x q hq,hC.2 x c hc,hz⟩)
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM D T F).mpr hF,
    fun x z => (hf x z).trans (and_congr_right (fun _ => he x z))⟩

theorem exists_operation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S W Q R Cap V default T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (hT : Representatives W R T) (hd : (Project.FirstOrderSemantics.reduct M).mem default T) (N : M.Carrier .set) :
    ∃ J G, Representatives N N J ∧ MapsTo J T G ∧ Graph hM w D S W Q R Cap V default N G := by
  obtain ⟨J,hJ⟩ := ConstructionProbeLetters.exists_representatives hM N N
  let schema : Project.BinarySchema 9 := {
    body := pairState 2 3 4 5 6 7 8 9 10 1 0
    freeClosed := pairState_freeClosed _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases W (Fin.cases Q (Fin.cases R (Fin.cases Cap (Fin.cases V (fun _ => default))))))))
    free := fun _ => w }
  have he (p out : M.Carrier .set) : schema.denote env p out ↔ ∃ s z,
      PureKuratowski.Code M p s z ∧ StateValue hM w D S W Q R Cap V default s z out :=
    pairState_semantics hM ((env.push p).push out) 2 3 4 5 6 7 8 9 10 1 0
  obtain ⟨G,hG,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := J) (target := T) (by
      intro p hp
      obtain ⟨s,z,_,_,hp⟩ := (hJ p).mp hp
      obtain ⟨out,_,ho⟩ := state_total hM hw hQ hR hCap hV hT hd s z
      exact ⟨out,(he p out).mpr ⟨s,z,hp,ho⟩⟩) (by
      intro p _ out out' ho ho'
      obtain ⟨s,z,hp,ho⟩ := (he p out).mp ho
      obtain ⟨s',z',hp',ho'⟩ := (he p out').mp ho'
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact state_unique hM hw hCap hV ho ho') (by
      intro p out _ ho
      obtain ⟨s,z,_,ho⟩ := (he p out).mp ho
      exact state_range hM hw hQ hR hCap hV hT hd ho)
  refine ⟨J,G,hJ,(ForcingSupportSize.native_mapsTo hM J T G).mpr hG,?_⟩
  intro s z out
  constructor
  · rintro ⟨p,hp,hpo⟩
    obtain ⟨s',z',hs,hz,hp'⟩ := (hJ p).mp ((hg p out).mp hpo).1
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    obtain ⟨s',z',hp',ho⟩ := (he p out).mp ((hg p out).mp hpo).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    exact ⟨hs,hz,ho⟩
  · rintro ⟨hs,hz,ho⟩
    obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM s z
    exact ⟨p,hp,(hg p out).mpr ⟨(hJ p).mpr ⟨s,z,hs,hz,hp⟩,(he p out).mpr ⟨s,z,hp,ho⟩⟩⟩

end PPAC.Migration.ConstructionProbeCostOperation
