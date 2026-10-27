/- Pinned MonoidRounds.Round.step and ConstructionIteration.structureWithTime.
The original chosen successor becomes a definable unique COMPLETE tuple in
the SAME internal L, using its existing set-like Jensen order. Both original
requests, their witnesses and the exact fromBase composition are retained.
This is the successor-selector consumed by the ordinal iteration; it is
not a claim that the full tower or internal Con has already been built. -/
import PPAC.Migration.ConstructionRoundFresh
import PPAC.Migration.ConstructibleSource

namespace PPAC.Migration.ConstructionRoundSelection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRoundFields ConstructionRoundSuccessors
open ConstructionRequestSchedule (ProbeCode MergerCode Request)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Fixed nine-field output; no Type-level choice of its components. -/
def Pack (W G e mark H C O base roots output : M.Carrier .set) : Prop :=
  ∃ t1 t2 t3 t4 t5 t6 t7,
    PureKuratowski.Code M output W t1 ∧ PureKuratowski.Code M t1 G t2 ∧
    PureKuratowski.Code M t2 e t3 ∧ PureKuratowski.Code M t3 mark t4 ∧
    PureKuratowski.Code M t4 H t5 ∧ PureKuratowski.Code M t5 C t6 ∧
    PureKuratowski.Code M t6 O t7 ∧ PureKuratowski.Code M t7 base roots

theorem pack_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (W G e mark H C O base roots : M.Carrier .set) :
    ∃ output, Pack W G e mark H C O base roots output := by
  obtain ⟨t7,h7⟩ := KuratowskiZF.exists_code hM base roots
  obtain ⟨t6,h6⟩ := KuratowskiZF.exists_code hM O t7
  obtain ⟨t5,h5⟩ := KuratowskiZF.exists_code hM C t6
  obtain ⟨t4,h4⟩ := KuratowskiZF.exists_code hM H t5
  obtain ⟨t3,h3⟩ := KuratowskiZF.exists_code hM mark t4
  obtain ⟨t2,h2⟩ := KuratowskiZF.exists_code hM e t3
  obtain ⟨t1,h1⟩ := KuratowskiZF.exists_code hM G t2
  obtain ⟨output,h0⟩ := KuratowskiZF.exists_code hM W t1
  exact ⟨output,t1,t2,t3,t4,t5,t6,t7,h0,h1,h2,h3,h4,h5,h6,h7⟩

theorem pack_injective {W G e mark H C O base roots W' G' e' mark' H' C' O' base' roots' output : M.Carrier .set}
    (hp : Pack W G e mark H C O base roots output)
    (hq : Pack W' G' e' mark' H' C' O' base' roots' output) :
    W = W' ∧ G = G' ∧ e = e' ∧ mark = mark' ∧ H = H' ∧ C = C' ∧
      O = O' ∧ base = base' ∧ roots = roots' := by
  obtain ⟨t1,t2,t3,t4,t5,t6,t7,h0,h1,h2,h3,h4,h5,h6,h7⟩ := hp
  obtain ⟨s1,s2,s3,s4,s5,s6,s7,g0,g1,g2,g3,g4,g5,g6,g7⟩ := hq
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h0 g0
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h1 g1
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h2 g2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h3 g3
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h4 g4
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h5 g5
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h6 g6
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective h7 g7
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def Done (w D mul zero one request W G mark O base roots : M.Carrier .set) : Prop :=
  ConstructionRoundFresh.Completed w D mul zero one request W G mark O base roots

def Candidate (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : M.Carrier .set) : Prop :=
  ∃ W G unitW markW HL LC O baseW roots,
    Pack W G unitW markW HL LC O baseW roots output ∧
    ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
    Done w D mul zero one request W G markW O baseW roots

def Picked (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : M.Carrier .set) : Prop :=
  (Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output ∧
    ∀ other, Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request other →
      ¬ InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M) other output) ∨
  (¬ (∃ other, Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request other)) ∧ output = zero

theorem candidate_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f request : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObjD : ObjectFields hM w Q R top D mul e mark H C)
    (hObjN : ObjectFields hM w Q R top N mulN eN markN HN CN)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f)
    (hq : Request w D mul e zero one request) :
    ∃ output, Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output := by
  rcases hq with ⟨a,b,node,hCode,hb,hne,hPath⟩ | ⟨n,P,hCode,hn,hnp,hP,hValid⟩
  · obtain ⟨W,G,unitW,markW,HL,LC,O,baseW,gen,hStep,hDone,hFresh⟩ :=
      ConstructionRoundFresh.probe hM hw hz hzw hQ hR hu hone htop hObjN hf hb hne hPath
    obtain ⟨output,hPack⟩ := pack_exists hM W G unitW markW HL LC O baseW gen
    exact ⟨output,W,G,unitW,markW,HL,LC,O,baseW,gen,hPack,hStep,Or.inl ⟨a,b,node,hCode,hDone,hFresh⟩⟩
  · obtain ⟨W,G,unitW,markW,HL,LC,O,baseW,roots,hStep,hDone,hFresh⟩ :=
      ConstructionRoundFresh.merger hM hw hz hzw hQ hR hu hone htop hObjD hObjN hf hn hnp hP hValid
    obtain ⟨output,hPack⟩ := pack_exists hM W G unitW markW HL LC O baseW roots
    exact ⟨output,W,G,unitW,markW,HL,LC,O,baseW,roots,hPack,hStep,Or.inr ⟨n,P,hCode,hDone,hFresh⟩⟩

def pack {m : Nat} (W G e mark H C O base roots output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (PureKuratowskiProject.code
  (.bound output.succ.succ.succ.succ.succ.succ.succ) (.bound W.succ.succ.succ.succ.succ.succ.succ) (.bound
  (6 : Fin (m+7)))) (.conj (PureKuratowskiProject.code (.bound (6 : Fin (m+7))) (.bound
  G.succ.succ.succ.succ.succ.succ.succ) (.bound (5 : Fin (m+7)))) (.conj (PureKuratowskiProject.code (.bound
  (5 : Fin (m+7))) (.bound e.succ.succ.succ.succ.succ.succ.succ) (.bound (4 : Fin (m+7)))) (.conj
  (PureKuratowskiProject.code (.bound (4 : Fin (m+7))) (.bound mark.succ.succ.succ.succ.succ.succ.succ)
  (.bound (3 : Fin (m+7)))) (.conj (PureKuratowskiProject.code (.bound (3 : Fin (m+7))) (.bound
  H.succ.succ.succ.succ.succ.succ.succ) (.bound (2 : Fin (m+7)))) (.conj (PureKuratowskiProject.code (.bound
  (2 : Fin (m+7))) (.bound C.succ.succ.succ.succ.succ.succ.succ) (.bound (1 : Fin (m+7)))) (.conj
  (PureKuratowskiProject.code (.bound (1 : Fin (m+7))) (.bound O.succ.succ.succ.succ.succ.succ.succ) (.bound
  (0 : Fin (m+7)))) (PureKuratowskiProject.code (.bound (0 : Fin (m+7))) (.bound
  base.succ.succ.succ.succ.succ.succ.succ) (.bound roots.succ.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem pack_freeClosed {m : Nat} (W G e mark H C O base roots output : Fin m) :
    (pack W G e mark H C O base roots output).FreeClosed := by
  simp -implicitDefEqProofs [pack,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem pack_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W G e mark H C O base roots output : Fin m) :
    Project.Formula.satisfies env (pack W G e mark H C O base roots output) ↔ Pack (env.bound W) (env.bound G) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound O) (env.bound base) (env.bound roots) (env.bound output) := by
  simp only [pack,Pack,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    KuratowskiZF.code_correct hM]
  rfl


def done {m : Nat} (w D mul zero one request W G mark O base roots : Fin m) : Project.Formula 1 m :=
  ConstructionRoundFresh.completed w D mul zero one request W G mark O base roots

theorem done_freeClosed {m : Nat} (w D mul zero one request W G mark O base roots : Fin m) :
    (done w D mul zero one request W G mark O base roots).FreeClosed :=
  ConstructionRoundFresh.completed_freeClosed _ _ _ _ _ _ _ _ _ _ _ _

theorem done_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D mul zero one request W G mark O base roots : Fin m) :
    Project.Formula.satisfies env (done w D mul zero one request W G mark O base roots) ↔
      Done (env.bound w) (env.bound D) (env.bound mul) (env.bound zero) (env.bound one) (env.bound request)
        (env.bound W) (env.bound G) (env.bound mark) (env.bound O) (env.bound base) (env.bound roots) :=
  ConstructionRoundFresh.completed_semantics hM env _ _ _ _ _ _ _ _ _ _ _ _


def candidate {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (pack (8 :
  Fin (m+9)) (7 : Fin (m+9)) (6 : Fin (m+9)) (5 : Fin (m+9)) (4 : Fin (m+9)) (3 : Fin (m+9)) (2 : Fin (m+9))
  (1 : Fin (m+9)) (0 : Fin (m+9)) output.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionRoundStepSyntax.step w.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ mark.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ
  eN.succ.succ.succ.succ.succ.succ.succ.succ.succ markN.succ.succ.succ.succ.succ.succ.succ.succ.succ
  HN.succ.succ.succ.succ.succ.succ.succ.succ.succ CN.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (7 : Fin (m+9)) (6 : Fin (m+9)) (5 : Fin
  (m+9)) (4 : Fin (m+9)) (3 : Fin (m+9)) (2 : Fin (m+9)) (1 : Fin (m+9))) (done
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ request.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 :
  Fin (m+9)) (7 : Fin (m+9)) (5 : Fin (m+9)) (2 : Fin (m+9)) (1 : Fin (m+9)) (0 : Fin (m+9))))))))))))))

theorem candidate_freeClosed {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : Fin m) :
    (candidate w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output).FreeClosed := by
  simp -implicitDefEqProofs [candidate,Definitional.Formula.FreeClosed,pack_freeClosed,ConstructionRoundStepSyntax.step_freeClosed,done_freeClosed]

theorem candidate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : Fin m) :
    Project.Formula.satisfies env (candidate w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output) ↔ Candidate hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) (env.bound f) (env.bound request) (env.bound output) := by
  simp only [candidate,Candidate,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    pack_semantics hM,ConstructionRoundStepSyntax.step_semantics hM,done_semantics hM]
  rfl

def picked {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (candidate w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output)
  (.forallE (.imp (candidate w.succ Q.succ R.succ top.succ zero.succ one.succ D.succ mul.succ e.succ
  mark.succ H.succ C.succ N.succ mulN.succ eN.succ markN.succ HN.succ CN.succ f.succ request.succ (0 : Fin
  (m+1))) (.neg (InnerModel.js_less_m (.bound (0 : Fin (m+1))) (.bound output.succ)))))) (.conj (.neg
  (.existsE (candidate w.succ Q.succ R.succ top.succ zero.succ one.succ D.succ mul.succ e.succ mark.succ
  H.succ C.succ N.succ mulN.succ eN.succ markN.succ HN.succ CN.succ f.succ request.succ (0 : Fin (m+1)))))
  (Project.Formula.extensionalEq (.bound output) (.bound zero))))

theorem picked_freeClosed {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : Fin m) :
    (picked w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output).FreeClosed := by
  simp -implicitDefEqProofs [picked,Definitional.Formula.FreeClosed,candidate_freeClosed,InnerModel.js_less_m_freeClosed,Project.Formula.extensionalEq]

theorem picked_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : Fin m) :
    Project.Formula.satisfies env (picked w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output) ↔ Picked hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) (env.bound f) (env.bound request) (env.bound output) := by
  simp only [picked,Picked,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_disj_iff,candidate_semantics hM,InnerModel.js_less_formula_l (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


theorem picked_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request x y : M.Carrier .set}
    (hx : Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request x) (hy : Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request y) : x = y := by
  rcases hx with ⟨hx,hxmin⟩ | ⟨hnx,rfl⟩
  · rcases hy with ⟨hy,hymin⟩ | ⟨hny,_⟩
    · rcases hOrder.2.2.1 x y with he | hxy | hyx
      · exact he
      · exact False.elim (hymin x hx hxy)
      · exact False.elim (hxmin y hy hyx)
    · exact False.elim (hny ⟨x,hx⟩)
  · rcases hy with ⟨hy,_⟩ | ⟨_,rfl⟩
    · exact False.elim (hnx ⟨y,hy⟩)
    · rfl

/-- Total even on invalid stage/input data. Separation is applied only to
a set initial segment plus ONE existing candidate, never to a proper class. -/
theorem picked_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request : M.Carrier .set) :
    ∃ output, Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output ∧
      ∀ other, Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request other → other = output := by
  classical
  let rawM := Project.FirstOrderSemantics.reduct M
  let schema : Project.UnarySchema 20 := {
    body := candidate (0 : Fin 20).succ (1 : Fin 20).succ (2 : Fin 20).succ (3 : Fin 20).succ (4 : Fin 20).succ (5 : Fin 20).succ (6 : Fin 20).succ (7 : Fin 20).succ (8 : Fin 20).succ (9 : Fin 20).succ (10 : Fin 20).succ (11 : Fin 20).succ (12 : Fin 20).succ (13 : Fin 20).succ (14 : Fin 20).succ (15 : Fin 20).succ (16 : Fin 20).succ (17 : Fin 20).succ (18 : Fin 20).succ (19 : Fin 20).succ (0 : Fin 21)
    freeClosed := candidate_freeClosed .. }
  let env : SetTheory.Env rawM 20 := { bound := Fin.cases w (Fin.cases Q (Fin.cases R (Fin.cases top (Fin.cases zero (Fin.cases one (Fin.cases D (Fin.cases mul (Fin.cases e (Fin.cases mark (Fin.cases H (Fin.cases C (Fin.cases N (Fin.cases mulN (Fin.cases eN (Fin.cases markN (Fin.cases HN (Fin.cases CN (Fin.cases f (fun _ => request))))))))))))))))))), free := fun _ => zero }
  have he (output) : schema.denote env output ↔ Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output := by
    exact candidate_semantics hM (env.push output) (0 : Fin 20).succ (1 : Fin 20).succ (2 : Fin 20).succ (3 : Fin 20).succ (4 : Fin 20).succ (5 : Fin 20).succ (6 : Fin 20).succ (7 : Fin 20).succ (8 : Fin 20).succ (9 : Fin 20).succ (10 : Fin 20).succ (11 : Fin 20).succ (12 : Fin 20).succ (13 : Fin 20).succ (14 : Fin 20).succ (15 : Fin 20).succ (16 : Fin 20).succ (17 : Fin 20).succ (18 : Fin 20).succ (19 : Fin 20).succ (0 : Fin 21)
  by_cases hn : ∃ output, Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output
  · obtain ⟨first,hfirst⟩ := hn
    obtain ⟨initial,hInitial⟩ := hOrder.2.2.2.2 first
    obtain ⟨bound,hBound⟩ := KP.exists_insert (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) initial first
    obtain ⟨candidates,hCandidates⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env bound
    have hIn (x) : rawM.mem x candidates ↔ rawM.mem x bound ∧ Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request x :=
      (hCandidates x).trans (and_congr_right fun _ => he x)
    have hFirst : rawM.mem first candidates := (hIn first).mpr ⟨(hBound first).mpr (Or.inr rfl),hfirst⟩
    obtain ⟨output,hOutput,hMin⟩ := hOrder.2.2.2.1 candidates ⟨first,hFirst⟩
    have hCandidate := ((hIn output).mp hOutput).2
    have hNoPrior : ∀ other, Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request other →
        ¬ InnerModel.Js_lt_d (M := rawM) other output := by
      intro other hOther hlt
      have hBoundOther : rawM.mem other bound := by
        apply (hBound other).mpr
        apply Or.inl
        apply (hInitial other).mpr
        rcases hMin first hFirst with heq | hltFirst
        · exact heq ▸ hlt
        · exact hOrder.2.1 other output first hlt hltFirst
      rcases hMin other ((hIn other).mpr ⟨hBoundOther,hOther⟩) with heq | hForward
      · exact hOrder.1 output (heq.symm ▸ hlt)
      · exact hOrder.1 output (hOrder.2.1 output other output hForward hlt)
    have hPick : Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output := Or.inl ⟨hCandidate,hNoPrior⟩
    exact ⟨output,hPick,fun other hOther => picked_unique hM hOrder hOther hPick⟩
  · have hPick : Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request zero := Or.inr ⟨hn,rfl⟩
    exact ⟨zero,hPick,fun other hOther => picked_unique hM hOrder hOther hPick⟩

theorem picked_is_candidate (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output : M.Carrier .set}
    (hn : ∃ other, Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request other)
    (hp : Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output) : Candidate hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output := by
  rcases hp with ⟨hc,_⟩ | ⟨hno,_⟩
  · exact hc
  · exact False.elim (hno hn)


def totalSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 20 (.existsE (.conj (picked (0 : Fin 20).succ (1 : Fin 20).succ (2 : Fin
    20).succ (3 : Fin 20).succ (4 : Fin 20).succ (5 : Fin 20).succ (6 : Fin 20).succ (7 : Fin 20).succ (8 :
    Fin 20).succ (9 : Fin 20).succ (10 : Fin 20).succ (11 : Fin 20).succ (12 : Fin 20).succ (13 : Fin
    20).succ (14 : Fin 20).succ (15 : Fin 20).succ (16 : Fin 20).succ (17 : Fin 20).succ (18 : Fin 20).succ
    (19 : Fin 20).succ (0 : Fin 21)) (.forallE (.imp (picked (0 : Fin 20).succ.succ (1 : Fin 20).succ.succ
    (2 : Fin 20).succ.succ (3 : Fin 20).succ.succ (4 : Fin 20).succ.succ (5 : Fin 20).succ.succ (6 : Fin
    20).succ.succ (7 : Fin 20).succ.succ (8 : Fin 20).succ.succ (9 : Fin 20).succ.succ (10 : Fin
    20).succ.succ (11 : Fin 20).succ.succ (12 : Fin 20).succ.succ (13 : Fin 20).succ.succ (14 : Fin
    20).succ.succ (15 : Fin 20).succ.succ (16 : Fin 20).succ.succ (17 : Fin 20).succ.succ (18 : Fin
    20).succ.succ (19 : Fin 20).succ.succ (0 : Fin 22)) (Project.Formula.extensionalEq (.bound (0 : Fin 22))
    (.bound (0 : Fin 21).succ)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,picked_freeClosed,Project.Formula.extensionalEq]

theorem total_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence totalSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) totalSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,picked_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  exact picked_total hM hOrder (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5) (bound 6) (bound 7) (bound 8) (bound 9) (bound 10) (bound 11) (bound 12) (bound 13) (bound 14) (bound 15) (bound 16) (bound 17) (bound 18) (bound 19)

def stepSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 21 (.imp (Project.Formula.isOmega (.bound (0 : Fin 21))) (.imp
    (Project.Formula.isEmpty (.bound (4 : Fin 21))) (.imp (.mem (.bound (4 : Fin 21)) (.bound (0 : Fin 21)))
    (.imp (ConstructionFractionOrder.carrier (0 : Fin 21) (1 : Fin 21)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 21) (1 : Fin 21) (2 : Fin 21)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 21) (20 : Fin 21) (5 : Fin 21) (5 : Fin 21)) (.imp
    (Project.Formula.isOrdinalOne (.bound (5 : Fin 21))) (.imp (ConstructionRealCuts.principal (0 : Fin 21)
    (1 : Fin 21) (20 : Fin 21) (3 : Fin 21)) (.imp (ConstructionRoundStepSyntax.objectFields (0 : Fin 21) (1
    : Fin 21) (2 : Fin 21) (3 : Fin 21) (6 : Fin 21) (7 : Fin 21) (8 : Fin 21) (9 : Fin 21) (10 : Fin 21)
    (11 : Fin 21)) (.imp (ConstructionRoundStepSyntax.objectFields (0 : Fin 21) (1 : Fin 21) (2 : Fin 21) (3
    : Fin 21) (12 : Fin 21) (13 : Fin 21) (14 : Fin 21) (15 : Fin 21) (16 : Fin 21) (17 : Fin 21)) (.imp
    (ConstructionRoundStepSyntax.mapFields (0 : Fin 21) (1 : Fin 21) (6 : Fin 21) (12 : Fin 21) (7 : Fin 21)
    (13 : Fin 21) (8 : Fin 21) (14 : Fin 21) (9 : Fin 21) (15 : Fin 21) (10 : Fin 21) (11 : Fin 21) (16 :
    Fin 21) (17 : Fin 21) (18 : Fin 21)) (.imp (ConstructionRequestSchedule.request (0 : Fin 21) (6 : Fin
    21) (7 : Fin 21) (8 : Fin 21) (4 : Fin 21) (5 : Fin 21) (19 : Fin 21)) (.existsE (.conj (picked (0 : Fin
    21).succ (1 : Fin 21).succ (2 : Fin 21).succ (3 : Fin 21).succ (4 : Fin 21).succ (5 : Fin 21).succ (6 :
    Fin 21).succ (7 : Fin 21).succ (8 : Fin 21).succ (9 : Fin 21).succ (10 : Fin 21).succ (11 : Fin 21).succ
    (12 : Fin 21).succ (13 : Fin 21).succ (14 : Fin 21).succ (15 : Fin 21).succ (16 : Fin 21).succ (17 : Fin
    21).succ (18 : Fin 21).succ (19 : Fin 21).succ (0 : Fin 22)) (.conj (candidate (0 : Fin 21).succ (1 :
    Fin 21).succ (2 : Fin 21).succ (3 : Fin 21).succ (4 : Fin 21).succ (5 : Fin 21).succ (6 : Fin 21).succ
    (7 : Fin 21).succ (8 : Fin 21).succ (9 : Fin 21).succ (10 : Fin 21).succ (11 : Fin 21).succ (12 : Fin
    21).succ (13 : Fin 21).succ (14 : Fin 21).succ (15 : Fin 21).succ (16 : Fin 21).succ (17 : Fin 21).succ
    (18 : Fin 21).succ (19 : Fin 21).succ (0 : Fin 22)) (.forallE (.imp (picked (0 : Fin 21).succ.succ (1 :
    Fin 21).succ.succ (2 : Fin 21).succ.succ (3 : Fin 21).succ.succ (4 : Fin 21).succ.succ (5 : Fin
    21).succ.succ (6 : Fin 21).succ.succ (7 : Fin 21).succ.succ (8 : Fin 21).succ.succ (9 : Fin
    21).succ.succ (10 : Fin 21).succ.succ (11 : Fin 21).succ.succ (12 : Fin 21).succ.succ (13 : Fin
    21).succ.succ (14 : Fin 21).succ.succ (15 : Fin 21).succ.succ (16 : Fin 21).succ.succ (17 : Fin
    21).succ.succ (18 : Fin 21).succ.succ (19 : Fin 21).succ.succ (0 : Fin 23))
    (Project.Formula.extensionalEq (.bound (0 : Fin 23)) (.bound (0 : Fin 22).succ))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,picked_freeClosed,candidate_freeClosed,
      Project.Formula.extensionalEq,Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.isOrdinalOne,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,
      ConstructionRequestSchedule.request_freeClosed]

theorem step_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence stepSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) stepSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,
    ConstructionRealCuts.principal_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRequestSchedule.request_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    picked_semantics hM,candidate_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  intro hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq
  obtain ⟨output,hPick,hUnique⟩ := picked_total hM hOrder (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5) (bound 6) (bound 7) (bound 8) (bound 9) (bound 10) (bound 11) (bound 12) (bound 13) (bound 14) (bound 15) (bound 16) (bound 17) (bound 18) (bound 19)
  have hExists := candidate_exists hM hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq
  exact ⟨output,hPick,picked_is_candidate hM hExists hPick,hUnique⟩

/-- Consume the existing full L theorem; no ambient global-choice axiom. -/
theorem l_order (hM : FirstOrder.Theory.Models M nativeZF) :
    Project.Gw_order_d (InnerModel.Js_lt_d
      (M := Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM))) := by
  classical
  let rawL := Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)
  let env : SetTheory.Env rawL 0 := ⟨Fin.elim0,fun _ => Classical.choice rawL.nonempty⟩
  have hL := ConstructibleSource.model_zf hM
  have hSentence : rawL.SatisfiesSentence InnerModel.js_universe_s :=
    InnerModel.js_l_model_l (ZF.models_kpi_l (ModelTransfer.project_models_iff.mp hM))
  have hGw := (Project.gw_sentence_sat_l (ModelTransfer.extensionality hL) InnerModel.js_less_s.schema env).mp
    ((Structure.satisfiesSentence_iff rawL InnerModel.js_universe_s).mp hSentence env.free)
  simpa only [Project.Gw_order_d,InnerModel.js_less_sat_l (ZF.modelsKP (ModelTransfer.project_models_iff.mp hL))] using hGw

theorem total_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative totalSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM totalSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) totalSentence).mp
    (total_models (ConstructibleSource.model_zf hM) (l_order hM))

theorem step_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative stepSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM stepSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) stepSentence).mp
    (step_models (ConstructibleSource.model_zf hM) (l_order hM))

end PPAC.Migration.ConstructionRoundSelection
