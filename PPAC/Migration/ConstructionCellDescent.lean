/- Pinned ProbeGates.append_old_exit_isOld/Gate.append_old (211-254),
   then ConcreteQuotients.Cell.descent_gate (18-45).
   Actual consumer: Attachment.gateStep and CellTower.finite_descent.
   Reuse internal Raw induction, the existing Word multiplication, exact
   exit gates and merger old-factor reflection. -/
import PPAC.Migration.ConstructionPersistentProfiles
import PPAC.Migration.ConstructionMergerOldEmbedding
import PPAC.Migration.ForcingSupportedNames

namespace PPAC.Migration.ConstructionCellDescent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeOldEmbedding (OldGraph old_word old_dvd_iff_headDiv)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeEvaluation (Eval eval_cons_forward eval_old_forward eval_word)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def OldExit (w D S zero W G q : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem q W → ∀ s d od z,
    HeadSome w D S q s → Old zero D d od → Product G q od z →
      ¬ HeadSome w D S z s → ∃ y, Old zero D y z

def oldExit {m : Nat} (w D S zero W G q : Fin m) : Project.Formula 1 m :=
  (.imp (.mem (.bound q) (.bound W)) (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionProbeGatesSyntax.headSome w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ q.succ.succ.succ.succ 3) (.imp (ConstructionProbeRaw.old zero.succ.succ.succ.succ D.succ.succ.succ.succ 2 1) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ.succ q.succ.succ.succ.succ 1 0)) (.imp (.neg (ConstructionProbeGatesSyntax.headSome w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ 0 3)) (.existsE (ConstructionProbeRaw.old zero.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ 0 1)))))))))))

theorem oldExit_freeClosed {m : Nat} (w D S zero W G q : Fin m) :
    (oldExit w D S zero W G q).FreeClosed := by
  simp -implicitDefEqProofs [oldExit,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeGatesSyntax.headSome_freeClosed,ConstructionProbeRaw.old_freeClosed]

theorem oldExit_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero W G q : Fin m) :
    Project.Formula.satisfies env (oldExit w D S zero W G q) ↔
      OldExit (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound W) (env.bound G) (env.bound q) := by
  simp only [oldExit,OldExit,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeGatesSyntax.headSome_semantics hM,
    ConstructionProbeRaw.old_semantics hM]
  rfl

/-- The source induction runs on every internal Raw length, through the
    existing formula-indexed induction. No external well-foundedness is used. -/
theorem append_old_exit_isOld (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) :
    ∀ q, OldExit w D S zero W G q := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases W (fun _ => G))))),
    free := fun _ => w }
  let schema : Project.UnarySchema 6 := {
    body := oldExit 1 2 3 4 5 6 0
    freeClosed := oldExit_freeClosed _ _ _ _ _ _ _ }
  have he q : schema.denote env q ↔ OldExit w D S zero W G q :=
    oldExit_semantics hM (env.push q) 1 2 3 4 5 6 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env schema hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro _ s d od z hHead _ _ _
    exact (old_no_head hz hOld hHead).elim) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro hq s' d od z hHead hd hProd hExit
    have hss := head_unique hM hw (show HeadSome w D S q s from ⟨t,hCons⟩) hHead
    subst s'
    obtain ⟨ht,hn⟩ := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp ((hW q).mp hq)
    have htW := (hW t).mpr ht
    obtain ⟨out,hEval,hAct⟩ := eval_cons_forward hM hw hCons ((hG q od z).mp hProd).2
    have hHeadB := (head_letterAct_ne_iff hM hw hz hzw hAlpha hAct).mp hExit
    have hOldOut : ∃ y, Old zero D y out := by
      rcases cases_raw hM hw hz hzw (word_raw hW htW) with ⟨x,hx⟩ | ⟨s',tail,hTail⟩
      · obtain ⟨_,y,_,hy⟩ := (oldAct_old_iff hz hd).mp (eval_old_forward hM hw hz hx hEval)
        exact ⟨y,hy⟩
      · have hExitTail : ¬ HeadSome w D S out s' := fun hh =>
          hn ((headDiv_of_same_head hM hw hz ⟨tail,hTail⟩ hh).mpr hHeadB)
        exact (he t).mp ih htW s' d od out ⟨tail,hTail⟩ hd ((hG t od out).mpr ⟨htW,hEval⟩) hExitTail
    obtain ⟨y,hy⟩ := hOldOut
    obtain ⟨r,hr,hbr⟩ := (headDiv_old_iff hz hy).mp hHeadB
    obtain ⟨oldr,hOldr⟩ := exists_old hM (zero := zero) hr
    have hbAct : OldAct w D S zero mul A b oldr out :=
      (oldAct_old_iff hz hOldr).mpr ⟨hb,y,hbr,hy⟩
    obtain ⟨exit,hExitGraph,_⟩ := hAlpha.2.2.2.1.1.2 s (cons_letter hCons)
    have hOldAct := (ConstructionProbeLetterAction.letterAct_oldAct_b hM hw hz hzw hm hAlpha hW
      (cons_letter hCons) (old_word hM hz hzw hW hOldr) hbAct hExitGraph).mp hAct
    obtain ⟨_,v,_,hv⟩ := (oldAct_old_iff hz hOldr).mp hOldAct
    exact ⟨v,hv⟩)
  intro q hq
  exact (he q).mp (hAll q (word_raw hW hq)) hq

/-- Literal Gate.append_old: an old multiple of the gate forces the
    actual product with any old right multiplier back into the old image. -/
theorem gate_append_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G q s g og d od z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGate : Gate w D S zero mul A W G q s g) (hHead : HeadSome w D S q s)
    (hg : Old zero D g og) (hd : Old zero D d od) (hProd : Product G q od z)
    (hBound : Divides W G og z) : ∃ y, Old zero D y z := by
  obtain ⟨hq,hEval⟩ := (hG q od z).mp hProd
  have hzW := eval_word hM hEval
  have hHeadDiv := (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hg hzW).mp hBound
  exact append_old_exit_isOld hM hw hz hzw hm hAlpha hW hb hG q hq s d od z hHead hd hProd
    (gate_head_ne hGate hzW hHeadDiv)

def GateAt (D N mul mulN O q : M.Carrier .set) : Prop := ∃ g fg,
  PureKuratowski.PairMember M g fg O ∧ Divides N mulN q fg ∧
  (∀ y fy, PureKuratowski.PairMember M y fy O → Divides N mulN q fy → Divides D mul g y) ∧
  (∀ x fx z, PureKuratowski.PairMember M x fx O → Product mulN q fx z →
    Divides N mulN fg z → ∃ y, PureKuratowski.PairMember M y z O)

def GateRule (D N mul mulN O : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q N → (∀ x, ¬ PureKuratowski.PairMember M x q O) →
    (∃ y fy, PureKuratowski.PairMember M y fy O ∧ Divides N mulN q fy) → GateAt D N mul mulN O q

/-- The probe case of Cell.descent_gate, including actual old-input consumption. -/
theorem probe_gate_rule (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hO : OldGraph zero D O) (hJ : ConditionalJoins D mul) (hCon : Conservative D W mul G O) :
    GateRule D W mul G O := by
  intro q hq hNew hMultiple
  rcases cases_raw hM hw hz hzw (word_raw hW hq) with ⟨x,hx⟩ | ⟨s,t,hCons⟩
  · exact (hNew x ((hO x q).mpr hx)).elim
  · obtain ⟨y,fy,hy,hqfy⟩ := hMultiple
    have hyOld := (hO y fy).mp hy
    obtain ⟨g,hg,hGate⟩ := ConstructionProbeConditionalJoins.gate_existence hM hw hz hzw hm
      hAlpha hW hb hG hUnit hO hJ hCon q s fy hq ⟨t,hCons⟩
      (old_word hM hz hzw hW hyOld) hqfy (old_no_head hz hyOld)
    obtain ⟨fg,hfg⟩ := exists_old hM (zero := zero) hg
    refine ⟨g,fg,(hO g fg).mpr hfg,?_,?_,?_⟩
    · exact (gate_dvd_old_iff hz hGate hfg (old_word hM hz hzw hW hfg)).mpr
        ⟨e,hm.1.1,(hm.1.2 g hg g).2.mpr rfl⟩
    · intro y fy hy hqfy
      exact (gate_dvd_old_iff hz hGate ((hO y fy).mp hy)
        (old_word hM hz hzw hW ((hO y fy).mp hy))).mp hqfy
    · intro x fx z hx hProd hBound
      obtain ⟨y,hy⟩ := gate_append_old hM hw hz hzw hm hAlpha hW hb hG hGate ⟨t,hCons⟩
        hfg ((hO x fx).mp hx) hProd hBound
      exact ⟨y,(hO y z).mpr hy⟩

/-- A merger introduces no new divisor of an old element; reuse the
    already proved exact factors_of_old, rather than a probe gate argument. -/
theorem merger_gate_rule (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B G T O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeRaw.Carrier w D L W)
    (hB : ConstructionProbeLetters.Representatives W W B) (hG : ForcingSupportSize.MapsTo B W G)
    (hTable : ConstructionMergerWordAction.ActionTable w D L zero mul A T)
    (hLaws : ConstructionMergerWordProduct.Laws w D L zero T G)
    (hO : OldGraph zero D O) : GateRule D W mul G O := by
  intro q _ hNew hMultiple
  obtain ⟨y,fy,hy,r,_,hProd⟩ := hMultiple
  obtain ⟨x,_,hx,_,_⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hB hG
    hTable hLaws ((hO y fy).mp hy) hProd
  exact (hNew x ((hO x q).mpr hx)).elim

/-- Literal source OldGateStep, with all products and divisibility measured
    in the SAME terminal monoid, including right factors outside the cut. -/
def OldGateStep (T mul S R : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q R → ¬ (Project.FirstOrderSemantics.reduct M).mem q S →
  (∃ y, (Project.FirstOrderSemantics.reduct M).mem y S ∧ Divides T mul q y) → ∃ g,
    (Project.FirstOrderSemantics.reduct M).mem g S ∧ Divides T mul q g ∧
    (∀ y, (Project.FirstOrderSemantics.reduct M).mem y S → Divides T mul q y → Divides T mul g y) ∧
    (∀ x z, (Project.FirstOrderSemantics.reduct M).mem x S → Product mul q x z →
      Divides T mul g z → (Project.FirstOrderSemantics.reduct M).mem z S)

/-- Source Attachment.gateStep: transport the actual gate along the existing
    conservative embedding and its literal composite old inclusion. -/
theorem attachment_gateStep
    {D N T mul mulN mulT eN eT O f H S R : M.Carrier .set}
    (hn : LeftCancelMonoid N mulN eN)
    (ht : LeftCancelMonoid T mulT eT)
    (hO : ForcingSupportSize.Injection D N O)
    (hPresO : ConstructionProbeLiftHom.PreservesProducts mul mulN O)
    (hf : Conservative N T mulN mulT f)
    (hPresF : ConstructionProbeLiftHom.PreservesProducts mulN mulT f)
    (hComp : ConstructionProbeMappedPath.NodeMap O f H)
    (hS : ForcingSupportedNames.Range D H S) (hR : ForcingSupportedNames.Range N f R)
    (hRule : GateRule D N mul mulN O) : OldGateStep T mulT S R := by
  have hReflect := ConstructionProbeAlphabetMap.division_reflection hn ht hf.1 hPresF hf.2.1
  intro q hq hNew hMultiple
  obtain ⟨v,hv,hvq⟩ := (hR q).mp hq
  have hNewV : ∀ x, ¬ PureKuratowski.PairMember M x v O := by
    intro x hx
    exact hNew ((hS q).mpr ⟨x,ForcingConditionGraphs.function_input hO.1.1 hx,
      (hComp x q).mpr ⟨v,hx,hvq⟩⟩)
  obtain ⟨y,hy,hqy⟩ := hMultiple
  obtain ⟨a,_,hay⟩ := (hS y).mp hy
  obtain ⟨oa,hoa,hoay⟩ := (hComp a y).mp hay
  obtain ⟨g,og,hg,hvg,hMin,hInput⟩ := hRule v hv hNewV
    ⟨a,oa,hoa,(hReflect v oa q y hvq hoay).mp hqy⟩
  obtain ⟨fg,hfg,_⟩ := hf.1.1.1.2 og (hO.1.2 g og hg)
  have hgH := (hComp g fg).mpr ⟨og,hg,hfg⟩
  refine ⟨fg,(hS fg).mpr ⟨g,ForcingConditionGraphs.function_input hO.1.1 hg,hgH⟩,
    (hReflect v og q fg hvq hfg).mpr hvg,?_,?_⟩
  · intro y hy hqy
    obtain ⟨a,_,hay⟩ := (hS y).mp hy
    obtain ⟨oa,hoa,hoay⟩ := (hComp a y).mp hay
    obtain ⟨d,hd,hgd⟩ := hMin a oa hoa ((hReflect v oa q y hvq hoay).mp hqy)
    obtain ⟨od,hod,_⟩ := hO.1.1.2 d hd
    obtain ⟨fd,hfd,_⟩ := hf.1.1.1.2 od (hO.1.2 d od hod)
    exact ⟨fd,hf.1.1.2 od fd hfd,hPresF og od oa fg fd y
      (hPresO g d a og od oa hgd hg hod hoa) hfg hfd hoay⟩
  · intro x z hx hProd hgz
    obtain ⟨a,_,hax⟩ := (hS x).mp hx
    obtain ⟨oa,hoa,hoax⟩ := (hComp a x).mp hax
    obtain ⟨vprod,hvprod,hp⟩ := (hn.2.1 v hv).1 oa (hO.1.2 a oa hoa)
    obtain ⟨z',hz',_⟩ := hf.1.1.1.2 vprod hvprod
    have he := (ht.2.1 q (hf.1.1.2 v q hvq)).2.1 x z' z (hf.1.1.2 oa x hoax)
      (hPresF v oa vprod q x z' hp hvq hoax hz') hProd
    subst z'
    obtain ⟨y,hy⟩ := hInput a oa vprod hoa hp ((hReflect og vprod fg z hfg hz').mp hgz)
    exact (hS z).mpr ⟨y,ForcingConditionGraphs.function_input hO.1.1 hy,
      (hComp y z).mpr ⟨vprod,hy,hz'⟩⟩

def gateAt {m : Nat} (D N mul mulN O q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ 1 0)) (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ.succ mulN.succ.succ q.succ.succ 0)) (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ 1 0)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ.succ.succ.succ mulN.succ.succ.succ.succ q.succ.succ.succ.succ 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ mul.succ.succ.succ.succ 3 1)))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ 2 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 1 0)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ 3 0)) (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ.succ 0 1))))))))))))))

theorem gateAt_freeClosed {m : Nat} (D N mul mulN O q : Fin m) :
    (gateAt D N mul mulN O q).FreeClosed := by
  simp -implicitDefEqProofs [gateAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem gateAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN O q : Fin m) :
    Project.Formula.satisfies env (gateAt D N mul mulN O q) ↔
      GateAt (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound O) (env.bound q) := by
  simp only [gateAt,
    GateAt,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    ConstructionBaseMonoid.divides_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def gateRule {m : Nat} (D N mul mulN O : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound N.succ)) (.imp (.forallE (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ 0 1)))) (.imp (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ 1 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ.succ.succ mulN.succ.succ.succ 2 0))))) (gateAt D.succ N.succ mul.succ mulN.succ O.succ 0)))))

theorem gateRule_freeClosed {m : Nat} (D N mul mulN O : Fin m) :
    (gateRule D N mul mulN O).FreeClosed := by
  simp -implicitDefEqProofs [gateRule,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,gateAt_freeClosed]

theorem gateRule_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN O : Fin m) :
    Project.Formula.satisfies env (gateRule D N mul mulN O) ↔
      GateRule (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound O) := by
  simp only [gateRule,
    GateRule,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    ConstructionBaseMonoid.divides_semantics (M := M),
    gateAt_semantics hM]
  rfl

def oldGateStep {m : Nat} (T mul S R : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound R.succ)) (.imp (.neg (.mem (.bound 0) (.bound S.succ))) (.imp (.existsE (.conj (.mem (.bound 0) (.bound S.succ.succ)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides T.succ.succ mul.succ.succ 1 0)))) (.existsE (.conj (.mem (.bound 0) (.bound S.succ.succ)) (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides T.succ.succ mul.succ.succ 1 0)) (.conj (.forallE (.imp (.mem (.bound 0) (.bound S.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides T.succ.succ.succ mul.succ.succ.succ 2 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides T.succ.succ.succ mul.succ.succ.succ 1 0))))) (.forallE (.forallE (.imp (.mem (.bound 1) (.bound S.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ 3 1 0)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides T.succ.succ.succ.succ mul.succ.succ.succ.succ 2 0)) (.mem (.bound 0) (.bound S.succ.succ.succ.succ)))))))))))))))

theorem oldGateStep_freeClosed {m : Nat} (T mul S R : Fin m) :
    (oldGateStep T mul S R).FreeClosed := by
  simp -implicitDefEqProofs [oldGateStep,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem oldGateStep_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (T mul S R : Fin m) :
    Project.Formula.satisfies env (oldGateStep T mul S R) ↔
      OldGateStep (env.bound T) (env.bound mul) (env.bound S) (env.bound R) := by
  simp only [oldGateStep,
    OldGateStep,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def probeSentence {m : Nat} (w D S zero mul A b W E e I G unit O : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeAlphabet.alphabet D mul e S I A E) (.imp (ConstructionProbeWord.wordCarrier w D S mul A b W) (.imp (.mem (.bound b) (.bound D)) (.imp (ConstructionProbeWordMonoidSyntax.multiplicationGraph w D S zero mul A b W E G) (.imp (ConstructionProbeRaw.old zero D e unit) (.imp (ConstructionProbeOldEmbeddingSyntax.oldGraph zero D O) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ConstructionProbeConservativeSyntax.conservative D W mul G O) (gateRule D W mul G O)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isEmpty,
      ConstructionProbeAlphabet.alphabet_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
      ConstructionProbeRaw.old_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      gateRule_freeClosed]

theorem probe_models {m : Nat} (w D S zero mul A b W E e I G unit O : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (probeSentence w D S zero mul A b W E e I G unit O)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (probeSentence w D S zero mul A b W E e I G unit O)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isOmega_iff,
    Project.Term.eval_bound,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ConstructionProbeRaw.old_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    gateRule_semantics hM]
  exact probe_gate_rule hM

theorem probe_kernel_certificate {m : Nat} (w D S zero mul A b W E e I G unit O : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (probeSentence w D S zero mul A b W E e I G unit O)) :=
  ModelTransfer.derives (fun _ hM => probe_models w D S zero mul A b W E e I G unit O hM)

def mergerSentence {m : Nat} (w D L zero mul A W B G T O : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionProbeRaw.carrier w D L W) (.imp (ConstructionProbeLetters.representatives W W B) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo G B W)) (.imp (ConstructionMergerWordAction.actionTable w D L zero mul A T) (.imp (ConstructionMergerWordProduct.laws w D L zero T G) (.imp (ConstructionProbeOldEmbeddingSyntax.oldGraph zero D O) (gateRule D W mul G O))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isEmpty,
      ConstructionProbeRaw.carrier_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,
      ConstructionMergerWordProduct.laws_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      gateRule_freeClosed]

theorem merger_models {m : Nat} (w D L zero mul A W B G T O : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mergerSentence w D L zero mul A W B G T O)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (mergerSentence w D L zero mul A W B G T O)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isOmega_iff,
    Project.Term.eval_bound,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    ConstructionProbeRaw.carrier_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionMergerWordAction.actionTable_semantics hM,
    ConstructionMergerWordProduct.laws_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    gateRule_semantics hM]
  exact merger_gate_rule hM

theorem merger_kernel_certificate {m : Nat} (w D L zero mul A W B G T O : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mergerSentence w D L zero mul A W B G T O)) :=
  ModelTransfer.derives (fun _ hM => merger_models w D L zero mul A W B G T O hM)

def attachmentSentence {m : Nat} (D N T mul mulN mulT eN eT O f H S R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid N mulN eN)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid T mulT eT)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection O D N)) (.imp (ConstructionProbeLiftHomSyntax.preservesProducts mul mulN O) (.imp (ConstructionProbeConservativeSyntax.conservative N T mulN mulT f) (.imp (ConstructionProbeLiftHomSyntax.preservesProducts mulN mulT f) (.imp (ConstructionProbeMappedPathSyntax.nodeMap O f H) (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D H S)) (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range N f R)) (.imp (gateRule D N mul mulN O) (oldGateStep T mulT S R)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      gateRule_freeClosed,
      oldGateStep_freeClosed]

theorem attachment_models {m : Nat} (D N T mul mulN mulT eN eT O f H S R : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (attachmentSentence D N T mul mulN mulT eN eT O f H S R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (attachmentSentence D N T mul mulN mulT eN eT O f H S R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),
    gateRule_semantics hM,
    oldGateStep_semantics hM]
  exact attachment_gateStep

theorem attachment_kernel_certificate {m : Nat} (D N T mul mulN mulT eN eT O f H S R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (attachmentSentence D N T mul mulN mulT eN eT O f H S R)) :=
  ModelTransfer.derives (fun _ hM => attachment_models D N T mul mulN mulT eN eT O f H S R hM)

end PPAC.Migration.ConstructionCellDescent
