/- Pinned PersistentCodes.lean:19-65, ConditionCodeSelection.
Actual consumers: ChainCode.selected_unique and dense_selected, then OrdinalCodes.
All conditions/codes are internal sets. Formula parameters preserve arbitrary
object-definable W/E; internal Separation and the existing minimum are reused. -/
import PPAC.Migration.InternalWellOrderChoice
import PPAC.Migration.GodelDefRecursion

namespace PPAC.Migration.ForcingPersistentSelection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Rel2 {k : Nat} (f : Project.Formula 1 (k+2))
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k)
    (p a : M.Carrier .set) : Prop := Project.Formula.satisfies ((env.push a).push p) f

def Rel3 {k : Nat} (f : Project.Formula 1 (k+3))
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k)
    (p a b : M.Carrier .set) : Prop := Project.Formula.satisfies (((env.push b).push a).push p) f

def rel2 {k m : Nat} (f : Project.Formula 1 (k+2)) (base : Fin k → Fin m) (p a : Fin m) : Project.Formula 1 m :=
  f.rename (Fin.cases p (Fin.cases a base))

def rel3 {k m : Nat} (f : Project.Formula 1 (k+3)) (base : Fin k → Fin m) (p a b : Fin m) : Project.Formula 1 m :=
  f.rename (Fin.cases p (Fin.cases a (Fin.cases b base)))

theorem rel2_semantics {k m : Nat} (f : Project.Formula 1 (k+2)) (base : Fin k → Fin m) (p a : Fin m)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) :
    Project.Formula.satisfies env (rel2 f base p a) ↔
      Rel2 f {bound := fun i => env.bound (base i), free := env.free} (env.bound p) (env.bound a) := by
  have he : env.reindex (Fin.cases p (Fin.cases a base)) =
      (({bound := fun i => env.bound (base i), free := env.free} : SetTheory.Env _ k).push (env.bound a)).push (env.bound p) := by
    apply congrArg (fun bound => (⟨bound,env.free⟩ : SetTheory.Env _ (k+2)))
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;> rfl
  simp only [rel2,Project.Formula.satisfies_rename,he,Rel2]

theorem rel3_semantics {k m : Nat} (f : Project.Formula 1 (k+3)) (base : Fin k → Fin m) (p a b : Fin m)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) :
    Project.Formula.satisfies env (rel3 f base p a b) ↔
      Rel3 f {bound := fun i => env.bound (base i), free := env.free} (env.bound p) (env.bound a) (env.bound b) := by
  have he : env.reindex (Fin.cases p (Fin.cases a (Fin.cases b base))) =
      ((({bound := fun i => env.bound (base i), free := env.free} : SetTheory.Env _ k).push (env.bound b)).push (env.bound a)).push (env.bound p) := by
    apply congrArg (fun bound => (⟨bound,env.free⟩ : SetTheory.Env _ (k+3)))
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => Fin.cases ?_ (fun t => ?_) l) j) i <;> rfl
  simp only [rel3,Project.Formula.satisfies_rename,he,Rel3]

def Selected (L W : M.Carrier .set → M.Carrier .set → Prop)
    (E : M.Carrier .set → M.Carrier .set → M.Carrier .set → Prop)
    (P A order a p : M.Carrier .set) : Prop :=
  W p a ∧ ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → L q p →
    ∀ b, (Project.FirstOrderSemantics.reduct M).mem b A → PureKuratowski.PairMember M b a order → ¬ (W q b ∧ E q a b)

theorem selected_mono {L W : M.Carrier .set → M.Carrier .set → Prop}
    {E : M.Carrier .set → M.Carrier .set → M.Carrier .set → Prop} {P A order a p q : M.Carrier .set}
    (htrans : ∀ r s t, (Project.FirstOrderSemantics.reduct M).mem r P → (Project.FirstOrderSemantics.reduct M).mem s P →
      (Project.FirstOrderSemantics.reduct M).mem t P → L r s → L s t → L r t)
    (hmono : ∀ r s b, (Project.FirstOrderSemantics.reduct M).mem r P → (Project.FirstOrderSemantics.reduct M).mem s P →
      (Project.FirstOrderSemantics.reduct M).mem b A → L r s → W s b → W r b)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a A) (hqp : L q p) (h : Selected L W E P A order a p) :
    Selected L W E P A order a q :=
  ⟨hmono q p a hq hp ha hqp h.1,fun r hr hrq => h.2 r hr (htrans r q p hr hq hp hrq hqp)⟩

theorem selected_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {L W : M.Carrier .set → M.Carrier .set → Prop}
    {E : M.Carrier .set → M.Carrier .set → M.Carrier .set → Prop} {P A order a b p : M.Carrier .set}
    (hWO : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order A)
    (hsymm : ∀ p a b, (Project.FirstOrderSemantics.reduct M).mem p P → (Project.FirstOrderSemantics.reduct M).mem a A →
      (Project.FirstOrderSemantics.reduct M).mem b A → E p a b → E p b a)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hpp : L p p)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a A) (hb : (Project.FirstOrderSemantics.reduct M).mem b A)
    (hsa : Selected L W E P A order a p) (hsb : Selected L W E P A order b p) (hab : E p a b) : a = b := by
  rcases hWO.linear.2.2 a ha b hb with he | hab' | hba
  · exact (ModelTransfer.extensionality hM).eq_of_same_members a b he
  · exact False.elim (hsb.2 p hp hpp a ha hab' ⟨hsa.1,hsymm p a b hp ha hb hab⟩)
  · exact False.elim (hsa.2 p hp hpp b hb hba ⟨hsb.1,hab⟩)


theorem dense_selected (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (hL : L.FreeClosed) (hW : W.FreeClosed) (hE : E.FreeClosed)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (P A order p a : M.Carrier .set)
    (hWO : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order A)
    (hrefl : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → Rel2 L env r r)
    (htrans : ∀ r s t, (Project.FirstOrderSemantics.reduct M).mem r P → (Project.FirstOrderSemantics.reduct M).mem s P →
      (Project.FirstOrderSemantics.reduct M).mem t P → Rel2 L env r s → Rel2 L env s t → Rel2 L env r t)
    (hemono : ∀ r s b c, (Project.FirstOrderSemantics.reduct M).mem r P → (Project.FirstOrderSemantics.reduct M).mem s P →
      (Project.FirstOrderSemantics.reduct M).mem b A → (Project.FirstOrderSemantics.reduct M).mem c A →
      Rel2 L env r s → Rel3 E env s b c → Rel3 E env r b c)
    (herefl : ∀ r b, (Project.FirstOrderSemantics.reduct M).mem r P → (Project.FirstOrderSemantics.reduct M).mem b A → Rel3 E env r b b)
    (hetrans : ∀ r b c d, (Project.FirstOrderSemantics.reduct M).mem r P → (Project.FirstOrderSemantics.reduct M).mem b A →
      (Project.FirstOrderSemantics.reduct M).mem c A → (Project.FirstOrderSemantics.reduct M).mem d A →
      Rel3 E env r b c → Rel3 E env r c d → Rel3 E env r b d)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (ha : (Project.FirstOrderSemantics.reduct M).mem a A)
    (hwa : Rel2 W env p a) :
    ∃ q, (Project.FirstOrderSemantics.reduct M).mem q P ∧ Rel2 L env q p ∧
      ∃ b, (Project.FirstOrderSemantics.reduct M).mem b A ∧ Selected (Rel2 L env) (Rel2 W env) (Rel3 E env) P A order b q ∧ Rel3 E env q a b := by
  let schema : Project.UnarySchema (k+3) := {
    body := .existsE (.conj (.mem (.bound 0) (.bound 4))
      (.conj (rel2 L (fun i => i.succ.succ.succ.succ.succ) 0 2)
        (.conj (rel2 W (fun i => i.succ.succ.succ.succ.succ) 0 1)
          (rel3 E (fun i => i.succ.succ.succ.succ.succ) 0 3 1))))
    freeClosed := by simp [Definitional.Formula.FreeClosed,rel2,rel3,hL,hW,hE] }
  obtain ⟨B,hB⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema (((env.push P).push a).push p) A
  have hb b : (Project.FirstOrderSemantics.reduct M).mem b B ↔
      (Project.FirstOrderSemantics.reduct M).mem b A ∧ ∃ q, (Project.FirstOrderSemantics.reduct M).mem q P ∧ Rel2 L env q p ∧ Rel2 W env q b ∧ Rel3 E env q a b := by
    rw [hB]
    simp only [schema,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,rel2_semantics,rel3_semantics]
    rfl
  obtain ⟨b,hmin,_⟩ := InternalWellOrderChoice.unique_minimum hM hWO
    (fun b hb' => ((hb b).mp hb').1) ⟨a,(hb a).mpr ⟨ha,p,hp,hrefl p hp,hwa,herefl p a hp ha⟩⟩
  obtain ⟨hbB,hleast⟩ := (InternalWellOrderChoice.least_graph hM order B b).mp hmin
  obtain ⟨hbA,q,hq,hqp,hwb,hab⟩ := (hb b).mp hbB
  refine ⟨q,hq,hqp,b,hbA,⟨hwb,?_⟩,hab⟩
  intro r hr hrq c hc hcb h
  exact hleast c ((hb c).mpr ⟨hc,r,hr,htrans r q p hr hq hp hrq hqp,h.1,
    hetrans r a b c hr ha hbA hc (hemono r q a b hr hq ha hbA hrq hab) h.2⟩) hcb


def selected {k m : Nat} (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (base : Fin k → Fin m) (P A order a p : Fin m) : Project.Formula 1 m :=
  (.conj (rel2 W base p a) (.forallE (.imp (.mem (.bound 0) (.bound P.succ)) (.imp (rel2 L (fun i => (base i).succ) 0 p.succ) (.forallE (.imp (.mem (.bound 0) (.bound A.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge order.succ.succ 0 a.succ.succ)) (.neg (.conj (rel2 W (fun i => (base i).succ.succ) 1 0) (rel3 E (fun i => (base i).succ.succ) 1 a.succ.succ 0))))))))))

theorem selected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat} (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (base : Fin k → Fin m) (P A order a p : Fin m)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) :
    Project.Formula.satisfies env (selected L W E base P A order a p) ↔
      Selected (Rel2 L (env.reindex base)) (Rel2 W (env.reindex base)) (Rel3 E (env.reindex base))
        (env.bound P) (env.bound A) (env.bound order) (env.bound a) (env.bound p) := by
  simp only [selected,Selected,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,rel2_semantics,rel3_semantics,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def laws {k m : Nat} (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (base : Fin k → Fin m) (P A : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (.mem (.bound 0) (.bound P.succ)) (rel2 L (fun i => (base i).succ) 0 0))) (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound P.succ.succ.succ)) (.imp (rel2 L (fun i => (base i).succ.succ.succ) 2 1) (.imp (rel2 L (fun i => (base i).succ.succ.succ) 1 0) (rel2 L (fun i => (base i).succ.succ.succ) 2 0))))))))) (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ.succ)) (.imp (rel2 L (fun i => (base i).succ.succ.succ) 2 1) (.imp (rel2 W (fun i => (base i).succ.succ.succ) 1 0) (rel2 W (fun i => (base i).succ.succ.succ) 2 0))))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound P.succ.succ.succ.succ)) (.imp (.mem (.bound 2) (.bound P.succ.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound A.succ.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ.succ.succ)) (.imp (rel2 L (fun i => (base i).succ.succ.succ.succ) 3 2) (.imp (rel3 E (fun i => (base i).succ.succ.succ.succ) 2 1 0) (rel3 E (fun i => (base i).succ.succ.succ.succ) 3 1 0))))))))))) (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound P.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ)) (rel3 E (fun i => (base i).succ.succ) 1 0 0))))) (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound A.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ.succ)) (.imp (rel3 E (fun i => (base i).succ.succ.succ) 2 1 0) (rel3 E (fun i => (base i).succ.succ.succ) 2 0 1)))))))) (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound P.succ.succ.succ.succ)) (.imp (.mem (.bound 2) (.bound A.succ.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound A.succ.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ.succ.succ)) (.imp (rel3 E (fun i => (base i).succ.succ.succ.succ) 3 2 1) (.imp (rel3 E (fun i => (base i).succ.succ.succ.succ) 3 1 0) (rel3 E (fun i => (base i).succ.succ.succ.succ) 3 2 0)))))))))))))))))

def conclusion {k m : Nat} (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (base : Fin k → Fin m) (P A order : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ.succ)) (.imp (rel2 L (fun i => (base i).succ.succ.succ) 1 2) (.imp (selected L W E (fun i => (base i).succ.succ.succ) P.succ.succ.succ A.succ.succ.succ order.succ.succ.succ 0 2) (selected L W E (fun i => (base i).succ.succ.succ) P.succ.succ.succ A.succ.succ.succ order.succ.succ.succ 0 1))))))))) (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound P.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound A.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ.succ)) (.imp (selected L W E (fun i => (base i).succ.succ.succ) P.succ.succ.succ A.succ.succ.succ order.succ.succ.succ 1 2) (.imp (selected L W E (fun i => (base i).succ.succ.succ) P.succ.succ.succ A.succ.succ.succ order.succ.succ.succ 0 2) (.imp (rel3 E (fun i => (base i).succ.succ.succ) 2 1 0) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))))))) (.forallE (.forallE (.imp (.mem (.bound 1) (.bound P.succ.succ)) (.imp (.mem (.bound 0) (.bound A.succ.succ)) (.imp (rel2 W (fun i => (base i).succ.succ) 1 0) (.existsE (.conj (.mem (.bound 0) (.bound P.succ.succ.succ)) (.conj (rel2 L (fun i => (base i).succ.succ.succ) 0 2) (.existsE (.conj (.mem (.bound 0) (.bound A.succ.succ.succ.succ)) (.conj (selected L W E (fun i => (base i).succ.succ.succ.succ) P.succ.succ.succ.succ A.succ.succ.succ.succ order.succ.succ.succ.succ 0 1) (rel3 E (fun i => (base i).succ.succ.succ.succ) 1 2 0))))))))))))))

def selectionSentence {k m : Nat} (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (hL : L.FreeClosed) (hW : W.FreeClosed) (hE : E.FreeClosed)
    (base : Fin k → Fin m) (P A order : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound A))
    (.imp (laws L W E base P A) (conclusion L W E base P A order)))
  freeClosed := by
    simp [laws,conclusion,selected,rel2,rel3,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,hL,hW,hE]
    exact Project.Formula.isSetCodedWellOrder_freeClosed _ _ _ rfl rfl

theorem selection_models {k m : Nat} (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (hL : L.FreeClosed) (hW : W.FreeClosed) (hE : E.FreeClosed)
    (base : Fin k → Fin m) (P A order : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectionSentence L W E hL hW hE base P A order)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro boundEnv
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    laws,conclusion,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    rel2_semantics,rel3_semantics,selected_semantics hM]
  intro hWO hlaws
  obtain ⟨hrefl,htrans,hwmono,hemono,herefl,hesymm,hetrans⟩ := hlaws
  refine ⟨?_,?_,?_⟩
  · intro p q a hp hq ha hqp hs
    exact selected_mono htrans hwmono hp hq ha hqp hs
  · intro p a b hp ha hb hsa hsb hab
    exact selected_unique hM hWO hesymm hp (hrefl p hp) ha hb hsa hsb hab
  · intro p a hp ha hwa
    exact dense_selected hM L W E hL hW hE
      ({bound := fun i => boundEnv (base i), free := free} : SetTheory.Env _ k) (boundEnv P) (boundEnv A) (boundEnv order) p a hWO hrefl htrans hemono herefl hetrans hp ha hwa

theorem selection_kernel_certificate {k m : Nat} (L W : Project.Formula 1 (k+2)) (E : Project.Formula 1 (k+3))
    (hL : L.FreeClosed) (hW : W.FreeClosed) (hE : E.FreeClosed)
    (base : Fin k → Fin m) (P A order : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectionSentence L W E hL hW hE base P A order)) :=
  ModelTransfer.derives (fun _ hM => selection_models L W E hL hW hE base P A order hM)

end PPAC.Migration.ForcingPersistentSelection
