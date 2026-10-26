/- Pinned ProbeWords.Path.act: actual quotient action, not representative-only laws. -/
import PPAC.Migration.ConstructionProbeLetters

namespace PPAC.Migration.ConstructionProbeAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionProbePath (FactorTable)
open ConstructionProbeTransitions (product_closed)
open ConstructionProbeLetters
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem representative {w D mul F C L projection c : M.Carrier .set}
    (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : Projection w D mul F C projection) (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ i x, (Project.FirstOrderSemantics.reduct M).mem i w ∧
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x c := by
  obtain ⟨p,hpC,hpc⟩ := projection_onto hL hp hc
  obtain ⟨i,x,hi,hx,hcode⟩ := (hC p).mp hpC
  exact ⟨i,x,hi,hx,p,hcode,hpc⟩

theorem projected (hM : FirstOrder.Theory.Models M nativeZF) {w D C L projection i x : M.Carrier .set}
    (hC : Representatives w D C) (hp : MapsTo C L projection)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c L ∧ Product projection i x c := by
  obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM i x
  obtain ⟨c,hpc,_⟩ := hp.1.2 p ((hC p).mpr ⟨i,x,hi,hx,hcode⟩)
  exact ⟨c,hp.2 p c hpc,p,hcode,hpc⟩

theorem projected_indices {w D C L projection i x c : M.Carrier .set}
    (hC : Representatives w D C) (hp : MapsTo C L projection) (hc : Product projection i x c) :
    (Project.FirstOrderSemantics.reduct M).mem i w ∧ (Project.FirstOrderSemantics.reduct M).mem x D := by
  obtain ⟨p,hcode,hpc⟩ := hc
  obtain ⟨i',x',hi,hx,hcode'⟩ := (hC p).mp (ForcingConditionGraphs.function_input hp.1 hpc)
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  exact ⟨hi,hx⟩

theorem projected_range {C L projection i x c : M.Carrier .set}
    (hp : MapsTo C L projection) (hc : Product projection i x c) :
    (Project.FirstOrderSemantics.reduct M).mem c L := by
  obtain ⟨p,_,hpc⟩ := hc
  exact hp.2 p c hpc

def Act (D mul projection b c d : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem b D ∧ ∃ i x bx,
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x c ∧
      Product mul b x bx ∧ Product projection i bx d

theorem act_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e F C L projection b c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives w D C)
    (hL : Letters w D mul F C L) (hp : MapsTo C L projection)
    (hProjection : Projection w D mul F C projection)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ d, (Project.FirstOrderSemantics.reduct M).mem d L ∧ Act D mul projection b c d := by
  obtain ⟨i,x,hi,hx,hxc⟩ := representative hC hL hProjection hc
  obtain ⟨bx,hbxD,hbx⟩ := (hm.2.1 b hb).1 x hx
  obtain ⟨d,hd,hbxd⟩ := projected hM hC hp hi hbxD
  exact ⟨d,hd,hb,i,x,bx,hx,hxc,hbx,hbxd⟩

theorem act_unique {w D mul e node F projection b c d f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hE : EqualityLaw w D mul F projection)
    (hd : Act D mul projection b c d) (hf : Act D mul projection b c f) : d = f := by
  obtain ⟨hb,i,x,bx,_,hxc,hbx,hbxd⟩ := hd
  obtain ⟨_,j,y,byv,_,hyc,hby,hbyf⟩ := hf
  have hxy := (letter_eq_iff hE hxc hyc).mp rfl
  exact (letter_eq_iff hE hbxd hbyf).mpr (ConstructionProbeTransitions.meets_left hm hF hb hbx hby hxy)

theorem act_injective {w D mul e node F projection b c d f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hE : EqualityLaw w D mul F projection)
    (hc : Act D mul projection b c f) (hd : Act D mul projection b d f) : c = d := by
  obtain ⟨hb,i,x,bx,hx,hxc,hbx,hbxf⟩ := hc
  obtain ⟨_,j,y,byv,hy,hyd,hby,hbyf⟩ := hd
  have hxy := (letter_eq_iff hE hbxf hbyf).mp rfl
  exact (letter_eq_iff hE hxc hyd).mpr (ConstructionProbeTransitions.meets_reflect_left hm hF hb hx hy hbx hby hxy)

theorem act_letter_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection b i x bx c d : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hp : MapsTo C L projection) (hE : EqualityLaw w D mul F projection)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hxc : Product projection i x c) (hbx : Product mul b x bx) :
    Act D mul projection b c d ↔ Product projection i bx d := by
  obtain ⟨hi,hx⟩ := projected_indices hC hp hxc
  constructor
  · intro hd
    obtain ⟨d',_,hbd⟩ := projected hM hC hp hi (product_closed hm hb hx hbx)
    have he := act_unique hm hF hE hd ⟨hb,i,x,bx,hx,hxc,hbx,hbd⟩
    exact he.symm ▸ hbd
  · exact fun hd => ⟨hb,i,x,bx,hx,hxc,hbx,hd⟩

theorem act_one {w D mul e F C L projection c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives w D C)
    (hL : Letters w D mul F C L) (hp : Projection w D mul F C projection)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) : Act D mul projection e c c := by
  obtain ⟨i,x,_,hx,hxc⟩ := representative hC hL hp hc
  exact ⟨hm.1.1,i,x,x,hx,hxc,((hm.1.2 x hx x).1).mpr rfl,hxc⟩

theorem act_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection b a ba c d f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hp : MapsTo C L projection) (hE : EqualityLaw w D mul F projection)
    (hba : Product mul b a ba) (hac : Act D mul projection a c d) (hbd : Act D mul projection b d f) :
    Act D mul projection ba c f := by
  obtain ⟨ha,i,x,ax,hx,hxc,hax,haxd⟩ := hac
  have hb := hbd.1
  have haxD := product_closed hm ha hx hax
  obtain ⟨bax,_,hbax⟩ := (hm.2.1 b hb).1 ax haxD
  have hbaxf := (act_letter_iff hM hm hF hC hp hE hb haxd hbax).mp hbd
  have hbax' := (hm.2.2 b a x ba ax bax hb ha hx hba hax).mpr hbax
  exact ⟨product_closed hm hb ha hba,i,x,bax,hx,hxc,hbax',hbaxf⟩

def act {m : Nat} (D mul projection b c d : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound b) (.bound D)) (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 1) (.bound D.succ.succ.succ))
      (.conj (ProjectSyntax.encode id (product projection.succ.succ.succ 2 1 c.succ.succ.succ))
        (.conj (ProjectSyntax.encode id (product mul.succ.succ.succ b.succ.succ.succ 1 0))
          (ProjectSyntax.encode id (product projection.succ.succ.succ 2 0 d.succ.succ.succ))))))))

theorem act_freeClosed {m : Nat} (D mul projection b c d : Fin m) : (act D mul projection b c d).FreeClosed := by
  simp -implicitDefEqProofs [act,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem act_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul projection b c d : Fin m) :
    Project.Formula.satisfies env (act D mul projection b c d) ↔
      Act (env.bound D) (env.bound mul) (env.bound projection) (env.bound b) (env.bound c) (env.bound d) := by
  simp only [act,Act,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def actPair {m : Nat} (D mul projection p d : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
    (act D.succ.succ mul.succ.succ projection.succ.succ 1 0 d.succ.succ)))

theorem actPair_freeClosed {m : Nat} (D mul projection p d : Fin m) : (actPair D mul projection p d).FreeClosed := by
  simp -implicitDefEqProofs [actPair,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,act_freeClosed]

theorem actPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul projection p d : Fin m) :
    Project.Formula.satisfies env (actPair D mul projection p d) ↔
      ∃ b c, PureKuratowski.Code M (env.bound p) b c ∧ Act (env.bound D) (env.bound mul) (env.bound projection) b c (env.bound d) := by
  simp only [actPair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,act_semantics hM]
  rfl

def ActionTable (D mul projection A : M.Carrier .set) : Prop := ∀ b c d,
  Product A b c d ↔ Act D mul projection b c d

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : MapsTo C L projection) (hProjection : Projection w D mul F C projection)
    (hE : EqualityLaw w D mul F projection) :
    ∃ I A, Representatives D L I ∧ MapsTo I L A ∧ ActionTable D mul projection A := by
  obtain ⟨I,hI⟩ := exists_representatives hM D L
  let schema : Project.BinarySchema 3 := { body := actPair 2 3 4 1 0, freeClosed := actPair_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases D (Fin.cases mul (fun _ => projection)), free := fun _ => D }
  have he : ∀ p d, schema.denote env p d ↔ ∃ b c, PureKuratowski.Code M p b c ∧ Act D mul projection b c d :=
    fun p d => actPair_semantics hM ((env.push p).push d) 2 3 4 1 0
  obtain ⟨A,hA,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := I) (target := L) (by
      intro p hpi
      obtain ⟨b,c,hb,hc,hcode⟩ := (hI p).mp hpi
      obtain ⟨d,_,hact⟩ := act_total hM hm hC hL hp hProjection hb hc
      exact ⟨d,(he p d).mpr ⟨b,c,hcode,hact⟩⟩) (by
      intro p _ d f hd hf
      obtain ⟨b,c,hcode,hd⟩ := (he p d).mp hd
      obtain ⟨b',c',hcode',hf⟩ := (he p f).mp hf
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact act_unique hm hF hE hd hf) (by
      intro p d _ hd
      obtain ⟨b,c,_,_,i,x,bx,_,_,_,hbd⟩ := (he p d).mp hd
      exact projected_range hp hbd)
  refine ⟨I,A,hI,(ForcingSupportSize.native_mapsTo hM I L A).mpr hA,fun b c d => ?_⟩
  constructor
  · rintro ⟨p,hcode,hpad⟩
    obtain ⟨_,hval⟩ := (hgraph p d).mp hpad
    obtain ⟨b',c',hcode',hact⟩ := (he p d).mp hval
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact hact
  · intro hact
    have hcopy := hact
    obtain ⟨hb,i,x,bx,_,hxc,_,_⟩ := hcopy
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM b c
    exact ⟨p,hcode,(hgraph p d).mpr ⟨(hI p).mpr ⟨b,c,hb,projected_range hp hxc,hcode⟩,
      (he p d).mpr ⟨b,c,hcode,hact⟩⟩⟩

def ActionLaws (mul e L A : M.Carrier .set) : Prop :=
  (∀ c, (Project.FirstOrderSemantics.reduct M).mem c L → Product A e c c) ∧
  (∀ b a ba c d f, Product mul b a ba → Product A a c d → Product A b d f → Product A ba c f) ∧
  (∀ b c d z, Product A b c z → Product A b d z → c = d)

def LetterActionLaw (D mul projection A : M.Carrier .set) : Prop :=
  ∀ b i x bx c d, (Project.FirstOrderSemantics.reduct M).mem b D →
    Product projection i x c → Product mul b x bx → (Product A b c d ↔ Product projection i bx d)

theorem action_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection A : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : MapsTo C L projection) (hProjection : Projection w D mul F C projection)
    (hE : EqualityLaw w D mul F projection) (hA : ActionTable D mul projection A) : ActionLaws mul e L A := by
  exact ⟨fun c hc => (hA e c c).mpr (act_one hm hC hL hProjection hc),
    fun b a ba c d f hba hac hbd => (hA ba c f).mpr
      (act_mul hM hm hF hC hp hE hba ((hA a c d).mp hac) ((hA b d f).mp hbd)),
    fun b c d z hc hd => act_injective hm hF hE ((hA b c z).mp hc) ((hA b d z).mp hd)⟩

theorem letter_action_law (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection A : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hp : MapsTo C L projection)
    (hE : EqualityLaw w D mul F projection) (hA : ActionTable D mul projection A) : LetterActionLaw D mul projection A :=
  fun b _ _ _ c d hb hc hbx => (hA b c d).trans (act_letter_iff hM hm hF hC hp hE hb hc hbx)

def actionTable {m : Nat} (D mul projection A : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (product A.succ.succ.succ 2 1 0)) (act
    D.succ.succ.succ mul.succ.succ.succ projection.succ.succ.succ 2 1 0)))))

theorem actionTable_freeClosed {m : Nat} (D mul projection A : Fin m) : (actionTable D mul projection A).FreeClosed := by
  simp -implicitDefEqProofs [actionTable,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,act_freeClosed]

theorem actionTable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul projection A : Fin m) :
    Project.Formula.satisfies env (actionTable D mul projection A) ↔
      ActionTable (env.bound D) (env.bound mul) (env.bound projection) (env.bound A) := by
  simp only [actionTable, ActionTable, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), product_semantics (M := M),
    act_semantics hM]
  rfl

def actionLaws {m : Nat} (mul e L A : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (.mem (.bound 0) (.bound L.succ)) (ProjectSyntax.encode id (product A.succ e.succ 0
    0)))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (product mul.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (ProjectSyntax.encode id (product
    A.succ.succ.succ.succ.succ.succ 4 2 1)) (.imp (ProjectSyntax.encode id (product
    A.succ.succ.succ.succ.succ.succ 5 1 0)) (ProjectSyntax.encode id (product A.succ.succ.succ.succ.succ.succ 3
    2 0))))))))))) (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (product
    A.succ.succ.succ.succ 3 2 0)) (.imp (ProjectSyntax.encode id (product A.succ.succ.succ.succ 3 1 0))
    (Project.Formula.extensionalEq (.bound 2) (.bound 1))))))))))

theorem actionLaws_freeClosed {m : Nat} (mul e L A : Fin m) : (actionLaws mul e L A).FreeClosed := by
  simp -implicitDefEqProofs [actionLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem actionLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (mul e L A : Fin m) :
    Project.Formula.satisfies env (actionLaws mul e L A) ↔
      ActionLaws (env.bound mul) (env.bound e) (env.bound L) (env.bound A) := by
  simp only [actionLaws, ActionLaws, Project.Formula.satisfies_forall_iff, GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM), product_semantics (M := M), Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM), Project.Term.eval_bound]
  rfl

def letterActionLaw {m : Nat} (D mul projection A : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 5) (.bound
    D.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (product
    projection.succ.succ.succ.succ.succ.succ 4 3 1)) (.imp (ProjectSyntax.encode id (product
    mul.succ.succ.succ.succ.succ.succ 5 3 2)) (.iff (ProjectSyntax.encode id (product
    A.succ.succ.succ.succ.succ.succ 5 1 0)) (ProjectSyntax.encode id (product
    projection.succ.succ.succ.succ.succ.succ 4 2 0))))))))))))

theorem letterActionLaw_freeClosed {m : Nat} (D mul projection A : Fin m) : (letterActionLaw D mul projection A).FreeClosed := by
  simp -implicitDefEqProofs [letterActionLaw,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem letterActionLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul projection A : Fin m) :
    Project.Formula.satisfies env (letterActionLaw D mul projection A) ↔
      LetterActionLaw (env.bound D) (env.bound mul) (env.bound projection) (env.bound A) := by
  simp only [letterActionLaw, LetterActionLaw, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    product_semantics (M := M), Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound]
  rfl

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound 0)) (.imp (.forallE (.neg
    (.mem (.bound 0) (.bound 5)))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin
    7) 2 3)) (.imp (ConstructionProbePath.path (0 : Fin 7) 1 2 3 4 5 6) (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.conj (ConstructionProbePath.factorTable (6 : Fin 13) 7 8 12 5) (.conj (representatives
    (6 : Fin 13) 7 4) (.conj (letters (6 : Fin 13) 7 8 5 4 3) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (2 : Fin 13) 4 3)) (.conj (projectionGraph (6 : Fin 13) 7 8 5 4 2) (.conj
    (equalityLaw (6 : Fin 13) 7 8 5 2) (.conj (representatives (7 : Fin 13) 3 1) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 13) 1 3)) (.conj (actionTable (7 : Fin 13) 8 2 0) (.conj (actionLaws (8 : Fin 13) 9 3 0) (letterActionLaw (7 : Fin 13) 8 2 0))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbePath.path_freeClosed,ConstructionProbePath.factorTable_freeClosed,
    representatives_freeClosed,letters_freeClosed,projectionGraph_freeClosed,equalityLaw_freeClosed,
    actionTable_freeClosed,actionLaws_freeClosed,letterActionLaw_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbePath.path_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbePath.factorTable_semantics hM,representatives_semantics hM,
    letters_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    projectionGraph_semantics hM,equalityLaw_semantics hM,actionTable_semantics hM,
    actionLaws_semantics hM,letterActionLaw_semantics hM]
  intro hw hz hm hp
  obtain ⟨pairs,hpairs⟩ := ConstructionProbePath.exists_ordered_pairs hM (bound 0)
  obtain ⟨F,_,hF⟩ := ConstructionProbePath.exists_factor_table hM hm hp hpairs
  obtain ⟨T,_,hT⟩ := ConstructionProbePath.exists_terminal_table hM hm hp
  have hTable := ConstructionProbePath.table_laws hM hw hz hm hp hF hT
  have hLaws := ConstructionProbeTransitions.meets_laws hM hw hm hp hF hTable
  obtain ⟨C,hC⟩ := exists_representatives hM (bound 0) (bound 1)
  obtain ⟨L,hL⟩ := exists_letters hM (bound 0) (bound 1) (bound 2) F C
  obtain ⟨projection,hp,hProjection⟩ := exists_projection hM hL
  have hE := equality_law hM hC hLaws hProjection
  obtain ⟨I,A,hI,hA,hAction⟩ := exists_action hM hm hF hC hL hp hProjection hE
  exact ⟨F,C,L,projection,I,A,hF,hC,hL,hp,hProjection,hE,hI,hA,hAction,
    action_laws hM hm hF hC hL hp hProjection hE hAction,
    letter_action_law hM hm hF hC hp hE hAction⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeAction
