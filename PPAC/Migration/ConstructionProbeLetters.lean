/- Actual internal direct-limit letters for pinned ProbeWords.Path.Letters.
Representatives are omega x D; classes use the original common-stage relation. -/
import PPAC.Migration.ConstructionProbeTransitions

namespace PPAC.Migration.ConstructionProbeLetters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ConstructionProbeTransitions (Meets MeetsLaws meets meets_freeClosed meets_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Representatives (w D C : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p C ↔
    ∃ i x, (Project.FirstOrderSemantics.reduct M).mem i w ∧
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M p i x

theorem exists_representatives (hM : FirstOrder.Theory.Models M nativeZF) (w D : M.Carrier .set) :
    ∃ C, Representatives w D C := by
  obtain ⟨C,hC⟩ := ZF.exists_cartesianProduct (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) w D
  exact ⟨C,fun p => ⟨fun h => by obtain ⟨i,hi,x,hx,hp⟩ := (hC p).mp h; exact ⟨i,x,hi,hx,hp⟩,
    fun ⟨i,x,hi,hx,hp⟩ => (hC p).mpr ⟨i,hi,x,hx,hp⟩⟩⟩

def Related (w D mul F p q : M.Carrier .set) : Prop := ∃ i x j y,
  PureKuratowski.Code M p i x ∧ PureKuratowski.Code M q j y ∧ Meets w D mul F i x j y

theorem related_refl {w D mul F C p : M.Carrier .set} (hC : Representatives w D C)
    (hL : MeetsLaws w D mul F) (hp : (Project.FirstOrderSemantics.reduct M).mem p C) : Related w D mul F p p := by
  obtain ⟨i,x,hi,hx,hcode⟩ := (hC p).mp hp
  exact ⟨i,x,i,x,hcode,hcode,hL.1 i x hi hx⟩

theorem related_symm {w D mul F p q : M.Carrier .set} (hL : MeetsLaws w D mul F)
    (h : Related w D mul F p q) : Related w D mul F q p := by
  obtain ⟨i,x,j,y,hp,hq,h⟩ := h
  exact ⟨j,y,i,x,hq,hp,hL.2.1 i x j y h⟩

theorem related_trans {w D mul F p q r : M.Carrier .set} (hL : MeetsLaws w D mul F)
    (hpq : Related w D mul F p q) (hqr : Related w D mul F q r) : Related w D mul F p r := by
  obtain ⟨i,x,j,y,hp,hq,hxy⟩ := hpq
  obtain ⟨j',y',k,z,hq',hr,hyz⟩ := hqr
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  exact ⟨i,x,k,z,hp,hr,hL.2.2.1 i x j y k z hxy hyz⟩

def related {m : Nat} (w D mul F p q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE (.conj
    (PureKuratowskiProject.code (.bound p.succ.succ.succ.succ) (.bound 3) (.bound 2))
    (.conj (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ) (.bound 1) (.bound 0))
      (meets w.succ.succ.succ.succ D.succ.succ.succ.succ mul.succ.succ.succ.succ F.succ.succ.succ.succ 3 2 1 0))))))

theorem related_freeClosed {m : Nat} (w D mul F p q : Fin m) : (related w D mul F p q).FreeClosed := by
  simp -implicitDefEqProofs [related,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,meets_freeClosed]

theorem related_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F p q : Fin m) :
    Project.Formula.satisfies env (related w D mul F p q) ↔
      Related (env.bound w) (env.bound D) (env.bound mul) (env.bound F) (env.bound p) (env.bound q) := by
  simp only [related,Related,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,meets_semantics hM]
  rfl

def Class (w D mul F C p c : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q c ↔
    (Project.FirstOrderSemantics.reduct M).mem q C ∧ Related w D mul F p q

def eqClass {m : Nat} (w D mul F C p c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound C.succ)) (related w.succ D.succ mul.succ F.succ p.succ 0)))

theorem eqClass_freeClosed {m : Nat} (w D mul F C p c : Fin m) : (eqClass w D mul F C p c).FreeClosed := by
  simp -implicitDefEqProofs [eqClass,Definitional.Formula.FreeClosed,related_freeClosed]

theorem eqClass_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F C p c : Fin m) :
    Project.Formula.satisfies env (eqClass w D mul F C p c) ↔
      Class (env.bound w) (env.bound D) (env.bound mul) (env.bound F) (env.bound C) (env.bound p) (env.bound c) := by
  simp only [eqClass,Class,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,related_semantics hM]
  rfl

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF) (w D mul F C p : M.Carrier .set) :
    ∃ c, Class w D mul F C p c := by
  let schema : Project.UnarySchema 5 := { body := related 1 2 3 4 5 0, freeClosed := related_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases mul (Fin.cases F (fun _ => p)))), free := fun _ => w }
  obtain ⟨c,hc⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env C
  exact ⟨c,fun q => (hc q).trans (and_congr_right fun _ => related_semantics hM (env.push q) 1 2 3 4 5 0)⟩

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF) {w D mul F C p c d : M.Carrier .set}
    (hc : Class w D mul F C p c) (hd : Class w D mul F C p d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun q => (hc q).trans (hd q).symm)

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {w D mul F C p q c d : M.Carrier .set}
    (hC : Representatives w D C) (hL : MeetsLaws w D mul F)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q C)
    (hc : Class w D mul F C p c) (hd : Class w D mul F C q d) :
    c = d ↔ Related w D mul F p q := by
  constructor
  · intro he
    have hself := (hd q).mpr ⟨hq,related_refl hC hL hq⟩
    exact ((hc q).mp (he.symm ▸ hself)).2
  · intro hpq
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro r
    rw [hc r,hd r]
    exact and_congr_right fun _ => ⟨fun h => related_trans hL (related_symm hL hpq) h,
      fun h => related_trans hL hpq h⟩

def Letters (w D mul F C L : M.Carrier .set) : Prop := ∀ c,
  (Project.FirstOrderSemantics.reduct M).mem c L ↔
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p C ∧ Class w D mul F C p c

theorem exists_letters (hM : FirstOrder.Theory.Models M nativeZF) (w D mul F C : M.Carrier .set) :
    ∃ L, Letters w D mul F C L := by
  let schema : Project.BinarySchema 5 := { body := eqClass 2 3 4 5 6 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases mul (Fin.cases F (fun _ => C)))), free := fun _ => w }
  have he : ∀ p c, schema.denote env p c ↔ Class w D mul F C p c :=
    fun p c => eqClass_semantics hM ((env.push p).push c) 2 3 4 5 6 1 0
  obtain ⟨L,hL⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env C (by
    intro p _
    obtain ⟨c,hc⟩ := exists_class hM w D mul F C p
    exact ⟨c,(he p c).mpr hc⟩) (by
    intro p c d hc hd
    exact class_unique hM ((he p c).mp hc) ((he p d).mp hd))
  exact ⟨L,fun c => (hL c).trans ⟨fun ⟨p,hp,hc⟩ => ⟨p,hp,(he p c).mp hc⟩,
    fun ⟨p,hp,hc⟩ => ⟨p,hp,(he p c).mpr hc⟩⟩⟩

def Projection (w D mul F C projection : M.Carrier .set) : Prop := ∀ p c,
  PureKuratowski.PairMember M p c projection ↔
    (Project.FirstOrderSemantics.reduct M).mem p C ∧ Class w D mul F C p c

theorem exists_projection (hM : FirstOrder.Theory.Models M nativeZF) {w D mul F C L : M.Carrier .set}
    (hL : Letters w D mul F C L) : ∃ projection, MapsTo C L projection ∧ Projection w D mul F C projection := by
  let schema : Project.BinarySchema 5 := { body := eqClass 2 3 4 5 6 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases mul (Fin.cases F (fun _ => C)))), free := fun _ => w }
  have he : ∀ p c, schema.denote env p c ↔ Class w D mul F C p c :=
    fun p c => eqClass_semantics hM ((env.push p).push c) 2 3 4 5 6 1 0
  obtain ⟨projection,hp,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := C) (target := L) (by
      intro p _
      obtain ⟨c,hc⟩ := exists_class hM w D mul F C p
      exact ⟨c,(he p c).mpr hc⟩) (by
      intro p _ c d hc hd
      exact class_unique hM ((he p c).mp hc) ((he p d).mp hd)) (by
      intro p c hp hc
      exact (hL c).mpr ⟨p,hp,(he p c).mp hc⟩)
  exact ⟨projection,(ForcingSupportSize.native_mapsTo hM C L projection).mpr hp,
    fun p c => (hgraph p c).trans (and_congr_right fun _ => he p c)⟩

def EqualityLaw (w D mul F projection : M.Carrier .set) : Prop := ∀ p q c d,
  PureKuratowski.PairMember M p c projection → PureKuratowski.PairMember M q d projection →
    (c = d ↔ Related w D mul F p q)

theorem equality_law (hM : FirstOrder.Theory.Models M nativeZF) {w D mul F C projection : M.Carrier .set}
    (hC : Representatives w D C) (hL : MeetsLaws w D mul F)
    (hp : Projection w D mul F C projection) : EqualityLaw w D mul F projection := by
  intro p q c d hpc hqd
  obtain ⟨_,hc⟩ := (hp p c).mp hpc
  obtain ⟨hqC,hd⟩ := (hp q d).mp hqd
  exact class_eq_iff hM hC hL hqC hc hd

theorem related_codes_iff {w D mul F p q i x j y : M.Carrier .set}
    (hp : PureKuratowski.Code M p i x) (hq : PureKuratowski.Code M q j y) :
    Related w D mul F p q ↔ Meets w D mul F i x j y := by
  constructor
  · rintro ⟨i',x',j',y',hp',hq',h⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
    exact h
  · exact fun h => ⟨i,x,j,y,hp,hq,h⟩

theorem letter_eq_iff {w D mul F projection i x j y c d : M.Carrier .set}
    (hE : EqualityLaw w D mul F projection)
    (hc : ForcingDiagramOrder.Product projection i x c) (hd : ForcingDiagramOrder.Product projection j y d) :
    c = d ↔ Meets w D mul F i x j y := by
  obtain ⟨p,hp,hpc⟩ := hc
  obtain ⟨q,hq,hqd⟩ := hd
  exact (hE p q c d hpc hqd).trans (related_codes_iff hp hq)

theorem letter_transition {w D mul F projection i j x y c d : M.Carrier .set}
    (hL : MeetsLaws w D mul F) (hE : EqualityLaw w D mul F projection)
    (hxy : ConstructionProbeTransitions.Transition D mul F i j x y)
    (hc : ForcingDiagramOrder.Product projection i x c) (hd : ForcingDiagramOrder.Product projection j y d) : c = d :=
  (letter_eq_iff hE hc hd).mpr (hL.2.2.2.1 i j x y hxy)

theorem projection_onto {w D mul F C L projection : M.Carrier .set}
    (hL : Letters w D mul F C L) (hp : Projection w D mul F C projection)
    {c : M.Carrier .set} (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p C ∧ PureKuratowski.PairMember M p c projection := by
  obtain ⟨p,hpC,hclass⟩ := (hL c).mp hc
  exact ⟨p,hpC,(hp p c).mpr ⟨hpC,hclass⟩⟩

def representatives {m : Nat} (w D C : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound C.succ)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound
    w.succ.succ.succ)) (.conj (.mem (.bound 0) (.bound D.succ.succ.succ)) (PureKuratowskiProject.code (.bound 2)
    (.bound 1) (.bound 0))))))))

theorem representatives_freeClosed {m : Nat} (w D C : Fin m) : (representatives w D C).FreeClosed := by
  simp -implicitDefEqProofs [representatives,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem representatives_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D C : Fin m) :
    Project.Formula.satisfies env (representatives w D C) ↔
      Representatives (env.bound w) (env.bound D) (env.bound C) := by
  simp only [representatives, Representatives, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Term.eval_bound, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff, KuratowskiZF.code_correct hM]
  rfl

def letters {m : Nat} (w D mul F C L : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound L.succ)) (.existsE (.conj (.mem (.bound 0) (.bound C.succ.succ))
    (eqClass w.succ.succ D.succ.succ mul.succ.succ F.succ.succ C.succ.succ 0 1)))))

theorem letters_freeClosed {m : Nat} (w D mul F C L : Fin m) : (letters w D mul F C L).FreeClosed := by
  simp -implicitDefEqProofs [letters,Definitional.Formula.FreeClosed,eqClass_freeClosed]

theorem letters_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F C L : Fin m) :
    Project.Formula.satisfies env (letters w D mul F C L) ↔
      Letters (env.bound w) (env.bound D) (env.bound mul) (env.bound F) (env.bound C) (env.bound L) := by
  simp only [letters, Letters, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, eqClass_semantics hM]
  rfl

def projectionGraph {m : Nat} (w D mul F C projection : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge projection.succ.succ 1 0)) (.conj
    (.mem (.bound 1) (.bound C.succ.succ)) (eqClass w.succ.succ D.succ.succ mul.succ.succ F.succ.succ
    C.succ.succ 1 0)))))

theorem projectionGraph_freeClosed {m : Nat} (w D mul F C projection : Fin m) : (projectionGraph w D mul F C projection).FreeClosed := by
  simp -implicitDefEqProofs [projectionGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eqClass_freeClosed]

theorem projectionGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F C projection : Fin m) :
    Project.Formula.satisfies env (projectionGraph w D mul F C projection) ↔
      Projection (env.bound w) (env.bound D) (env.bound mul) (env.bound F) (env.bound C) (env.bound projection) := by
  simp only [projectionGraph, Projection, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Term.eval_bound, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, eqClass_semantics hM]
  rfl

def equalityLaw {m : Nat} (w D mul F projection : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    projection.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    projection.succ.succ.succ.succ 2 0)) (.iff (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (related w.succ.succ.succ.succ
    D.succ.succ.succ.succ mul.succ.succ.succ.succ F.succ.succ.succ.succ 3 2))))))))

theorem equalityLaw_freeClosed {m : Nat} (w D mul F projection : Fin m) : (equalityLaw w D mul F projection).FreeClosed := by
  simp -implicitDefEqProofs [equalityLaw,Project.Formula.extensionalEq,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,related_freeClosed]

theorem equalityLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F projection : Fin m) :
    Project.Formula.satisfies env (equalityLaw w D mul F projection) ↔
      EqualityLaw (env.bound w) (env.bound D) (env.bound mul) (env.bound F) (env.bound projection) := by
  simp only [equalityLaw, EqualityLaw, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_extensionalEq_iff_eq
    (ModelTransfer.extensionality hM), GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, related_semantics hM]
  rfl

/-- Construct the actual quotient from the original source Path, discharging
all equivalence-law premises with the preceding source transition proof. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (.forallE (.neg (.mem (.bound 0) (.bound 5))))
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 7) 2 3))
        (.imp (ConstructionProbePath.path (0 : Fin 7) 1 2 3 4 5 6)
          (.existsE (.existsE (.existsE (.existsE
            (.conj (ConstructionProbePath.factorTable (4 : Fin 11) 5 6 10 3)
              (.conj (representatives (4 : Fin 11) 5 2)
                (.conj (letters (4 : Fin 11) 5 6 3 2 1)
                  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 11) 2 1))
                    (.conj (projectionGraph (4 : Fin 11) 5 6 3 2 0)
                      (equalityLaw (4 : Fin 11) 5 6 3 0))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbePath.path_freeClosed,ConstructionProbePath.factorTable_freeClosed,
    representatives_freeClosed,letters_freeClosed,projectionGraph_freeClosed,equalityLaw_freeClosed]

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
    projectionGraph_semantics hM,equalityLaw_semantics hM]
  intro hw hz hm hp
  obtain ⟨pairs,hpairs⟩ := ConstructionProbePath.exists_ordered_pairs hM (bound 0)
  obtain ⟨F,_,hF⟩ := ConstructionProbePath.exists_factor_table hM hm hp hpairs
  obtain ⟨T,_,hT⟩ := ConstructionProbePath.exists_terminal_table hM hm hp
  have hTable := ConstructionProbePath.table_laws hM hw hz hm hp hF hT
  have hLaws := ConstructionProbeTransitions.meets_laws hM hw hm hp hF hTable
  obtain ⟨C,hC⟩ := exists_representatives hM (bound 0) (bound 1)
  obtain ⟨L,hL⟩ := exists_letters hM (bound 0) (bound 1) (bound 2) F C
  obtain ⟨p,hp,hProjection⟩ := exists_projection hM hL
  exact ⟨F,C,L,p,hF,hC,hL,hp,hProjection,equality_law hM hC hLaws hProjection⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeLetters
