/- Pinned MergerWords.copySetoid/Copies/copy_eq_iff/copy_injective.
Use the EXISTING ProbeLetters native Separation/functional-image/function-graph
pattern with the actual prescribed-copy relation. No equivalence closure, choice
of representatives, or external quotient model. Consumer: Copies right action. -/
import PPAC.Migration.ConstructionMergerRelations
import PPAC.Migration.ConstructionProbeAction

namespace PPAC.Migration.ConstructionMergerCopies
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerRelations (CopyRel Valid rel rel_freeClosed rel_semantics)
open ConstructionProbeLetters (Representatives exists_representatives)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Related (n D mul P p q : M.Carrier .set) : Prop := ∃ i x j y,
  PureKuratowski.Code M p i x ∧ PureKuratowski.Code M q j y ∧ CopyRel n D mul P i x j y

theorem related_refl {n D mul P C p : M.Carrier .set} (hC : Representatives n D C)
    (hL : Valid n D mul P) (hp : (Project.FirstOrderSemantics.reduct M).mem p C) : Related n D mul P p p := by
  obtain ⟨i,x,hi,hx,hcode⟩ := (hC p).mp hp
  exact ⟨i,x,i,x,hcode,hcode,hL.1 i x hi hx⟩

theorem related_symm {n D mul P p q : M.Carrier .set} (hL : Valid n D mul P)
    (h : Related n D mul P p q) : Related n D mul P q p := by
  obtain ⟨i,x,j,y,hp,hq,h⟩ := h
  exact ⟨j,y,i,x,hq,hp,hL.2.1 i x j y h⟩

theorem related_trans {n D mul P p q r : M.Carrier .set} (hL : Valid n D mul P)
    (hpq : Related n D mul P p q) (hqr : Related n D mul P q r) : Related n D mul P p r := by
  obtain ⟨i,x,j,y,hp,hq,hxy⟩ := hpq
  obtain ⟨j',y',k,z,hq',hr,hyz⟩ := hqr
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  exact ⟨i,x,k,z,hp,hr,hL.2.2 i x j y k z hxy hyz⟩

def related {m : Nat} (n D mul P p q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE (.conj
    (PureKuratowskiProject.code (.bound p.succ.succ.succ.succ) (.bound 3) (.bound 2))
    (.conj (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ) (.bound 1) (.bound 0))
      (rel n.succ.succ.succ.succ D.succ.succ.succ.succ mul.succ.succ.succ.succ P.succ.succ.succ.succ 3 2 1 0))))))

theorem related_freeClosed {m : Nat} (n D mul P p q : Fin m) : (related n D mul P p q).FreeClosed := by
  simp -implicitDefEqProofs [related,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,rel_freeClosed]

theorem related_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul P p q : Fin m) :
    Project.Formula.satisfies env (related n D mul P p q) ↔
      Related (env.bound n) (env.bound D) (env.bound mul) (env.bound P) (env.bound p) (env.bound q) := by
  simp only [related,Related,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,rel_semantics hM]
  rfl

def Class (n D mul P C p c : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q c ↔
    (Project.FirstOrderSemantics.reduct M).mem q C ∧ Related n D mul P p q

def eqClass {m : Nat} (n D mul P C p c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound C.succ)) (related n.succ D.succ mul.succ P.succ p.succ 0)))

theorem eqClass_freeClosed {m : Nat} (n D mul P C p c : Fin m) : (eqClass n D mul P C p c).FreeClosed := by
  simp -implicitDefEqProofs [eqClass,Definitional.Formula.FreeClosed,related_freeClosed]

theorem eqClass_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul P C p c : Fin m) :
    Project.Formula.satisfies env (eqClass n D mul P C p c) ↔
      Class (env.bound n) (env.bound D) (env.bound mul) (env.bound P) (env.bound C) (env.bound p) (env.bound c) := by
  simp only [eqClass,Class,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,related_semantics hM]
  rfl

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF) (n D mul P C p : M.Carrier .set) :
    ∃ c, Class n D mul P C p c := by
  let schema : Project.UnarySchema 5 := { body := related 1 2 3 4 5 0, freeClosed := related_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases n (Fin.cases D (Fin.cases mul (Fin.cases P (fun _ => p)))), free := fun _ => n }
  obtain ⟨c,hc⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env C
  exact ⟨c,fun q => (hc q).trans (and_congr_right fun _ => related_semantics hM (env.push q) 1 2 3 4 5 0)⟩

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF) {n D mul P C p c d : M.Carrier .set}
    (hc : Class n D mul P C p c) (hd : Class n D mul P C p d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun q => (hc q).trans (hd q).symm)

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {n D mul P C p q c d : M.Carrier .set}
    (hC : Representatives n D C) (hL : Valid n D mul P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q C)
    (hc : Class n D mul P C p c) (hd : Class n D mul P C q d) :
    c = d ↔ Related n D mul P p q := by
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

def Copies (n D mul P C L : M.Carrier .set) : Prop := ∀ c,
  (Project.FirstOrderSemantics.reduct M).mem c L ↔
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p C ∧ Class n D mul P C p c

theorem exists_copies (hM : FirstOrder.Theory.Models M nativeZF) (n D mul P C : M.Carrier .set) :
    ∃ L, Copies n D mul P C L := by
  let schema : Project.BinarySchema 5 := { body := eqClass 2 3 4 5 6 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases n (Fin.cases D (Fin.cases mul (Fin.cases P (fun _ => C)))), free := fun _ => n }
  have he : ∀ p c, schema.denote env p c ↔ Class n D mul P C p c :=
    fun p c => eqClass_semantics hM ((env.push p).push c) 2 3 4 5 6 1 0
  obtain ⟨L,hL⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env C (by
    intro p _
    obtain ⟨c,hc⟩ := exists_class hM n D mul P C p
    exact ⟨c,(he p c).mpr hc⟩) (by
    intro p c d hc hd
    exact class_unique hM ((he p c).mp hc) ((he p d).mp hd))
  exact ⟨L,fun c => (hL c).trans ⟨fun ⟨p,hp,hc⟩ => ⟨p,hp,(he p c).mp hc⟩,
    fun ⟨p,hp,hc⟩ => ⟨p,hp,(he p c).mpr hc⟩⟩⟩

def Projection (n D mul P C projection : M.Carrier .set) : Prop := ∀ p c,
  PureKuratowski.PairMember M p c projection ↔
    (Project.FirstOrderSemantics.reduct M).mem p C ∧ Class n D mul P C p c

theorem exists_projection (hM : FirstOrder.Theory.Models M nativeZF) {n D mul P C L : M.Carrier .set}
    (hL : Copies n D mul P C L) : ∃ projection, MapsTo C L projection ∧ Projection n D mul P C projection := by
  let schema : Project.BinarySchema 5 := { body := eqClass 2 3 4 5 6 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases n (Fin.cases D (Fin.cases mul (Fin.cases P (fun _ => C)))), free := fun _ => n }
  have he : ∀ p c, schema.denote env p c ↔ Class n D mul P C p c :=
    fun p c => eqClass_semantics hM ((env.push p).push c) 2 3 4 5 6 1 0
  obtain ⟨projection,hp,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := C) (target := L) (by
      intro p _
      obtain ⟨c,hc⟩ := exists_class hM n D mul P C p
      exact ⟨c,(he p c).mpr hc⟩) (by
      intro p _ c d hc hd
      exact class_unique hM ((he p c).mp hc) ((he p d).mp hd)) (by
      intro p c hp hc
      exact (hL c).mpr ⟨p,hp,(he p c).mp hc⟩)
  exact ⟨projection,(ForcingSupportSize.native_mapsTo hM C L projection).mpr hp,
    fun p c => (hgraph p c).trans (and_congr_right fun _ => he p c)⟩

def EqualityLaw (n D mul P projection : M.Carrier .set) : Prop := ∀ p q c d,
  PureKuratowski.PairMember M p c projection → PureKuratowski.PairMember M q d projection →
    (c = d ↔ Related n D mul P p q)

theorem equality_law (hM : FirstOrder.Theory.Models M nativeZF) {n D mul P C projection : M.Carrier .set}
    (hC : Representatives n D C) (hL : Valid n D mul P)
    (hp : Projection n D mul P C projection) : EqualityLaw n D mul P projection := by
  intro p q c d hpc hqd
  obtain ⟨_,hc⟩ := (hp p c).mp hpc
  obtain ⟨hqC,hd⟩ := (hp q d).mp hqd
  exact class_eq_iff hM hC hL hqC hc hd

theorem related_codes_iff {n D mul P p q i x j y : M.Carrier .set}
    (hp : PureKuratowski.Code M p i x) (hq : PureKuratowski.Code M q j y) :
    Related n D mul P p q ↔ CopyRel n D mul P i x j y := by
  constructor
  · rintro ⟨i',x',j',y',hp',hq',h⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
    exact h
  · exact fun h => ⟨i,x,j,y,hp,hq,h⟩

theorem copy_eq_iff {n D mul P projection i x j y c d : M.Carrier .set}
    (hE : EqualityLaw n D mul P projection)
    (hc : ForcingDiagramOrder.Product projection i x c) (hd : ForcingDiagramOrder.Product projection j y d) :
    c = d ↔ CopyRel n D mul P i x j y := by
  obtain ⟨p,hp,hpc⟩ := hc
  obtain ⟨q,hq,hqd⟩ := hd
  exact (hE p q c d hpc hqd).trans (related_codes_iff hp hq)

theorem projection_onto {n D mul P C L projection : M.Carrier .set}
    (hL : Copies n D mul P C L) (hp : Projection n D mul P C projection)
    {c : M.Carrier .set} (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p C ∧ PureKuratowski.PairMember M p c projection := by
  obtain ⟨p,hpC,hclass⟩ := (hL c).mp hc
  exact ⟨p,hpC,(hp p c).mpr ⟨hpC,hclass⟩⟩

theorem representative {n D mul P C L projection c : M.Carrier .set}
    (hC : Representatives n D C) (hL : Copies n D mul P C L)
    (hp : Projection n D mul P C projection)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ i x, (Project.FirstOrderSemantics.reduct M).mem i n ∧
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ ForcingDiagramOrder.Product projection i x c := by
  obtain ⟨p,hpC,hpc⟩ := projection_onto hL hp hc
  obtain ⟨i,x,hi,hx,hcode⟩ := (hC p).mp hpC
  exact ⟨i,x,hi,hx,p,hcode,hpc⟩

theorem copy_injective {n D mul P C L projection i x y c : M.Carrier .set}
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection)
    (hx : ForcingDiagramOrder.Product projection i x c)
    (hy : ForcingDiagramOrder.Product projection i y c) : x = y := by
  obtain ⟨hi,hxD⟩ := ConstructionProbeAction.projected_indices hC hp hx
  have hyD := (ConstructionProbeAction.projected_indices hC hp hy).2
  exact (ConstructionMergerRelations.rel_same_copy hi hxD hyD).mp ((copy_eq_iff hEq hx hy).mp rfl)

theorem exists_quotient (hM : FirstOrder.Theory.Models M nativeZF)
    (n D mul P : M.Carrier .set) (hValid : Valid n D mul P) :
    ∃ C L projection, Representatives n D C ∧ MapsTo C L projection ∧
      Copies n D mul P C L ∧ Projection n D mul P C projection ∧ EqualityLaw n D mul P projection := by
  obtain ⟨C,hC⟩ := exists_representatives hM n D
  obtain ⟨L,hL⟩ := exists_copies hM n D mul P C
  obtain ⟨projection,hp,hProjection⟩ := exists_projection hM hL
  exact ⟨C,L,projection,hC,hp,hL,hProjection,equality_law hM hC hValid hProjection⟩

def copies {m : Nat} (n D mul P C L : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound L.succ)) (.existsE (.conj (.mem (.bound 0) (.bound C.succ.succ))
    (eqClass n.succ.succ D.succ.succ mul.succ.succ P.succ.succ C.succ.succ 0 1)))))

theorem copies_freeClosed {m : Nat} (n D mul P C L : Fin m) : (copies n D mul P C L).FreeClosed := by
  simp -implicitDefEqProofs [copies,Definitional.Formula.FreeClosed,eqClass_freeClosed]

theorem copies_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul P C L : Fin m) :
    Project.Formula.satisfies env (copies n D mul P C L) ↔
      Copies (env.bound n) (env.bound D) (env.bound mul) (env.bound P) (env.bound C) (env.bound L) := by
  simp only [copies, Copies, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, eqClass_semantics hM]
  rfl

def projectionGraph {m : Nat} (n D mul P C projection : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge projection.succ.succ 1 0)) (.conj
    (.mem (.bound 1) (.bound C.succ.succ)) (eqClass n.succ.succ D.succ.succ mul.succ.succ P.succ.succ
    C.succ.succ 1 0)))))

theorem projectionGraph_freeClosed {m : Nat} (n D mul P C projection : Fin m) : (projectionGraph n D mul P C projection).FreeClosed := by
  simp -implicitDefEqProofs [projectionGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eqClass_freeClosed]

theorem projectionGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul P C projection : Fin m) :
    Project.Formula.satisfies env (projectionGraph n D mul P C projection) ↔
      Projection (env.bound n) (env.bound D) (env.bound mul) (env.bound P) (env.bound C) (env.bound projection) := by
  simp only [projectionGraph, Projection, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Term.eval_bound, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, eqClass_semantics hM]
  rfl

def equalityLaw {m : Nat} (n D mul P projection : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    projection.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    projection.succ.succ.succ.succ 2 0)) (.iff (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (related n.succ.succ.succ.succ
    D.succ.succ.succ.succ mul.succ.succ.succ.succ P.succ.succ.succ.succ 3 2))))))))

theorem equalityLaw_freeClosed {m : Nat} (n D mul P projection : Fin m) : (equalityLaw n D mul P projection).FreeClosed := by
  simp -implicitDefEqProofs [equalityLaw,Project.Formula.extensionalEq,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,related_freeClosed]

theorem equalityLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul P projection : Fin m) :
    Project.Formula.satisfies env (equalityLaw n D mul P projection) ↔
      EqualityLaw (env.bound n) (env.bound D) (env.bound mul) (env.bound P) (env.bound projection) := by
  simp only [equalityLaw, EqualityLaw, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_extensionalEq_iff_eq
    (ModelTransfer.extensionality hM), GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, related_semantics hM]
  rfl

end PPAC.Migration.ConstructionMergerCopies
