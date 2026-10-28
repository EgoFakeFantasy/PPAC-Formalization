/- Pinned Diagrams.exists_overlap_prescription:180 -> amalgamate:217.
The optional table is the ORIGINAL partial graph of (i,j) -> (a,b).
Reuse existing uniformize_formula_l, native products/Separation and literal
CopyRel/WellFormed. All indices are internal sets; no standard-n restriction. -/
import PPAC.Migration.ConstructionDiagramPlacements

namespace PPAC.Migration.ConstructionDiagramPrescription
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection)
open ForcingConditionGraphs (FunctionOn)
open ForcingDiagramOrder (Sub Product)
open ConstructionDiagramPlacements (ExactOverlap RangeIntersection LabelCones)
open ConstructionMergerRelations (Start Prescription CopyRel Valid)
open ConstructionRequestCarrier (WellFormed)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Family (n D I F : M.Carrier .set) : Prop :=
  FunctionOn n F ∧ ∀ i r, PureKuratowski.PairMember M i r F → Injection D I r

def ExactFamily (n D I mul F : M.Carrier .set) : Prop :=
  ∀ i j r s, (Project.FirstOrderSemantics.reduct M).mem i n →
    (Project.FirstOrderSemantics.reduct M).mem j n → i ≠ j →
    PureKuratowski.PairMember M i r F → PureKuratowski.PairMember M j s F → ExactOverlap D I mul r s

def CommonRoot (D I mul r s a b : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem a D ∧ (Project.FirstOrderSemantics.reduct M).mem b D ∧
    ∃ p, Injection D I p ∧ Sub D mul r a p ∧ Sub D mul s b p ∧ RangeIntersection D r s p

def Candidate (n D I mul F key ab : M.Carrier .set) : Prop :=
  ∃ i j a b r s, PureKuratowski.Code M key i j ∧ PureKuratowski.Code M ab a b ∧
    (Project.FirstOrderSemantics.reduct M).mem i n ∧ (Project.FirstOrderSemantics.reduct M).mem j n ∧
    i ≠ j ∧ PureKuratowski.PairMember M i r F ∧ PureKuratowski.PairMember M j s F ∧ CommonRoot D I mul r s a b

def KeyDomain (n D I mul F U : M.Carrier .set) : Prop :=
  ∀ key, (Project.FirstOrderSemantics.reduct M).mem key U ↔ ∃ ab, Candidate n D I mul F key ab

def Matches (n D mul F P : M.Carrier .set) : Prop :=
  ∀ i x j y r s, (Project.FirstOrderSemantics.reduct M).mem i n →
    (Project.FirstOrderSemantics.reduct M).mem x D →
    (Project.FirstOrderSemantics.reduct M).mem j n →
    (Project.FirstOrderSemantics.reduct M).mem y D →
    PureKuratowski.PairMember M i r F → PureKuratowski.PairMember M j s F →
    ((∃ z, PureKuratowski.PairMember M x z r ∧ PureKuratowski.PairMember M y z s) ↔ CopyRel n D mul P i x j y)

def NoDiagonal (P : M.Carrier .set) : Prop := ∀ i a b, ¬ Start P i i a b

def DisjointNone (D F P : M.Carrier .set) : Prop :=
  ∀ i j r s, PureKuratowski.PairMember M i r F → PureKuratowski.PairMember M j s F →
    (∀ z, ¬ (ConstructionPlacementTriple.ImageAt r D z ∧ ConstructionPlacementTriple.ImageAt s D z)) →
    ∀ a b, ¬ Start P i j a b

def Result (n D mul F P : M.Carrier .set) : Prop :=
  WellFormed n D P ∧ Prescription n D P ∧ Valid n D mul P ∧ Matches n D mul F P ∧ NoDiagonal P ∧ DisjointNone D F P

def commonRoot {m : Nat} (D I mul r s a b : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound a) (.bound D)) (.conj (.mem (.bound b) (.bound D)) (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.injection (0 : Fin (m+1)) D.succ I.succ)) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ mul.succ r.succ a.succ (0 : Fin (m+1)))) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ mul.succ s.succ b.succ (0 : Fin (m+1))))
  (ConstructionDiagramPlacements.rangeIntersection D.succ r.succ s.succ (0 : Fin (m+1)))))))))
theorem commonRoot_freeClosed {m : Nat} (D I mul r s a b : Fin m) :
    (commonRoot D I mul r s a b).FreeClosed := by
  simp -implicitDefEqProofs [commonRoot,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionDiagramPlacements.rangeIntersection_freeClosed]

theorem commonRoot_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul r s a b : Fin m) :
    Project.Formula.satisfies env (commonRoot D I mul r s a b) ↔
      CommonRoot (env.bound D) (env.bound I) (env.bound mul) (env.bound r) (env.bound s) (env.bound a) (env.bound b) := by
  simp only [commonRoot,CommonRoot,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ConstructionDiagramPlacements.rangeIntersection_semantics hM,Project.Term.eval_bound]
  rfl

def candidate {m : Nat} (n D I mul F key ab : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound
  key.succ.succ.succ.succ.succ.succ) (.bound (5 : Fin (m+6))) (.bound (4 : Fin (m+6)))) (.conj
  (PureKuratowskiProject.code (.bound ab.succ.succ.succ.succ.succ.succ) (.bound (3 : Fin (m+6))) (.bound (2
  : Fin (m+6)))) (.conj (.mem (.bound (5 : Fin (m+6))) (.bound n.succ.succ.succ.succ.succ.succ)) (.conj
  (.mem (.bound (4 : Fin (m+6))) (.bound n.succ.succ.succ.succ.succ.succ)) (.conj (.neg
  (Project.Formula.extensionalEq (.bound (5 : Fin (m+6))) (.bound (4 : Fin (m+6))))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (1 : Fin
  (m+6)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ (4 : Fin
  (m+6)) (0 : Fin (m+6)))) (commonRoot D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ (1 : Fin (m+6)) (0 : Fin (m+6)) (3 : Fin (m+6)) (2 : Fin
  (m+6))))))))))))))))
theorem candidate_freeClosed {m : Nat} (n D I mul F key ab : Fin m) :
    (candidate n D I mul F key ab).FreeClosed := by
  simp -implicitDefEqProofs [candidate,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,
    Project.Formula.extensionalEq,ProjectSyntax.freeClosed,commonRoot_freeClosed]

theorem candidate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D I mul F key ab : Fin m) :
    Project.Formula.satisfies env (candidate n D I mul F key ab) ↔
      Candidate (env.bound n) (env.bound D) (env.bound I) (env.bound mul) (env.bound F) (env.bound key) (env.bound ab) := by
  simp only [candidate,Candidate,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,commonRoot_semantics hM,Project.Term.eval_bound]
  rfl

theorem exists_selected_table (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) (n D I mul F : M.Carrier .set) :
    ∃ U DD P, KeyDomain n D I mul F U ∧
      (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) DD D D ∧
      (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) P U DD ∧
      ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨NN,hNN⟩ := ZF.exists_cartesianProduct hZF pair n n
  obtain ⟨DD,hDD⟩ := ZF.exists_cartesianProduct hZF pair D D
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases n (Fin.cases D (Fin.cases I (Fin.cases mul (fun _ => F)))), free := fun _ => n }
  let schema : Project.BinarySchema 5 := {
    body := candidate 2 3 4 5 6 1 0
    freeClosed := candidate_freeClosed _ _ _ _ _ _ _ }
  have hSchema key ab : schema.denote env key ab ↔ Candidate n D I mul F key ab := by
    simpa only [Project.BinarySchema.denote,schema] using! candidate_semantics hM ((env.push key).push ab) 2 3 4 5 6 1 0
  let domainSchema : Project.UnarySchema 5 := {
    body := .existsE (candidate 2 3 4 5 6 1 0)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,candidate_freeClosed] }
  obtain ⟨U,hU⟩ := ZF.separation_exists_d hZF domainSchema env NN
  have hDomain : KeyDomain n D I mul F U := by
    intro key
    have hd : domainSchema.denote env key ↔ ∃ ab, Candidate n D I mul F key ab := by
      simpa only [Project.UnarySchema.denote,domainSchema,Project.Formula.satisfies_exists_iff] using!
        exists_congr (fun ab => candidate_semantics hM ((env.push key).push ab) 2 3 4 5 6 1 0)
    constructor
    · intro hk
      exact hd.mp ((hU key).mp hk).2
    · rintro ⟨ab,h⟩
      have hSaved := h
      obtain ⟨i,j,a,b,r,s,hkey,_,hi,hj,_⟩ := h
      exact (hU key).mpr ⟨(hNN key).mpr ⟨i,hi,j,hj,hkey⟩,hd.mpr ⟨ab,hSaved⟩⟩
  obtain ⟨P,hP,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l pair
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema env (X := U) (Y := DD) (by
      intro key hk
      obtain ⟨ab,h⟩ := (hDomain key).mp hk
      have hDDab : (Project.FirstOrderSemantics.reduct M).mem ab DD := by
        obtain ⟨i,j,a,b,r,s,_,hab,_,_,_,_,_,ha,hb,_⟩ := h
        exact (hDD ab).mpr ⟨a,ha,b,hb,hab⟩
      exact ⟨ab,hDDab,(hSchema key ab).mpr h⟩)
  exact ⟨U,DD,P,hDomain,hDD,hP,fun key ab h => (hSchema key ab).mp (hSelect key ab h)⟩

theorem start_selected {n D I mul F P i j a b : M.Carrier .set}
    (hSelect : ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab)
    (h : Start P i j a b) :
    ∃ r s, PureKuratowski.PairMember M i r F ∧ PureKuratowski.PairMember M j s F ∧
      (Project.FirstOrderSemantics.reduct M).mem i n ∧ (Project.FirstOrderSemantics.reduct M).mem j n ∧
      i ≠ j ∧ CommonRoot D I mul r s a b := by
  obtain ⟨ab,hab,key,hkey,hPair⟩ := h
  obtain ⟨u,v,c,d,r,s,hKey,hAB,hu,hv,huv,hur,hvs,hRoot⟩ := hSelect key ab hPair
  obtain ⟨ei,ej⟩ := PureKuratowski.code_injective hkey hKey
  obtain ⟨ea,eb⟩ := PureKuratowski.code_injective hab hAB
  subst u; subst v; subst c; subst d
  exact ⟨r,s,hur,hvs,hu,hv,huv,hRoot⟩

theorem table_wellFormed (hM : FirstOrder.Theory.Models M nativeZF)
    {n D I mul F U DD P : M.Carrier .set}
    (hP : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) P U DD)
    (hSelect : ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab) :
    WellFormed n D P := by
  intro row hrow
  obtain ⟨key,ab,hrowCode⟩ := hP.1.1 row hrow
  obtain ⟨i,j,a,b,r,s,hKey,hAB,hi,hj,_,_,_,hRoot⟩ := hSelect key ab ⟨row,hrowCode,hrow⟩
  exact ⟨i,j,a,b,key,ab,hrowCode,hKey,hAB,hi,hj,hRoot.1,hRoot.2.1⟩

theorem table_prescription (hM : FirstOrder.Theory.Models M nativeZF)
    {n D I mul F U DD P : M.Carrier .set}
    (hP : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) P U DD)
    (hSelect : ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab) :
    Prescription n D P := by
  refine ⟨?_,?_⟩
  · intro i j a b h
    obtain ⟨r,s,_,_,hi,hj,_,hRoot⟩ := start_selected hSelect h
    exact ⟨hi,hj,hRoot.1,hRoot.2.1⟩
  · intro i j a b c d h h'
    let pair := KuratowskiZF.interpretation hM
    obtain ⟨ab,hab,key,hkey,hPair⟩ := h
    obtain ⟨cd,hcd,key',hkey',hPair'⟩ := h'
    have ek := pair.unique hkey hkey'
    subst key'
    have ev := hP.1.2 key ab cd hPair hPair'
    subst cd
    exact PureKuratowski.code_injective hab hcd

theorem start_label_cones {n D I mul F P i j r s a b : M.Carrier .set}
    (hF : Family n D I F)
    (hSelect : ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab)
    (hStart : Start P i j a b)
    (hri : PureKuratowski.PairMember M i r F) (hsj : PureKuratowski.PairMember M j s F) :
    LabelCones D mul r s a b := by
  obtain ⟨r',s',hir,hjs,_,_,_,_,_,p,hp,ha,hb,hInter⟩ := start_selected hSelect hStart
  have er := ForcingConditionGraphs.function_unique hF.1 hri hir
  have es := ForcingConditionGraphs.function_unique hF.1 hsj hjs
  subst r'; subst s'
  exact ConstructionDiagramPlacements.equal_iff_of_common_sub (hF.2 i r hri) (hF.2 j s hsj) hp ha hb hInter

theorem table_matches (hM : FirstOrder.Theory.Models M nativeZF)
    {n D I mul F U DD P : M.Carrier .set}
    (hF : Family n D I F) (hExact : ExactFamily n D I mul F)
    (hDomain : KeyDomain n D I mul F U)
    (hDD : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) DD D D)
    (hP : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) P U DD)
    (hSelect : ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab) :
    Matches n D mul F P := by
  let pair := KuratowskiZF.interpretation hM
  intro i x j y r s hi hx hj hy hri hsj
  by_cases hij : i = j
  · subst j
    have er := ForcingConditionGraphs.function_unique hF.1 hri hsj
    subst s
    apply Iff.trans ?_ (ConstructionMergerRelations.rel_same_copy hi hx hy).symm
    constructor
    · rintro ⟨z,hxz,hyz⟩
      exact (hF.2 i r hri).2 x y z hxz hyz
    · intro hxy
      subst y
      obtain ⟨z,hxz,_⟩ := (hF.2 i r hri).1.1.2 x hx
      exact ⟨z,hxz,hxz⟩
  · constructor
    · intro hLabel
      rcases hExact i j r s hi hj hij hri hsj with hDisjoint | ⟨a,b,p,ha,hb,hp,hSubR,hSubS,hInter⟩
      · obtain ⟨z,hxz,hyz⟩ := hLabel
        exact False.elim (hDisjoint z ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩)
      · obtain ⟨key,hkey⟩ := pair.total i j
        obtain ⟨ab,hab⟩ := pair.total a b
        have hCandidate : Candidate n D I mul F key ab :=
          ⟨i,j,a,b,r,s,hkey,hab,hi,hj,hij,hri,hsj,ha,hb,p,hp,hSubR,hSubS,hInter⟩
        obtain ⟨chosen,hChosen,hPair⟩ := hP.2.2 key ((hDomain key).mpr ⟨ab,hCandidate⟩)
        obtain ⟨c,hc,d,hd,hcd⟩ := (hDD chosen).mp hChosen
        have hStart : Start P i j c d := ⟨chosen,hcd,key,hkey,hPair⟩
        obtain ⟨t,ht,hct,hdt⟩ := (start_label_cones hF hSelect hStart hri hsj x y hx hy).mp hLabel
        exact ⟨hi,hx,hj,hy,Or.inr ⟨hij,c,d,t,hStart,ht,hct,hdt⟩⟩
    · rintro ⟨_,_,_,_,hRel⟩
      rcases hRel with ⟨he,_⟩ | ⟨_,a,b,t,hStart,ht,hat,hbt⟩
      · exact False.elim (hij he)
      · exact (start_label_cones hF hSelect hStart hri hsj x y hx hy).mpr ⟨t,ht,hat,hbt⟩

theorem matches_valid {n D I mul F P : M.Carrier .set}
    (hF : Family n D I F) (hMatch : Matches n D mul F P) : Valid n D mul P := by
  refine ⟨?_,?_,?_⟩
  · intro i x hi hx
    obtain ⟨r,hri,_⟩ := hF.1.2 i hi
    obtain ⟨z,hxz,_⟩ := (hF.2 i r hri).1.1.2 x hx
    exact (hMatch i x i x r r hi hx hi hx hri hri).mp ⟨z,hxz,hxz⟩
  · intro i x j y h
    have hSaved := h
    obtain ⟨hi,hx,hj,hy,_⟩ := h
    obtain ⟨r,hri,_⟩ := hF.1.2 i hi
    obtain ⟨s,hsj,_⟩ := hF.1.2 j hj
    obtain ⟨z,hxz,hyz⟩ := (hMatch i x j y r s hi hx hj hy hri hsj).mpr hSaved
    exact (hMatch j y i x s r hj hy hi hx hsj hri).mp ⟨z,hyz,hxz⟩
  · intro i x j y k z h h'
    have hSaved := h
    obtain ⟨hi,hx,hj,hy,_⟩ := h
    have hSaved' := h'
    obtain ⟨_,_,hk,hz,_⟩ := h'
    obtain ⟨r,hri,_⟩ := hF.1.2 i hi
    obtain ⟨s,hsj,_⟩ := hF.1.2 j hj
    obtain ⟨t,htk,_⟩ := hF.1.2 k hk
    obtain ⟨a,hxa,hya⟩ := (hMatch i x j y r s hi hx hj hy hri hsj).mpr hSaved
    obtain ⟨b,hyb,hzb⟩ := (hMatch j y k z s t hj hy hk hz hsj htk).mpr hSaved'
    have he := ForcingConditionGraphs.function_unique (hF.2 j s hsj).1.1 hya hyb
    exact (hMatch i x k z r t hi hx hk hz hri htk).mp ⟨a,hxa,by simpa only [he] using hzb⟩

theorem table_noDiagonal {n D I mul F P : M.Carrier .set}
    (hSelect : ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab) : NoDiagonal P := by
  intro i a b h
  obtain ⟨_,_,_,_,_,_,hne,_⟩ := start_selected hSelect h
  exact hne rfl

theorem no_start_of_disjoint {n D I mul F P i j r s : M.Carrier .set}
    (hF : Family n D I F)
    (hSelect : ∀ key ab, PureKuratowski.PairMember M key ab P → Candidate n D I mul F key ab)
    (hri : PureKuratowski.PairMember M i r F) (hsj : PureKuratowski.PairMember M j s F)
    (hDisjoint : ∀ z, ¬ (ConstructionPlacementTriple.ImageAt r D z ∧ ConstructionPlacementTriple.ImageAt s D z)) :
    ∀ a b, ¬ Start P i j a b := by
  intro a b h
  obtain ⟨r',s',hir,hjs,_,_,_,ha,_,p,hp,hSubR,hSubS,_⟩ := start_selected hSelect h
  have er := ForcingConditionGraphs.function_unique hF.1 hri hir
  have es := ForcingConditionGraphs.function_unique hF.1 hsj hjs
  subst r'; subst s'
  obtain ⟨z,haz,_⟩ := hp.1.1.2 a ha
  obtain ⟨_,x,hx,_,hxz⟩ := (hSubR a z).mp haz
  obtain ⟨_,y,hy,_,hyz⟩ := (hSubS a z).mp haz
  exact hDisjoint z ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩

theorem exists_prescription (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {n D I mul F : M.Carrier .set} (hF : Family n D I F) (hExact : ExactFamily n D I mul F) :
    ∃ P, Result n D mul F P := by
  obtain ⟨U,DD,P,hDomain,hDD,hP,hSelect⟩ := exists_selected_table hM hChoice n D I mul F
  have hMatch := table_matches hM hF hExact hDomain hDD hP hSelect
  exact ⟨P,table_wellFormed hM hP hSelect,table_prescription hM hP hSelect,
    matches_valid hF hMatch,hMatch,table_noDiagonal hSelect,fun _ _ _ _ hri hsj hDis => no_start_of_disjoint hF hSelect hri hsj hDis⟩

def family {m : Nat} (n D I F : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn F n))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ 1 0))
      (ProjectSyntax.encode id (Source.SetLanguage.injection (0 : Fin (m+2)) D.succ.succ I.succ.succ)))))

theorem family_freeClosed {m : Nat} (n D I F : Fin m) : (family n D I F).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D I F : Fin m) :
    Project.Formula.satisfies env (family n D I F) ↔
      Family (env.bound n) (env.bound D) (env.bound I) (env.bound F) := by
  simp only [family,Family,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,
    ForcingSupportSize.injection_semantics (M := M)]
  rfl

def exactFamily {m : Nat} (n D I mul F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound
  n.succ.succ.succ.succ)) (.imp (.mem (.bound (2 : Fin (m+4))) (.bound n.succ.succ.succ.succ)) (.imp (.neg
  (Project.Formula.extensionalEq (.bound (3 : Fin (m+4))) (.bound (2 : Fin (m+4))))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin
  (m+4)))) (ConstructionDiagramPlacements.exactOverlap D.succ.succ.succ.succ I.succ.succ.succ.succ
  mul.succ.succ.succ.succ (1 : Fin (m+4)) (0 : Fin (m+4))))))))))))
theorem exactFamily_freeClosed {m : Nat} (n D I mul F : Fin m) : (exactFamily n D I mul F).FreeClosed := by
  simp -implicitDefEqProofs [exactFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,ConstructionDiagramPlacements.exactOverlap_freeClosed]

theorem exactFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D I mul F : Fin m) :
    Project.Formula.satisfies env (exactFamily n D I mul F) ↔
      ExactFamily (env.bound n) (env.bound D) (env.bound I) (env.bound mul) (env.bound F) := by
  simp only [exactFamily,ExactFamily,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ConstructionDiagramPlacements.exactOverlap_semantics hM,Project.Term.eval_bound]
  rfl

def matchesF {m : Nat} (n D mul F P : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (5 : Fin (m+6))) (.bound
  n.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (4 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (3 : Fin (m+6))) (.bound
  n.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (2 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  F.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (1 : Fin (m+6)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) (0 : Fin (m+6)))) (.iff (.existsE
  (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound (5 : Fin (m+7))) (.bound
  (0 : Fin (m+7))) (.bound (2 : Fin (m+7)))) (Project.Formula.orderedPairMem
  PureKuratowskiProject.convention (.bound (3 : Fin (m+7))) (.bound (0 : Fin (m+7))) (.bound (1 : Fin
  (m+7)))))) (ConstructionMergerRelations.rel n.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ (5 : Fin
  (m+6)) (4 : Fin (m+6)) (3 : Fin (m+6)) (2 : Fin (m+6))))))))))))))))
theorem matches_freeClosed {m : Nat} (n D mul F P : Fin m) : (matchesF n D mul F P).FreeClosed := by
  simp -implicitDefEqProofs [matchesF,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.orderedPairMem_freeClosed,ConstructionMergerRelations.rel_freeClosed]

theorem matches_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul F P : Fin m) :
    Project.Formula.satisfies env (matchesF n D mul F P) ↔
      Matches (env.bound n) (env.bound D) (env.bound mul) (env.bound F) (env.bound P) := by
  simp only [matchesF,Matches,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    ConstructionMergerRelations.rel_semantics hM,Project.Term.eval_bound]
  rfl

def noDiagonal {m : Nat} (P : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.neg (ConstructionMergerRelations.start P.succ.succ.succ 2 2 1 0))))

theorem noDiagonal_freeClosed {m : Nat} (P : Fin m) : (noDiagonal P).FreeClosed := by
  simp -implicitDefEqProofs [noDiagonal,Definitional.Formula.FreeClosed,ConstructionMergerRelations.start_freeClosed]

theorem noDiagonal_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P : Fin m) :
    Project.Formula.satisfies env (noDiagonal P) ↔ NoDiagonal (env.bound P) := by
  simp only [noDiagonal,NoDiagonal,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,
    ConstructionMergerRelations.start_semantics hM]
  rfl

def disjointNone {m : Nat} (D F P : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  F.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge F.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4)))) (.imp (.forallE (.neg
  (.conj (ConstructionPlacementTriple.imageAt (2 : Fin (m+5)) D.succ.succ.succ.succ.succ (0 : Fin (m+5)))
  (ConstructionPlacementTriple.imageAt (1 : Fin (m+5)) D.succ.succ.succ.succ.succ (0 : Fin (m+5))))))
  (.forallE (.forallE (.neg (ConstructionMergerRelations.start P.succ.succ.succ.succ.succ.succ (5 : Fin
  (m+6)) (4 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6)))))))))))))
theorem disjointNone_freeClosed {m : Nat} (D F P : Fin m) : (disjointNone D F P).FreeClosed := by
  simp -implicitDefEqProofs [disjointNone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionPlacementTriple.imageAt_freeClosed,ConstructionMergerRelations.start_freeClosed]

theorem disjointNone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D F P : Fin m) :
    Project.Formula.satisfies env (disjointNone D F P) ↔ DisjointNone (env.bound D) (env.bound F) (env.bound P) := by
  simp only [disjointNone,DisjointNone,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionPlacementTriple.imageAt_semantics hM,ConstructionMergerRelations.start_semantics hM]
  rfl

def result {m : Nat} (n D mul F P : Fin m) : Project.Formula 1 m :=
  .conj (ConstructionRequestCarrier.wellFormed n D P)
    (.conj (ConstructionMergerRelations.prescription n D P)
      (.conj (ConstructionMergerRelations.valid n D mul P)
        (.conj (matchesF n D mul F P) (.conj (noDiagonal P) (disjointNone D F P)))))

theorem result_freeClosed {m : Nat} (n D mul F P : Fin m) : (result n D mul F P).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,
    ConstructionRequestCarrier.wellFormed_freeClosed,ConstructionMergerRelations.prescription_freeClosed,
    ConstructionMergerRelations.valid_freeClosed,matches_freeClosed,noDiagonal_freeClosed,disjointNone_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul F P : Fin m) :
    Project.Formula.satisfies env (result n D mul F P) ↔
      Result (env.bound n) (env.bound D) (env.bound mul) (env.bound F) (env.bound P) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,
    ConstructionRequestCarrier.wellFormed_semantics hM,ConstructionMergerRelations.prescription_semantics hM,
    ConstructionMergerRelations.valid_semantics hM,matches_semantics hM,noDiagonal_semantics hM,disjointNone_semantics hM]

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 5
    (.imp (family 0 1 2 4) (.imp (exactFamily 0 1 2 3 4)
      (.existsE (result (0 : Fin 5).succ (1 : Fin 5).succ (3 : Fin 5).succ (4 : Fin 5).succ 0))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,family_freeClosed,exactFamily_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    family_semantics hM,exactFamily_semantics hM,result_semantics hM]
  exact fun hF hExact => exists_prescription hM hChoice hF hExact

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

/-- Actual consumer of the ALREADY PROVED all-internal finite Merger
property on the SAME final row; returns actual roots and exact realization
inside Complete, with the SAME newly constructed literal prescription. -/
theorem realize_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w history kappa D mul e mark H C incoming base n I F : M.Carrier .set}
    (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa D mul e mark H C incoming base kappa)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hF : Family n D I F) (hExact : ExactFamily n D I mul F) :
    ∃ P, Result n D mul F P ∧ ConstructionSaturationMergers.Complete n P D mul := by
  obtain ⟨P,hResult⟩ := exists_prescription hM hChoice hF hExact
  have hComplete := hMergers D mul e mark H C incoming base n P hRow hn
    hResult.1 hResult.2.1 hResult.2.2.1
  exact ⟨P,hResult,hComplete⟩

def realizationSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 14
    (.imp (ConstructionSaturationMergers.allMergers (0 : Fin 14) 1 2) (.imp (ConstructionTowerHistory.row (1
    : Fin 14) 2 3 4 5 6 7 8 9 10 2) (.imp (.mem (.bound (11 : Fin 14)) (.bound 0)) (.imp (family (11 : Fin
    14) 3 12 13) (.imp (exactFamily (11 : Fin 14) 3 12 4 13) (.existsE (.conj (result (11 : Fin 14).succ (3
    : Fin 14).succ (4 : Fin 14).succ (13 : Fin 14).succ 0) (ConstructionSaturationMergers.complete (11 : Fin
    14).succ 0 (3 : Fin 14).succ (4 : Fin 14).succ))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      family_freeClosed,exactFamily_freeClosed,result_freeClosed,ConstructionSaturationMergers.complete_freeClosed]

theorem realization_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence realizationSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) realizationSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    family_semantics hM,exactFamily_semantics hM,result_semantics hM,
    ConstructionSaturationMergers.complete_semantics hM,Project.Term.eval_bound]
  exact fun hMergers hRow hn hF hExact => realize_family hM hChoice hMergers hRow hn hF hExact

theorem realization_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative realizationSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM realizationSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) realizationSentence).mp (realization_models hL hChoice)

end PPAC.Migration.ConstructionDiagramPrescription
