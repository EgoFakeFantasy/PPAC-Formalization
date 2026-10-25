/- Pinned ForcingNames.lean:283-348: the union name includes every common
strengthening. Native Cartesian product and Separation give the exact range;
no choice of a strengthening and no new recursion principle is used. -/
import PPAC.Migration.ForcingPairName

namespace PPAC.Migration.ForcingUnionName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def edgeEntry {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P sigma child q : Fin m) : Formula m :=
  .ex (.ex (.ex ((Source.SetLanguage.edge sigma.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      ((Source.SetLanguage.edge (Fin.last m).castSucc.castSucc child.castSucc.castSucc.castSucc
        (Fin.last (m+2))).conj ((Formula.mem q.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc).conj
          ((ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
            q.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).conj
            (ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
              q.castSucc.castSucc.castSucc (Fin.last (m+2)))))))))

def EdgeEntry {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P sigma child q : M.Carrier .set) : Prop :=
  ∃ chi p r, PureKuratowski.PairMember M chi p sigma ∧ PureKuratowski.PairMember M child r chi ∧
    (Definitional.Project.FirstOrderSemantics.reduct M).mem q P ∧
      ForcingMapConditions.MapRel R params q p ∧ ForcingMapConditions.MapRel R params q r

theorem edgeEntry_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P sigma child q : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (edgeEntry R rho P sigma child q) ↔
      EdgeEntry R (fun i => v (rho i)) (v P) (v sigma) (v child) (v q) := by
  simp only [edgeEntry, Formula.Realize, KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc, EdgeEntry]
  rfl

def entry {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P sigma z : Fin m) : Formula m :=
  .ex (.ex ((PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (edgeEntry R (paramsUp (paramsUp rho)) P.castSucc.castSucc sigma.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1)))))

def Entry {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P sigma z : M.Carrier .set) : Prop :=
  ∃ child q, PureKuratowski.Code M z child q ∧ EdgeEntry R params P sigma child q

theorem entry_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P sigma z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entry R rho P sigma z) ↔
      Entry R (fun i => v (rho i)) (v P) (v sigma) (v z) := by
  simp only [entry, Formula.Realize, KuratowskiZF.source_code, edgeEntry_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, Entry]
  rfl

def unionName {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P sigma output : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) output.castSucc).iff
    (entry R (paramsUp rho) P.castSucc sigma.castSucc (Fin.last m)))

def UnionName {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P sigma output : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z output ↔ Entry R params P sigma z

theorem unionName_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P sigma output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (unionName R rho P sigma output) ↔
      UnionName R (fun i => v (rho i)) (v P) (v sigma) (v output) := by
  simp only [unionName, Source.Formula.iff, Formula.Realize, entry_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, UnionName]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)

theorem exists_unionName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P sigma : M.Carrier .set) :
    ∃ output, UnionName R params P sigma output := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨b, hb⟩ := ForcingMapConditions.coordinate_bound hM sigma
  obtain ⟨U, hU⟩ := SetTheory.KP.exists_union (SetTheory.ZF.modelsKP hZF) b
  obtain ⟨c, hc⟩ := ForcingMapConditions.coordinate_bound hM U
  obtain ⟨product, hProduct⟩ := SetTheory.ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) c P
  let inputs : Fin (n+2) → M.Carrier .set := Fin.lastCases sigma (Fin.lastCases P params)
  let query := entry R (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
  have hSep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨output, hOutput⟩ := hSep inputs product
  have hQuery : ∀ z, Formula.Realize E (Fin.lastCases z inputs) query ↔ Entry R params P sigma z := by
    intro z
    simpa only [inputs, query, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (entry_semantics (M := M) (Fin.lastCases z inputs) R (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2)))
  refine ⟨output, fun z => ?_⟩
  constructor
  · intro hz
    exact (hQuery z).mp ((hOutput z).mp hz).2
  · intro hz
    refine (hOutput z).mpr ⟨?_, (hQuery z).mpr hz⟩
    obtain ⟨child, q, hCode, chi, p, r, hp, hr, hq, _, _⟩ := hz
    have he : PureKuratowski.PairMember M child r U := by
      obtain ⟨code, hCode, hMem⟩ := hr
      exact ⟨code, hCode, (hU code).mpr ⟨chi, (hb chi p hp).1, hMem⟩⟩
    exact (hProduct z).mpr ⟨child, (hc child r he).1, q, hq, hCode⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P sigma x y : M.Carrier .set}
    (hx : UnionName R params P sigma x) (hy : UnionName R params P sigma y) : x = y :=
  (ModelTransfer.extensionality hM).eq_of_same_members x y (fun z => (hx z).trans (hy z).symm)

theorem edge_unionName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P sigma output : M.Carrier .set}
    (h : UnionName R params P sigma output) (child q : M.Carrier .set) :
    PureKuratowski.PairMember M child q output ↔ EdgeEntry R params P sigma child q := by
  constructor
  · rintro ⟨z, hCode, hz⟩
    obtain ⟨child', q', hCode', he⟩ := (h z).mp hz
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hCode hCode'
    exact he
  · intro he
    obtain ⟨z, hCode⟩ := KuratowskiZF.exists_code hM child q
    exact ⟨z, hCode, (h z).mpr ⟨child, q, hCode, he⟩⟩

theorem isName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P sigma output : M.Carrier .set}
    (h : UnionName R params P sigma output) (hs : ForcingNames.IsName P sigma) : ForcingNames.IsName P output := by
  apply ForcingNames.intro_name hM P output
  intro z hz
  obtain ⟨child, q, hCode, chi, p, r, hp, hr, hq, _, _⟩ := (h z).mp hz
  exact ⟨child, q, hCode, hq, (ForcingNames.child_condition (ForcingNames.child_condition hs hp).2 hr).2⟩

def existenceSentence {n : Nat} (R : Formula (n+2)) (P sigma : Fin n) : Source.Sentence :=
  (Formula.ex (unionName R Fin.castSucc P.castSucc sigma.castSucc (Fin.last n))).close

def uniquenessSentence {n : Nat} (R : Formula (n+2)) (P sigma x y : Fin n) : Source.Sentence :=
  ((unionName R id P sigma x).imp ((unionName R id P sigma y).imp (.equal x y))).close

def edgeSentence {n : Nat} (R : Formula (n+2)) (P sigma output child q : Fin n) : Source.Sentence :=
  ((unionName R id P sigma output).imp ((Source.SetLanguage.edge output child q).iff
    (edgeEntry R id P sigma child q))).close

def nameSentence {n : Nat} (R : Formula (n+2)) (P sigma output : Fin n) : Source.Sentence :=
  ((unionName R id P sigma output).imp ((ForcingNames.isName P sigma).imp (ForcingNames.isName P output))).close

theorem existence_models {n : Nat} (R : Formula (n+2)) (P sigma : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence R P sigma)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨output, ho⟩ := exists_unionName hM R v (v P) (v sigma)
  refine ⟨output, ?_⟩
  let env : Fin (n+1) → M.Carrier .set := Fin.lastCases output v
  apply (unionName_semantics (M := M) env R Fin.castSucc P.castSucc sigma.castSucc (Fin.last n)).mpr
  simpa only [env, Fin.lastCases_last, Fin.lastCases_castSucc] using ho

theorem uniqueness_models {n : Nat} (R : Formula (n+2)) (P sigma x y : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence R P sigma x y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hx hy
  exact unique hM ((unionName_semantics (M := M) v R id P sigma x).mp hx) ((unionName_semantics (M := M) v R id P sigma y).mp hy)

theorem edge_models {n : Nat} (R : Formula (n+2)) (P sigma output child q : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (edgeSentence R P sigma output child q)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  have he := edge_unionName hM ((unionName_semantics (M := M) v R id P sigma output).mp h) (v child) (v q)
  have hl := KuratowskiZF.source_edge (M := M) v output child q
  have hr := edgeEntry_semantics (M := M) v R id P sigma child q
  exact ⟨fun hz => hr.mpr (he.mp (hl.mp hz)), fun hz => hl.mpr (he.mpr (hr.mp hz))⟩

theorem name_models {n : Nat} (R : Formula (n+2)) (P sigma output : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (nameSentence R P sigma output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h hs
  exact (ForcingNames.isName_semantics (M := M) v P output).mpr
    (isName hM ((unionName_semantics (M := M) v R id P sigma output).mp h) ((ForcingNames.isName_semantics (M := M) v P sigma).mp hs))

theorem existence_kernel_certificate {n : Nat} (R : Formula (n+2)) (P sigma : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence R P sigma)) :=
  ModelTransfer.derives (fun _ hM => existence_models R P sigma hM)
theorem uniqueness_kernel_certificate {n : Nat} (R : Formula (n+2)) (P sigma x y : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence R P sigma x y)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models R P sigma x y hM)
theorem edge_kernel_certificate {n : Nat} (R : Formula (n+2)) (P sigma output child q : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (edgeSentence R P sigma output child q)) :=
  ModelTransfer.derives (fun _ hM => edge_models R P sigma output child q hM)
theorem name_kernel_certificate {n : Nat} (R : Formula (n+2)) (P sigma output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (nameSentence R P sigma output)) :=
  ModelTransfer.derives (fun _ hM => name_models R P sigma output hM)

/-- Exactly the source filter hypotheses: subset, upward closure, directedness. -/
def filter {n : Nat} (R : Formula (n+2)) (p : Formula (n+1)) (P : Fin n) : Formula n :=
  (Formula.all ((MinimalPredicates.pred p Fin.castSucc (Fin.last n)).imp
    (.mem (Fin.last n) P.castSucc))).conj
  ((Formula.all (Formula.all ((Formula.mem (Fin.last n).castSucc P.castSucc.castSucc).imp
    ((MinimalPredicates.pred p (fun i => i.castSucc.castSucc) (Fin.last (n+1))).imp
      ((ReplacementPredicates.rel R (fun i => i.castSucc.castSucc) (Fin.last (n+1)) (Fin.last n).castSucc).imp
        (MinimalPredicates.pred p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc)))))).conj
  (Formula.all (Formula.all ((MinimalPredicates.pred p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc).imp
    ((MinimalPredicates.pred p (fun i => i.castSucc.castSucc) (Fin.last (n+1))).imp
      (.ex ((MinimalPredicates.pred p (fun i => i.castSucc.castSucc.castSucc) (Fin.last (n+2))).conj
        ((ReplacementPredicates.rel R (fun i => i.castSucc.castSucc.castSucc)
          (Fin.last (n+2)) (Fin.last n).castSucc.castSucc).conj
          (ReplacementPredicates.rel R (fun i => i.castSucc.castSucc.castSucc)
            (Fin.last (n+2)) (Fin.last (n+1)).castSucc)))))))))

def Filter {n : Nat} (R : Formula (n+2)) (p : Formula (n+1))
    (params : Fin n → M.Carrier .set) (P : M.Carrier .set) : Prop :=
  (∀ x, ForcingClassEvaluation.Predicate p params x → (Definitional.Project.FirstOrderSemantics.reduct M).mem x P) ∧
  (∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P →
    ∀ q, ForcingClassEvaluation.Predicate p params q → ForcingMapConditions.MapRel R params q x →
      ForcingClassEvaluation.Predicate p params x) ∧
  (∀ x, ForcingClassEvaluation.Predicate p params x → ∀ y, ForcingClassEvaluation.Predicate p params y →
    ∃ q, ForcingClassEvaluation.Predicate p params q ∧ ForcingMapConditions.MapRel R params q x ∧
      ForcingMapConditions.MapRel R params q y)

theorem filter_semantics {n : Nat} (v : Fin n → M.Carrier .set) (R : Formula (n+2))
    (p : Formula (n+1)) (P : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (filter R p P) ↔ Filter R p v (v P) := by
  simp only [filter, Formula.Realize, ForcingClassEvaluation.predicate_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc, Filter]
  constructor
  · rintro ⟨hsub, hup, hdir⟩
    exact ⟨hsub, fun x hx q hq hr => hup x q hx hq hr, fun x hx y hy => hdir x y hx hy⟩
  · rintro ⟨hsub, hup, hdir⟩
    exact ⟨hsub, fun x q hx hq hr => hup x hx q hq hr, fun x y hx hy => hdir x hx y hy⟩

theorem evaluate_unionName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {p : Formula (n+1)} {params : Fin n → M.Carrier .set}
    {P sigma name value output : M.Carrier .set}
    (h : UnionName R params P sigma name) (hf : Filter R p params P) (hs : ForcingNames.IsName P sigma)
    (hv : ForcingClassEvaluation.Evaluated p params sigma value)
    (ho : ForcingClassEvaluation.Evaluated p params name output) :
    ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z output ↔
      ∃ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x value ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem z x := by
  intro z
  constructor
  · intro hz
    obtain ⟨child, q, he, hq, hzEval⟩ := (ForcingClassEvaluation.mem_evaluation hM ho z).mp hz
    obtain ⟨chi, a, b, ha, hb, _, hqa, hqb⟩ := (edge_unionName hM h child q).mp he
    have hChi := (ForcingNames.child_condition hs ha).2
    have haG := hf.2.1 a (ForcingNames.child_condition hs ha).1 q hq hqa
    have hbG := hf.2.1 b (ForcingNames.child_condition hChi hb).1 q hq hqb
    obtain ⟨x, hxEval⟩ := ForcingClassEvaluation.exists_evaluation hM p params chi
    exact ⟨x, (ForcingClassEvaluation.mem_evaluation hM hv x).mpr ⟨chi, a, ha, haG, hxEval⟩,
      (ForcingClassEvaluation.mem_evaluation hM hxEval z).mpr ⟨child, b, hb, hbG, hzEval⟩⟩
  · rintro ⟨x, hx, hz⟩
    obtain ⟨chi, a, ha, haG, hxEval⟩ := (ForcingClassEvaluation.mem_evaluation hM hv x).mp hx
    obtain ⟨child, b, hb, hbG, hzEval⟩ := (ForcingClassEvaluation.mem_evaluation hM hxEval z).mp hz
    obtain ⟨q, hq, hqa, hqb⟩ := hf.2.2 a haG b hbG
    exact (ForcingClassEvaluation.mem_evaluation hM ho z).mpr
      ⟨child, q, (edge_unionName hM h child q).mpr ⟨chi, a, b, ha, hb, hf.1 q hq, hqa, hqb⟩, hq, hzEval⟩

def evaluationSentence {n : Nat} (R : Formula (n+2)) (p : Formula (n+1))
    (P sigma name value output : Fin n) : Source.Sentence :=
  ((unionName R id P sigma name).imp ((filter R p P).imp ((ForcingNames.isName P sigma).imp
    ((ForcingClassEvaluation.evaluation p id sigma value).imp
      ((ForcingClassEvaluation.evaluation p id name output).imp (InsertSyntax.unionOf output value)))))).close

theorem evaluation_models {n : Nat} (R : Formula (n+2)) (p : Formula (n+1))
    (P sigma name value output : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (evaluationSentence R p P sigma name value output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h hf hs hv ho
  have he := evaluate_unionName hM ((unionName_semantics (M := M) v R id P sigma name).mp h)
    ((filter_semantics (M := M) v R p P).mp hf) ((ForcingNames.isName_semantics (M := M) v P sigma).mp hs)
    ((ForcingClassEvaluation.evaluation_semantics (M := M) v p id sigma value).mp hv)
    ((ForcingClassEvaluation.evaluation_semantics (M := M) v p id name output).mp ho)
  simp only [InsertSyntax.unionOf, InsertSyntax.unionFiber, Source.Formula.iff, Formula.Realize,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact fun z => ⟨(he z).mp, (he z).mpr⟩

theorem evaluation_kernel_certificate {n : Nat} (R : Formula (n+2)) (p : Formula (n+1))
    (P sigma name value output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (evaluationSentence R p P sigma name value output)) :=
  ModelTransfer.derives (fun _ hM => evaluation_models R p P sigma name value output hM)

end PPAC.Migration.ForcingUnionName
