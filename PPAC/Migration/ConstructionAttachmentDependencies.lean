/- Pinned CellTowers.coefficients/dependencies:299-325 and
CellCuts.selected_dependencies/selected_word:94-123. A single fixed
attachment supplies the same internal support graph for all its words.
Global tower newIndex/stepCell assembly remains a separate consumer. -/
import PPAC.Migration.ConstructionAttachmentCoefficients
import PPAC.Migration.ConstructionRoundSelection
import PPAC.Migration.ConstructionCountableConservativeHull

namespace PPAC.Migration.ConstructionAttachmentDependencies
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCellGeneration
open ConstructionCellCoefficients (Finite Coefficients)
open ConstructionAttachmentCoefficients (ImageResult)
open ConstructionRealCuts (Subset)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn IdentityGraph function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Support (w D I V H e old generators x S : M.Carrier .set) : Prop :=
  Subset S D ∧ Finite w S ∧ ClosureMember I V H e old generators S x

def support {m : Nat} (w D I V H e old generators x S : Fin m) : Project.Formula 1 m :=
  .conj (Project.Formula.subset (.bound S) (.bound D))
    (.conj (ConstructionCellCoefficients.finite w S)
      (closureMember I V H e old generators S x))

theorem support_freeClosed {m : Nat} (w D I V H e old generators x S : Fin m) :
    (support w D I V H e old generators x S).FreeClosed := by
  simp [support,Definitional.Formula.FreeClosed,Project.Formula.subset,
    ConstructionCellCoefficients.finite_freeClosed,closureMember_freeClosed]

theorem support_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D I V H e old generators x S : Fin m) :
    Project.Formula.satisfies env (support w D I V H e old generators x S) ↔
      Support (env.bound w) (env.bound D) (env.bound I) (env.bound V) (env.bound H)
        (env.bound e) (env.bound old) (env.bound generators) (env.bound x) (env.bound S) := by
  simp only [support,Support,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    ConstructionCellCoefficients.finite_semantics hM,closureMember_semantics hM]

/-- A definable representative of the source chosen finite support. -/
def Picked (w D I V H e old generators x S : M.Carrier .set) : Prop :=
  Support w D I V H e old generators x S ∧ ∀ T,
    Support w D I V H e old generators x T →
      ¬ InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M) T S

def picked {m : Nat} (w D I V H e old generators x S : Fin m) : Project.Formula 1 m :=
  .conj (support w D I V H e old generators x S)
    (.forallE (.imp (support w.succ D.succ I.succ V.succ H.succ e.succ old.succ generators.succ x.succ 0)
      (.neg (InnerModel.js_less_m (.bound 0) (.bound S.succ)))))

theorem picked_freeClosed {m : Nat} (w D I V H e old generators x S : Fin m) :
    (picked w D I V H e old generators x S).FreeClosed := by
  simp -implicitDefEqProofs [picked,Definitional.Formula.FreeClosed,support_freeClosed,
    InnerModel.js_less_m_freeClosed]

theorem picked_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D I V H e old generators x S : Fin m) :
    Project.Formula.satisfies env (picked w D I V H e old generators x S) ↔
      Picked (env.bound w) (env.bound D) (env.bound I) (env.bound V) (env.bound H)
        (env.bound e) (env.bound old) (env.bound generators) (env.bound x) (env.bound S) := by
  simp only [picked,Picked,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,support_semantics hM,
    InnerModel.js_less_formula_l (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM))]
  rfl

theorem picked_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w D I V H e old generators x : M.Carrier .set}
    (hx : Coefficients w D I V H e old generators x) :
    ∃ S, Picked w D I V H e old generators x S := by
  let schema : Project.UnarySchema 9 := {
    body := support 1 2 3 4 5 6 7 8 9 0
    freeClosed := support_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases I (Fin.cases V (Fin.cases H
      (Fin.cases e (Fin.cases old (Fin.cases generators (fun _ => x))))))))
    free := fun _ => w }
  have he S : schema.denote env S ↔ Support w D I V H e old generators x S :=
    support_semantics hM (env.push S) 1 2 3 4 5 6 7 8 9 0
  obtain ⟨S,hS,hMin⟩ := ConstructionRoundSelection.least_denote hM hOrder schema env (by
    obtain ⟨S,hS⟩ := hx
    exact ⟨S,(he S).mpr hS⟩)
  exact ⟨S,(he S).mp hS,fun T hT => hMin T ((he T).mpr hT)⟩

theorem picked_unique
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w D I V H e old generators x S T : M.Carrier .set}
    (hS : Picked w D I V H e old generators x S)
    (hT : Picked w D I V H e old generators x T) : S = T := by
  rcases hOrder.2.2.1 S T with he | hST | hTS
  · exact he
  · exact (hT.2 S hS.1 hST).elim
  · exact (hS.2 T hT.1 hTS).elim

def Supports (w D I V H e old generators R C : M.Carrier .set) : Prop :=
  FunctionOn R C ∧ ∀ x S, PureKuratowski.PairMember M x S C ↔
    (Project.FirstOrderSemantics.reduct M).mem x R ∧ Picked w D I V H e old generators x S

theorem exists_supports (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w D I V H e old generators R : M.Carrier .set}
    (hCoeff : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x R →
      Coefficients w D I V H e old generators x) :
    ∃ C, Supports w D I V H e old generators R C := by
  let schema : Project.BinarySchema 8 := {
    body := picked 2 3 4 5 6 7 8 9 1 0
    freeClosed := picked_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases I (Fin.cases V (Fin.cases H
      (Fin.cases e (Fin.cases old (fun _ => generators)))))))
    free := fun _ => w }
  have he x S : schema.denote env x S ↔ Picked w D I V H e old generators x S :=
    picked_semantics hM ((env.push x).push S) 2 3 4 5 6 7 8 9 1 0
  have ht : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x R → ∃ S, schema.denote env x S := by
    intro x hx
    obtain ⟨S,hS⟩ := picked_total hM hOrder (hCoeff x hx)
    exact ⟨S,(he x S).mpr hS⟩
  have hu : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x R → ∀ S T,
      schema.denote env x S → schema.denote env x T → S = T :=
    fun _ _ _ _ hs ht => picked_unique hOrder ((he _ _).mp hs) ((he _ _).mp ht)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env R ht hu
  obtain ⟨C,hC,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF
    (KuratowskiZF.interpretation hM) schema env ht hu
    (fun x S hx hS => (hA S).mpr ⟨x,hx,hS⟩)
  exact ⟨C,((ForcingSupportSize.native_mapsTo hM R A C).mpr hC).1,
    fun x S => (hGraph x S).trans (and_congr_right fun _ => he x S)⟩

/-- Exact active-stage dependency set; old words have the empty row.
The coefficient row is read from the SAME chosen support graph C. -/
def Row (D I generators parameters C x Y : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z Y ↔
    ¬ (Project.FirstOrderSemantics.reduct M).mem x D ∧
      ((Project.FirstOrderSemantics.reduct M).mem z parameters ∨
        (∃ i, (Project.FirstOrderSemantics.reduct M).mem i I ∧ PureKuratowski.PairMember M i z generators) ∨
        ∃ S, PureKuratowski.PairMember M x S C ∧ (Project.FirstOrderSemantics.reduct M).mem z S)

def row {m : Nat} (D I generators parameters C x Y : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound Y.succ))
    (.conj (.neg (.mem (.bound x.succ) (.bound D.succ)))
      (.disj (.mem (.bound 0) (.bound parameters.succ))
        (.disj (.existsE (.conj (.mem (.bound 0) (.bound I.succ.succ))
          (ProjectSyntax.encode id (Source.SetLanguage.edge generators.succ.succ 0 1))))
          (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ x.succ.succ 0))
            (.mem (.bound 1) (.bound 0))))))))

theorem row_freeClosed {m : Nat} (D I generators parameters C x Y : Fin m) :
    (row D I generators parameters C x Y).FreeClosed := by
  simp [row,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem row_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (D I generators parameters C x Y : Fin m) :
    Project.Formula.satisfies env (row D I generators parameters C x Y) ↔
      Row (env.bound D) (env.bound I) (env.bound generators) (env.bound parameters)
        (env.bound C) (env.bound x) (env.bound Y) := by
  simp only [row,Row,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem row_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I V H e old generators R C parameters x : M.Carrier .set}
    (hC : Supports w D I V H e old generators R C) (hx : (Project.FirstOrderSemantics.reduct M).mem x R)
    (hD : Subset D V) (hP : Subset parameters V) (hGen : MapsTo I V generators) :
    ∃ Y, Row D I generators parameters C x Y ∧ Subset Y V := by
  obtain ⟨S,hxS,_⟩ := hC.1.2 x hx
  have hSD := ((hC.2 x S).mp hxS).2.1.1
  obtain ⟨g,hg⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) ((ForcingSupportSize.native_mapsTo hM I V generators).mp hGen).1
      ((ForcingSupportSize.native_mapsTo hM I V generators).mp hGen).2.1
  have hKP := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  classical
  by_cases ho : (Project.FirstOrderSemantics.reduct M).mem x D
  · obtain ⟨Y,hY⟩ := KP.exists_empty hKP
    exact ⟨Y,fun z => iff_of_false (hY z) (fun h => h.1 ho),fun z hz => (hY z hz).elim⟩
  · obtain ⟨B,hB⟩ := KP.exists_unionOfTwo hKP parameters g
    obtain ⟨Y,hY⟩ := KP.exists_unionOfTwo hKP B S
    have hr : Row D I generators parameters C x Y := by
      intro z
      constructor
      · intro hz
        refine ⟨ho,?_⟩
        rcases (hY z).mp hz with hz | hz
        · rcases (hB z).mp hz with hz | hz
          · exact Or.inl hz
          · obtain ⟨i,hiz⟩ := (hg z).mp hz
            exact Or.inr (Or.inl ⟨i,ForcingConditionGraphs.function_input hGen.1 hiz,hiz⟩)
        · exact Or.inr (Or.inr ⟨S,hxS,hz⟩)
      · rintro ⟨_,hz | ⟨i,_,hiz⟩ | ⟨T,hxT,hz⟩⟩
        · exact (hY z).mpr (Or.inl ((hB z).mpr (Or.inl hz)))
        · exact (hY z).mpr (Or.inl ((hB z).mpr (Or.inr ((hg z).mpr ⟨i,hiz⟩))))
        · have he := function_unique hC.1 hxT hxS
          exact (hY z).mpr (Or.inr (he ▸ hz))
    refine ⟨Y,hr,?_⟩
    intro z hz
    rcases ((hr z).mp hz).2 with hz | ⟨i,_,hiz⟩ | ⟨T,hxT,hz⟩
    · exact hP z hz
    · exact hGen.2 i z hiz
    · have he := function_unique hC.1 hxT hxS
      exact hD z (hSD z (he ▸ hz))

def Graph (D I generators parameters R C deps : M.Carrier .set) : Prop :=
  FunctionOn R deps ∧ ∀ x Y, PureKuratowski.PairMember M x Y deps ↔
    (Project.FirstOrderSemantics.reduct M).mem x R ∧ Row D I generators parameters C x Y

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I V H e old generators R C parameters : M.Carrier .set}
    (hC : Supports w D I V H e old generators R C)
    (hD : Subset D V) (hP : Subset parameters V) (hGen : MapsTo I V generators) :
    ∃ deps, Graph D I generators parameters R C deps := by
  let schema : Project.BinarySchema 5 := {
    body := row 2 3 4 5 6 1 0
    freeClosed := row_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases generators (Fin.cases parameters (fun _ => C))))
    free := fun _ => R }
  have he x Y : schema.denote env x Y ↔ Row D I generators parameters C x Y :=
    row_semantics hM ((env.push x).push Y) 2 3 4 5 6 1 0
  have ht : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x R → ∃ Y, schema.denote env x Y := by
    intro x hx
    obtain ⟨Y,hY,_⟩ := row_exists hM hC hx hD hP hGen
    exact ⟨Y,(he x Y).mpr hY⟩
  have hu : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x R → ∀ Y Z,
      schema.denote env x Y → schema.denote env x Z → Y = Z := by
    intro x _ Y Z hY hZ
    exact (ModelTransfer.extensionality hM).eq_of_same_members Y Z
      (fun z => (((he x Y).mp hY) z).trans (((he x Z).mp hZ) z).symm)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env R ht hu
  obtain ⟨deps,hd,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF
    (KuratowskiZF.interpretation hM) schema env ht hu
    (fun x Y hx hY => (hA Y).mpr ⟨x,hx,hY⟩)
  exact ⟨deps,((ForcingSupportSize.native_mapsTo hM R A deps).mpr hd).1,
    fun x Y => (hGraph x Y).trans (and_congr_right fun _ => he x Y)⟩

/-- Dependency closure supplies retention of THIS chosen support and ALL
parameters/generators. No support-retention premise remains. -/
theorem selected_word (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I V H e old generators R C parameters deps retained x : M.Carrier .set}
    (hC : Supports w D I V H e old generators R C)
    (hG : Graph D I generators parameters R C deps) (hId : IdentityGraph D old)
    (hGen : MapsTo I V generators)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (hxR : (Project.FirstOrderSemantics.reduct M).mem x R)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x retained)
    (hNew : ¬ (Project.FirstOrderSemantics.reduct M).mem x D) :
    Subset parameters retained ∧ MapsTo I retained generators ∧
      ∃ cut, (∀ a, (Project.FirstOrderSemantics.reduct M).mem a cut ↔
        (Project.FirstOrderSemantics.reduct M).mem a retained ∧ (Project.FirstOrderSemantics.reduct M).mem a D) ∧
        ClosureMember I V H e old generators cut x := by
  obtain ⟨S,hxS,_⟩ := hC.1.2 x hxR
  obtain ⟨Y,hxY,_⟩ := hG.1.2 x hxR
  have hRow := ((hG.2 x Y).mp hxY).2
  have hRet := hClosed x Y hx hxY
  have hSupport := ((hC.2 x S).mp hxS).2.1
  have hs : Subset S retained := fun z hz => hRet z ((hRow z).mpr ⟨hNew,Or.inr (Or.inr ⟨S,hxS,hz⟩)⟩)
  refine ⟨fun z hz => hRet z ((hRow z).mpr ⟨hNew,Or.inl hz⟩),⟨hGen.1,?_⟩,?_⟩
  · intro i z hiz
    exact hRet z ((hRow z).mpr ⟨hNew,Or.inr (Or.inl ⟨i,ForcingConditionGraphs.function_input hGen.1 hiz,hiz⟩)⟩)
  · apply ConstructionAttachmentCoefficients.exists_retained_cut hM hId hSupport.1 ?_ hSupport.2.2
    intro a z ha haz
    have he := ((hId a z).mp haz).2
    exact he ▸ hs a ha


/-- Consume the SAME actual attachment endpoint and composite generators. -/
theorem exists_for_attachment (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w D I W V H e O P F R old generators parameters : M.Carrier .set}
    (hA : ImageResult w D I W V H e O P F R old generators) (hP : Subset parameters V) :
    ∃ C deps, Supports w D I V H e old generators R C ∧ Graph D I generators parameters R C deps := by
  obtain ⟨_,hRV,hDR,_,_,_,hGen,_,hCoeff⟩ := hA
  obtain ⟨C,hC⟩ := exists_supports hM hOrder hCoeff
  obtain ⟨deps,hd⟩ := exists_graph hM hC (fun a ha => hRV a (hDR a ha)) hP hGen
  exact ⟨C,deps,hC,hd⟩

/-- dependencies_countable: reuse donor ordinal images and finite union bounds. -/
theorem row_small (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I V H e old generators R C parameters x Y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Supports w D I V H e old generators R C)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x R)
    (hGen : MapsTo I V generators)
    (hI : ForcingSupportSize.Small I w) (hP : ForcingSupportSize.Small parameters w)
    (hRow : Row D I generators parameters C x Y) : ForcingSupportSize.Small Y w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨S,hxS,_⟩ := hC.1.2 x hx
  have hFinite := ((hC.2 x S).mp hxS).2.1.2.1
  obtain ⟨n,hn,hSn⟩ := ConstructionCellCoefficients.finite_bound hM hw hFinite
  obtain ⟨sn,hsn⟩ := (ForcingSupportSize.native_small hM S n).mp hSn
  obtain ⟨nw,hnw⟩ := ZF.exists_inclusionInjection hZF pair (fun z hz => hw.transitive hZF n hn z hz)
  have hSw := ZF.exists_compositionInjection hZF pair hsn hnw
  have hNative := (ForcingSupportSize.native_mapsTo hM I V generators).mp hGen
  obtain ⟨g,hg⟩ := ZF.exists_range_of_setFunction hZF pair hNative.1 hNative.2.1
  have hToG : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo pair generators I g :=
    ⟨hNative.1,hNative.2.1,fun i hi => by
      obtain ⟨z,_,hiz⟩ := hNative.2.2 i hi
      exact ⟨z,(hg z).mpr ⟨i,hiz⟩,hiz⟩⟩
  have hGw := ExistingOrdinalImage.ordinal_image_bound_l pair hZF (hw.isOrdinal hZF)
    ((ForcingSupportSize.native_small hM I w).mp hI) hToG (fun z hz => by
      obtain ⟨i,hiz⟩ := (hg z).mp hz
      exact ⟨i,hNative.input_mem_of_pairMember hiz,hiz⟩)
  obtain ⟨idw,hIdw⟩ := ZF.exists_identityBijection hZF pair w
  have hInf : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal pair w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l pair hZF hw,⟨idw,hIdw.1⟩⟩
  obtain ⟨B,hB⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) parameters g
  obtain ⟨U,hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B S
  have hBw := ExistingCardinalBounds.infinite_union_two_l pair hZF hw hInf
    ((ForcingSupportSize.native_small hM parameters w).mp hP) hGw hB
  have hUw := ExistingCardinalBounds.infinite_union_two_l pair hZF hw hInf hBw hSw hU
  apply ForcingSupportSize.small_subset hM (B := U) ?_ ((ForcingSupportSize.native_small hM U w).mpr hUw)
  intro z hz
  rcases ((hRow z).mp hz).2 with hz | ⟨i,_,hiz⟩ | ⟨T,hxT,hz⟩
  · exact (hU z).mpr (Or.inl ((hB z).mpr (Or.inl hz)))
  · exact (hU z).mpr (Or.inl ((hB z).mpr (Or.inr ((hg z).mpr ⟨i,hiz⟩))))
  · have he := function_unique hC.1 hxT hxS
    exact (hU z).mpr (Or.inr (he ▸ hz))

theorem countable_rows (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I V H e old generators R C parameters deps : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Supports w D I V H e old generators R C)
    (hG : Graph D I generators parameters R C deps)
    (hGen : MapsTo I V generators)
    (hI : ForcingSupportSize.Small I w) (hP : ForcingSupportSize.Small parameters w) :
    ∀ x Y, PureKuratowski.PairMember M x Y deps → ForcingSupportSize.Small Y w := by
  intro x Y hxy
  obtain ⟨hx,hRow⟩ := (hG.2 x Y).mp hxy
  exact row_small hM hw hC hx hGen hI hP hRow

def supports {m : Nat} (w D I V H e old generators R C : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn C R))
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ 1 0))
      (.conj (.mem (.bound 1) (.bound R.succ.succ))
        (picked w.succ.succ D.succ.succ I.succ.succ V.succ.succ H.succ.succ e.succ.succ
          old.succ.succ generators.succ.succ 1 0)))))

theorem supports_freeClosed {m : Nat} (w D I V H e old generators R C : Fin m) :
    (supports w D I V H e old generators R C).FreeClosed := by
  simp [supports,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,picked_freeClosed]

theorem supports_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D I V H e old generators R C : Fin m) :
    Project.Formula.satisfies env (supports w D I V H e old generators R C) ↔
      Supports (env.bound w) (env.bound D) (env.bound I) (env.bound V) (env.bound H)
        (env.bound e) (env.bound old) (env.bound generators) (env.bound R) (env.bound C) := by
  simp only [supports,Supports,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.functionOn_semantics (M := M),picked_semantics hM]
  rfl

def graph {m : Nat} (D I generators parameters R C deps : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn deps R))
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge deps.succ.succ 1 0))
      (.conj (.mem (.bound 1) (.bound R.succ.succ))
        (row D.succ.succ I.succ.succ generators.succ.succ parameters.succ.succ C.succ.succ 1 0)))))

theorem graph_freeClosed {m : Nat} (D I generators parameters R C deps : Fin m) :
    (graph D I generators parameters R C deps).FreeClosed := by
  simp [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,row_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (D I generators parameters R C deps : Fin m) :
    Project.Formula.satisfies env (graph D I generators parameters R C deps) ↔
      Graph (env.bound D) (env.bound I) (env.bound generators) (env.bound parameters)
        (env.bound R) (env.bound C) (env.bound deps) := by
  simp only [graph,Graph,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.functionOn_semantics (M := M),row_semantics hM]
  rfl

def constructionSentence {m : Nat} (w D I W V H e O P F R old generators parameters : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionAttachmentCoefficients.imageResult w D I W V H e O P F R old generators)
      (.imp (Project.Formula.subset (.bound parameters) (.bound V))
        (.existsE (.existsE (.conj
          (supports w.succ.succ D.succ.succ I.succ.succ V.succ.succ H.succ.succ e.succ.succ
            old.succ.succ generators.succ.succ R.succ.succ 1)
          (graph D.succ.succ I.succ.succ generators.succ.succ parameters.succ.succ R.succ.succ 1 0))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.subset,
      ConstructionAttachmentCoefficients.imageResult_freeClosed,supports_freeClosed,graph_freeClosed]

theorem construction_models {m : Nat} (w D I W V H e O P F R old generators parameters : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence (constructionSentence w D I W V H e O P F R old generators parameters)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w D I W V H e O P F R old generators parameters)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionAttachmentCoefficients.imageResult_semantics hM,supports_semantics hM,graph_semantics hM]
  exact exists_for_attachment hM hOrder

/-- Discharge the global order through the EXISTING internal L interpretation. -/
theorem construction_kernel_certificate {m : Nat} (w D I W V H e O P F R old generators parameters : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (constructionSentence w D I W V H e O P F R old generators parameters))) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM (constructionSentence w D I W V H e O P F R old generators parameters)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM))
      (constructionSentence w D I W V H e O P F R old generators parameters)).mp
    (construction_models w D I W V H e O P F R old generators parameters
      (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

def selectedSentence {m : Nat} (w D I V H e old generators R C parameters deps retained x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (supports w D I V H e old generators R C)
      (.imp (graph D I generators parameters R C deps)
        (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D old))
          (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo generators I V))
            (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained)
              (.imp (.mem (.bound x) (.bound R)) (.imp (.mem (.bound x) (.bound retained))
                (.imp (.neg (.mem (.bound x) (.bound D)))
                  (.conj (Project.Formula.subset (.bound parameters) (.bound retained))
                    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo generators I retained))
                      (.existsE (.conj (ConstructionAttachmentCoefficients.intersection 0 retained.succ D.succ)
                        (closureMember I.succ V.succ H.succ e.succ old.succ generators.succ 0 x.succ)))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.subset,ProjectSyntax.freeClosed,
      supports_freeClosed,graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,
      ConstructionAttachmentCoefficients.intersection_freeClosed,closureMember_freeClosed]

theorem selected_models {m : Nat} (w D I V H e old generators R C parameters deps retained x : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedSentence w D I V H e old generators R C parameters deps retained x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (selectedSentence w D I V H e old generators R C parameters deps retained x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_subset_iff,supports_semantics hM,graph_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,
    ConstructionAttachmentCoefficients.intersection_semantics (M := M),closureMember_semantics hM]
  exact selected_word hM

theorem selected_kernel_certificate {m : Nat} (w D I V H e old generators R C parameters deps retained x : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (selectedSentence w D I V H e old generators R C parameters deps retained x)) :=
  ModelTransfer.derives (fun _ hM => selected_models w D I V H e old generators R C parameters deps retained x hM)

def countableSentence {m : Nat} (w D I V H e old generators R C parameters deps : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (supports w D I V H e old generators R C)
      (.imp (graph D I generators parameters R C deps)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo generators I V))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small I w))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small parameters w))
      (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge deps.succ.succ 1 0)) (ProjectSyntax.encode id (ForcingSupportSize.small 0 w.succ.succ)))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,
      Project.Formula.isEmpty,Project.Formula.isSuccessor,ProjectSyntax.freeClosed,supports_freeClosed,graph_freeClosed]

theorem countable_models {m : Nat} (w D I V H e old generators R C parameters deps : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (countableSentence w D I V H e old generators R C parameters deps)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (countableSentence w D I V H e old generators R C parameters deps)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_forall_iff,Project.Term.eval_bound,supports_semantics hM,graph_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.small_semantics (M := M)]
  exact countable_rows hM

theorem countable_kernel_certificate {m : Nat} (w D I V H e old generators R C parameters deps : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (countableSentence w D I V H e old generators R C parameters deps)) :=
  ModelTransfer.derives (fun _ hM => countable_models w D I V H e old generators R C parameters deps hM)

end PPAC.Migration.ConstructionAttachmentDependencies
