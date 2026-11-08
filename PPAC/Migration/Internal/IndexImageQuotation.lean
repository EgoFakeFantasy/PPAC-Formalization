import PPAC.Migration.Internal.SchemaIndexQuotation
import PPAC.Migration.Internal.NativeSubstitutionEnvironment
import PPAC.Migration.Internal.NativeTopQuotationIndices

/-! Identify the ACTUAL index-to-variable-image conversion with native term
quotation by existing field readings and full INTERNAL list extensionality.
No replacement conversion, recursion kernel or semantic oracle is introduced. -/
namespace PPAC.Migration.Internal.IndexImageQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open IndexTermImageCodeSyntax (converted converted_rename)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem same_field_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {tb tf : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm tb tf))
    (bound : Bool) (indices : Fin values.length → Nat)
    (shape : ∀ j, PureSyntaxQuotation.termTree (values.get j) = .node (SyntaxVariableSyntax.tag bound) [leaf (indices j)])
    (w I T a c d r L i q : Fin m) (j : Fin values.length) (hw : Derives Γ (omega w))
    (hc : Derives Γ (converted bound w I T a c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a (SyntaxTermSyntax.limit bound c d) I))
    (hL : Derives Γ (TermImageQuotationSyntax.images values w L))
    (hmem : Derives Γ (.mem i a)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i))
    (hp : Derives Γ (SchemaIndexQuotation.value j.val (indices j) r)) :
    Derives Γ ((field w T i q).iff (field w L i q)) := by
  let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral (indices j) (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ (indices j) w hw)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hc1 : Derives Δ (converted bound w.castSucc I.castSucc T.castSucc a.castSucc c.castSucc d.castSucc) :=
    of_eq (converted_rename bound w I T a c d Fin.castSucc) (under hc P)
  have hr1 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc r.castSucc a.castSucc (SyntaxTermSyntax.limit bound c.castSucc d.castSucc) I.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxMapCodeSyntax.encoded_rename,SyntaxTermSyntax.limit_map]) (under hr P)
  have hL1 : Derives Δ (TermImageQuotationSyntax.images values w.castSucc L.castSucc) :=
    of_eq (TermImageQuotationSyntax.images_rename values w L Fin.castSucc) (under hL P)
  have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i.castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ i Fin.castSucc) (under hi P)
  have hp1 : Derives Δ (SchemaIndexQuotation.value j.val (indices j) r.castSucc) :=
    of_eq (SchemaIndexQuotation.value_rename _ _ r Fin.castSucc) (under hp P)
  have he := SchemaIndexQuotation.value_at _ _ _ _ _ hp1 hi1 (.conjR hP)
  have hT := IndexTermImageCodeFields.at_edge hZ1 bound w.castSucc I.castSucc T.castSucc a.castSucc c.castSucc d.castSucc r.castSucc i.castSucc (Fin.last m) q.castSucc hc1 hr1 he
  have hF := TermImageQuotationFields.field_at hZ1 values w.castSucc L.castSucc j i.castSucc q.castSucc hw1 hL1 hi1
  have hTree : Derives Δ ((field w.castSucc L.castSucc i.castSucc q.castSucc).iff
      (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag bound) [leaf (indices j)]) w.castSucc q.castSucc)) :=
    of_eq (by simp only [PureQuotationSyntax.term,shape j]) hF
  have hV := OriginalQuotationVariableFields.variable_iff hZ1 bound (indices j) w.castSucc (Fin.last m) q.castSucc hw1 (.conjR hP)
  have hFCode := SyntaxTypeLocalTransfer.iff_trans hTree hV
  have hm : Derives Δ (.mem i.castSucc a.castSucc) := under hmem P
  have ho : Derives Δ ((field w.castSucc T.castSucc i.castSucc q.castSucc).iff (field w.castSucc L.castSucc i.castSucc q.castSucc)) := by
    apply Derives.conjI
    · apply Derives.impI
      have code := Derives.impE (add (.conjL hT) _) (.conjI (add hm _) (.hyp (Or.inl rfl)))
      exact Derives.impE (add (.conjR hFCode) _) code
    · apply Derives.impI
      have code := Derives.impE (add (.conjL hFCode) _) (.hyp (Or.inl rfl))
      exact .conjR (Derives.impE (add (.conjR hT) _) code)
  exact of_eq (by simp only [Formula.raise,Formula.iff,Formula.rename,field_rename]) ho

/-- Every actual converted list is the exact native image quotation, once the
ACTUAL original index graph has its quoted native values. All fields and
candidate lists are internal, including arbitrary internal decoder witnesses. -/
theorem converted_images {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {tb tf : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm tb tf))
    (bound : Bool) (indices : Fin values.length → Nat)
    (shape : ∀ j, PureSyntaxQuotation.termTree (values.get j) = .node (SyntaxVariableSyntax.tag bound) [leaf (indices j)])
    (w I T a c d r : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral values.length a))
    (hc : Derives Γ (converted bound w I T a c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a (SyntaxTermSyntax.limit bound c d) I))
    (hp : ∀ j, Derives Γ (SchemaIndexQuotation.value j.val (indices j) r)) :
    Derives Γ (TermImageQuotationSyntax.images values w T) := by
  let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj (TermImageQuotationSyntax.images values w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (TermImageQuotationFields.exists_images hZ values w hw)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a.castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ a Fin.castSucc) (under ha P)
  have hc1 : Derives Δ (converted bound w.castSucc I.castSucc T.castSucc a.castSucc c.castSucc d.castSucc) :=
    of_eq (converted_rename bound w I T a c d Fin.castSucc) (under hc P)
  have hr1 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc r.castSucc a.castSucc (SyntaxTermSyntax.limit bound c.castSucc d.castSucc) I.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxMapCodeSyntax.encoded_rename,SyntaxTermSyntax.limit_map]) (under hr P)
  have hp1 (j : Fin values.length) : Derives Δ (SchemaIndexQuotation.value j.val (indices j) r.castSucc) :=
    of_eq (SchemaIndexQuotation.value_rename _ _ r Fin.castSucc) (under (hp j) P)
  have hAgree : Derives Δ (StructuralListCodeSyntax.agree w.castSucc a.castSucc T.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let B := Source.Formula.mem (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc
    let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Δ))
    have hB : Derives Ξ B := .hyp (Or.inl rfl)
    have hZ3 := SyntaxRenameBinders.zf_under_2 hZ1 B
    have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,omega_rename]) (SyntaxRenameBinders.under_2 hw1 B)
    have ha3 : Derives Ξ (SyntaxNumeralSyntax.numeral values.length a.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha1 B)
    have hc3 : Derives Ξ (converted bound w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,converted_rename]) (SyntaxRenameBinders.under_2 hc1 B)
    have hr3 : Derives Ξ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc
        (SyntaxTermSyntax.limit bound c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) I.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SyntaxMapCodeSyntax.encoded_rename,SyntaxTermSyntax.limit_map]) (SyntaxRenameBinders.under_2 hr1 B)
    have hL3 : Derives Ξ (TermImageQuotationSyntax.images values w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,TermImageQuotationSyntax.images_rename]) (SyntaxRenameBinders.under_2 (.conjR hP) B)
    have hp3 (j : Fin values.length) : Derives Ξ (SchemaIndexQuotation.value j.val (indices j) r.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SchemaIndexQuotation.value_rename]) (SyntaxRenameBinders.under_2 (hp1 j) B)
    have hBelow := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ3 values.length a.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc ha3)) hB
    apply Derives.impE (SyntaxPositionSyntax.below_imp values.length (Fin.last (m+1)).castSucc _ ?_) hBelow
    intro j
    apply Derives.impI
    let J := SyntaxNumeralSyntax.numeral j.val (Fin.last (m+1)).castSucc
    have hJ : Derives (Context.add J Ξ) J := .hyp (Or.inl rfl)
    exact same_field_at (ZFContext.add hZ3 J) values bound indices shape _ _ _ _ _ _ _ _ _ _ j
      (add hw3 J) (add hc3 J) (add hr3 J) (add hL3 J) (add hB J) hJ (add (hp3 j) J)
  have ht := IndexTermImageCodeTyping.term_list bound _ _ _ _ _ _ hc1
  have hLengthT : Derives Δ (StructuralListLengthSyntax.hasLength w.castSucc T.castSucc a.castSucc) := .conjR (.conjL (.conjR (.conjR ht)))
  have hLengthL := TermImageQuotationFields.length_at hZ1 values w.castSucc (Fin.last m) a.castSucc hw1 (.conjR hP) ha1
  have hEq := StructuralListCodeInduction.unique hZ1 w.castSucc a.castSucc T.castSucc (Fin.last m) hw1 hLengthT hLengthL hAgree
  let Q := TermImageQuotationSyntax.images values w.castSucc.castSucc (Fin.last (m+1))
  have q0 : Q.instantiate (Fin.last m) = TermImageQuotationSyntax.images values w.castSucc (Fin.last m) := by
    simp only [Q,Formula.instantiate,TermImageQuotationSyntax.images_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have q1 : Q.instantiate T.castSucc = TermImageQuotationSyntax.images values w.castSucc T.castSucc := by
    simp only [Q,Formula.instantiate,TermImageQuotationSyntax.images_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have ho := of_eq q1 (Derives.eqSubst Q (eq_symm hEq) (of_eq q0.symm (.conjR hP)))
  exact of_eq (TermImageQuotationSyntax.images_rename values w T Fin.castSucc).symm ho

/-- Identify both ACTUAL converted lists with the ORIGINAL native variable
substitution environment. The existing conversion environment is consumed;
no quotation environment is assumed as an extra correctness oracle. -/
theorem renaming_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (ρ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sb sort → YesMetaZFC.Logic.FirstOrder.Variable tb sort)
    (τ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sf sort → YesMetaZFC.Logic.FirstOrder.Variable tf sort)
    (w I J R S a b c d r s : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I))
    (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J))
    (hp : ∀ j : Fin sb.length, Derives Γ (SchemaIndexQuotation.value j.val
      (ρ (NativeTopQuotationIndices.entryAt sb j)).index r))
    (hq : ∀ j : Fin sf.length, Derives Γ (SchemaIndexQuotation.value j.val
      (τ (NativeTopQuotationIndices.entryAt sf j)).index s)) :
    Derives Γ (NativeSubstitutionSyntax.environment (fun entry => .bvar (ρ entry)) (fun entry => .fvar (τ entry)) w a b c d R S) := by
  let σ : NativeSubstitutionSyntax.Mapping sb tb tf := fun entry => .bvar (ρ entry)
  let υ : NativeSubstitutionSyntax.Mapping sf tb tf := fun entry => .fvar (τ entry)
  let bs := NativeSubstitutionImages.images sb σ
  let fs := NativeSubstitutionImages.images sf υ
  let bi (j : Fin bs.length) := (ρ (NativeTopQuotationIndices.entryAt sb (NativeTopQuotationIndices.sourceIndex σ j))).index
  let fi (j : Fin fs.length) := (τ (NativeTopQuotationIndices.entryAt sf (NativeTopQuotationIndices.sourceIndex υ j))).index
  have hbs (j : Fin bs.length) : PureSyntaxQuotation.termTree (bs.get j) = .node (SyntaxVariableSyntax.tag true) [leaf (bi j)] := by
    simp only [bs,NativeTopQuotationIndices.get_at,σ,PureSyntaxQuotation.termTree,SyntaxVariableSyntax.tag,bi,↓reduceIte] <;> rfl
  have hfs (j : Fin fs.length) : PureSyntaxQuotation.termTree (fs.get j) = .node (SyntaxVariableSyntax.tag false) [leaf (fi j)] := by
    simp only [fs,NativeTopQuotationIndices.get_at,υ,PureSyntaxQuotation.termTree,SyntaxVariableSyntax.tag,fi] <;> rfl
  have hbp (j : Fin bs.length) : Derives Γ (SchemaIndexQuotation.value j.val (bi j) r) := hp (NativeTopQuotationIndices.sourceIndex σ j)
  have hfp (j : Fin fs.length) : Derives Γ (SchemaIndexQuotation.value j.val (fi j) s) := hq (NativeTopQuotationIndices.sourceIndex υ j)
  have hB := converted_images hZ bs true bi hbs w I R a c d r hw
    (of_eq (by simp only [bs,NativeSubstitutionImages.images_length]) ha) (.conjL he) (of_eq (by rfl) hr) hbp
  have hF := converted_images hZ fs false fi hfs w J S b c d s hw
    (of_eq (by simp only [fs,NativeSubstitutionImages.images_length]) hb) (.conjR he) (of_eq (by rfl) hs) hfp
  exact .conjI (.conjI hB hF) (.conjI (IndexTermImageCodeTyping.term_list true w I R a c d (.conjL he))
    (IndexTermImageCodeTyping.term_list false w J S b c d (.conjR he)))

end PPAC.Migration.Internal.IndexImageQuotation
