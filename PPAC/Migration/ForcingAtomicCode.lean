import PPAC.Migration.ForcingAtomicRelations
import PPAC.Migration.Internal.PureQuotationTypedFormulas
import PPAC.Migration.Internal.TypedArgumentListConstruction
import PPAC.Migration.Internal.FreeSubstImageCode
import PPAC.Migration.Internal.ProofTreeEntryFacts
import PPAC.Migration.Internal.SyntaxIdentityUnique
import PPAC.Migration.Internal.IndexTermImageCodeUnique

/-! Literal migrated atomic-forcing code: internal construction, not a Con proof.
The input atom terms are arbitrary internal codes in a closed source context.
Target bound scope is internal; only the fixed ground-language template is a
host AST. All actual image lists are constructed by the existing internal syntax interfaces. -/
namespace PPAC.Migration.ForcingAtomicCode
section Templates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature

private def roles : (n : Nat) → VariableSubstitution ℒ
    (fo_bound_context (n+4)) (fo_bound_context 2) (fo_bound_context (n+2))
  | 0 => fun v => match v with
    | .here => .fvar .here
    | .there .here => .fvar (.there .here)
    | .there (.there .here) => .bvar (.there .here)
    | .there (.there (.there .here)) => .bvar .here
    | .there (.there (.there (.there v))) => nomatch v
  | n+1 => fun v => match v with
    | .here => .fvar .here
    | .there v => by
      simpa only [fo_bound_context, List.replicate_succ] using (roles n v).weakenFree SetSort.set

def sourceTemplate {n} (equality : Bool) (R : Source.Formula (n+2)) : Source.Formula (n+4) :=
  ForcingAtomicRelations.forces equality R
    (fun i => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc
    (Fin.last (n+2)).castSucc (Fin.last (n+3))
    (Fin.last (n+1)).castSucc.castSucc

/-- Bounds 0/1 are y/x; free variables are the original R parameters, P, p.
This is a typed substitution in the LITERAL existing forcing formula. -/
def template {n} (equality : Bool) (R : Source.Formula (n+2)) :
    PureSyntaxQuotation.Fm (fo_bound_context 2) (fo_bound_context (n+2)) :=
  (Translation.formula fo_bound_variable (sourceTemplate equality R)).substituteMapped
    (roles n) (fun {sort} (v : FirstOrder.Variable ([] : FirstOrder.SortContext ℒ) sort) => nomatch v)

end Templates

open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

private theorem closed_term_target {m} {Γ : Context m} (w a z b x : Fin m)
    (hz : Derives Γ (empty z)) (hc : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x)) :
    Derives Γ (SyntaxTermSyntax.term w a b x) := by
  apply Derives.conjI hc
  apply Derives.disjE (.conjR hx)
  · exact .disjL (.hyp (Or.inl rfl))
  · let P := SyntaxTermSyntax.branch false w z x
    let B := SyntaxTermSyntax.branchWitness false w z x
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hz1 := of_eq (empty_rename z Fin.castSucc) (under (add hz P) B)
    exact .botE (.impE (empty_at z.castSucc (Fin.last m) hz1) (.conjL (.hyp (Or.inl rfl))))

private theorem forest_typed {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w size a b L : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral k size))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (ht : ∀ i, Derives Γ (SyntaxTermSyntax.term w a b (xs i)))
    (hf : Derives Γ (SyntaxForestSyntax.forest k w xs L)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w size a b L) := by
  induction k generalizing m with
  | zero => exact TypedArgumentListConstruction.nil_list hZ w size a b L hw hn hc hf
  | succ k ih =>
    let P := (SyntaxNumeralSyntax.numeral k (Fin.last m)).conj (successor size.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Γ)
    apply SyntaxNumeralSyntax.eliminate_succ k size _ hn
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hf1 := of_eq (SyntaxForestSyntax.forest_rename (k+1) w xs L Fin.castSucc) (under hf P)
    let B := (Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
      ((SyntaxForestSyntax.forest k w.castSucc.castSucc
        (fun i => (xs i.succ).castSucc.castSucc) (Fin.last (m+1))).conj
        (StructuralListSyntax.consCode w.castSucc.castSucc (xs 0).castSucc.castSucc
          (Fin.last (m+1)) L.castSucc.castSucc))
    let Ξ := Context.add B (Context.image Formula.raise Δ)
    apply SyntaxForestSyntax.eliminate_cons k w.castSucc (fun i => (xs i).castSucc) L.castSucc _ hf1
    have hB : Derives Ξ B := .hyp (Or.inl rfl)
    have lift2 {Q : Formula m} (h : Derives Γ Q) : Derives Ξ Q.raise.raise := under (under h P) B
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (lift2 hw)
    have hc2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc
        a.castSucc.castSucc b.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (lift2 hc)
    have ht2 (i : Fin (k+1)) : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc
        a.castSucc.castSucc b.castSucc.castSucc (xs i).castSucc.castSucc) := of_eq
      (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (lift2 (ht i))
    have hn2 := of_eq (SyntaxNumeralSyntax.numeral_rename k (Fin.last m) Fin.castSucc) (under (.conjL hP) B)
    have hs2 := of_eq (successor_rename size.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hP) B)
    have htail := ih (ZFContext.under (ZFContext.under hZ P) B) w.castSucc.castSucc
      (Fin.last m).castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
      (fun i => (xs i.succ).castSucc.castSucc) hw2 hn2 hc2 (fun i => ht2 i.succ) (.conjL (.conjR hB))
    have hout := TypedArgumentListConstruction.cons_list (ZFContext.under (ZFContext.under hZ P) B)
      w.castSucc.castSucc (Fin.last m).castSucc size.castSucc.castSucc
      a.castSucc.castSucc b.castSucc.castSucc (xs 0).castSucc.castSucc
      (Fin.last (m+1)) L.castSucc.castSucc hw2 (ht2 0) htail (.conjR (.conjR hB)) hs2
    exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) hout

private def freeImages {m} (w a f S : Fin m) : Formula m := .ex
  ((SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)).conj
    (IndexTermImageCodeSyntax.converted false w.castSucc (Fin.last m) S.castSucc
      f.castSucc a.castSucc f.castSucc))

private theorem freeImages_rename {m l} (w a f S : Fin m) (r : Fin m → Fin l) :
    (freeImages w a f S).rename r = freeImages (r w) (r a) (r f) (r S) := by
  simp only [freeImages, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename,
    IndexTermImageCodeSyntax.converted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private def existsFreeImages {m} (w a f : Fin m) : Formula m := .ex
  (freeImages w.castSucc a.castSucc f.castSucc (Fin.last m))

private theorem existsFreeImages_rename {m l} (w a f : Fin m) (r : Fin m → Fin l) :
    (existsFreeImages w a f).rename r = existsFreeImages (r w) (r a) (r f) := by
  simp only [existsFreeImages, Formula.rename, freeImages_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem freeImages_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (.mem a w)) (hf : Derives Γ (.mem f w)) :
    Derives Γ (existsFreeImages w a f) := by
  let B := SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxIdentityCode.exists_code hZ w f hw hf)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hctx : Derives Δ (SyntaxTermSyntax.contexts w.castSucc a.castSucc f.castSucc) :=
    .conjI (under ha B) (under hf B)
  have hm := SyntaxIdentityCode.map_code w.castSucc f.castSucc (Fin.last m) hB
  have he := IndexTermImageCodeExistence.exists_code (ZFContext.under hZ B) false
    w.castSucc (Fin.last m) f.castSucc a.castSucc f.castSucc hw1 (.conjI hctx hm)
  let C := IndexTermImageCodeSyntax.converted false w.castSucc.castSucc (Fin.last m).castSucc
    (Fin.last (m+1)) f.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) he
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hi2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc f.castSucc
    (Fin.last m) Fin.castSucc) (under hB C)
  have hfree : Derives Ξ (freeImages w.castSucc.castSucc a.castSucc.castSucc
      f.castSucc.castSucc (Fin.last (m+1))) := by
    apply Derives.exI (Fin.last m).castSucc
    exact of_eq (by simp only [C, Formula.instantiate, Formula.rename,
      SyntaxIdentityMapSyntax.identityCode_rename, IndexTermImageCodeSyntax.converted_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hi2 hC)
  have hout : Derives Ξ (existsFreeImages w.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, freeImages_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hfree
  exact of_eq (by simp only [Formula.raise, existsFreeImages_rename]) hout

private theorem freeImages_typed {m} {Γ : Context m} (w a f S : Fin m)
    (h : Derives Γ (freeImages w a f S)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w f a f S) := by
  let B := (SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)).conj
    (IndexTermImageCodeSyntax.converted false w.castSucc (Fin.last m) S.castSucc
      f.castSucc a.castSucc f.castSucc)
  apply Derives.exE (p := B) h
  have hB : Derives (Context.add B (Context.image Formula.raise Γ)) B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f a f S Fin.castSucc).symm
    (IndexTermImageCodeTyping.term_list false w.castSucc (Fin.last m) S.castSucc
      f.castSucc a.castSucc f.castSucc (.conjR hB))

private def matrix {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 2 (v 0)).conj
    ((SyntaxNumeralSyntax.numeral (n+2) (v 1)).conj
      ((PureQuotationTypedSyntax.formulaValue (template equality R) w (v 0) (v 1) (v 2)).conj
        ((SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) (v 3)).conj
          ((SyntaxMixedImageCodeSyntax.termList w (v 0) a (v 1) (v 3)).conj
            ((freeImages w a (v 1) (v 4)).conj
              (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 3) (v 4) (v 0) (v 1) a (v 1) (v 2) q))))))

private theorem matrix_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (v : Fin 5 → Fin m) (r : Fin m → Fin l) :
    (matrix equality R w a x y q v).rename r =
      matrix equality R (r w) (r a) (r x) (r y) (r q) (fun i => r (v i)) := by
  simp only [matrix, Formula.rename, SyntaxNumeralSyntax.numeral_rename,
    PureQuotationTypedSyntax.formulaValue, PureQuotationSyntax.formula_rename,
    FormulaCodeSyntax.formulaCode_rename, SyntaxForestSyntax.forest_rename,
    ProofTreeEntryFacts.args2_map, SyntaxMixedImageCodeSyntax.termList_rename,
    freeImages_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private def body {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) : Formula (m+5) :=
  matrix equality R (old 5 w) (old 5 a) (old 5 x) (old 5 y) (old 5 q) (slot 5)

def compiled {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) : Formula m := existsMany 5 (body equality R w a x y q)

theorem compiled_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (r : Fin m → Fin l) :
    (compiled equality R w a x y q).rename r = compiled equality R (r w) (r a) (r x) (r y) (r q) := by
  simp only [compiled, existsMany_rename, body, matrix_rename, lift_old, lift_slot]

def existsCompiled {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y : Fin m) : Formula m := .ex
  (compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m))

private theorem existsCompiled_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y : Fin m) (r : Fin m → Fin l) :
    (existsCompiled equality R w a x y).rename r = existsCompiled equality R (r w) (r a) (r x) (r y) := by
  simp only [existsCompiled, Formula.rename, compiled_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure Inputs (n m : Nat) (Γ : Context m) (w t f a x y : Fin m) : Prop where
  hw : Derives Γ (omega w)
  ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 t)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hx : Derives Γ (SyntaxTermSyntax.term w a f x)
  hy : Derives Γ (SyntaxTermSyntax.term w a f y)

private theorem underInputs {n m} {Γ : Context m} {w t f a x y : Fin m}
    (h : Inputs n m Γ w t f a x y) (B : Formula (m+1)) :
    Inputs n (m+1) (Context.add B (Context.image Formula.raise Γ))
      w.castSucc t.castSucc f.castSucc a.castSucc x.castSucc y.castSucc := by
  exact {
  hw := of_eq (omega_rename w Fin.castSucc) (under h.hw B)
  ht := of_eq (SyntaxNumeralSyntax.numeral_rename 2 t Fin.castSucc) (under h.ht B)
  hf := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf B)
  hx := of_eq (SyntaxTermSyntax.term_rename w a f x Fin.castSucc) (under h.hx B)
  hy := of_eq (SyntaxTermSyntax.term_rename w a f y Fin.castSucc) (under h.hy B) }

private theorem quotation_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w t f N : Fin m) (r : Fin m → Fin l) :
    (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N).rename r =
      PureQuotationTypedSyntax.formulaValue (template equality R) (r w) (r t) (r f) (r N) := by
  simp only [PureQuotationTypedSyntax.formulaValue, Formula.rename,
    PureQuotationSyntax.formula_rename, FormulaCodeSyntax.formulaCode_rename]

private theorem assemble {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y N U V : Fin m)
    (h : Inputs n m Γ w t f a x y)
    (hN : Derives Γ (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N))
    (hU : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) U))
    (htU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w t a f U))
    (hV : Derives Γ (freeImages w a f V)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  have hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w U V t f a f N) :=
    .conjI (.conjR hN) (.conjI htU (freeImages_typed w a f V hV))
  let B := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc U.castSucc V.castSucc
    t.castSucc f.castSucc a.castSucc f.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B)
    (SyntaxMixedFormulaOutputInduction.actual_exists hZ w U V t f a f N h.hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h1 := underInputs h B
  have hN1 := of_eq (quotation_rename equality R w t f N Fin.castSucc) (under hN B)
  have hU1 := of_eq (by simpa only [ProofTreeEntryFacts.args2_map] using
    SyntaxForestSyntax.forest_rename 2 w (SetLanguage.args2 y x) U Fin.castSucc) (under hU B)
  have htU1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w t a f U Fin.castSucc) (under htU B)
  have hV1 := of_eq (freeImages_rename w a f V Fin.castSucc) (under hV B)
  let v : Fin 5 → Fin (m+1) := Fin.cases t.castSucc (Fin.cases f.castSucc
    (Fin.cases N.castSucc (SetLanguage.args2 U.castSucc V.castSucc)))
  have hm : Derives Δ (matrix equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m) v) :=
    .conjI h1.ht (.conjI h1.hf (.conjI hN1 (.conjI hU1 (.conjI htU1 (.conjI hV1 hB)))))
  have hc : Derives Δ (compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 5 _ v
    exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm
  have ho : Derives Δ (existsCompiled equality R w.castSucc a.castSucc x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

private theorem with_free_images {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y N U : Fin m)
    (h : Inputs n m Γ w t f a x y)
    (hN : Derives Γ (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N))
    (hU : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) U))
    (htU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w t a f U)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  let B := freeImages w.castSucc a.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B)
    (freeImages_exists hZ w a f h.hw (.conjL (.conjL h.hx)) (.conjR (.conjL h.hx)))
  have h1 := underInputs h B
  have hN1 := of_eq (quotation_rename equality R w t f N Fin.castSucc) (under hN B)
  have hU1 := of_eq (by simpa only [ProofTreeEntryFacts.args2_map] using
    SyntaxForestSyntax.forest_rename 2 w (SetLanguage.args2 y x) U Fin.castSucc) (under hU B)
  have htU1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w t a f U Fin.castSucc) (under htU B)
  have ho := assemble (ZFContext.under hZ B) equality R w.castSucc t.castSucc f.castSucc
    a.castSucc x.castSucc y.castSucc N.castSucc U.castSucc (Fin.last m)
    h1 hN1 hU1 htU1 (.hyp (Or.inl rfl))
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

private theorem with_bound_images {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y N : Fin m)
    (h : Inputs n m Γ w t f a x y)
    (hN : Derives Γ (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  have hn : ∀ i, Derives Γ (.mem (SetLanguage.args2 y x i) w) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact SyntaxTerms.range hZ w a f y h.hw h.hy
    · refine Fin.cases ?_ (fun v => Fin.elim0 v) j
      exact SyntaxTerms.range hZ w a f x h.hw h.hx
  have he := SyntaxForests.exists_forest hZ 2 w (SetLanguage.args2 y x) h.hw
    (SyntaxForestSyntax.intro_inputs 2 w (SetLanguage.args2 y x) hn)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxForestSyntax.forest 2 w.castSucc (SetLanguage.args2 y.castSucc x.castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (of_eq (by
    simp only [B, SyntaxForestSyntax.existsForest, ProofTreeEntryFacts.args2_map]) he)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h1 := underInputs h B
  have hN1 := of_eq (quotation_rename equality R w t f N Fin.castSucc) (under hN B)
  have hterms : ∀ i, Derives Δ (SyntaxTermSyntax.term w.castSucc a.castSucc f.castSucc
      (SetLanguage.args2 y.castSucc x.castSucc i)) := by
    intro i
    refine Fin.cases h1.hy (fun j => ?_) i
    exact Fin.cases h1.hx (fun v => Fin.elim0 v) j
  have htU := forest_typed (ZFContext.under hZ B) w.castSucc t.castSucc a.castSucc f.castSucc
    (Fin.last m) (SetLanguage.args2 y.castSucc x.castSucc)
    h1.hw h1.ht (.conjL h1.hx) hterms (.conjR hB)
  have ho := with_free_images (ZFContext.under hZ B) equality R w.castSucc t.castSucc f.castSucc
    a.castSucc x.castSucc y.castSucc N.castSucc (Fin.last m) h1 hN1 (.conjR hB) htU
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

private theorem with_template {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y : Fin m)
    (h : Inputs n m Γ w t f a x y) :
    Derives Γ (existsCompiled equality R w a x y) := by
  have ht : Derives Γ (SyntaxNumeralSyntax.numeral
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 2).length t) := by
    have he : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 2).length = 2 := by
      exact List.length_replicate ..
    exact Eq.mpr (congrArg (fun k => Derives Γ (SyntaxNumeralSyntax.numeral k t)) he) h.ht
  have hf : Derives Γ (SyntaxNumeralSyntax.numeral
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) := by
    have he : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 := by
      exact List.length_replicate ..
    exact Eq.mpr (congrArg (fun k => Derives Γ (SyntaxNumeralSyntax.numeral k f)) he) h.hf
  have he := PureQuotationTypedFormulas.exists_typed hZ (template equality R) w t f h.hw ht hf
  let B := PureQuotationTypedSyntax.formulaValue (template equality R)
    w.castSucc t.castSucc f.castSucc (Fin.last m)
  apply Derives.exE (p := B) he
  have ho := with_bound_images (ZFContext.under hZ B) equality R w.castSucc t.castSucc f.castSucc
    a.castSucc x.castSucc y.castSucc (Fin.last m) (underInputs h B) (.hyp (Or.inl rfl))
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

/-- Construct every quotation, scope numeral, and substitution image internally.
The input terms have zero free variables; their bound scope may be nonstandard. -/
theorem total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x))
    (hy : Derives Γ (SyntaxTermSyntax.term w a z y)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ 2 w hw)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  let C := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxNumeralSyntax.numeral (n+2) (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) (SyntaxNumerals.exists_numeral (ZFContext.under hZ B) (n+2) w.castSucc hw1)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have lift2 {Q : Formula m} (h : Derives Γ Q) : Derives Ξ Q.raise.raise := under (under h B) C
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (lift2 hw)
  have hz2 : Derives Ξ (empty z.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, empty_rename]) (lift2 hz)
  have hx2 : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (lift2 hx)
  have hy2 : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc y.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (lift2 hy)
  have hc : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))) :=
    .conjI (.conjL (.conjL hx2)) (.conjL hC)
  have ht2 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 (Fin.last m) Fin.castSucc) (under (.conjR hB) C)
  have h : Inputs n (m+2) Ξ w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      a.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc :=
    ⟨hw2, ht2, .conjR hC, closed_term_target _ _ _ _ _ hz2 hc hx2, closed_term_target _ _ _ _ _ hz2 hc hy2⟩
  have ho := with_template (ZFContext.under (ZFContext.under hZ B) C) equality R
    w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc
    x.castSucc.castSucc y.castSucc.castSucc h
  exact of_eq (by simp only [Formula.raise, existsCompiled_rename]) ho

def typed {m} (n : Nat) (w a q : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral (n+2) (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc q.castSucc a.castSucc (Fin.last m)))

private theorem typed_rename {m l} (n : Nat) (w a q : Fin m) (r : Fin m → Fin l) :
    (typed n w a q).rename r = typed n (r w) (r a) (r q) := by
  simp only [typed, Formula.rename, SyntaxNumeralSyntax.numeral_rename,
    FormulaCodeSyntax.formulaCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Every actual compiler output has the exact target bound/free scope. -/
theorem compiled_type {n m} {Γ : Context m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (h : Derives Γ (compiled equality R w a x y q)) :
    Derives Γ (typed n w a q) := by
  let B := body equality R w a x y q
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B (typed n w a q) h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf := Derives.conjL (.conjR hB)
  have hQ := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
  have ht := SyntaxMixedFormulaJudgment.target_type (old 5 w) (slot 5 3) (slot 5 4)
    (slot 5 0) (slot 5 1) (old 5 a) (slot 5 1) (slot 5 2) (old 5 q) hQ
  have ho : Derives Δ (typed n (old 5 w) (old 5 a) (old 5 q)) := by
    apply Derives.exI (slot 5 1)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename,
      SyntaxNumeralSyntax.numeral_rename, FormulaCodeSyntax.formulaCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hf ht)
  exact of_eq (typed_rename n w a q (old 5)).symm ho

def sentence {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxTermSyntax.term w a z x).imp
    ((SyntaxTermSyntax.term w a z y).imp (existsCompiled equality R w a x y))))).close

def typeSentence {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y q : Fin m) : Source.Sentence :=
  ((compiled equality R w a x y q).imp (typed n w a q)).close

theorem kernel_certificate {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence equality R w a z x y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _)
    equality R w a z x y (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem type_kernel_certificate {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (typeSentence equality R w a x y q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact compiled_type equality R w a x y q (.hyp (Or.inl rfl))


private theorem freeImages_scope_subst {m} {Γ : Context m} (w a f g S : Fin m)
    (he : Derives Γ (.equal f g)) (h : Derives Γ (freeImages w a f S)) :
    Derives Γ (freeImages w a g S) := by
  let F := freeImages w.castSucc a.castSucc (Fin.last m) S.castSucc
  exact of_eq (by simp only [F, Formula.instantiate, freeImages_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst F he (of_eq (by simp only [F, Formula.instantiate, freeImages_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem converted_index_subst {m} {Γ : Context m} (w I J T f a : Fin m)
    (he : Derives Γ (.equal I J))
    (h : Derives Γ (IndexTermImageCodeSyntax.converted false w I T f a f)) :
    Derives Γ (IndexTermImageCodeSyntax.converted false w J T f a f) := by
  let F := IndexTermImageCodeSyntax.converted false w.castSucc (Fin.last m) T.castSucc f.castSucc a.castSucc f.castSucc
  exact of_eq (by simp only [F, Formula.instantiate, IndexTermImageCodeSyntax.converted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst F he (of_eq (by simp only [F, Formula.instantiate, IndexTermImageCodeSyntax.converted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem freeImages_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f S T : Fin m) (hw : Derives Γ (omega w))
    (hS : Derives Γ (freeImages w a f S)) (hT : Derives Γ (freeImages w a f T)) :
    Derives Γ (.equal S T) := by
  let B := (SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)).conj
    (IndexTermImageCodeSyntax.converted false w.castSucc (Fin.last m) S.castSucc f.castSucc a.castSucc f.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hS
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hT1 := of_eq (freeImages_rename w a f T Fin.castSucc) (under hT B)
  let C := (SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))).conj
    (IndexTermImageCodeSyntax.converted false w.castSucc.castSucc (Fin.last (m+1)) T.castSucc.castSucc
      f.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc)
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) hT1
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ B) C
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) C)
  have hId := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc f.castSucc (Fin.last m) Fin.castSucc)
    (under (.conjL hB) C)
  have hConv := of_eq (IndexTermImageCodeSyntax.converted_rename false w.castSucc (Fin.last m) S.castSucc
    f.castSucc a.castSucc f.castSucc Fin.castSucc) (under (.conjR hB) C)
  have he := SyntaxIdentityUnique.code_unique hZ2 w.castSucc.castSucc f.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 hId (.conjL hC)
  have hc := converted_index_subst w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    S.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc he hConv
  exact IndexTermImageCodeUnique.unique hZ2 false w.castSucc.castSucc (Fin.last (m+1))
    S.castSucc.castSucc T.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc
    hw2 hc (.conjR hC)

private theorem mixed_inputs_subst {m} {Γ : Context m} (w a q : Fin m)
    (xs ys : Fin 5 → Fin m) (he : ∀ i, Derives Γ (.equal (xs i) (ys i)))
    (h : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (xs 3) (xs 4) (xs 0) (xs 1) a (xs 1) (xs 2) q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (ys 3) (ys 4) (ys 0) (ys 1) a (ys 1) (ys 2) q) := by
  let F0 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (xs 3).castSucc (xs 4).castSucc (Fin.last m) (xs 1).castSucc a.castSucc (xs 1).castSucc (xs 2).castSucc q.castSucc
  have h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (xs 3) (xs 4) (ys 0) (xs 1) a (xs 1) (xs 2) q) := by
    exact of_eq (by simp only [F0, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst F0 (he 0) (of_eq (by simp only [F0, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let F1 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (xs 3).castSucc (xs 4).castSucc (ys 0).castSucc (Fin.last m) a.castSucc (Fin.last m) (xs 2).castSucc q.castSucc
  have h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (xs 3) (xs 4) (ys 0) (ys 1) a (ys 1) (xs 2) q) := by
    exact of_eq (by simp only [F1, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst F1 (he 1) (of_eq (by simp only [F1, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  let F2 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (xs 3).castSucc (xs 4).castSucc (ys 0).castSucc (ys 1).castSucc a.castSucc (ys 1).castSucc (Fin.last m) q.castSucc
  have h3 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (xs 3) (xs 4) (ys 0) (ys 1) a (ys 1) (ys 2) q) := by
    exact of_eq (by simp only [F2, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst F2 (he 2) (of_eq (by simp only [F2, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h2))
  let F3 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (Fin.last m) (xs 4).castSucc (ys 0).castSucc (ys 1).castSucc a.castSucc (ys 1).castSucc (ys 2).castSucc q.castSucc
  have h4 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (ys 3) (xs 4) (ys 0) (ys 1) a (ys 1) (ys 2) q) := by
    exact of_eq (by simp only [F3, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst F3 (he 3) (of_eq (by simp only [F3, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h3))
  let F4 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (ys 3).castSucc (Fin.last m) (ys 0).castSucc (ys 1).castSucc a.castSucc (ys 1).castSucc (ys 2).castSucc q.castSucc
  have h5 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (ys 3) (ys 4) (ys 0) (ys 1) a (ys 1) (ys 2) q) := by
    exact of_eq (by simp only [F4, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst F4 (he 4) (of_eq (by simp only [F4, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h4))
  exact h5

private theorem matrix_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w a x y q v : Fin m)
    (xs ys : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (matrix equality R w a x y q xs))
    (hy : Derives Γ (matrix equality R w a x y v ys)) : Derives Γ (.equal q v) := by
  have ht := SyntaxNumerals.unique hZ 2 (xs 0) (ys 0) (.conjL hx) (.conjL hy)
  have hf := SyntaxNumerals.unique hZ (n+2) (xs 1) (ys 1) (.conjL (.conjR hx)) (.conjL (.conjR hy))
  have hNx := Derives.conjL (.conjR (.conjR hx))
  have hNy := Derives.conjL (.conjR (.conjR hy))
  have hN := PureQuotationSyntax.formula_unique hZ (template equality R) w (xs 2) (ys 2) hw (.conjL hNx) (.conjL hNy)
  have hUx := Derives.conjL (.conjR (.conjR (.conjR hx)))
  have hUy := Derives.conjL (.conjR (.conjR (.conjR hy)))
  have hU := SyntaxForests.unique hZ 2 w (SetLanguage.args2 y x) (xs 3) (ys 3) hw hUx hUy
  have hVx := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))
  have hVy := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))
  have hVa := freeImages_scope_subst w a (xs 1) (ys 1) (xs 4) hf hVx
  have hV := freeImages_unique hZ w a (ys 1) (xs 4) (ys 4) hw hVa hVy
  have hQx := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))
  have hQy := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))
  have he : ∀ i, Derives Γ (.equal (xs i) (ys i)) := by
    intro i
    exact Fin.cases ht (Fin.cases hf (Fin.cases hN (Fin.cases hU (Fin.cases hV (fun j => Fin.elim0 j))))) i
  have hQa := mixed_inputs_subst w a q xs ys he hQx
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (ys 3) (ys 4) (ys 0) (ys 1) a (ys 1) (ys 2) q v hw hQa hQy

/-- Independent quotation/length/list/identity witnesses give the same output.
No canonical witness, supplied recursive correctness, or output type is assumed. -/
theorem unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w a x y q v : Fin m)
    (hw : Derives Γ (omega w))
    (hq : Derives Γ (compiled equality R w a x y q))
    (hv : Derives Γ (compiled equality R w a x y v)) : Derives Γ (.equal q v) := by
  let B := body equality R w a x y q
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv1 := of_eq (compiled_rename equality R w a x y v (old 5)) (HornBinderRules.under_body 5 hv B)
  let C := body equality R (old 5 w) (old 5 a) (old 5 x) (old 5 y) (old 5 v)
  let Ξ := Context.add C (raisedContext 5 Δ)
  apply HornBinderRules.eliminate_many 5 C _ hv1
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 5 (old 5 w))) :=
    of_eq (by simp only [omega_rename])
      (HornBinderRules.under_body 5 (HornBinderRules.under_body 5 hw B) C)
  have hx2 : Derives Ξ (matrix equality R (old 5 (old 5 w)) (old 5 (old 5 a))
      (old 5 (old 5 x)) (old 5 (old 5 y)) (old 5 (old 5 q)) (fun i => old 5 (slot 5 i))) :=
    of_eq (by simp only [B, body, matrix_rename]) (HornBinderRules.under_body 5 hB C)
  exact matrix_unique (HornBinderRules.zf_body 5 (HornBinderRules.zf_body 5 hZ B) C) equality R
    (old 5 (old 5 w)) (old 5 (old 5 a)) (old 5 (old 5 x)) (old 5 (old 5 y))
    (old 5 (old 5 q)) (old 5 (old 5 v)) (fun i => old 5 (slot 5 i)) (slot 5) hw2 hx2 hC


/-- Every candidate using any actual compiler witnesses equals this result. -/
def uniqueOutput {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y q : Fin m) : Formula m := .all
  ((compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

private theorem uniqueOutput_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput equality R w a x y q).rename r = uniqueOutput equality R (r w) (r a) (r x) (r y) (r q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem unique_output {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w a x y q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled equality R w a x y q)) :
    Derives Γ (uniqueOutput equality R w a x y q) := by
  apply Derives.allI
  apply Derives.impI
  let B := compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hq1 := of_eq (compiled_rename equality R w a x y q Fin.castSucc) (under hq B)
  exact unique (ZFContext.under hZ B) equality R w.castSucc a.castSucc x.castSucc y.castSucc
    (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

/-- Typed unique output, with every witness still existential inside ZF. -/
def fiber {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y : Fin m) : Formula m := .ex
  ((compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)).conj
    ((typed n w.castSucc a.castSucc (Fin.last m)).conj
      (uniqueOutput equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m))))

private theorem fiber_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y : Fin m) (r : Fin m → Fin l) :
    (fiber equality R w a x y).rename r = fiber equality R (r w) (r a) (r x) (r y) := by
  simp only [fiber, Formula.rename, compiled_rename, typed_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x)) (hy : Derives Γ (SyntaxTermSyntax.term w a z y)) :
    Derives Γ (fiber equality R w a x y) := by
  let B := compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (total hZ equality R w a z x y hw hz hx hy)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht := compiled_type equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m) hB
  have hu := unique_output (ZFContext.under hZ B) equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hB
  have ho : Derives Δ (fiber equality R w.castSucc a.castSucc x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, compiled_rename, typed_rename,
      uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hB (.conjI ht hu))
  exact of_eq (fiber_rename equality R w a x y Fin.castSucc).symm ho

def uniqueSentence {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y q v : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled equality R w a x y q).imp
    ((compiled equality R w a x y v).imp (.equal q v)))).close

def fiberSentence {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxTermSyntax.term w a z x).imp
    ((SyntaxTermSyntax.term w a z y).imp (fiber equality R w a x y))))).close

theorem unique_kernel_certificate {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y q v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence equality R w a x y q v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    equality R w a x y q v (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (fiberSentence equality R w a z x y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _)
    equality R w a z x y (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingAtomicCode
