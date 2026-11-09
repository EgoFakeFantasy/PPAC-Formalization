import PPAC.Migration.Internal.SyntaxTermImageGraph
import PPAC.Migration.Internal.SyntaxMixedImageCodeExistence
import PPAC.Migration.Internal.TypedArgumentListConstruction
import PPAC.Migration.ForcingMemberGuardOpening

/-! The specific diagonal free-image update needed by the original relation
guard: selected p-slot takes bound-zero, all other slots keep their actual old
values. Original Replacement graph and original list encoder are reused.
Every index, length, graph, term and candidate list is an internal object. -/
namespace PPAC.Migration.ForcingReflexiveImages
open Internal Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedImageCodeSyntax (encoded encoded_rename termList termList_rename)
open SyntaxTermImageSyntax (imageMap imageMap_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem args3_map {m l} (f j h : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (SetLanguage.args3 f j h i)) = SetLanguage.args3 (ρ f) (ρ j) (ρ h) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun e => Fin.elim0 e) i) i) i

private def value {m} (f j h i q : Fin m) : Formula m :=
  ((Formula.equal i j).conj (.equal q h)).disj (((Formula.equal i j).neg).conj (edge f i q))
private theorem value_rename {m l} (f j h i q : Fin m) (ρ : Fin m → Fin l) :
    (value f j h i q).rename ρ = value (ρ f) (ρ j) (ρ h) (ρ i) (ρ q) := by
  simp only [value, Formula.rename, Formula.neg, edge_rename]
private def matrix : Formula 5 := value 0 1 2 3 4
private theorem matrix_rel {m} (ρ : Fin 3 → Fin m) (i q : Fin m) :
    rel matrix ρ i q = value (ρ 0) (ρ 1) (ρ 2) i q := by
  simp only [rel, SetLanguage.relation, matrix, value_rename]
  rfl

private theorem unique_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f a j h i q v : Fin m)
    (hf : Derives Γ (functionOn f a)) (hq : Derives Γ (value f j h i q))
    (hv : Derives Γ (value f j h i v)) : Derives Γ (.equal q v) := by
  apply Derives.disjE hq
  · let Q := (Formula.equal i j).conj (.equal q h)
    have hQ : Derives (Context.add Q Γ) Q := .hyp (Or.inl rfl)
    apply Derives.disjE (add hv Q)
    · exact eq_trans (add (.conjR hQ) _) (eq_symm (.conjR (.hyp (Or.inl rfl))))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add (.conjL hQ) _))
  · let Q := ((Formula.equal i j).neg).conj (edge f i q)
    have hQ : Derives (Context.add Q Γ) Q := .hyp (Or.inl rfl)
    apply Derives.disjE (add hv Q)
    · exact .botE (.impE (add (.conjL hQ) _) (.conjL (.hyp (Or.inl rfl))))
    · exact GraphProperties.single_valued f a i q v
        (ZFContext.arithmetic (ZFContext.add (ZFContext.add hZ Q) _)).base.extensionality
        (add (add hf Q) _) (add (.conjR hQ) _) (.conjR (.hyp (Or.inl rfl)))

private theorem point_exists {m} {Γ : Context m} (f a j h i : Fin m)
    (hf : Derives Γ (functionOn f a)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (.ex (value f.castSucc j.castSucc h.castSucc i.castSucc (Fin.last m))) := by
  apply SourcePropositional.by_cases (.equal i j)
  · have hv : Derives (Context.add (.equal i j) Γ) (value f j h i h) := .disjL (.conjI (.hyp (Or.inl rfl)) (.eqRefl h))
    apply Derives.exI h
    exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  · let N := (Formula.equal i j).neg
    let E := edge f.castSucc i.castSucc (Fin.last m)
    let Δ := Context.add E (Context.image Formula.raise (Context.add N Γ))
    apply Derives.exE (p := E) (GraphProperties.output_exists f a i (add hf N) (add hi N))
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hN : Derives Δ (Formula.equal i.castSucc j.castSucc).neg := under (.hyp (Or.inl rfl) : Derives (Context.add N Γ) N) E
    have hout : Derives Δ (.ex (value f.castSucc.castSucc j.castSucc.castSucc h.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)))) := by
      apply Derives.exI (Fin.last m)
      have hv : Derives Δ (value f.castSucc j.castSucc h.castSucc i.castSucc (Fin.last m)) := .disjR (.conjI hN hE)
      exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
    exact of_eq (by simp only [Formula.raise, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) hout

private theorem point_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 3 → Fin m) (a i : Fin m)
    (hf : Derives Γ (functionOn (ρ 0) a)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (fiber matrix ρ i) := by
  have he : Derives Γ (hasValue matrix ρ i) := of_eq (by simp only [hasValue, matrix_rel, paramsUp])
    (point_exists (ρ 0) a (ρ 1) (ρ 2) i hf hi)
  let Y := rel matrix (paramsUp ρ) i.castSucc (Fin.last m)
  let Δ1 := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hY : Derives Δ1 Y := .hyp (Or.inl rfl)
  have hu : Derives Δ1 (unique matrix (paramsUp ρ) i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel matrix (paramsUp (paramsUp ρ)) i.castSucc.castSucc (Fin.last (m+1))
    let Δ2 := Context.add Z (Context.image Formula.raise Δ1)
    have hZp : Derives Δ2 Z := .hyp (Or.inl rfl)
    exact unique_value (ZFContext.under (ZFContext.under hZ Y) Z) (ρ 0).castSucc.castSucc a.castSucc.castSucc
      (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
      (of_eq (by simp only [Formula.raise, functionOn_rename]) (under (under hf Y) Z))
      (of_eq (by simp only [Z, matrix_rel, paramsUp]) hZp)
      (of_eq (by simp only [Y, Formula.raise, matrix_rel, value_rename, paramsUp]) (under hY Z))
  have hout : Derives Δ1 (fiber matrix (paramsUp ρ) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) hout

private theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f a j h : Fin m)
    (hf : Derives Γ (functionOn f a)) : Derives Γ (ReplacementPredicates.total matrix (SetLanguage.args3 f j h) a) := by
  apply Derives.allI
  apply Derives.impI
  let I := Formula.mem (Fin.last m) a.castSucc
  let Δ := Context.add I (Context.image Formula.raise Γ)
  exact point_fiber (ZFContext.under hZ I) (paramsUp (SetLanguage.args3 f j h)) a.castSucc (Fin.last m)
    (of_eq (functionOn_rename f a Fin.castSucc) (under hf I)) (.hyp (Or.inl rfl))

private theorem typed_value {m} {Γ : Context m} (w f a c d j h i q : Fin m)
    (hf : Derives Γ (imageMap w f a c d)) (hh : Derives Γ (SyntaxTermSyntax.term w c d h))
    (hv : Derives Γ (value f j h i q)) : Derives Γ (SyntaxTermSyntax.term w c d q) := by
  apply Derives.disjE hv
  · exact TypedArgumentListConstruction.term_output_subst w c d h q (eq_symm (.conjR (.hyp (Or.inl rfl)))) (add hh _)
  · exact SyntaxTermImageSyntax.image_type w f a c d i q (add hf _) (.conjR (.hyp (Or.inl rfl)))

private theorem typed_outputs {m} {Γ : Context m} (w f a c d j h : Fin m)
    (hf : Derives Γ (imageMap w f a c d)) (hh : Derives Γ (SyntaxTermSyntax.term w c d h)) :
    Derives Γ (SyntaxTermImageGraph.outputsTyped matrix (SetLanguage.args3 f j h) w a c d) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (rel matrix (paramsUp (paramsUp (SetLanguage.args3 f j h))) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact typed_value w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc j.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (of_eq (by simp only [Formula.raise, imageMap_rename]) (SyntaxRenameBinders.under_2 hf H))
    (of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (SyntaxRenameBinders.under_2 hh H))
    (of_eq (by simp only [matrix_rel, paramsUp]; rfl) (.conjR hH))

/-- Old decoder, original point-update graph, and new encoder are genuine
object witnesses, not external lists or selected Type-level functions. -/
def data {m} (w a c d L j h D f g : Fin m) : Formula m :=
  (encoded w f a c d L).conj ((RelationGraphSyntax.functionGraph matrix (SetLanguage.args3 f j h) a g).conj (encoded w g a c d D))

theorem data_rename {m l} (w a c d L j h D f g : Fin m) (ρ : Fin m → Fin l) :
    (data w a c d L j h D f g).rename ρ = data (ρ w) (ρ a) (ρ c) (ρ d) (ρ L) (ρ j) (ρ h) (ρ D) (ρ f) (ρ g) := by
  simp only [data, Formula.rename, encoded_rename, RelationGraphSyntax.functionGraph_rename]
  congr 2

def body {m} (w a c d L j h D : Fin m) : Formula (m+2) :=
  data (old 2 w) (old 2 a) (old 2 c) (old 2 d) (old 2 L) (old 2 j) (old 2 h) (old 2 D) (slot 2 0) (slot 2 1)

def replacement {m} (w a c d L j h D : Fin m) : Formula m := existsMany 2 (body w a c d L j h D)

theorem replacement_rename {m l} (w a c d L j h D : Fin m) (ρ : Fin m → Fin l) :
    (replacement w a c d L j h D).rename ρ = replacement (ρ w) (ρ a) (ρ c) (ρ d) (ρ L) (ρ j) (ρ h) (ρ D) := by
  simp only [replacement, existsMany_rename, body, data_rename, lift_old, lift_slot]

def existsReplacement {m} (w a c d L j h : Fin m) : Formula m := .ex
  (replacement w.castSucc a.castSucc c.castSucc d.castSucc L.castSucc j.castSucc h.castSucc (Fin.last m))

theorem existsReplacement_rename {m l} (w a c d L j h : Fin m) (ρ : Fin m → Fin l) :
    (existsReplacement w a c d L j h).rename ρ = existsReplacement (ρ w) (ρ a) (ρ c) (ρ d) (ρ L) (ρ j) (ρ h) := by
  simp only [existsReplacement, Formula.rename, replacement_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Construct the actual replacement code using ONLY the original generic
Replacement/image graph and the original structural-list encoder. -/
theorem exists_replacement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d L j h : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (termList w a c d L))
    (hh : Derives Γ (SyntaxTermSyntax.term w c d h)) : Derives Γ (existsReplacement w a c d L j h) := by
  let F := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc
  let Δ1 := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) (SyntaxMixedImageCodeExistence.exists_graph hZ w a c d L hw hL)
  have hF : Derives Δ1 F := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ F
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw F)
  have hh1 := of_eq (SyntaxTermSyntax.term_rename w c d h Fin.castSucc) (under hh F)
  have hImg := Derives.conjL hF
  have he := SyntaxTermImageGraph.exists_image hZ1 matrix (SetLanguage.args3 (Fin.last m) j.castSucc h.castSucc)
    w.castSucc a.castSucc c.castSucc d.castSucc hw1 (.conjL hImg) (.conjL (.conjR hImg))
    (total hZ1 (Fin.last m) a.castSucc j.castSucc h.castSucc (SyntaxTermImageSyntax.image_function _ _ _ _ _ hImg))
    (typed_outputs w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc j.castSucc h.castSucc hImg hh1)
  let G := (imageMap w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc).conj
    (RelationGraphSyntax.functionGraph matrix (SetLanguage.args3 (Fin.last m).castSucc j.castSucc.castSucc h.castSucc.castSucc) a.castSucc.castSucc (Fin.last (m+1)))
  let Δ2 := Context.add G (Context.image Formula.raise Δ1)
  apply Derives.exE (p := G) he
  have hG : Derives Δ2 G := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 G
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 G)
  let D := encoded w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Δ3 := Context.add D (Context.image Formula.raise Δ2)
  apply Derives.exE (p := D) (SyntaxMixedImageCodeExistence.exists_code hZ2 w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc hw2 (.conjL hG))
  have hD : Derives Δ3 D := .hyp (Or.inl rfl)
  have hF3 : Derives Δ3 (encoded w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [F, Formula.raise, encoded_rename]) (under (under hF G) D)
  have hG3 := under hG D
  have hGraph3 : Derives Δ3 (RelationGraphSyntax.functionGraph matrix (SetLanguage.args3 (Fin.last m).castSucc.castSucc j.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc) a.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (by simp only [RelationGraphSyntax.functionGraph_rename, args3_map]) (.conjR hG3)
  have hout : Derives Δ3 (existsReplacement w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc) := by
    have hr : Derives Δ3 (replacement w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc (Fin.last (m+2))) := by
      apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)
      exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) (.conjI hF3 (.conjI hGraph3 hD))
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, replacement_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  exact of_eq (by simp only [Formula.raise, existsReplacement_rename]) hout

/-- Field law for ALL internal indices/candidates, including nonstandard.
Only the selected slot changes. -/
def fieldResult {m} (w L j h D i q : Fin m) : Formula m :=
  (StructuralListFieldSyntax.field w D i q).iff
    (((Formula.equal i j).conj (.equal q h)).disj (((Formula.equal i j).neg).conj (StructuralListFieldSyntax.field w L i q)))

theorem fieldResult_rename {m l} (w L j h D i q : Fin m) (ρ : Fin m → Fin l) :
    (fieldResult w L j h D i q).rename ρ = fieldResult (ρ w) (ρ L) (ρ j) (ρ h) (ρ D) (ρ i) (ρ q) := by
  simp only [fieldResult, Formula.iff, Formula.neg, Formula.rename, StructuralListFieldSyntax.field_rename]

private theorem at_graph_field {m} {Γ : Context m} (w a c d L j h D f g i q : Fin m)
    (he : Derives Γ (data w a c d L j h D f g)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (fieldResult w L j h D i q) := by
  have hOld := SyntaxMixedImageCodeFields.edges w f a c d L i q (.conjL he)
  have hNew := SyntaxMixedImageCodeFields.edges w g a c d D i q (.conjR (.conjR he))
  have hGraph := RelationGraphSyntax.law_at matrix (SetLanguage.args3 f j h) a g i q (.conjR (.conjL (.conjR he)))
  have hGraph' : Derives Γ ((edge g i q).iff ((Formula.mem i a).conj (value f j h i q))) :=
    of_eq (by simp only [matrix_rel]; rfl) hGraph
  apply Derives.conjI
  · apply Derives.impI
    let Q := StructuralListFieldSyntax.field w D i q
    have hV : Derives (Context.add Q Γ) (value f j h i q) :=
      .conjR (.impE (add (.conjL hGraph') Q) (.impE (add (.conjR hNew) Q) (.conjI (add hi Q) (.hyp (Or.inl rfl)))))
    apply Derives.disjE hV
    · exact .disjL (.hyp (Or.inl rfl))
    · have hq := (Derives.hyp (Or.inl rfl) : Derives (Context.add (((Formula.equal i j).neg).conj (edge f i q)) (Context.add Q Γ)) _)
      exact .disjR (.conjI (.conjL hq) (.conjR (.impE (add (add (.conjL hOld) Q) _) (.conjR hq))))
  · apply Derives.impI
    let Q := ((Formula.equal i j).conj (.equal q h)).disj (((Formula.equal i j).neg).conj (StructuralListFieldSyntax.field w L i q))
    have hV : Derives (Context.add Q Γ) (value f j h i q) := by
      apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .disjL (.hyp (Or.inl rfl))
      · have hq := (Derives.hyp (Or.inl rfl) : Derives (Context.add (((Formula.equal i j).neg).conj (StructuralListFieldSyntax.field w L i q)) (Context.add Q Γ)) _)
        exact .disjR (.conjI (.conjL hq) (.impE (add (add (.conjR hOld) Q) _) (.conjI (add (add hi Q) _) (.conjR hq))))
    exact .conjR (.impE (add (.conjL hNew) Q) (.impE (add (.conjR hGraph') Q) (.conjI (add hi Q) hV)))

theorem field_iff {m} {Γ : Context m} (w a c d L j h D i q : Fin m)
    (hr : Derives Γ (replacement w a c d L j h D)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (fieldResult w L j h D i q) := by
  let B := body w a c d L j h D
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := at_graph_field (old 2 w) (old 2 a) (old 2 c) (old 2 d) (old 2 L) (old 2 j) (old 2 h) (old 2 D) (slot 2 0) (slot 2 1) (old 2 i) (old 2 q) hB (HornBinderRules.under_body 2 hi B)
  exact of_eq (fieldResult_rename w L j h D i q (old 2)).symm hout

theorem target_type {m} {Γ : Context m} (w a c d L j h D : Fin m)
    (hr : Derives Γ (replacement w a c d L j h D)) : Derives Γ (termList w a c d D) := by
  let B := body w a c d L j h D
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := SyntaxMixedImageCodeFields.term_list (old 2 w) (slot 2 1) (old 2 a) (old 2 c) (old 2 d) (old 2 D) (.conjR (.conjR hB))
  exact of_eq (termList_rename w a c d D (old 2)).symm hout

/-- Actual target head, actual updated lifted free table, and actual output
of the SAME original relation guard under K/updatedH. -/
def diagonalData {m} (w z f T A C K H j Q head D F : Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w C T z head).conj ((replacement w f C T H j head D).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted w K D A f C T Q F))

theorem diagonalData_rename {m l} (w z f T A C K H j Q head D F : Fin m) (ρ : Fin m → Fin l) :
    (diagonalData w z f T A C K H j Q head D F).rename ρ = diagonalData (ρ w) (ρ z) (ρ f) (ρ T) (ρ A) (ρ C) (ρ K) (ρ H) (ρ j) (ρ Q) (ρ head) (ρ D) (ρ F) := by
  simp only [diagonalData, Formula.rename, SyntaxMixedImageHead.head_rename, replacement_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def diagonalBody {m} (w z f T A C K H j Q : Fin m) : Formula (m+3) :=
  diagonalData (old 3 w) (old 3 z) (old 3 f) (old 3 T) (old 3 A) (old 3 C) (old 3 K) (old 3 H) (old 3 j) (old 3 Q) (slot 3 0) (slot 3 1) (slot 3 2)

def diagonal {m} (w z f T A C K H j Q : Fin m) : Formula m := existsMany 3 (diagonalBody w z f T A C K H j Q)

theorem diagonal_rename {m l} (w z f T A C K H j Q : Fin m) (ρ : Fin m → Fin l) :
    (diagonal w z f T A C K H j Q).rename ρ = diagonal (ρ w) (ρ z) (ρ f) (ρ T) (ρ A) (ρ C) (ρ K) (ρ H) (ρ j) (ρ Q) := by
  simp only [diagonal, existsMany_rename, diagonalBody, diagonalData_rename, lift_old, lift_slot]

/-- Concrete consumer: build bound-zero and the actual replacement list,
then run the EXISTING full mixed formula transformer on the SAME real guard.
No new recursion, supplied output, or field-law oracle is used. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s j rawHead Q : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f rawHead Q)) :
    Derives Γ (diagonal w z f T A C K H j Q) := by
  have hw := Derives.conjL hf
  have hz := Derives.conjL (.conjR (.conjR hf))
  have hl := Derives.conjL (.conjR (.conjR (.conjR (.conjR hf))))
  have hP := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T A C K H hl
  have hC := Derives.conjR (.conjR hInput)
  have hLists := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H hl
  have hQ := ForcingGuardCode.compiled_type order Reln w A f rawHead Q hc
  have he := SyntaxMixedImageHead.code_exists hZ w z C T z hw (.conjL (.conjL hP)) (.conjR (.conjL hP)) hC hz
  let X := SyntaxMixedImageHead.head w.castSucc C.castSucc T.castSucc z.castSucc (Fin.last m)
  let Δ1 := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) he
  have hX : Derives Δ1 X := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ X
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw X)
  have hLists1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w A f C T K H Fin.castSucc) (under hLists X)
  have hd := exists_replacement hZ1 w.castSucc f.castSucc C.castSucc T.castSucc H.castSucc j.castSucc (Fin.last m) hw1 (.conjR hLists1) (.conjR (.conjR hX))
  let U := replacement w.castSucc.castSucc f.castSucc.castSucc C.castSucc.castSucc T.castSucc.castSucc H.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ2 := Context.add U (Context.image Formula.raise Δ1)
  apply Derives.exE (p := U) hd
  have hU : Derives Δ2 U := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 U
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 U)
  have hK2 := of_eq (termList_rename w.castSucc A.castSucc C.castSucc T.castSucc K.castSucc Fin.castSucc) (under (.conjL hLists1) U)
  have hD2 := target_type w.castSucc.castSucc f.castSucc.castSucc C.castSucc.castSucc T.castSucc.castSucc H.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hU
  have hQ2 : Derives Δ2 (FormulaCodeSyntax.formulaCode w.castSucc.castSucc Q.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (under (under hQ X) U)
  have ho := SyntaxMixedFormulaOutputInduction.actual_exists hZ2 w.castSucc.castSucc K.castSucc.castSucc (Fin.last (m+1)) A.castSucc.castSucc f.castSucc.castSucc C.castSucc.castSucc T.castSucc.castSucc Q.castSucc.castSucc hw2 (.conjI hQ2 (.conjI hK2 hD2))
  let Y := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc A.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc Q.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Δ3 := Context.add Y (Context.image Formula.raise Δ2)
  apply Derives.exE (p := Y) ho
  have hY : Derives Δ3 Y := .hyp (Or.inl rfl)
  have hX3 : Derives Δ3 (SyntaxMixedImageHead.head w.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := of_eq (by simp only [X, Formula.raise, SyntaxMixedImageHead.head_rename]) (under (under hX U) Y)
  have hU3 : Derives Δ3 (replacement w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [U, Formula.raise, replacement_rename]) (under hU Y)
  have hout : Derives Δ3 (diagonal (old 3 w) (old 3 z) (old 3 f) (old 3 T) (old 3 A) (old 3 C) (old 3 K) (old 3 H) (old 3 j) (old 3 Q)) := by
    apply HornBinderRules.intro_many 3 _ (SetLanguage.args3 (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))
    exact of_eq (by simp only [diagonalBody, diagonalData_rename, assign_old, assign_slot]; rfl) (.conjI hX3 (.conjI hU3 hY))
  exact of_eq (by simp only [Formula.raise, diagonal_rename]; rfl) hout

end PPAC.Migration.ForcingReflexiveImages
