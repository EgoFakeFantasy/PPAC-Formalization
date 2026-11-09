import PPAC.Migration.ForcingAtomCode
import PPAC.Migration.Internal.SyntaxTopAbstractExistence
import PPAC.Migration.Internal.SyntaxMixedImageCodeUnique

/-! Pinned source: ForcingQuotient.AtomicData.Force, negative and existential
branches; native consumer: the recursive forcing-formula code compiler.
Concrete forcing-condition rebind: a designated free condition is replaced
by the new bound condition, while old bounds shift. All scopes/indices/codes are
objects. Existing Replacement, table construction and mixed substitution are
reused; this is not a full recursive forcing interpreter or a Con proof. -/
namespace PPAC.Migration.ForcingConditionRebind
open Internal Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)
set_option maxRecDepth 16384

private theorem excluded {m} {Γ : Context m} (p : Formula m) : Derives Γ (p.disj p.neg) := by
  apply Derives.classical
  let N := (p.disj p.neg).neg
  have hN : Derives (Context.add N Γ) N := .hyp (Or.inl rfl)
  have hn : Derives (Context.add N Γ) p.neg := .impI (.impE (add hN p) (.disjL (.hyp (Or.inl rfl))))
  exact .impE hN (.disjR hn)

/-- Exact free-variable table: replace j by t, leave every other free index. -/
def value {m} (w j t i q : Fin m) : Formula m :=
  ((Formula.equal i j).conj (.equal q t)).disj
    ((Formula.equal i j).neg.conj (SyntaxVariableSyntax.code false w i q))

theorem value_rename {m l} (w j t i q : Fin m) (r : Fin m → Fin l) :
    (value w j t i q).rename r = value (r w) (r j) (r t) (r i) (r q) := by
  simp only [value, Formula.neg, Formula.rename, SyntaxVariableSyntax.code_rename]

private theorem value_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t i q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (value w j t i q)) (hv : Derives Γ (value w j t i v)) :
    Derives Γ (.equal q v) := by
  apply Derives.disjE hq
  · let P := (Formula.equal i j).conj (.equal q t)
    have hP : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    apply Derives.disjE (add hv P)
    · exact eq_trans (.conjR (add hP _)) (eq_symm (.conjR (.hyp (Or.inl rfl))))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.conjL (add hP _)))
  · let P := (Formula.equal i j).neg.conj (SyntaxVariableSyntax.code false w i q)
    have hP : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    apply Derives.disjE (add hv P)
    · exact .botE (.impE (.conjL (add hP _)) (.conjL (.hyp (Or.inl rfl))))
    · exact SyntaxVariables.unique (ZFContext.add (ZFContext.add hZ P) _) false w i q v
        (add (add hw P) _) (.conjR (add hP _)) (.conjR (.hyp (Or.inl rfl)))

private theorem value_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) :
    Derives Γ (.ex (value w.castSucc j.castSucc t.castSucc i.castSucc (Fin.last m))) := by
  apply Derives.disjE (excluded (Formula.equal i j))
  · have hv : Derives (Context.add (Formula.equal i j) Γ) (value w j t i t) :=
      .disjL (.conjI (.hyp (Or.inl rfl)) (.eqRefl t))
    apply Derives.exI t
    exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  · let N := (Formula.equal i j).neg
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc i.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add N Γ))
    apply Derives.exE (p := B) (SyntaxVariables.exists_code (ZFContext.add hZ N) false w i (add hw N) (add hi N))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hn : Derives Δ (Formula.equal i.castSucc j.castSucc).neg := of_eq (by simp only [N, Formula.raise, Formula.neg, Formula.rename])
      (under (Derives.hyp (Or.inl rfl) : Derives (Context.add N Γ) N) B)
    have ho : Derives Δ (.ex (value w.castSucc.castSucc j.castSucc.castSucc t.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)))) := by
      apply Derives.exI (Fin.last m)
      have hv : Derives Δ (value w.castSucc j.castSucc t.castSucc i.castSucc (Fin.last m)) := .disjR (.conjI hn (.conjR hB))
      exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
    exact of_eq (by simp only [Formula.raise, Formula.rename, value_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

private theorem value_type {m} {Γ : Context m} (w j t f A i q : Fin m)
    (hc : Derives Γ (SyntaxTermSyntax.contexts w A f)) (hi : Derives Γ (.mem i f))
    (ht : Derives Γ (SyntaxTermSyntax.term w A f t)) (hv : Derives Γ (value w j t i q)) :
    Derives Γ (SyntaxTermSyntax.term w A f q) := by
  apply Derives.disjE hv
  · exact SyntaxAtomLogic.term_output_subst w A f t q (eq_symm (.conjR (.hyp (Or.inl rfl)))) (add ht _)
  · exact SyntaxTermSyntax.intro_term false w A f q i (.conjI (add hc _) (add hi _)) (.conjR (.hyp (Or.inl rfl)))

private def matrix {p} (w j t : Fin p) : Formula (p+2) :=
  value w.castSucc.castSucc j.castSucc.castSucc t.castSucc.castSucc (Fin.last p).castSucc (Fin.last (p+1))

private theorem matrix_rel {p m} (w j t : Fin p) (rho : Fin p → Fin m) (i q : Fin m) :
    ReplacementPredicates.rel (matrix w j t) rho i q = value (rho w) (rho j) (rho t) i q := by
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, value_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem total_matrix {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t : Fin p)
    (rho : Fin p → Fin m) (f : Fin m) (hw : Derives Γ (omega (rho w))) (hf : Derives Γ (.mem f (rho w))) :
    Derives Γ (ReplacementPredicates.total (matrix w j t) rho f) := by
  apply Derives.allI
  apply Derives.impI
  let I := Formula.mem (Fin.last m) f.castSucc
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ I
  have hw1 := of_eq (omega_rename (rho w) Fin.castSucc) (under hw I)
  have hi := StructuralListTraceOrder.member_member hZ1 (rho w).castSucc (Fin.last m) f.castSucc hw1 (under hf I) (.hyp (Or.inl rfl))
  have he : Derives Δ (ReplacementPredicates.hasValue (matrix w j t) (paramsUp rho) (Fin.last m)) :=
    of_eq (by simp only [ReplacementPredicates.hasValue, matrix_rel, paramsUp])
      (value_exists hZ1 (rho w).castSucc (rho j).castSucc (rho t).castSucc (Fin.last m) hw1 hi)
  let B := ReplacementPredicates.rel (matrix w j t) (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add B (Context.image Formula.raise Δ)
  apply Derives.exE (p := B) he
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hu : Derives Ξ (ReplacementPredicates.unique (matrix w j t) (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))) := by
    apply Derives.allI
    apply Derives.impI
    let C := ReplacementPredicates.rel (matrix w j t) (paramsUp (paramsUp (paramsUp rho)))
      (Fin.last m).castSucc.castSucc (Fin.last (m+2))
    have hx : Derives (Context.add C (Context.image Formula.raise Ξ))
        (value (rho w).castSucc.castSucc.castSucc (rho j).castSucc.castSucc.castSucc
          (rho t).castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) :=
      of_eq (by simp only [B, Formula.raise, matrix_rel, paramsUp, value_rename]) (under hB C)
    have hy : Derives (Context.add C (Context.image Formula.raise Ξ))
        (value (rho w).castSucc.castSucc.castSucc (rho j).castSucc.castSucc.castSucc
          (rho t).castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))) :=
      of_eq (by simp only [C, matrix_rel, paramsUp]) (.hyp (Or.inl rfl))
    have hw3 : Derives (Context.add C (Context.image Formula.raise Ξ)) (omega (rho w).castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw1 B) C)
    exact value_unique (ZFContext.under (ZFContext.under hZ1 B) C) _ _ _ _ _ _ hw3 hy hx
  have ho : Derives Ξ (ReplacementPredicates.fiber (matrix w j t) (paramsUp (paramsUp rho)) (Fin.last m).castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, ReplacementPredicates.rel_rename,
      ReplacementPredicates.unique_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hB hu)
  exact of_eq (ReplacementPredicates.fiber_rename (matrix w j t) (paramsUp rho) (Fin.last m) Fin.castSucc).symm ho

private theorem typed_matrix {p m} {Γ : Context m} (w j t : Fin p) (rho : Fin p → Fin m) (f A : Fin m)
    (hc : Derives Γ (SyntaxTermSyntax.contexts (rho w) A f)) (ht : Derives Γ (SyntaxTermSyntax.term (rho w) A f (rho t))) :
    Derives Γ (SyntaxTermImageGraph.outputsTyped (matrix w j t) rho (rho w) f A f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc f.castSucc.castSucc).conj
    (ReplacementPredicates.rel (matrix w j t) (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (raisedContext 2 Γ)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv : Derives Δ (value (rho w).castSucc.castSucc (rho j).castSucc.castSucc (rho t).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) := of_eq (by simp only [matrix_rel, paramsUp]) (.conjR hB)
  have hc2 : Derives Δ (SyntaxTermSyntax.contexts (rho w).castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (OrderedPairElimination.under_two hc B)
  have ht2 : Derives Δ (SyntaxTermSyntax.term (rho w).castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc (rho t).castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (OrderedPairElimination.under_two ht B)
  exact value_type _ _ _ _ _ _ _ hc2 (.conjL hB) ht2 hv

def law {m} (w j t f g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc f.castSucc.castSucc).conj
      (value w.castSucc.castSucc j.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

private theorem matrix_law {p m} (w j t : Fin p) (rho : Fin p → Fin m) (f g : Fin m) :
    RelationGraphSyntax.edgeLaw (matrix w j t) rho f g = law (rho w) (rho j) (rho t) f g := by
  simp only [RelationGraphSyntax.edgeLaw, matrix_rel, paramsUp, law]

def mapped {m} (w j t f A g : Fin m) : Formula m :=
  (SyntaxTermImageSyntax.imageMap w g f A f).conj (law w j t f g)

theorem law_rename {m l} (w j t f g : Fin m) (r : Fin m → Fin l) :
    (law w j t f g).rename r = law (r w) (r j) (r t) (r f) (r g) := by
  simp only [law, Formula.iff, Formula.rename, edge_rename, value_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem mapped_rename {m l} (w j t f A g : Fin m) (r : Fin m → Fin l) :
    (mapped w j t f A g).rename r = mapped (r w) (r j) (r t) (r f) (r A) (r g) := by
  simp only [mapped, Formula.rename, SyntaxTermImageSyntax.imageMap_rename, law_rename]

private theorem exists_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t f A : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxTermSyntax.contexts w A f))
    (ht : Derives Γ (SyntaxTermSyntax.term w A f t)) :
    Derives Γ (.ex (mapped w.castSucc j.castSucc t.castSucc f.castSucc A.castSucc (Fin.last m))) := by
  have he := SyntaxTermImageGraph.exists_image hZ (matrix w j t) (id : Fin m → Fin m) w f A f hw (.conjR hc) hc
    (total_matrix hZ w j t id f hw (.conjR hc)) (typed_matrix w j t id f A hc ht)
  let B := (SyntaxTermImageSyntax.imageMap w.castSucc (Fin.last m) f.castSucc A.castSucc f.castSucc).conj
    (RelationGraphSyntax.functionGraph (matrix w j t) (paramsUp (id : Fin m → Fin m)) f.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hl := of_eq (matrix_law w j t (paramsUp (id : Fin m → Fin m)) f.castSucc (Fin.last m)) (.conjR (.conjR hB))
  have ho : Derives Δ (.ex (mapped w.castSucc.castSucc j.castSucc.castSucc t.castSucc.castSucc f.castSucc.castSucc A.castSucc.castSucc (Fin.last (m+1)))) := by
    apply Derives.exI (Fin.last m)
    have hm : Derives Δ (mapped w.castSucc j.castSucc t.castSucc f.castSucc A.castSucc (Fin.last m)) := .conjI (.conjL hB) hl
    exact of_eq (by simp only [Formula.instantiate, mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hm
  exact of_eq (by simp only [Formula.raise, Formula.rename, mapped_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho


private theorem mapped_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t f A g h : Fin m)
    (hg : Derives Γ (mapped w j t f A g)) (hh : Derives Γ (mapped w j t f A h)) : Derives Γ (.equal g h) := by
  have hG : Derives Γ (RelationGraphSyntax.functionGraph (matrix w j t) id f g) :=
    .conjI (SyntaxTermImageSyntax.image_function w g f A f (.conjL hg))
      (of_eq (matrix_law w j t id f g).symm (.conjR hg))
  have hH : Derives Γ (RelationGraphSyntax.functionGraph (matrix w j t) id f h) :=
    .conjI (SyntaxTermImageSyntax.image_function w h f A f (.conjL hh))
      (of_eq (matrix_law w j t id f h).symm (.conjR hh))
  exact RelationGraph.unique_graph hZ (matrix w j t) id f g h hG hH

private def boundData {m} (w a f A F R : Fin m) : Formula m :=
  (SyntaxVariableTableSyntax.shifted true w a A f F).conj (SyntaxMixedImageCodeSyntax.encoded w F a A f R)

private theorem boundData_rename {m l} (w a f A F R : Fin m) (r : Fin m → Fin l) :
    (boundData w a f A F R).rename r = boundData (r w) (r a) (r f) (r A) (r F) (r R) := by
  simp only [boundData, Formula.rename, SyntaxVariableTableSyntax.shifted_rename, SyntaxMixedImageCodeSyntax.encoded_rename]

private def boundBody {m} (w a f A : Fin m) : Formula (m+2) := boundData (old 2 w) (old 2 a) (old 2 f) (old 2 A) (slot 2 0) (slot 2 1)

private def existsBound {m} (w a f A : Fin m) : Formula m := existsMany 2 (boundBody w a f A)

private theorem bound_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f A : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxTermSyntax.contexts w A f))
    (ha : Derives Γ (.mem a w)) (hs : Derives Γ (successor A a)) : Derives Γ (existsBound w a f A) := by
  let B := SyntaxVariableTableSyntax.shifted true w.castSucc a.castSucc A.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxVariableTableExistence.shifted_exists hZ true w a A f hw hc ha hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm := SyntaxVariableTableUnique.shifted_type true w.castSucc a.castSucc A.castSucc f.castSucc (Fin.last m) hB
  let C := SyntaxMixedImageCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) (SyntaxMixedImageCodeExistence.exists_code (ZFContext.under hZ B) w.castSucc (Fin.last m) a.castSucc A.castSucc f.castSucc hw1 hm)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hb := of_eq (SyntaxVariableTableSyntax.shifted_rename true w.castSucc a.castSucc A.castSucc f.castSucc (Fin.last m) Fin.castSucc) (under hB C)
  have ho : Derives Ξ (existsBound w.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc A.castSucc.castSucc) := by
    apply HornBinderRules.intro_many 2 _ (SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1)))
    exact of_eq (by simp only [boundBody, boundData_rename, assign_old, assign_slot]; rfl) (.conjI hb hC)
  exact of_eq (by simp only [existsBound, Formula.raise, existsMany_rename, boundBody, boundData_rename,
    lift_old, lift_slot]) ho

private def freeData {m} (w j t f A G S : Fin m) : Formula m :=
  (mapped w j t f A G).conj (SyntaxMixedImageCodeSyntax.encoded w G f A f S)

private theorem freeData_rename {m l} (w j t f A G S : Fin m) (r : Fin m → Fin l) :
    (freeData w j t f A G S).rename r = freeData (r w) (r j) (r t) (r f) (r A) (r G) (r S) := by
  simp only [freeData, Formula.rename, mapped_rename, SyntaxMixedImageCodeSyntax.encoded_rename]

private def freeBody {m} (w j t f A : Fin m) : Formula (m+2) := freeData (old 2 w) (old 2 j) (old 2 t) (old 2 f) (old 2 A) (slot 2 0) (slot 2 1)

private def existsFree {m} (w j t f A : Fin m) : Formula m := existsMany 2 (freeBody w j t f A)

private theorem free_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t f A : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxTermSyntax.contexts w A f))
    (ht : Derives Γ (SyntaxTermSyntax.term w A f t)) : Derives Γ (existsFree w j t f A) := by
  let B := mapped w.castSucc j.castSucc t.castSucc f.castSucc A.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (exists_map hZ w j t f A hw hc ht)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  let C := SyntaxMixedImageCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc f.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) (SyntaxMixedImageCodeExistence.exists_code (ZFContext.under hZ B) w.castSucc (Fin.last m) f.castSucc A.castSucc f.castSucc hw1 (.conjL hB))
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hb := of_eq (mapped_rename w.castSucc j.castSucc t.castSucc f.castSucc A.castSucc (Fin.last m) Fin.castSucc) (under hB C)
  have ho : Derives Ξ (existsFree w.castSucc.castSucc j.castSucc.castSucc t.castSucc.castSucc f.castSucc.castSucc A.castSucc.castSucc) := by
    apply HornBinderRules.intro_many 2 _ (SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1)))
    exact of_eq (by simp only [freeBody, freeData_rename, assign_old, assign_slot]; rfl) (.conjI hb hC)
  exact of_eq (by simp only [existsFree, Formula.raise, existsMany_rename, freeBody, freeData_rename,
    lift_old, lift_slot]) ho


private structure Inputs {m} (Γ : Context m) (w a f A n : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hs : Derives Γ (successor A a)
  hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a f)

private theorem underInputs2 {m} {Γ : Context m} {w a f A n : Fin m}
    (h : Inputs Γ w a f A n) (B : Formula (m+2)) :
    Inputs (Context.add B (raisedContext 2 Γ)) (old 2 w) (old 2 a) (old 2 f) (old 2 A) (old 2 n) := by
  exact {
    hw := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h.hw B)
    hs := of_eq (successor_rename A a (old 2)) (HornBinderRules.under_body 2 h.hs B)
    hn := of_eq (FormulaCodeSyntax.formulaCode_rename w n a f (old 2)) (HornBinderRules.under_body 2 h.hn B) }

private theorem target_contexts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {w a f A n : Fin m}
    (h : Inputs Γ w a f A n) : Derives Γ (SyntaxTermSyntax.contexts w A f) := by
  have hc := Derives.conjR (FormulaCodeProperties.guards w n a f h.hn)
  exact .conjI (OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality h.hw (.conjL hc) h.hs) (.conjR hc)

def data {m} (w a f A j n q : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w A f (v 0) (v 1)).conj
    ((boundData w a f A (v 2) (v 3)).conj
      ((freeData w j (v 1) f A (v 4) (v 5)).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 3) (v 5) a f A f n q)))

theorem data_rename {m l} (w a f A j n q : Fin m) (v : Fin 6 → Fin m) (r : Fin m → Fin l) :
    (data w a f A j n q v).rename r = data (r w) (r a) (r f) (r A) (r j) (r n) (r q) (fun i => r (v i)) := by
  simp only [data, Formula.rename, SyntaxMixedImageHead.head_rename, boundData_rename, freeData_rename,
    SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private def body {m} (w a f A j n q : Fin m) : Formula (m+6) :=
  data (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 n) (old 6 q) (slot 6)

/-- Actual head, shifted bound table, conditional free table, both encoded
lists, and the complete existing formula substitution are all inside EX. -/
def compiled {m} (w a f A j n q : Fin m) : Formula m := existsMany 6 (body w a f A j n q)

theorem compiled_rename {m l} (w a f A j n q : Fin m) (r : Fin m → Fin l) :
    (compiled w a f A j n q).rename r = compiled (r w) (r a) (r f) (r A) (r j) (r n) (r q) := by
  simp only [compiled, existsMany_rename, body, data_rename, lift_old, lift_slot]

def existsCompiled {m} (w a f A j n : Fin m) : Formula m := .ex
  (compiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m))

private theorem existsCompiled_rename {m l} (w a f A j n : Fin m) (r : Fin m → Fin l) :
    (existsCompiled w a f A j n).rename r = existsCompiled (r w) (r a) (r f) (r A) (r j) (r n) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem from_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f A j n z t F R G S : Fin m) (h : Inputs Γ w a f A n)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z t))
    (hb : Derives Γ (boundData w a f A F R)) (hf : Derives Γ (freeData w j t f A G S)) :
    Derives Γ (existsCompiled w a f A j n) := by
  have hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a f A f n) := .conjI h.hn
    (.conjI (SyntaxMixedImageCodeFields.term_list w F a A f R (.conjR hb))
      (SyntaxMixedImageCodeFields.term_list w G f A f S (.conjR hf)))
  let B := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc f.castSucc A.castSucc f.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w R S a f A f n h.hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f z t Fin.castSucc) (under hh B)
  have hb1 := of_eq (boundData_rename w a f A F R Fin.castSucc) (under hb B)
  have hf1 := of_eq (freeData_rename w j t f A G S Fin.castSucc) (under hf B)
  let v : Fin 6 → Fin (m+1) := Fin.cases z.castSucc (Fin.cases t.castSucc
    (Fin.cases F.castSucc (Fin.cases R.castSucc (SetLanguage.args2 G.castSucc S.castSucc))))
  have hd : Derives Δ (data w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m) v) :=
    .conjI hh1 (.conjI hb1 (.conjI hf1 hB))
  have hc : Derives Δ (compiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 6 _ v
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsCompiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsCompiled_rename w a f A j n Fin.castSucc).symm ho

private theorem from_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f A j n z t F R : Fin m) (h : Inputs Γ w a f A n)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z t)) (hb : Derives Γ (boundData w a f A F R)) :
    Derives Γ (existsCompiled w a f A j n) := by
  let B := freeBody w j t f A
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _
    (free_exists hZ w j t f A h.hw (target_contexts hZ h) (.conjR (.conjR hh)))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh2 := of_eq (SyntaxMixedImageHead.head_rename w A f z t (old 2)) (HornBinderRules.under_body 2 hh B)
  have hb2 := of_eq (boundData_rename w a f A F R (old 2)) (HornBinderRules.under_body 2 hb B)
  have ho := from_tables (HornBinderRules.zf_body 2 hZ B)
    (old 2 w) (old 2 a) (old 2 f) (old 2 A) (old 2 j) (old 2 n) (old 2 z) (old 2 t)
    (old 2 F) (old 2 R) (slot 2 0) (slot 2 1) (underInputs2 h B) hh2 hb2 hB
  exact of_eq (existsCompiled_rename w a f A j n (old 2)).symm ho

private theorem from_head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f A j n z t : Fin m) (h : Inputs Γ w a f A n)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z t)) : Derives Γ (existsCompiled w a f A j n) := by
  let B := boundBody w a f A
  let Δ := Context.add B (raisedContext 2 Γ)
  have ha := Derives.conjL (.conjR (FormulaCodeProperties.guards w n a f h.hn))
  apply HornBinderRules.eliminate_many 2 B _ (bound_exists hZ w a f A h.hw (target_contexts hZ h) ha h.hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh2 := of_eq (SyntaxMixedImageHead.head_rename w A f z t (old 2)) (HornBinderRules.under_body 2 hh B)
  have ho := from_bound (HornBinderRules.zf_body 2 hZ B) (old 2 w) (old 2 a) (old 2 f) (old 2 A)
    (old 2 j) (old 2 n) (old 2 z) (old 2 t) (slot 2 0) (slot 2 1) (underInputs2 h B) hh2 hB
  exact of_eq (existsCompiled_rename w a f A j n (old 2)).symm ho

/-- Total on all internal formula codes/scopes, including nonstandard ones.
No output, head, table, code list, or valid substitution execution is supplied. -/
theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f A j n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (successor A a))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a f)) : Derives Γ (existsCompiled w a f A j n) := by
  let B := SyntaxMixedImageHead.head (old 2 w) (old 2 A) (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add B (raisedContext 2 Γ)
  have hc := Derives.conjR (FormulaCodeProperties.guards w n a f hn)
  have he : Derives Γ (existsMany 2 B) := SyntaxMixedImageHead.exists_head hZ w a A f hw (.conjL hc) (.conjR hc) hs
  apply HornBinderRules.eliminate_many 2 B _ he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := from_head (HornBinderRules.zf_body 2 hZ B) (old 2 w) (old 2 a) (old 2 f) (old 2 A)
    (old 2 j) (old 2 n) (slot 2 0) (slot 2 1) (underInputs2 ⟨hw,hs,hn⟩ B) hB
  exact of_eq (existsCompiled_rename w a f A j n (old 2)).symm ho

theorem compiled_type {m} {Γ : Context m} (w a f A j n q : Fin m) (h : Derives Γ (compiled w a f A j n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q A f) := by
  let B := body w a f A j n q
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w q A f (old 6)).symm
    (SyntaxMixedFormulaJudgment.target_type (old 6 w) (slot 6 3) (slot 6 5) (old 6 a) (old 6 f)
      (old 6 A) (old 6 f) (old 6 n) (old 6 q) (.conjR (.conjR (.conjR hB))))


private theorem mapped_term_subst {m} {Γ : Context m} (w j t f A G u : Fin m)
    (he : Derives Γ (.equal t u)) (h : Derives Γ (mapped w j t f A G)) :
    Derives Γ (mapped w j u f A G) := by
  let P := mapped w.castSucc j.castSucc (Fin.last m) f.castSucc A.castSucc G.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem substituted_lists {m} {Γ : Context m} (w R S a f A n q U V : Fin m)
    (hR : Derives Γ (.equal R U)) (hS : Derives Γ (.equal S V))
    (h : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f A f n q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w U V a f A f n q) := by
  let P := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (Fin.last m) S.castSucc a.castSucc f.castSucc A.castSucc f.castSucc n.castSucc q.castSucc
  have h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w U S a f A f n q) :=
    of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P hR (of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc U.castSucc (Fin.last m) a.castSucc f.castSucc A.castSucc f.castSucc n.castSucc q.castSucc
  exact of_eq (by simp only [Q, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst Q hS (of_eq (by simp only [Q, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))

private theorem data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f A j n q v : Fin m) (xs ys : Fin 6 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (data w a f A j n q xs)) (hy : Derives Γ (data w a f A j n v ys)) :
    Derives Γ (.equal q v) := by
  have hHx := Derives.conjL hx
  have hHy := Derives.conjL hy
  have hz := OmegaUniversal.empty_unique (xs 0) (ys 0) (ZFContext.arithmetic hZ).base.extensionality (.conjL hHx) (.conjL hHy)
  have hc := AbstractVariableIndex.code_index_subst true w (xs 0) (ys 0) (xs 1) hz (.conjL (.conjR hHx))
  have ht := SyntaxVariables.unique hZ true w (ys 0) (xs 1) (ys 1) hw hc (.conjL (.conjR hHy))
  have hBx := Derives.conjL (.conjR hx)
  have hBy := Derives.conjL (.conjR hy)
  have hF := SyntaxVariableTableUnique.shifted_unique hZ true w a A f (xs 2) (ys 2) (.conjL hBx) (.conjL hBy)
  have hRx := SyntaxMixedImageCodeUnique.subst_graph w (xs 2) a A f (xs 3) (ys 2) hF (.conjR hBx)
  have hR := SyntaxMixedImageCodeUnique.unique_code hZ w (ys 2) a A f (xs 3) (ys 3) hw hRx (.conjR hBy)
  have hGx := Derives.conjL (.conjR (.conjR hx))
  have hGy := Derives.conjL (.conjR (.conjR hy))
  have hm := mapped_term_subst w j (xs 1) f A (xs 4) (ys 1) ht (.conjL hGx)
  have hG := mapped_unique hZ w j (ys 1) f A (xs 4) (ys 4) hm (.conjL hGy)
  have hSx := SyntaxMixedImageCodeUnique.subst_graph w (xs 4) f A f (xs 5) (ys 4) hG (.conjR hGx)
  have hS := SyntaxMixedImageCodeUnique.unique_code hZ w (ys 4) f A f (xs 5) (ys 5) hw hSx (.conjR hGy)
  have hQx := substituted_lists w (xs 3) (xs 5) a f A n q (ys 3) (ys 5) hR hS (.conjR (.conjR (.conjR hx)))
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (ys 3) (ys 5) a f A f n q v hw hQx (.conjR (.conjR (.conjR hy)))

/-- Outputs agree even when all six internal execution witnesses differ. -/
theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f A j n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled w a f A j n q))
    (hv : Derives Γ (compiled w a f A j n v)) : Derives Γ (.equal q v) := by
  let B := body w a f A j n q
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv1 := of_eq (compiled_rename w a f A j n v (old 6)) (HornBinderRules.under_body 6 hv B)
  let C := body (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 n) (old 6 v)
  let Ξ := Context.add C (raisedContext 6 Δ)
  apply HornBinderRules.eliminate_many 6 C _ hv1
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 6 (old 6 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 6 (HornBinderRules.under_body 6 hw B) C)
  have hx2 : Derives Ξ (data (old 6 (old 6 w)) (old 6 (old 6 a)) (old 6 (old 6 f))
      (old 6 (old 6 A)) (old 6 (old 6 j)) (old 6 (old 6 n)) (old 6 (old 6 q)) (fun i => old 6 (slot 6 i))) :=
    of_eq (by simp only [B, body, data_rename]) (HornBinderRules.under_body 6 hB C)
  exact data_unique (HornBinderRules.zf_body 6 (HornBinderRules.zf_body 6 hZ B) C)
    (old 6 (old 6 w)) (old 6 (old 6 a)) (old 6 (old 6 f)) (old 6 (old 6 A))
    (old 6 (old 6 j)) (old 6 (old 6 n)) (old 6 (old 6 q)) (old 6 (old 6 v))
    (fun i => old 6 (slot 6 i)) (slot 6) hw2 hx2 hC

def uniqueOutput {m} (w a f A j n q : Fin m) : Formula m := .all
  ((compiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m)).imp
    (.equal (Fin.last m) q.castSucc))

private theorem uniqueOutput_rename {m l} (w a f A j n q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput w a f A j n q).rename r = uniqueOutput (r w) (r a) (r f) (r A) (r j) (r n) (r q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f A j n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled w a f A j n q)) :
    Derives Γ (uniqueOutput w a f A j n q) := by
  apply Derives.allI
  apply Derives.impI
  let B := compiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ B) w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc
    (Fin.last m) q.castSucc (of_eq (omega_rename w Fin.castSucc) (under hw B))
    (.hyp (Or.inl rfl)) (of_eq (compiled_rename w a f A j n q Fin.castSucc) (under hq B))

def fiber {m} (w a f A j n : Fin m) : Formula m := .ex
  ((compiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m)).conj
    ((FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) A.castSucc f.castSucc).conj
      (uniqueOutput w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m))))

private theorem fiber_rename {m l} (w a f A j n : Fin m) (r : Fin m → Fin l) :
    (fiber w a f A j n).rename r = fiber (r w) (r a) (r f) (r A) (r j) (r n) := by
  simp only [fiber, Formula.rename, compiled_rename, FormulaCodeSyntax.formulaCode_rename,
    uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f A j n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (successor A a))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a f)) : Derives Γ (fiber w a f A j n) := by
  let B := compiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (total hZ w a f A j n hw hs hn)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht := compiled_type w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m) hB
  have hu := unique_output (ZFContext.under hZ B) w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc (Fin.last m) hw1 hB
  have ho : Derives Δ (fiber w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, compiled_rename,
      FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI hB (.conjI ht hu))
  exact of_eq (fiber_rename w a f A j n Fin.castSucc).symm ho

def sentence {m} (w a f A j n : Fin m) : Source.Sentence :=
  ((omega w).imp ((successor A a).imp ((FormulaCodeSyntax.formulaCode w n a f).imp
    (fiber w a f A j n)))).close

def uniqueSentence {m} (w a f A j n q v : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled w a f A j n q).imp ((compiled w a f A j n v).imp (.equal q v)))).close

theorem kernel_certificate {m} (w a f A j n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a f A j n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    w a f A j n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem unique_kernel_certificate {m} (w a f A j n q v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence w a f A j n q v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    w a f A j n q v (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))


/- Reuse ports for the existential child environment; the old private
Replacement proofs and every old public proof body remain unchanged. -/
theorem selected_map_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t f A : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxTermSyntax.contexts w A f))
    (ht : Derives Γ (SyntaxTermSyntax.term w A f t)) :
    Derives Γ (.ex (mapped w.castSucc j.castSucc t.castSucc f.castSucc A.castSucc (Fin.last m))) :=
  exists_map hZ w j t f A hw hc ht

theorem selected_map_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w j t f A g h : Fin m)
    (hg : Derives Γ (mapped w j t f A g)) (hh : Derives Γ (mapped w j t f A h)) : Derives Γ (.equal g h) :=
  mapped_unique hZ w j t f A g h hg hh

end PPAC.Migration.ForcingConditionRebind
