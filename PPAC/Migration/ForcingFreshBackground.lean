import PPAC.Migration.ForcingScopeIdentity
import PPAC.Migration.ForcingProofUniversal
import PPAC.Migration.Internal.SyntaxCodedMixedTermFields
import PPAC.Migration.Internal.IndexTermImageCodeFields

/-! Original fresh FIRST-free-slot weak/abstract cancellation. All runtime
scope, index, term and formula values stay internal. Use existing exact
fields and the completed full formula diagram, not a new recursion/induction. -/
namespace PPAC.Migration.ForcingFreshBackground
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxCodedMixedTermSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def freeInput {m} (w z b A B I J R S K H i x u t : Fin m) : Formula m :=
  (omega w).conj ((SyntaxFreeShiftSyntax.shiftCode w b B J).conj
    ((IndexTermImageCodeSyntax.environment w I J R S z b z B).conj
      ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w z b A B K H).conj
        ((Formula.mem i b).conj ((SyntaxVariableSyntax.code false w i x).conj
          ((substituted w R S z b z B x u).conj (substituted w K H z B A b u t)))))))

private theorem freeInput_rename {m l} (w z b A B I J R S K H i x u t : Fin m) (ρ : Fin m → Fin l) :
    (freeInput w z b A B I J R S K H i x u t).rename ρ =
      freeInput (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ I) (ρ J) (ρ R) (ρ S) (ρ K) (ρ H) (ρ i) (ρ x) (ρ u) (ρ t) := by
  simp only [freeInput, Formula.rename, omega_rename, SyntaxFreeShiftSyntax.shiftCode_rename,
    IndexTermImageCodeSyntax.environment_rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename,
    SyntaxVariableSyntax.code_rename, substituted_rename]

/-- OLD free i -> fresh-free successor j -> OLD free i, in the ACTUAL
converted shift and original abstract-prefix fields. Both graph and index
witnesses are generated/eliminated inside the object derivation. -/
private theorem free_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B I J R S K H i x u t : Fin m)
    (hi : Derives Γ (freeInput w z b A B I J R S K H i x u t)) : Derives Γ (.equal x t) := by
  let E0 := (SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) b.castSucc B.castSucc J.castSucc).conj
    (SyntaxFreeShiftSyntax.shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) (.conjL (.conjR hi))
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have h1 := of_eq (freeInput_rename w z b A B I J R S K H i x u t Fin.castSucc) (under hi E0)
  have hZ1 := ZFContext.under hZ E0
  have hj := InsertExistence.exists_insert i.castSucc i.castSucc
    (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union
  let E1 := successor (Fin.last (m+1)) (old 2 i)
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) hj
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have h2 := of_eq (freeInput_rename w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc I.castSucc J.castSucc
    R.castSucc S.castSucc K.castSucc H.castSucc i.castSucc x.castSucc u.castSucc t.castSucc Fin.castSucc) (under h1 E1)
  have hZ2 := ZFContext.under hZ1 E1
  have hw2 := Derives.conjL h2
  have hEnv := Derives.conjL (.conjR (.conjR h2))
  have hAbs := Derives.conjL (.conjR (.conjR (.conjR h2)))
  have hIndex := Derives.conjL (.conjR (.conjR (.conjR (.conjR h2))))
  have hX := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h2)))))
  have h0 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h2))))))
  have h1q := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h2))))))
  have hGraph : Derives Δ2 ((SyntaxMapCodeSyntax.encoded (old 2 w) (Fin.last m).castSucc (old 2 b) (old 2 B) (old 2 J)).conj
      (SyntaxFreeShiftSyntax.shiftMap (old 2 w) (old 2 b) (old 2 B) (Fin.last m).castSucc)) :=
    of_eq (by simp only [E0, Formula.raise, Formula.rename, SyntaxMapCodeSyntax.encoded_rename,
      SyntaxFreeShiftSyntax.shiftMap_rename]; rfl) (under hE0 E1)
  have hedge := Derives.impE (.conjR (SyntaxFreeShiftGraph.edge_iff (old 2 b) (Fin.last m).castSucc
    (old 2 i) (Fin.last (m+1)) (SyntaxFreeShiftGraph.to_graph _ _ _ _ (.conjR hGraph)))) (.conjI hIndex hE1)
  have hField := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ2 false
    (old 2 w) (old 2 R) (old 2 S) (old 2 z) (old 2 b) (old 2 z) (old 2 B) (old 2 x) (old 2 u) (old 2 i)
    hw2 (IndexTermImageCodeTyping.environment_lists _ _ _ _ _ _ _ _ _ hEnv) hX)) h0
  have hU := Derives.impE (.conjL (IndexTermImageCodeFields.at_edge hZ2 false (old 2 w) (old 2 J) (old 2 S)
    (old 2 b) (old 2 z) (old 2 B) (Fin.last m).castSucc (old 2 i) (Fin.last (m+1)) (old 2 u)
    (.conjR hEnv) (.conjL hGraph) hedge)) hField
  have hFieldAbs := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ2 false
    (old 2 w) (old 2 K) (old 2 H) (old 2 z) (old 2 B) (old 2 A) (old 2 b) (old 2 u) (old 2 t) (Fin.last (m+1))
    hw2 (SyntaxTopCodedEnvironmentTyping.abstract_lists _ _ _ _ _ _ _ hAbs) hU)) h1q
  have hT := Derives.impE (.conjL (SyntaxTopCodedEnvironmentFields.abstract_free hZ2
    (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 K) (old 2 H)
    (Fin.last (m+1)) (old 2 i) (old 2 t) hw2 hAbs hIndex hE1)) hFieldAbs
  exact SyntaxVariables.unique hZ2 false (old 2 w) (old 2 i) (old 2 x) (old 2 t) hw2 hX hT

theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B I J R S K H x u t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hShift : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hEnv : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S z b z B))
    (hAbs : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w z b A B K H))
    (h0 : Derives Γ (substituted w R S z b z B x u))
    (h1 : Derives Γ (substituted w K H z B A b u t)) : Derives Γ (.equal x t) := by
  apply OriginalTermScopeElimination.eliminate w z b x (.equal x t)
    (SyntaxCodedMixedTermTyping.source_type w R S z b z B x u h0)
  intro bound
  cases bound
  · let E := SyntaxTermSyntax.branchWitness false w b x
    let Δ := Context.add E (Context.image Formula.raise Γ)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hp := free_at (ZFContext.under hZ E) w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc I.castSucc J.castSucc
      R.castSucc S.castSucc K.castSucc H.castSucc (Fin.last m) x.castSucc u.castSucc t.castSucc
      (.conjI (of_eq (omega_rename w Fin.castSucc) (under hw E)) (.conjI
        (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J Fin.castSucc) (under hShift E)) (.conjI
          (of_eq (IndexTermImageCodeSyntax.environment_rename w I J R S z b z B Fin.castSucc) (under hEnv E)) (.conjI
            (of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w z b A B K H Fin.castSucc) (under hAbs E)) (.conjI
              (.conjL hE) (.conjI (.conjR hE) (.conjI
                (of_eq (substituted_rename w R S z b z B x u Fin.castSucc) (under h0 E))
                (of_eq (substituted_rename w K H z B A b u t Fin.castSucc) (under h1 E)))))))))
    exact hp
  · let E := SyntaxTermSyntax.branchWitness true w z x
    let Δ := Context.add E (Context.image Formula.raise Γ)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    exact .botE (.impE (OmegaSyntax.empty_at z.castSucc (Fin.last m)
      (of_eq (empty_rename z Fin.castSucc) (under hz E))) (.conjL hE))

private def four {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

/-- Reuse the SAME promoted free identity and SAME converted free table for
both the direct edge and the final identity edge. No extra free table choice. -/
def frame {m} (w z b A B G I J R S K H I2 R2 : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxFreeShiftSyntax.shiftCode w b B J).conj
    ((IndexTermImageCodeSyntax.environment w I J R S z b z B).conj
      ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w z b A B K H).conj
        ((SyntaxIdentityMapSyntax.identityCode w A I2).conj
          ((IndexTermImageCodeSyntax.converted true w I2 R2 A A b).conj
            (ForcingScopeIdentity.promotedData w z b A G v)))))))

theorem frame_rename {m l} (w z b A B G I J R S K H I2 R2 : Fin m) (v : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (frame w z b A B G I J R S K H I2 R2 v).rename ρ =
      frame (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ G) (ρ I) (ρ J) (ρ R) (ρ S) (ρ K) (ρ H) (ρ I2) (ρ R2) (fun i => ρ (v i)) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, SyntaxFreeShiftSyntax.shiftCode_rename,
    IndexTermImageCodeSyntax.environment_rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename,
    SyntaxIdentityMapSyntax.identityCode_rename, IndexTermImageCodeSyntax.converted_rename, ForcingScopeIdentity.promotedData_rename]

private theorem identity_env {m} {Γ : Context m} (w z b A G I2 R2 : Fin m) (v : Fin 4 → Fin m)
    (hBound : Derives Γ (IndexTermImageCodeSyntax.converted true w I2 R2 A A b))
    (hProm : Derives Γ (ForcingScopeIdentity.promotedData w z b A G v)) :
    Derives Γ (IndexTermImageCodeSyntax.environment w I2 (v 1) R2 (v 3) A b A b) :=
  .conjI hBound (.conjR (.conjL (.conjR (.conjR hProm))))

theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B G I J R S K H I2 R2 : Fin m) (v : Fin 4 → Fin m)
    (hi : Derives Γ (frame w z b A B G I J R S K H I2 R2 v)) :
    Derives Γ (ForcingTermDiagram.diagram w (four z z A A) (four b B b b)
      (four R K R2 (v 2)) (four S H (v 3) (v 3))) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := (ForcingTermDiagram.step (old 5 w) (four (old 5 z) (old 5 z) (old 5 A) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 b) (old 5 b))
      (four (old 5 R) (old 5 K) (old 5 R2) (old 5 (v 2)))
      (four (old 5 S) (old 5 H) (old 5 (v 3)) (old 5 (v 3))) 0 (slot 5 0) (slot 5 1)).conj
    ((ForcingTermDiagram.step (old 5 w) (four (old 5 z) (old 5 z) (old 5 A) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 b) (old 5 b))
      (four (old 5 R) (old 5 K) (old 5 R2) (old 5 (v 2)))
      (four (old 5 S) (old 5 H) (old 5 (v 3)) (old 5 (v 3))) 1 (slot 5 1) (slot 5 2)).conj
      ((ForcingTermDiagram.step (old 5 w) (four (old 5 z) (old 5 z) (old 5 A) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 b) (old 5 b))
      (four (old 5 R) (old 5 K) (old 5 R2) (old 5 (v 2)))
      (four (old 5 S) (old 5 H) (old 5 (v 3)) (old 5 (v 3))) 2 (slot 5 2) (slot 5 3)).conj
        (ForcingTermDiagram.step (old 5 w) (four (old 5 z) (old 5 z) (old 5 A) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 b) (old 5 b))
      (four (old 5 R) (old 5 K) (old 5 R2) (old 5 (v 2)))
      (four (old 5 S) (old 5 H) (old 5 (v 3)) (old 5 (v 3))) 3 (slot 5 0) (slot 5 4))))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h5 := of_eq (frame_rename w z b A B G I J R S K H I2 R2 v (old 5)) (HornBinderRules.under_body 5 hi E)
  have hZ5 := HornBinderRules.zf_body 5 hZ E
  have hw := Derives.conjL h5
  have hz := Derives.conjL (.conjR h5)
  have hShift := Derives.conjL (.conjR (.conjR h5))
  have hEnv := Derives.conjL (.conjR (.conjR (.conjR h5)))
  have hAbs := Derives.conjL (.conjR (.conjR (.conjR (.conjR h5))))
  have hIA := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h5)))))
  have hCB := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h5))))))
  have hProm := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h5))))))
  have hXT := term hZ5 (old 5 w) (old 5 z) (old 5 b) (old 5 A) (old 5 B) (old 5 I) (old 5 J)
    (old 5 R) (old 5 S) (old 5 K) (old 5 H) (slot 5 0) (slot 5 1) (slot 5 2)
    hw hz hShift hEnv hAbs (.conjL hE) (.conjL (.conjR hE))
  have hTY := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 A) (old 5 b)
    (old 5 I2) (old 5 (v 1)) (old 5 R2) (old 5 (v 3)) (slot 5 2) (slot 5 3)
    hw hIA (.conjL (.conjR hProm)) (identity_env _ _ _ _ _ _ _ _ hCB hProm)
    (.conjL (.conjR (.conjR hE)))
  have hXO := ForcingScopeIdentity.promoted_term_identity hZ5 (old 5 w) (old 5 z) (old 5 b) (old 5 A) (old 5 G)
    (slot 5 0) (slot 5 4) (fun i => old 5 (v i)) hw hz hProm (.conjR (.conjR (.conjR hE)))
  exact eq_trans (eq_symm hTY) (eq_trans (eq_symm hXT) hXO)

/-- The full INTERNAL formula induction is REUSED, not repeated. Literal
same G direct output comes from the completed promoted-code consumer. -/
theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B G W Q I J R S K H I2 R2 : Fin m) (v : Fin 4 → Fin m)
    (hf : Derives Γ (frame w z b A B G I J R S K H I2 R2 v))
    (hWeak : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S z b z B G W))
    (hAbs : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W Q)) : Derives Γ (.equal Q G) := by
  have hw := Derives.conjL hf
  have hKM := Derives.conjL (.conjR (.conjR (.conjR (.conjR hf))))
  have hIA := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))
  have hCB := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf))))))
  have hProm := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf))))))
  have hEnv2 := identity_env w z b A G I2 R2 v hCB hProm
  have hJ := Derives.conjL (.conjR hProm)
  have htQ := SyntaxTopFormulaTyping.abstract_target_type w z b A B W Q hAbs
  have hSelf := SyntaxIdentityInduction.reflexive hZ w I2 (v 1) A b Q hw hIA hJ htQ
  have hId := IndexFormulaRenameInduction.forward hZ w I2 (v 1) R2 (v 3) A b A b Q Q hw hEnv2 hSelf
  have hAQ := Derives.impE (.conjL (SyntaxTopFormulaCodes.abstract_at_codes hZ w z b A B W Q K H hw hKM)) hAbs
  have hDirect := Derives.conjL (.conjR (.conjR (.conjR hProm)))
  exact ForcingFormulaInduction.cancel hZ w (four z z A A) (four b B b b)
    (four R K R2 (v 2)) (four S H (v 3) (v 3)) G W Q Q G hw
    (term_diagram hZ w z b A B G I J R S K H I2 R2 v hf) hWeak hAQ hId hDirect

/-- Only actual original free-head weakening, with original scope guards.
No chosen operation tables, abstract output or expected equality. -/
def input {m} (w z b A B G W : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A z).conj (SyntaxWeakenFreeSyntax.weakened w z b B G W)))

theorem input_rename {m l} (w z b A B G W : Fin m) (ρ : Fin m → Fin l) :
    (input w z b A B G W).rename ρ = input (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ G) (ρ W) := by
  simp only [input, Formula.rename, omega_rename, empty_rename, successor_rename, SyntaxWeakenFreeSyntax.weakened_rename]

private def opening {m} (w z b A B G W I J R S K H : Fin m) : Formula m :=
  (input w z b A B G W).conj ((SyntaxFreeShiftSyntax.shiftCode w b B J).conj
    ((IndexTermImageCodeSyntax.environment w I J R S z b z B).conj
      ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w z b A B K H).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w R S z b z B G W))))

private theorem opening_rename {m l} (w z b A B G W I J R S K H : Fin m) (ρ : Fin m → Fin l) :
    (opening w z b A B G W I J R S K H).rename ρ =
      opening (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ G) (ρ W) (ρ I) (ρ J) (ρ R) (ρ S) (ρ K) (ρ H) := by
  simp only [opening, Formula.rename, input_rename, SyntaxFreeShiftSyntax.shiftCode_rename,
    IndexTermImageCodeSyntax.environment_rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename,
    SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private structure Opened {m} (Γ : Context m) (w z b A B G W I J R S K H : Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  ho : Derives Γ (opening w z b A B G W I J R S K H)

private theorem Opened.in_body {m l} {Γ : Context m} {w z b A B G W I J R S K H : Fin m}
    (h : Opened Γ w z b A B G W I J R S K H) (E : Formula (m+l)) :
    Opened (Context.add E (raisedContext l Γ)) (old l w) (old l z) (old l b) (old l A) (old l B) (old l G) (old l W)
      (old l I) (old l J) (old l R) (old l S) (old l K) (old l H) :=
  ⟨HornBinderRules.zf_body l h.zf E, of_eq (opening_rename w z b A B G W I J R S K H (old l)) (HornBinderRules.under_body l h.ho E)⟩

private theorem Opened.source {m} {Γ : Context m} {w z b A B G W I J R S K H : Fin m}
    (h : Opened Γ w z b A B G W I J R S K H) : Derives Γ (FormulaCodeSyntax.formulaCode w G z b) :=
  .conjL (SyntaxWeakenFreeOutput.input_of_weakened h.zf w z b B G W
    (.conjL (.conjL h.ho)) (.conjR (.conjR (.conjR (.conjL h.ho)))))

private theorem at_abstract {m} {Γ : Context m} (w z b A B G W I J R S K H I2 R2 Q : Fin m)
    (v : Fin 4 → Fin m) (h : Opened Γ w z b A B G W I J R S K H)
    (hp : Derives Γ (ForcingScopeIdentity.promotedData w z b A G v))
    (hI2 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I2))
    (hR2 : Derives Γ (IndexTermImageCodeSyntax.converted true w I2 R2 A A b))
    (hQ : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W Q)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  have hi := Derives.conjL h.ho
  have hf : Derives Γ (frame w z b A B G I J R S K H I2 R2 v) := .conjI (.conjL hi) (.conjI
    (.conjL (.conjR hi)) (.conjI (.conjL (.conjR h.ho)) (.conjI (.conjL (.conjR (.conjR h.ho))) (.conjI
      (.conjL (.conjR (.conjR (.conjR h.ho)))) (.conjI hI2 (.conjI hR2 hp))))))
  have he := formula h.zf w z b A B G W Q I J R S K H I2 R2 v hf
    (.conjR (.conjR (.conjR (.conjR h.ho)))) hQ
  let P := SyntaxTopFormulaSyntax.abstracted w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc W.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxTopFormulaSyntax.abstracted_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxTopFormulaSyntax.abstracted_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hQ))

private theorem with_image {m} {Γ : Context m} (w z b A B G W I J R S K H I2 R2 : Fin m)
    (v : Fin 4 → Fin m) (h : Opened Γ w z b A B G W I J R S K H)
    (hp : Derives Γ (ForcingScopeIdentity.promotedData w z b A G v))
    (hI2 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I2))
    (hR2 : Derives Γ (IndexTermImageCodeSyntax.converted true w I2 R2 A A b)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  have hi := Derives.conjL h.ho
  have hw := Derives.conjL hi
  have hKM := Derives.conjL (.conjR (.conjR (.conjR h.ho)))
  have htW := SyntaxWeakenFreeOutput.target_type w z b B G W (.conjR (.conjR (.conjR hi)))
  have he := SyntaxTopFormulaExistence.abstract_at_codes_exists h.zf w z b A B W K H hw hKM htW
  let E := SyntaxTopFormulaSyntax.abstracted w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc W.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hh := at_abstract w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc G.castSucc W.castSucc
    I.castSucc J.castSucc R.castSucc S.castSucc K.castSucc H.castSucc I2.castSucc R2.castSucc (Fin.last m)
    (fun i => (v i).castSucc) (h.in_body E)
    (of_eq (ForcingScopeIdentity.promotedData_rename w z b A G v Fin.castSucc) (under hp E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w A I2 Fin.castSucc) (under hI2 E))
    (of_eq (IndexTermImageCodeSyntax.converted_rename true w I2 R2 A A b Fin.castSucc) (under hR2 E)) hE
  exact of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G Fin.castSucc).symm hh

private theorem with_identity {m} {Γ : Context m} (w z b A B G W I J R S K H I2 : Fin m)
    (v : Fin 4 → Fin m) (h : Opened Γ w z b A B G W I J R S K H)
    (hp : Derives Γ (ForcingScopeIdentity.promotedData w z b A G v))
    (hI2 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I2)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  have hi := Derives.conjL h.ho
  have hw := Derives.conjL hi
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w G A b
    (.conjR (.conjR (.conjR (.conjR hp)))))
  have he := IndexTermImageCodeExistence.exists_code h.zf true w I2 A A b hw
    (.conjI hCtx (SyntaxIdentityCode.map_code w A I2 hI2))
  let E := IndexTermImageCodeSyntax.converted true w.castSucc I2.castSucc (Fin.last m) A.castSucc A.castSucc b.castSucc
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hh := with_image w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc G.castSucc W.castSucc
    I.castSucc J.castSucc R.castSucc S.castSucc K.castSucc H.castSucc I2.castSucc (Fin.last m)
    (fun i => (v i).castSucc) (h.in_body E)
    (of_eq (ForcingScopeIdentity.promotedData_rename w z b A G v Fin.castSucc) (under hp E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w A I2 Fin.castSucc) (under hI2 E)) hE
  exact of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G Fin.castSucc).symm hh

private theorem with_promotion {m} {Γ : Context m} (w z b A B G W I J R S K H : Fin m)
    (v : Fin 4 → Fin m) (h : Opened Γ w z b A B G W I J R S K H)
    (hp : Derives Γ (ForcingScopeIdentity.promotedData w z b A G v)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  have hw := Derives.conjL (.conjL h.ho)
  have hA := Derives.conjL (.conjR (FormulaCodeProperties.guards w G A b
    (.conjR (.conjR (.conjR (.conjR hp))))))
  have he := SyntaxIdentityCode.exists_code h.zf w A hw hA
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc A.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hh := with_identity w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc G.castSucc W.castSucc
    I.castSucc J.castSucc R.castSucc S.castSucc K.castSucc H.castSucc (Fin.last m)
    (fun i => (v i).castSucc) (h.in_body E)
    (of_eq (ForcingScopeIdentity.promotedData_rename w z b A G v Fin.castSucc) (under hp E)) hE
  exact of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G Fin.castSucc).symm hh

private theorem after_opening {m} {Γ : Context m} (w z b A B G W I J R S K H : Fin m)
    (h : Opened Γ w z b A B G W I J R S K H) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  have hi := Derives.conjL h.ho
  have he := ForcingScopeIdentity.promote h.zf w z b A G (.conjL hi) (.conjL (.conjR hi))
    (.conjL (.conjR (.conjR hi))) h.source
  let E := ForcingScopeIdentity.promotedData (old 4 w) (old 4 z) (old 4 b) (old 4 A) (old 4 G) (slot 4)
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hh := with_promotion (old 4 w) (old 4 z) (old 4 b) (old 4 A) (old 4 B) (old 4 G) (old 4 W)
    (old 4 I) (old 4 J) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (slot 4) (h.in_body E) hE
  exact of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G (old 4)).symm hh

private structure Raw {m} (Γ : Context m) (w z b A B G W : Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hi : Derives Γ (input w z b A B G W)

private theorem Raw.in_body {m l} {Γ : Context m} {w z b A B G W : Fin m}
    (h : Raw Γ w z b A B G W) (E : Formula (m+l)) :
    Raw (Context.add E (raisedContext l Γ)) (old l w) (old l z) (old l b) (old l A) (old l B) (old l G) (old l W) :=
  ⟨HornBinderRules.zf_body l h.zf E, of_eq (input_rename w z b A B G W (old l)) (HornBinderRules.under_body l h.hi E)⟩

private theorem after_environment {m} {Γ : Context m} (w z b A B G W I J R S : Fin m)
    (h : Raw Γ w z b A B G W)
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hEnv : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S z b z B))
    (hMixed : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S z b z B G W)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  have hw := Derives.conjL h.hi
  have hWeak := Derives.conjR (.conjR (.conjR h.hi))
  have hInp := SyntaxWeakenFreeOutput.input_of_weakened h.zf w z b B G W hw hWeak
  have hAbsInput : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z b A B) :=
    .conjI (.conjR (FormulaCodeProperties.guards w G z b (.conjL hInp)))
      (.conjI (.conjL (.conjR (.conjR h.hi))) (.conjR hInp))
  have he := SyntaxTopCodedEnvironmentExistence.abstract_exists h.zf w z b A B hw hAbsInput
  let E := SyntaxTopCodedEnvironmentSyntax.abstractCoded (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (slot 2 0) (slot 2 1)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hRaw := h.in_body E
  have hJ2 := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J (old 2)) (HornBinderRules.under_body 2 hJ E)
  have hEnv2 := of_eq (IndexTermImageCodeSyntax.environment_rename w I J R S z b z B (old 2)) (HornBinderRules.under_body 2 hEnv E)
  have hMix2 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S z b z B G W (old 2)) (HornBinderRules.under_body 2 hMixed E)
  have hh := after_opening (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 G) (old 2 W)
    (old 2 I) (old 2 J) (old 2 R) (old 2 S) (slot 2 0) (slot 2 1)
    ⟨hRaw.zf, .conjI hRaw.hi (.conjI hJ2 (.conjI hEnv2 (.conjI hE hMix2)))⟩
  exact of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G (old 2)).symm hh

private def weakData {m} (w z b B G W I J : Fin m) : Formula m :=
  (SyntaxIdentityMapSyntax.identityCode w z I).conj ((SyntaxFreeShiftSyntax.shiftCode w b B J).conj
    (SyntaxRenameJudgmentSyntax.renamed w I J z b z B G W))

private theorem weakData_rename {m l} (w z b B G W I J : Fin m) (ρ : Fin m → Fin l) :
    (weakData w z b B G W I J).rename ρ =
      weakData (ρ w) (ρ z) (ρ b) (ρ B) (ρ G) (ρ W) (ρ I) (ρ J) := by
  simp only [weakData, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename,
    SyntaxFreeShiftSyntax.shiftCode_rename, SyntaxRenameJudgmentSyntax.renamed_rename]

private theorem after_weak {m} {Γ : Context m} (w z b A B G W I J : Fin m)
    (h : Raw Γ w z b A B G W) (hv : Derives Γ (weakData w z b B G W I J)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  have hw := Derives.conjL h.hi
  have he := IndexTermImageEnvironment.exists_environment h.zf w I J z b z B hw
    (SyntaxIdentityCode.map_code w z I (.conjL hv))
    (SyntaxFreeShiftCode.map_code w b B J (.conjL (.conjR hv)))
  let E := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 z) (old 2 b) (old 2 z) (old 2 B)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h2 := h.in_body E
  have hv2 := of_eq (weakData_rename w z b B G W I J (old 2)) (HornBinderRules.under_body 2 hv E)
  have hm := IndexFormulaRenameInduction.forward h2.zf (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 z) (old 2 b) (old 2 z) (old 2 B) (old 2 G) (old 2 W) (.conjL h2.hi) hE (.conjR (.conjR hv2))
  have hh := after_environment (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 G) (old 2 W)
    (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) h2 (.conjL (.conjR hv2)) hE hm
  exact of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G (old 2)).symm hh

/-- Original ACTUAL weakening -> original ACTUAL abstraction back to SAME G.
All THIRTEEN operation/code/output witnesses are generated and eliminated.
No frame, chosen tables, abstract output or expected equality premise. -/
theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A B G W : Fin m)
    (hi : Derives Γ (input w z b A B G W)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G) := by
  let E := weakData (old 2 w) (old 2 z) (old 2 b) (old 2 B) (old 2 G) (old 2 W) (slot 2 0) (slot 2 1)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (.conjR (.conjR (.conjR hi)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h2 := (show Raw Γ w z b A B G W from ⟨hZ, hi⟩).in_body E
  have hh := after_weak (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 G) (old 2 W) (slot 2 0) (slot 2 1) h2 hE
  exact of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G (old 2)).symm hh

def sentence {m} (w z b A B G W : Fin m) : Source.Sentence :=
  ((input w z b A B G W).imp (SyntaxTopFormulaSyntax.abstracted w z b A B W G)).close

theorem kernel_certificate {m} (w z b A B G W : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z b A B G W)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w z b A B G W
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have hE : Derives Γ E := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) w z b A B G W hE

/-- Consume the newly proved actual weak/abstract cancellation immediately.
The old Global abstraction answer premise is REMOVED. Only actual original
weakening into the SAME generated canonical Global remains to be matched by
the source freshening consumer. Body/forall proofs are generated as before. -/
theorem generalize_layout {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z))
    (hWeak : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B G (v 3)))
    (h : Derives Γ (ForcingProofUniversal.resultData test w z b A B Extra Pre Tail H v)) :
    Derives Γ (ForcingProofUniversal.guarded test w z b A B G (v 3) (v 4) Tail) := by
  have hG := Derives.conjL (SyntaxWeakenFreeOutput.input_of_weakened hZ w z b B G (v 3) hw hWeak)
  have hAbs := derive hZ w z b A B G (v 3) (.conjI hw (.conjI hz (.conjI hA hWeak)))
  exact ForcingProofUniversal.generalize_layout hZ test w z b A B G Extra Pre Tail H v hw hz hG hAbs h

def guardedInput {m} (test : Formula 1) (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A z).conj
    ((SyntaxWeakenFreeSyntax.weakened w z b B G (v 3)).conj
      (ForcingProofUniversal.resultData test w z b A B Extra Pre Tail H v))))

def guardedSentence {m} (test : Formula 1) (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) : Source.Sentence :=
  ((guardedInput test w z b A B G Extra Pre Tail H v).imp
    (ForcingProofUniversal.guarded test w z b A B G (v 3) (v 4) Tail)).close

theorem guarded_kernel_certificate {m} (test : Formula 1) (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (guardedSentence test w z b A B G Extra Pre Tail H v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := guardedInput test w z b A B G Extra Pre Tail H v
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have hE : Derives Γ E := .hyp (Or.inl rfl)
  exact generalize_layout (ZFContext.add (ZFContext.source_ZF m) E) test w z b A B G Extra Pre Tail H v
    (.conjL hE) (.conjL (.conjR hE)) (.conjL (.conjR (.conjR hE)))
    (.conjL (.conjR (.conjR (.conjR hE)))) (.conjR (.conjR (.conjR (.conjR hE))))

end PPAC.Migration.ForcingFreshBackground
