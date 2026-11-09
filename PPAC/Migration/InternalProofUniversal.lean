import PPAC.Migration.InternalProofQuantifier
import PPAC.Migration.InternalProofBackground
import PPAC.Migration.Internal.LogicalAbstractNode
import PPAC.Migration.Internal.LogicalRule22Head

/-! Original quantified proof steps needed by force_mono / force_of_dense.
Actual native AbstractFreeTop judgments discharge the original rule21 queries.
All scopes, formulas, abstractions, logical certificates and proof codes are
internal, including nonstandard values. Original forall node and original
27-case logical table are reused, with no new checker or proof kernel. -/
namespace PPAC.Migration.InternalProofUniversal
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofConjunction (proved proved_rename)
open YesMetaZFC.Automation
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def five {α} (a b c d e : α) : Fin 5 → α := Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun _ => e))))
private def seven {α} (a b c d e f g : α) : Fin 7 → α := Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e (Fin.cases f (fun _ => g))))))

private theorem imp_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b F H I : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (formulaCode w F z b)) (hH : Derives Γ (formulaCode w H z b))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w F H I)) : Derives Γ (formulaCode w I z b) :=
  .impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b F H I hw hc))
    (.conjI (.conjR (FormulaCodeProperties.guards w F z b hF)) (.conjI hF hH))

private theorem all_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A F U : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w z b))
    (hA : Derives Γ (successor A z)) (hF : Derives Γ (formulaCode w F A b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) : Derives Γ (formulaCode w U z b) :=
  .impE (.conjR (FormulaCodeKnownLogical.forall_iff hZ w z b F U hw hc))
    (.conjI hctx (.impE (.conjR (FormulaCodeBranchSyntax.at_successor hZ w F z b A hA)) hF))

/-- Reuse an ACTUAL member of the original logical table and original row.
The existing logical Node/header producer supplies the complete proof. -/
private theorem original_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (shape : ObjectLogicalAxiom.Shape) (hshape : shape ∈ ObjectLogicalAxiom.shapes)
    (w z b I c row : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hI : Derives Γ (formulaCode w I z b)) (hc : Derives Γ (.mem c w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c I) row))
    (hn : Derives Γ (LogicalOriginalNodeSyntax.node shape w row)) : Derives Γ (proved test w z b I) := by
  have ht : Derives Γ (LogicalOriginalNodeSyntax.table w row) := ProofTreeRootSyntax.disjoin_intro _ _
    (List.mem_map.mpr ⟨shape, hshape, rfl⟩) hn
  have hq : Derives Γ (OriginalLogicalExprQuery.rowQuery 3 0 w (SetLanguage.args3 b c I)) := by
    apply Derives.exI row
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      LogicalTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr ht)
  exact InternalProofTemplates.logical_proof test w z b I c
    (InternalProofOperations.logical hZ test w z b I c hw hz (.conjI hI (.conjI hc hq)))

/-- Original rule21: source free B, target free b; A and B are ACTUAL
successors obtained from the two native abstraction judgments. -/
def distributionData {m} (w z b A B F H G J K X V U L I : Fin m) : Formula m :=
  (SyntaxTopFormulaSyntax.abstracted w z b A B F G).conj
    ((SyntaxTopFormulaSyntax.abstracted w z b A B H J).conj
      ((SyntaxLogicalSyntax.binaryCode 2 w G J K).conj
        ((SyntaxLogicalSyntax.singleCode 9 w K X).conj
          ((SyntaxLogicalSyntax.singleCode 9 w G V).conj
            ((SyntaxLogicalSyntax.singleCode 9 w J U).conj
              ((SyntaxLogicalSyntax.binaryCode 2 w V U L).conj (SyntaxLogicalSyntax.binaryCode 2 w X L I)))))))

theorem distributionData_rename {m l} (w z b A B F H G J K X V U L I : Fin m) (ρ : Fin m → Fin l) :
    (distributionData w z b A B F H G J K X V U L I).rename ρ =
      distributionData (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ F) (ρ H) (ρ G) (ρ J) (ρ K) (ρ X) (ρ V) (ρ U) (ρ L) (ρ I) := by
  simp only [distributionData, Formula.rename, SyntaxTopFormulaSyntax.abstracted_rename,
    SyntaxLogicalSyntax.binaryCode_rename, SyntaxLogicalSyntax.singleCode_rename]

private theorem distribution_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B F H G J K X V U L I c row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (distributionData w z b A B F H G J K X V U L I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 21 w (SyntaxAtomSyntax.two F H) c))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c I) row)) :
    Derives Γ (proved test w z b I) := by
  have hAF := Derives.conjL hd
  have hAH := Derives.conjL (.conjR hd)
  have hK := Derives.conjL (.conjR (.conjR hd))
  have hX := Derives.conjL (.conjR (.conjR (.conjR hd)))
  have hV := Derives.conjL (.conjR (.conjR (.conjR (.conjR hd))))
  have hU := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hd)))))
  have hL := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hd))))))
  have hI := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hd))))))
  have hEnv := SyntaxTopFormulaTyping.abstract_environment w z b A B F G hAF
  have hctx := Derives.conjL hEnv
  have hA := Derives.conjL (.conjR hEnv)
  have hB := Derives.conjR (.conjR hEnv)
  have hFt := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B F G hw hAF
  have hHt := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B H J hw hAH
  have hGt := SyntaxTopFormulaTyping.abstract_target_type w z b A B F G hAF
  have hJt := SyntaxTopFormulaTyping.abstract_target_type w z b A B H J hAH
  have hKt := imp_type hZ w A b G J K hw hGt hJt hK
  have hXt := all_type hZ w z b A K X hw hctx hA hKt hX
  have hVt := all_type hZ w z b A G V hw hctx hA hGt hV
  have hUt := all_type hZ w z b A J U hw hctx hA hJt hU
  have hLt := imp_type hZ w z b V U L hw hVt hUt hL
  have hIt := imp_type hZ w z b X L I hw hXt hLt hI
  let env := five b F H G J
  have hN : Derives Γ (environmentNat 5 w env) := .conjI (.conjR (.conjR (FormulaCodeProperties.guards w G A b hGt)))
    (.conjI (.conjL (FormulaCodeProperties.guards w F z B hFt)) (.conjI (.conjL (FormulaCodeProperties.guards w H z B hHt))
      (.conjI (.conjL (FormulaCodeProperties.guards w G A b hGt)) (.conjI (.conjL (FormulaCodeProperties.guards w J A b hJt)) HornRuleSyntax.truth_proved))))
  have hValues : Derives Γ (LogicalRule21Head.atValues w row env (seven c K X V U L I)) := by
    change Derives Γ ((SyntaxNodeSyntax.constructor 2 21 w (SyntaxAtomSyntax.two F H) c).conj
      ((SyntaxLogicalSyntax.binaryCode 2 w G J K).conj ((SyntaxLogicalSyntax.singleCode 9 w K X).conj
        ((SyntaxLogicalSyntax.singleCode 9 w G V).conj ((SyntaxLogicalSyntax.singleCode 9 w J U).conj
          ((SyntaxLogicalSyntax.binaryCode 2 w V U L).conj ((SyntaxLogicalSyntax.binaryCode 2 w X L I).conj
            (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c I) row))))))))
    exact .conjI hc (.conjI hK (.conjI hX (.conjI hV (.conjI hU (.conjI hL (.conjI hI hr))))))
  have hHead := LogicalRule21Head.intro_normalized w row env (seven c K X V U L I) hValues
  have hSpec := LogicalAbstractSyntax.intro_specification21 w z A env hA
    (LogicalAbstractSyntax.intro_atOneSpecification21 w z A B env hB (.conjI hFt (.conjI hHt (.conjI hAF hAH))))
  have hNormalized : Derives Γ (LogicalAbstractNodeSyntax.normalized21 w z row) := by
    apply HornBinderRules.intro_many 5 _ env
    exact of_eq (by simp only [LogicalAbstractNodeSyntax.normalizedBody21, LogicalAbstractNodeSyntax.normalizedMatrix21,
      Formula.rename, environmentNat_rename, LogicalRule21Head.normalized_rename, LogicalAbstractSyntax.specification21_rename, assign_old, assign_slot])
      (.conjI hN (.conjI hHead hSpec))
  have hNode := Derives.impE (.conjR (LogicalAbstractNode.normalized_node21_iff hZ w z row hw hz)) hNormalized
  have hOriginal := Derives.impE (.conjR (LogicalOriginalNodes.rule21_iff w row)) hNode
  have hShape : ObjectLogicalAxiom.rule21 ∈ ObjectLogicalAxiom.shapes := by
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, or_true, true_or]
  exact original_row hZ test ObjectLogicalAxiom.rule21 hShape w z b I c row hw hz hIt
    (ProofTreeConstructorFacts.range hZ 2 21 w c (SyntaxAtomSyntax.two F H) hw hc) hr hOriginal

private theorem distribution_at_certificate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B F H G J K X V U L I c : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (distributionData w z b A B F H G J K X V U L I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 21 w (SyntaxAtomSyntax.two F H) c)) :
    Derives Γ (proved test w z b I) := by
  have hG := SyntaxTopFormulaTyping.abstract_target_type w z b A B F G (.conjL hd)
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w G A b hG))
  have hIN := ProofTreeConstructorFacts.range hZ 2 7 w I (SyntaxAtomSyntax.two X L) hw (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hd)))))))
  have hcN := ProofTreeConstructorFacts.range hZ 2 21 w c (SyntaxAtomSyntax.two F H) hw hc
  have he := SyntaxConstructors.exists_constructor hZ 3 0 w (SetLanguage.args3 b c I) hw
    (.conjI hb (.conjI hcN (.conjI hIN (.eqRefl w))))
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 0 w.castSucc (SetLanguage.args3 b.castSucc c.castSucc I.castSucc) (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hp := distribution_at_row (ZFContext.under hZ Q) test
    w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc F.castSucc H.castSucc G.castSucc J.castSucc K.castSucc X.castSucc V.castSucc U.castSucc L.castSucc I.castSucc c.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (distributionData_rename w z b A B F H G J K X V U L I Fin.castSucc) (under hd Q))
    (by simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using under hc Q) (.conjR hQ)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm hp

/-- Build the ORIGINAL rule21 certificate, row and proof internally, using the
ACTUAL two native abstraction judgments. No logical query/certificate/proof is
supplied. The result is the original forall-distribution axiom at real codes. -/
theorem distribution_axiom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B F H G J K X V U L I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (distributionData w z b A B F H G J K X V U L I)) :
    Derives Γ (proved test w z b I) := by
  have hFN := SyntaxTopFormulaTyping.abstract_source_natural w z b A B F G (.conjL hd)
  have hHN := SyntaxTopFormulaTyping.abstract_source_natural w z b A B H J (.conjL (.conjR hd))
  have he := SyntaxConstructors.exists_constructor hZ 2 21 w (SyntaxAtomSyntax.two F H) hw (.conjI hFN (.conjI hHN (.eqRefl w)))
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 21 w.castSucc (SyntaxAtomSyntax.two F.castSucc H.castSucc) (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hp := distribution_at_certificate (ZFContext.under hZ Q) test
    w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc F.castSucc H.castSucc G.castSucc J.castSucc K.castSucc X.castSucc V.castSucc U.castSucc L.castSucc I.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (distributionData_rename w z b A B F H G J K X V U L I Fin.castSucc) (under hd Q)) (.conjR hQ)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm hp

def vacuityData {m} (w z b A G V I : Fin m) : Formula m :=
  (successor A z).conj ((formulaCode w G z b).conj ((formulaCode w G A b).conj
    ((SyntaxLogicalSyntax.singleCode 9 w G V).conj (SyntaxLogicalSyntax.binaryCode 2 w G V I))))

theorem vacuityData_rename {m l} (w z b A G V I : Fin m) (ρ : Fin m → Fin l) :
    (vacuityData w z b A G V I).rename ρ = vacuityData (ρ w) (ρ z) (ρ b) (ρ A) (ρ G) (ρ V) (ρ I) := by
  simp only [vacuityData, Formula.rename, successor_rename, formulaCode_rename,
    SyntaxLogicalSyntax.singleCode_rename, SyntaxLogicalSyntax.binaryCode_rename]

private theorem static_types_rename {m l} (n : Nat) (w z : Fin m) (env : Fin (n+1) → Fin m) (ρ : Fin m → Fin l) :
    (LogicalStaticQueries.types n false w z env).rename ρ =
      LogicalStaticQueries.types n false (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [LogicalStaticQueries.types, LogicalStaticQueries.conjoin_rename, LogicalStaticQueries.typed,
    Bool.false_eq_true, ↓reduceIte, formulaCode_rename]

private theorem vacuity_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A G V I c row : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (vacuityData w z b A G V I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 1 22 w (fun _ => G) c))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c I) row)) :
    Derives Γ (proved test w z b I) := by
  have hA := Derives.conjL hd
  have hG0 := Derives.conjL (.conjR hd)
  have hGt := Derives.conjL (.conjR (.conjR hd))
  have hV := Derives.conjL (.conjR (.conjR (.conjR hd)))
  have hI := Derives.conjR (.conjR (.conjR (.conjR hd)))
  have hVt := all_type hZ w z b A G V hw (.conjR (FormulaCodeProperties.guards w G z b hG0)) hA hGt hV
  have hIt := imp_type hZ w z b G V I hw hG0 hVt hI
  let env := SyntaxAtomSyntax.two b G
  have hN : Derives Γ (environmentNat 2 w env) := .conjI (.conjR (.conjR (FormulaCodeProperties.guards w G z b hG0)))
    (.conjI (.conjL (FormulaCodeProperties.guards w G z b hG0)) HornRuleSyntax.truth_proved)
  have hValues : Derives Γ (LogicalRule22Head.atValues w row env (SetLanguage.args3 c V I)) := by
    change Derives Γ ((SyntaxNodeSyntax.constructor 1 22 w (fun _ => G) c).conj
      ((SyntaxLogicalSyntax.singleCode 9 w G V).conj ((SyntaxLogicalSyntax.binaryCode 2 w G V I).conj
        (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c I) row))))
    exact .conjI hc (.conjI hV (.conjI hI hr))
  have hHead := LogicalRule22Head.intro_normalized w row env (SetLanguage.args3 c V I) hValues
  have hTypes : Derives Γ (LogicalStaticQueries.types 1 false w z env) := .conjI hG0 HornRuleSyntax.truth_proved
  have hNormalized : Derives Γ (LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule22Head.normalized) w z row) := by
    apply HornBinderRules.intro_many 2 _ env
    exact of_eq (by simp only [LogicalStaticNodeSyntax.normalizedBody, LogicalStaticNodeSyntax.normalizedMatrix,
      Formula.rename, environmentNat_rename, LogicalRule22Head.normalized_rename, static_types_rename, assign_old, assign_slot])
      (.conjI hN (.conjI hHead hTypes))
  have hNode := Derives.impE (.conjR (LogicalStaticNode.normalized_node_iff hZ 1 false ObjectLogicalAxiom.rule22.head
    (@LogicalRule22Head.normalized) LogicalStaticPatterns.rule22_head_variables (@LogicalRule22Head.head_iff) w z row hw hz)) hNormalized
  have hOriginal := Derives.impE (.conjR (LogicalOriginalNodes.rule22_iff w row)) hNode
  have hShape : ObjectLogicalAxiom.rule22 ∈ ObjectLogicalAxiom.shapes := by
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, or_true, true_or]
  exact original_row hZ test ObjectLogicalAxiom.rule22 hShape w z b I c row hw hz hIt
    (ProofTreeConstructorFacts.range hZ 1 22 w c (fun _ => G) hw hc) hr hOriginal

private theorem vacuity_at_certificate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A G V I c : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (vacuityData w z b A G V I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 1 22 w (fun _ => G) c)) :
    Derives Γ (proved test w z b I) := by
  have hG := Derives.conjL (.conjR hd)
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w G z b hG))
  have hIN := ProofTreeConstructorFacts.range hZ 2 7 w I (SyntaxAtomSyntax.two G V) hw (.conjR (.conjR (.conjR (.conjR hd))))
  have hcN := ProofTreeConstructorFacts.range hZ 1 22 w c (fun _ => G) hw hc
  have he := SyntaxConstructors.exists_constructor hZ 3 0 w (SetLanguage.args3 b c I) hw
    (.conjI hb (.conjI hcN (.conjI hIN (.eqRefl w))))
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 0 w.castSucc (SetLanguage.args3 b.castSucc c.castSucc I.castSucc) (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hp := vacuity_at_row (ZFContext.under hZ Q) test
    w.castSucc z.castSucc b.castSucc A.castSucc G.castSucc V.castSucc I.castSucc c.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (vacuityData_rename w z b A G V I Fin.castSucc) (under hd Q))
    (by simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename] using under hc Q) (.conjR hQ)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm hp

/-- ORIGINAL rule22 proof at real formula/forall/implication codes. Both logical
certificate and row are internally generated; no query or proof is supplied. -/
theorem vacuity_axiom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A G V I : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (vacuityData w z b A G V I)) : Derives Γ (proved test w z b I) := by
  have hGN := Derives.conjL (FormulaCodeProperties.guards w G z b (.conjL (.conjR hd)))
  have he := SyntaxConstructors.exists_constructor hZ 1 22 w (fun _ => G) hw (.conjI hGN (.eqRefl w))
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 1 22 w.castSucc (fun _ => G.castSucc) (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hp := vacuity_at_certificate (ZFContext.under hZ Q) test
    w.castSucc z.castSucc b.castSucc A.castSucc G.castSucc V.castSucc I.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (vacuityData_rename w z b A G V I Fin.castSucc) (under hd Q)) (.conjR hQ)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm hp

private theorem forall_proof {m} {Γ : Context m} (test : Formula 1) (w z b F c : Fin m)
    (h : Derives Γ (InternalProofOperations.existsResult test 3 w z (SetLanguage.args3 b F c))) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let T := InternalProofOperations.result test 3 w.castSucc z.castSucc (Fin.last m) (fun i => (SetLanguage.args3 b F c i).castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) h
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have out : Derives Δ (InternalProofConjunction.proved test w.castSucc z.castSucc b.castSucc F.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename,
      empty_rename, ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (show Derives Δ ((Formula.mem (Fin.last m) w.castSucc).conj
        ((InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc F.castSucc (Fin.last m)).conj
          ((empty b.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc)))) from
        .conjI (.conjL ht) (.conjR (.conjR ht)))
  exact of_eq (InternalProofConjunction.proved_rename test w z b F Fin.castSucc).symm out

/-- Original forall body and complete original proof/Root package. -/
def allProved {m} (test : Formula 1) (w z b J : Fin m) : Formula m := .ex
  ((SyntaxLogicalSyntax.singleCode 9 w.castSucc J.castSucc (Fin.last m)).conj
    (proved test w.castSucc z.castSucc b.castSucc (Fin.last m)))

theorem allProved_rename {m l} (test : Formula 1) (w z b J : Fin m) (ρ : Fin m → Fin l) :
    (allProved test w z b J).rename ρ = allProved test (ρ w) (ρ z) (ρ b) (ρ J) := by
  simp only [allProved, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, proved_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem generalize_at_child {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B F J p : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B F J))
    (hpn : Derives Γ (.mem p w)) (hp : Derives Γ (InternalMPProof.annotated test w z B F p)) :
    Derives Γ (allProved test w z b J) := by
  have he := InternalProofOperations.forall_produce hZ test w z b A B F J p hw hz (.conjI ha (.conjI hpn hp))
  let Q := (SyntaxNodeSyntax.constructor 1 9 w.castSucc (fun _ : Fin 1 => J.castSucc) (Fin.last m)).conj
    (InternalProofOperations.existsResult test 3 w.castSucc z.castSucc (SetLanguage.args3 b.castSucc (Fin.last m) p.castSucc))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hpU := forall_proof test w.castSucc z.castSucc b.castSucc (Fin.last m) p.castSucc (.conjR hQ)
  have hout : Derives Δ (allProved test w.castSucc z.castSucc b.castSucc J.castSucc) := by
    apply Derives.exI (Fin.last m)
    have hPair : Derives Δ ((SyntaxLogicalSyntax.singleCode 9 w.castSucc J.castSucc (Fin.last m)).conj
      (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))) := .conjI (.conjL hQ) hpU
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
      proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hPair
  exact of_eq (allProved_rename test w z b J Fin.castSucc).symm hout

/-- Consume a REAL mode3 abstraction and an existing internal child proof.
The original forall node, forall code, proof and conditional Root are generated
internally; no child code or runtime scope is assumed externally standard. -/
theorem generalize {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B F J : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B F J))
    (hp : Derives Γ (proved test w z B F)) : Derives Γ (allProved test w z b J) := by
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    ((InternalMPProof.annotated test w.castSucc z.castSucc B.castSucc F.castSucc (Fin.last m)).conj
      ((empty B.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc)))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hp
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hout := generalize_at_child (ZFContext.under hZ Q) test
    w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc F.castSucc J.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B F J Fin.castSucc) (under ha Q)) (.conjL hQ) (.conjL (.conjR hQ))
  exact of_eq (allProved_rename test w z b J Fin.castSucc).symm hout

/-- A fixed background is unchanged by the ACTUAL abstraction: W abstracts
back to the SAME G, which has bound scope zero. The child proof has the real
extended free scope B, not an externally fixed numeral scope. -/
def input {m} (test : Formula 1) (w z b A B G W F J I : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((formulaCode w G z b).conj
    ((SyntaxTopFormulaSyntax.abstracted w z b A B W G).conj
      ((SyntaxTopFormulaSyntax.abstracted w z b A B F J).conj
        ((SyntaxLogicalSyntax.binaryCode 2 w W F I).conj (proved test w z B I))))))

theorem input_rename {m l} (test : Formula 1) (w z b A B G W F J I : Fin m) (ρ : Fin m → Fin l) :
    (input test w z b A B G W F J I).rename ρ =
      input test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ G) (ρ W) (ρ F) (ρ J) (ρ I) := by
  simp only [input, Formula.rename, omega_rename, empty_rename, formulaCode_rename,
    SyntaxTopFormulaSyntax.abstracted_rename, SyntaxLogicalSyntax.binaryCode_rename, proved_rename]

def guarded {m} (test : Formula 1) (w z b G J : Fin m) : Formula m := .ex
  ((SyntaxLogicalSyntax.singleCode 9 w.castSucc J.castSucc (Fin.last m)).conj
    (InternalProofBackground.implication test w.castSucc z.castSucc b.castSucc G.castSucc (Fin.last m)))

theorem guarded_rename {m l} (test : Formula 1) (w z b G J : Fin m) (ρ : Fin m → Fin l) :
    (guarded test w z b G J).rename ρ = guarded test (ρ w) (ρ z) (ρ b) (ρ G) (ρ J) := by
  simp only [guarded, Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
    InternalProofBackground.implication_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Full same-background forall introduction. Generate EVERY formula,
certificate, row and proof witness using the ORIGINAL mode3, forall node,
rule21/rule22 and MP/compose producers. Neither G nor the conclusion is assumed
proved. All runtime scopes and codes remain arbitrary internal/nonstandard. -/
theorem guarded_generalize {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B G W F J I : Fin m) (h : Derives Γ (input test w z b A B G W F J I)) :
    Derives Γ (guarded test w z b G J) := by
  have tag2 : SyntaxLogicalSyntax.binaryTag (2 : Fin 4) = 7 := rfl
  have hw := Derives.conjL h
  have hz := Derives.conjL (.conjR h)
  have hG0 := Derives.conjL (.conjR (.conjR h))
  have hAW := Derives.conjL (.conjR (.conjR (.conjR h)))
  have hAF := Derives.conjL (.conjR (.conjR (.conjR (.conjR h))))
  have hCI := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h)))))
  have hpI := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))
  have hEnv := SyntaxTopFormulaTyping.abstract_environment w z b A B W G hAW
  have hctx := Derives.conjL hEnv
  have hA := Derives.conjL (.conjR hEnv)
  have hWt := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B W G hw hAW
  have hFt := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B F J hw hAF
  have hGt := SyntaxTopFormulaTyping.abstract_target_type w z b A B W G hAW
  have hJt := SyntaxTopFormulaTyping.abstract_target_type w z b A B F J hAF
  have hIt := imp_type hZ w z B W F I hw hWt hFt hCI
  let Q0 := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc J.castSucc) (Fin.last m))
  let Δ1 := Context.add Q0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q0) (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two G J) hw (.conjI (.conjL (FormulaCodeProperties.guards w G A b hGt)) (.conjI (.conjL (FormulaCodeProperties.guards w J A b hJt)) (.eqRefl w))))
  have hQ0 : Derives Δ1 Q0 := .hyp (Or.inl rfl)
  have hcK : Derives Δ1 (SyntaxLogicalSyntax.binaryCode 2 w.castSucc G.castSucc J.castSucc (Fin.last m)) := .conjR hQ0
  have htK := imp_type (ZFContext.under hZ Q0) w.castSucc A.castSucc b.castSucc G.castSucc J.castSucc (Fin.last m) (by simpa only [Formula.raise, omega_rename] using (under hw Q0)) (by simpa only [Formula.raise, formulaCode_rename] using (under hGt Q0)) (by simpa only [Formula.raise, formulaCode_rename] using (under hJt Q0)) hcK
  have hAbsI := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.abstract_binary_iff (ZFContext.under hZ Q0) 2 w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc I.castSucc (Fin.last m) W.castSucc F.castSucc G.castSucc J.castSucc (by simpa only [Formula.raise, omega_rename] using (under hw Q0)) (.conjI (by simpa only [Formula.raise, SyntaxTopEnvironmentSyntax.abstractInput_rename] using (under hEnv Q0)) (by simpa only [Formula.raise, formulaCode_rename] using (under hIt Q0))) (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] using (under hCI Q0)) hcK)) (.conjI (by simpa only [Formula.raise, SyntaxTopFormulaSyntax.abstracted_rename] using (under hAW Q0)) (by simpa only [Formula.raise, SyntaxTopFormulaSyntax.abstracted_rename] using (under hAF Q0)))
  let Q1 := (SyntaxLogicalSyntax.singleCode 9 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj (proved test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)))
  let Δ2 := Context.add Q1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := Q1) (generalize (ZFContext.under hZ Q0) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc I.castSucc (Fin.last m) (by simpa only [Formula.raise, omega_rename] using (under hw Q0)) (by simpa only [Formula.raise, empty_rename] using (under hz Q0)) hAbsI (by simpa only [Formula.raise, proved_rename] using (under hpI Q0)))
  have hQ1 : Derives Δ2 Q1 := .hyp (Or.inl rfl)
  have hcX := Derives.conjL hQ1
  have hpX := Derives.conjR hQ1
  have htX := all_type (ZFContext.under (ZFContext.under hZ Q0) Q1) w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (by simpa only [Formula.raise, omega_rename] using (under (under hw Q0) Q1)) (by simpa only [Formula.raise, SyntaxTermSyntax.contexts_rename] using (under (under hctx Q0) Q1)) (by simpa only [Formula.raise, successor_rename] using (under (under hA Q0) Q1)) (by simpa only [Formula.raise, formulaCode_rename] using (under htK Q1)) hcX
  let Q2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 1 9 w.castSucc.castSucc.castSucc (fun _ => G.castSucc.castSucc.castSucc) (Fin.last (m+2)))
  let Δ3 := Context.add Q2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := Q2) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under hZ Q0) Q1) 1 9 w.castSucc.castSucc (fun _ => G.castSucc.castSucc) (by simpa only [Formula.raise, omega_rename] using (under (under hw Q0) Q1)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc G.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under hGt Q0) Q1)))) (.eqRefl w.castSucc.castSucc)))
  have hQ2 : Derives Δ3 Q2 := .hyp (Or.inl rfl)
  have hcV : Derives Δ3 (SyntaxLogicalSyntax.singleCode 9 w.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc (Fin.last (m+2))) := .conjR hQ2
  have htV := all_type (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc (Fin.last (m+2)) (by simpa only [Formula.raise, omega_rename] using (under (under (under hw Q0) Q1) Q2)) (by simpa only [Formula.raise, SyntaxTermSyntax.contexts_rename] using (under (under (under hctx Q0) Q1) Q2)) (by simpa only [Formula.raise, successor_rename] using (under (under (under hA Q0) Q1) Q2)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under hGt Q0) Q1) Q2)) hcV
  let Q3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 1 9 w.castSucc.castSucc.castSucc.castSucc (fun _ => J.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)))
  let Δ4 := Context.add Q3 (Context.image Formula.raise Δ3)
  apply Derives.exE (p := Q3) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) 1 9 w.castSucc.castSucc.castSucc (fun _ => J.castSucc.castSucc.castSucc) (by simpa only [Formula.raise, omega_rename] using (under (under (under hw Q0) Q1) Q2)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under hJt Q0) Q1) Q2)))) (.eqRefl w.castSucc.castSucc.castSucc)))
  have hQ3 : Derives Δ4 Q3 := .hyp (Or.inl rfl)
  have hcU : Derives Δ4 (SyntaxLogicalSyntax.singleCode 9 w.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))) := .conjR hQ3
  have htU := all_type (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) w.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under hw Q0) Q1) Q2) Q3)) (by simpa only [Formula.raise, SyntaxTermSyntax.contexts_rename] using (under (under (under (under hctx Q0) Q1) Q2) Q3)) (by simpa only [Formula.raise, successor_rename] using (under (under (under (under hA Q0) Q1) Q2) Q3)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under hJt Q0) Q1) Q2) Q3)) hcU
  let Q4 := (Formula.mem (Fin.last (m+4)) w.castSucc.castSucc.castSucc.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc) (Fin.last (m+4)))
  let Δ5 := Context.add Q4 (Context.image Formula.raise Δ4)
  apply Derives.exE (p := Q4) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) 2 7 w.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last (m+2)).castSucc (Fin.last (m+3))) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under hw Q0) Q1) Q2) Q3)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc z.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under htV Q3)))) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) z.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc htU)) (.eqRefl w.castSucc.castSucc.castSucc.castSucc))))
  have hQ4 : Derives Δ5 Q4 := .hyp (Or.inl rfl)
  have hcL : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 2 w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))) := .conjR hQ4
  have htL := imp_type (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) w.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under htV Q3) Q4)) (by simpa only [Formula.raise, formulaCode_rename] using (under htU Q4)) hcL
  let Q5 := (Formula.mem (Fin.last (m+5)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc) (Fin.last (m+5)))
  let Δ6 := Context.add Q5 (Context.image Formula.raise Δ5)
  apply Derives.exE (p := Q5) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+4))) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under htX Q2) Q3) Q4)))) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)) z.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc htL)) (.eqRefl w.castSucc.castSucc.castSucc.castSucc.castSucc))))
  have hQ5 : Derives Δ6 Q5 := .hyp (Or.inl rfl)
  have hcAx : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5))) := .conjR hQ5
  have htAx := imp_type (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under htX Q2) Q3) Q4) Q5)) (by simpa only [Formula.raise, formulaCode_rename] using (under htL Q5)) hcAx
  let Q6 := (Formula.mem (Fin.last (m+6)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+6)))
  let Δ7 := Context.add Q6 (Context.image Formula.raise Δ6)
  apply Derives.exE (p := Q6) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under hG0 Q0) Q1) Q2) Q3) Q4) Q5)))) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under htV Q3) Q4) Q5)))) (.eqRefl w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))))
  have hQ6 : Derives Δ7 Q6 := .hyp (Or.inl rfl)
  have hcVac : Derives Δ7 (SyntaxLogicalSyntax.binaryCode 2 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+6))) := .conjR hQ6
  have htVac := imp_type (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) Q6) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5) Q6)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under (under hG0 Q0) Q1) Q2) Q3) Q4) Q5) Q6)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under htV Q3) Q4) Q5) Q6)) hcVac
  let Q7 := (Formula.mem (Fin.last (m+7)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+7)))
  let Δ8 := Context.add Q7 (Context.image Formula.raise Δ7)
  apply Derives.exE (p := Q7) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) Q6) 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5) Q6)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under (under hG0 Q0) Q1) Q2) Q3) Q4) Q5) Q6)))) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under htU Q4) Q5) Q6)))) (.eqRefl w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))))
  have hQ7 : Derives Δ8 Q7 := .hyp (Or.inl rfl)
  have hcOut : Derives Δ8 (SyntaxLogicalSyntax.binaryCode 2 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+7))) := .conjR hQ7
  have htOut := imp_type (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under (under (under hG0 Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under htU Q4) Q5) Q6) Q7)) hcOut
  have hDist : Derives Δ8 (distributionData w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc W.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc F.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc) := .conjI (by simpa only [Formula.raise, SyntaxTopFormulaSyntax.abstracted_rename] using (under (under (under (under (under (under (under (under hAW Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, SyntaxTopFormulaSyntax.abstracted_rename] using (under (under (under (under (under (under (under (under hAF Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] using (under (under (under (under (under (under (under hcK Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename] using (under (under (under (under (under (under hcX Q2) Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename] using (under (under (under (under (under hcV Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename] using (under (under (under (under hcU Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] using (under (under (under hcL Q5) Q6) Q7)) (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] using (under (under hcAx Q6) Q7))))))))
  have hpAx := distribution_axiom (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7) test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc W.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc F.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, empty_rename] using (under (under (under (under (under (under (under (under hz Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) hDist
  have hpL := InternalProofConjunction.modus_ponens (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7) test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, empty_rename] using (under (under (under (under (under (under (under (under hz Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under htX Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under htL Q5) Q6) Q7)) (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename, SyntaxLogicalSyntax.binaryCode, tag2, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under (under hcAx Q6) Q7)) (by simpa only [Formula.raise, proved_rename] using (under (under (under (under (under (under hpX Q2) Q3) Q4) Q5) Q6) Q7)) hpAx
  have hVac : Derives Δ8 (vacuityData w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc) := .conjI (by simpa only [Formula.raise, successor_rename] using (under (under (under (under (under (under (under (under hA Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under (under (under hG0 Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under (under (under hGt Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (.conjI (by simpa only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename] using (under (under (under (under (under hcV Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] using (under hcVac Q7)))))
  have hpVac := vacuity_axiom (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7) test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, empty_rename] using (under (under (under (under (under (under (under (under hz Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) hVac
  have hpOut := InternalProofImplication.compose (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7) test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+7)) (by simpa only [Formula.raise, omega_rename] using (under (under (under (under (under (under (under (under hw Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, empty_rename] using (under (under (under (under (under (under (under (under hz Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under (under (under (under hG0 Q0) Q1) Q2) Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under (under htV Q3) Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under (under htU Q4) Q5) Q6) Q7)) (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename, SyntaxLogicalSyntax.binaryCode, tag2, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under hcVac Q7)) (by simpa only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename, SyntaxLogicalSyntax.binaryCode, tag2, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under (under (under hcL Q5) Q6) Q7)) hcOut hpVac hpL
  have hImp : Derives Δ8 (InternalProofBackground.implication test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+7))
    have hPair : Derives Δ8 ((SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+7))).conj (proved test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)))) := .conjI hcOut hpOut
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hPair
  have hout : Derives Δ8 (guarded test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc
    have hPair : Derives Δ8 ((SyntaxLogicalSyntax.singleCode 9 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc).conj (InternalProofBackground.implication test w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc)) := .conjI (by simpa only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename] using (under (under (under (under hcU Q4) Q5) Q6) Q7)) hImp
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, InternalProofBackground.implication_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hPair
  exact of_eq (by simp only [Formula.raise, guarded_rename]) hout

def sentence {m} (target : Bool) (w z b A B G W F J I : Fin m) : Source.Sentence :=
  ((input (OriginalAxiomCodeTest.test target) w z b A B G W F J I).imp
    (guarded (OriginalAxiomCodeTest.test target) w z b G J)).close

theorem kernel_certificate {m} (target : Bool) (w z b A B G W F J I : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b A B G W F J I)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input (OriginalAxiomCodeTest.test target) w z b A B G W F J I
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact guarded_generalize (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z b A B G W F J I h

end PPAC.Migration.InternalProofUniversal
