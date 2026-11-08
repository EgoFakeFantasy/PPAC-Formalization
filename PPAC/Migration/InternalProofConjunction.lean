import PPAC.Migration.InternalProofOperations
import PPAC.Migration.ForcingLogicalCode

/-! Uniform code-level conjunction composition for the conjunction cases of the
pinned `basic_mono` / `basic_of_dense` proofs. Use original rule11 and two actual
MP nodes; no new logical checker, kernel, truth predicate or code backend.
All formula, free-scope and proof witnesses remain internal, including nonstandard.
This is a native target-proof operation, not yet interpreted forcing soundness. -/
namespace PPAC.Migration.InternalProofConjunction
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open YesMetaZFC.Automation
set_option maxRecDepth 16384

/-- Actual internal proof witness, exact original header, and original Root at
empty free scope. Formula typing is kept as its separate original predicate. -/
def proved {m} (test : Formula 1) (w z b F : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    ((InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc F.castSucc (Fin.last m)).conj
      ((empty b.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc))))
theorem proved_rename {m l} (test : Formula 1) (w z b F : Fin m) (r : Fin m → Fin l) :
    (proved test w z b F).rename r = proved test (r w) (r z) (r b) (r F) := by
  simp only [proved, Formula.rename, InternalMPProof.annotated_rename, empty_rename,
    ProofTreeEntryFacts.root_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem from_mp {m} {Γ : Context m} (test : Formula 1) (w z b B p q : Fin m)
    (h : Derives Γ (InternalMPProof.existsBuilt test w z b B p q)) : Derives Γ (proved test w z b B) := by
  let T := InternalMPProof.built test w.castSucc z.castSucc b.castSucc B.castSucc p.castSucc q.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) h
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have out : Derives Δ (proved test w.castSucc z.castSucc b.castSucc B.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename,
      empty_rename, ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI (.conjL ht) (.conjR (.conjR ht)))
  exact of_eq (proved_rename test w z b B Fin.castSucc).symm out

private theorem from_logical {m} {Γ : Context m} (test : Formula 1) (w z b F c : Fin m)
    (h : Derives Γ (InternalProofOperations.existsResult test 0 w z (SetLanguage.args3 b F c))) : Derives Γ (proved test w z b F) := by
  let T := InternalProofOperations.result test 0 w.castSucc z.castSucc (Fin.last m) (fun i => (SetLanguage.args3 b F c i).castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) h
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have out : Derives Δ (proved test w.castSucc z.castSucc b.castSucc F.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename,
      empty_rename, ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (show Derives Δ ((Formula.mem (Fin.last m) w.castSucc).conj
        ((InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc F.castSucc (Fin.last m)).conj
          ((empty b.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc)))) from
        .conjI (.conjL ht) (.conjR (.conjR ht)))
  exact of_eq (proved_rename test w z b F Fin.castSucc).symm out

/-- Existential proof witnesses compose by the actual original MP producer. -/
theorem modus_ponens {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A B I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hi : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I))
    (ha : Derives Γ (proved test w z b A)) (hq : Derives Γ (proved test w z b I)) : Derives Γ (proved test w z b B) := by
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    ((InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc A.castSucc (Fin.last m)).conj
      ((empty b.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) A.castSucc)))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) ha
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz T)
  have hA1 := of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)
  have hB1 := of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T)
  have hi1 : Derives Δ (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two A.castSucc B.castSucc) I.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hi T)
  have hq1 := of_eq (proved_rename test w z b I Fin.castSucc) (under hq T)
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have outer : Derives Δ (proved test w.castSucc z.castSucc b.castSucc B.castSucc) := by
    let U := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
      ((InternalMPProof.annotated test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc I.castSucc.castSucc (Fin.last (m+1))).conj
        ((empty b.castSucc.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc.castSucc (Fin.last (m+1)) I.castSucc.castSucc)))
    let Ξ := Context.add U (Context.image Formula.raise Δ)
    apply Derives.exE (p := U) hq1
    have hu : Derives Ξ U := .hyp (Or.inl rfl)
    have hp1 : Derives Δ (InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc A.castSucc (Fin.last m)) := .conjL (.conjR ht)
    have hp2 := of_eq (InternalMPProof.annotated_rename test w.castSucc z.castSucc b.castSucc A.castSucc (Fin.last m) Fin.castSucc) (under hp1 U)
    have he := InternalMPProof.produce (ZFContext.under (ZFContext.under hZ T) U) test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc
      A.castSucc.castSucc B.castSucc.castSucc I.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 U))
      (of_eq (empty_rename z.castSucc Fin.castSucc) (under hz1 U))
      (of_eq (formulaCode_rename w.castSucc A.castSucc z.castSucc b.castSucc Fin.castSucc) (under hA1 U))
      (of_eq (formulaCode_rename w.castSucc B.castSucc z.castSucc b.castSucc Fin.castSucc) (under hB1 U))
      (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hi1 U))
      hp2 (.conjL (.conjR hu))
    have out := from_mp test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) he
    exact of_eq (proved_rename test w.castSucc z.castSucc b.castSucc B.castSucc Fin.castSucc).symm out
  exact of_eq (proved_rename test w z b B Fin.castSucc).symm outer


private theorem implication_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A B I : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I)) : Derives Γ (formulaCode w I z b) :=
  .impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b A B I hw hc))
    (.conjI (.conjR (FormulaCodeProperties.guards w A z b hA)) (.conjI hA hB))
private theorem conjunction_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A B C : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C)) : Derives Γ (formulaCode w C z b) :=
  .impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b A B C hw hc))
    (.conjI (.conjR (FormulaCodeProperties.guards w A z b hA)) (.conjI hA hB))

private theorem axiom_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C D I c row : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hC : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (hD : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) D))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A D) I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 11 w (SyntaxAtomSyntax.two A B) c))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c I) row)) : Derives Γ (proved test w z b I) := by
  let env := SetLanguage.args3 b A B
  let ys : Fin 4 → Fin m := Fin.cases c (Fin.cases C (SyntaxAtomSyntax.two D I))
  have hgA := FormulaCodeProperties.guards w A z b hA
  have hgB := FormulaCodeProperties.guards w B z b hB
  have hn : Derives Γ (environmentNat 3 w env) :=
    .conjI (.conjR (.conjR hgA)) (.conjI (.conjL hgA) (.conjI (.conjL hgB) HornRuleSyntax.truth_proved))
  have hnrm : Derives Γ (LogicalRule11Head.normalized w row env) :=
    LogicalRule11Head.intro_normalized w row env ys (.conjI hc (.conjI hC (.conjI hD (.conjI hI hr))))
  have hh := Derives.impE (.conjR (LogicalRule11Head.head_iff hZ w row env hw hn)) hnrm
  have hb := LogicalStaticNode.head_bounds hZ ObjectLogicalAxiom.rule11.head LogicalStaticPatterns.rule11_head_variables w row env hw hn hh
  have htypes : Derives Γ (LogicalStaticQueries.types 2 false w z env) := .conjI hA (.conjI hB HornRuleSyntax.truth_proved)
  have hqs := Derives.impE (.conjR (LogicalStaticQueries.bundle_iff hZ 2 false w z env hw hn hz)) htypes
  have hlist := of_eq (LogicalStaticPatterns.rule11_actual_list_bundle w env).symm hqs
  have hm : Derives Γ (LogicalOriginalNodeSyntax.matrix ObjectLogicalAxiom.rule11 w row env) := .conjI hn (.conjI hb (.conjI hh hlist))
  have hnode : Derives Γ (LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule11 w row) := by
    apply HornBinderRules.intro_many 3 (LogicalOriginalNodeSyntax.body ObjectLogicalAxiom.rule11 w row) env
    exact of_eq (by simp only [LogicalOriginalNodeSyntax.body, LogicalTableRenaming.matrix_rename, assign_old, assign_slot]) hm
  have ht : Derives Γ (LogicalOriginalNodeSyntax.table w row) := .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hnode)))))))))))
  have hquery : Derives Γ (OriginalLogicalExprQuery.rowQuery 3 0 w (SetLanguage.args3 b c I)) := by
    apply Derives.exI row
    exact of_eq (by simp only [Formula.instantiate, Formula.rename,
      SyntaxNodeSyntax.constructor_rename, LogicalTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr ht)
  have hCT := conjunction_type hZ w z b A B C hw hA hB hC
  have hDT := implication_type hZ w z b B C D hw hB hCT hD
  have hIT := implication_type hZ w z b A D I hw hA hDT hI
  have hcN := ProofTreeConstructorFacts.range hZ 2 11 w c (SyntaxAtomSyntax.two A B) hw hc
  exact from_logical test w z b I c (InternalProofOperations.logical hZ test w z b I c hw hz (.conjI hIT (.conjI hcN hquery)))

private theorem axiom_at_certificate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C D I c : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hC : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (hD : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) D))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A D) I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 11 w (SyntaxAtomSyntax.two A B) c)) : Derives Γ (proved test w z b I) := by
  have hCT := conjunction_type hZ w z b A B C hw hA hB hC
  have hIT := implication_type hZ w z b A D I hw hA (implication_type hZ w z b B C D hw hB hCT hD) hI
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w A z b hA))
  have hi := Derives.conjL (FormulaCodeProperties.guards w I z b hIT)
  have hcN := ProofTreeConstructorFacts.range hZ 2 11 w c (SyntaxAtomSyntax.two A B) hw hc
  have hin := SyntaxForestSyntax.intro_inputs 3 w (SetLanguage.args3 b c I)
    (fun i => Fin.cases hb (fun i => Fin.cases hcN (fun i => Fin.cases hi (fun e => Fin.elim0 e) i) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 0 w.castSucc (fun i => (SetLanguage.args3 b c I i).castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxConstructors.exists_constructor hZ 3 0 w (SetLanguage.args3 b c I) hw hin)
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have out := axiom_at_row (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc D.castSucc I.castSucc c.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)) (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hC T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hD T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hc T))
    (.conjR ht)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm out

/-- Generates the original rule11 certificate and entire local query, rather
than assuming a logical test or a proof of the instantiated axiom. -/
theorem conjunction_axiom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C D I : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hC : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (hD : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) D))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A D) I)) : Derives Γ (proved test w z b I) := by
  have hAN := Derives.conjL (FormulaCodeProperties.guards w A z b hA)
  have hBN := Derives.conjL (FormulaCodeProperties.guards w B z b hB)
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two A B)
    (fun i => Fin.cases hAN (fun i => Fin.cases hBN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 11 w.castSucc (SyntaxAtomSyntax.two A.castSucc B.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 11 w (SyntaxAtomSyntax.two A B) hw hin)
  apply Derives.exE (p := T) he
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have out := axiom_at_certificate (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc D.castSucc I.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)) (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hC T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hD T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI T)) (.conjR ht)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm out

private theorem conjoin_at_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C D : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (hd : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) D))
    (ha : Derives Γ (proved test w z b A)) (hb : Derives Γ (proved test w z b B)) : Derives Γ (proved test w z b C) := by
  have hCT := conjunction_type hZ w z b A B C hw hA hB hc
  have hDT := implication_type hZ w z b B C D hw hB hCT hd
  have hAN := Derives.conjL (FormulaCodeProperties.guards w A z b hA)
  have hDN := Derives.conjL (FormulaCodeProperties.guards w D z b hDT)
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two A D)
    (fun i => Fin.cases hAN (fun i => Fin.cases hDN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two A.castSucc D.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two A D) hw hin)
  apply Derives.exE (p := T) he
  have hZ1 := ZFContext.under hZ T
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz T)
  have hA1 := of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)
  have hB1 := of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T)
  have hC1 := of_eq (formulaCode_rename w C z b Fin.castSucc) (under hCT T)
  have hD1 := of_eq (formulaCode_rename w D z b Fin.castSucc) (under hDT T)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 2 5 w.castSucc (SyntaxAtomSyntax.two A.castSucc B.castSucc) C.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hc T)
  have hd1 : Derives Δ (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two B.castSucc C.castSucc) D.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hd T)
  have ha1 := of_eq (proved_rename test w z b A Fin.castSucc) (under ha T)
  have hb1 := of_eq (proved_rename test w z b B Fin.castSucc) (under hb T)
  have hax := conjunction_axiom hZ1 test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc D.castSucc (Fin.last m)
    hw1 hz1 hA1 hB1 hc1 hd1 (.conjR ht)
  have hmid := modus_ponens hZ1 test w.castSucc z.castSucc b.castSucc A.castSucc D.castSucc (Fin.last m) hw1 hz1 hA1 hD1 (.conjR ht) ha1 hax
  have out := modus_ponens hZ1 test w.castSucc z.castSucc b.castSucc B.castSucc C.castSucc D.castSucc hw1 hz1 hB1 hC1 hd1 hb1 hmid
  exact of_eq (proved_rename test w z b C Fin.castSucc).symm out

/-- The two implication codes, rule11 certificate, local query, logical proof
and both MP parents are generated from the two real child proofs. -/
theorem conjoin {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (ha : Derives Γ (proved test w z b A)) (hb : Derives Γ (proved test w z b B)) : Derives Γ (proved test w z b C) := by
  have hCT := conjunction_type hZ w z b A B C hw hA hB hc
  have hBN := Derives.conjL (FormulaCodeProperties.guards w B z b hB)
  have hCN := Derives.conjL (FormulaCodeProperties.guards w C z b hCT)
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two B C)
    (fun i => Fin.cases hBN (fun i => Fin.cases hCN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two B.castSucc C.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two B C) hw hin)
  apply Derives.exE (p := T) he
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have out := conjoin_at_tail (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)) (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hc T)) (.conjR ht)
    (of_eq (proved_rename test w z b A Fin.castSucc) (under ha T)) (of_eq (proved_rename test w z b B Fin.castSucc) (under hb T))
  exact of_eq (proved_rename test w z b C Fin.castSucc).symm out

def conjoined {m} (test : Formula 1) (w z b A B : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 2 5 w.castSucc (SyntaxAtomSyntax.two A.castSucc B.castSucc) (Fin.last m)).conj
    ((formulaCode w.castSucc (Fin.last m) z.castSucc b.castSucc).conj
      (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))))
theorem conjoined_rename {m l} (test : Formula 1) (w z b A B : Fin m) (r : Fin m → Fin l) :
    (conjoined test w z b A B).rename r = conjoined test (r w) (r z) (r b) (r A) (r B) := by
  simp only [conjoined, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map,
    formulaCode_rename, proved_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Generates the conjunction formula code as well as its actual proof code. -/
theorem conjoin_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (ha : Derives Γ (proved test w z b A)) (hb : Derives Γ (proved test w z b B)) : Derives Γ (conjoined test w z b A B) := by
  have hAN := Derives.conjL (FormulaCodeProperties.guards w A z b hA)
  have hBN := Derives.conjL (FormulaCodeProperties.guards w B z b hB)
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two A B)
    (fun i => Fin.cases hAN (fun i => Fin.cases hBN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 5 w.castSucc (SyntaxAtomSyntax.two A.castSucc B.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 5 w (SyntaxAtomSyntax.two A B) hw hin)
  apply Derives.exE (p := T) he
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ T
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz T)
  have hA1 := of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)
  have hB1 := of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T)
  have hp := conjoin hZ1 test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc (Fin.last m) hw1 hz1 hA1 hB1 (.conjR ht)
    (of_eq (proved_rename test w z b A Fin.castSucc) (under ha T)) (of_eq (proved_rename test w z b B Fin.castSucc) (under hb T))
  have hCT := conjunction_type hZ1 w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc (Fin.last m) hw1 hA1 hB1 (.conjR ht)
  have out : Derives Δ (conjoined test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map,
      formulaCode_rename, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR ht) (.conjI hCT hp))
  exact of_eq (conjoined_rename test w z b A B Fin.castSucc).symm out

def input {m} (test : Formula 1) (w z b A B : Fin m) : Formula m :=
  (formulaCode w A z b).conj ((formulaCode w B z b).conj ((proved test w z b A).conj (proved test w z b B)))
theorem input_rename {m l} (test : Formula 1) (w z b A B : Fin m) (r : Fin m → Fin l) :
    (input test w z b A B).rename r = input test (r w) (r z) (r b) (r A) (r B) := by
  simp only [input, Formula.rename, formulaCode_rename, proved_rename]
def sentence {m} (target : Bool) (w z b A B : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((input (OriginalAxiomCodeTest.test target) w z b A B).imp
    (conjoined (OriginalAxiomCodeTest.test target) w z b A B)))).close

theorem kernel_certificate {m} (target : Bool) (w z b A B : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b A B)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Γ := Context.add (input (OriginalAxiomCodeTest.test target) w z b A B)
    (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hi : Derives Γ (input (OriginalAxiomCodeTest.test target) w z b A B) := .hyp (Or.inl rfl)
  exact conjoin_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    (OriginalAxiomCodeTest.test target) w z b A B
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl)))
    (.conjL hi) (.conjL (.conjR hi)) (.conjL (.conjR (.conjR hi))) (.conjR (.conjR (.conjR hi)))

/-- Direct consumer of the ACTUAL accepted forcing compiler's AND output.
Its original full output type recovers both child types; no replacement
formula, logical-test premise, or extra typing oracle is introduced. -/
theorem compiled_conjunction {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (R : Source.Formula (n+2)) (w z a b j N M Q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (ForcingLogicalCode.binary 0 R w z a b j N M Q))
    (hN : Derives Γ (proved test w z b N)) (hM : Derives Γ (proved test w z b M)) :
    Derives Γ (proved test w z b Q) := by
  have hctor : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two N M) Q) := .conjL hc
  have htype := ForcingLogicalCode.binary_type 0 R w z a b j N M Q hc
  have ht := Derives.impE (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z b N M Q hw hctor)) htype
  exact conjoin hZ test w z b N M Q hw hz (.conjL (.conjR ht)) (.conjR (.conjR ht)) hctor hN hM

def forcingSentence {n m} (target : Bool) (R : Source.Formula (n+2)) (w z a b j N M Q : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((ForcingLogicalCode.binary 0 R w z a b j N M Q).imp
    ((proved (OriginalAxiomCodeTest.test target) w z b N).imp
      ((proved (OriginalAxiomCodeTest.test target) w z b M).imp
        (proved (OriginalAxiomCodeTest.test target) w z b Q)))))).close

theorem forcing_kernel_certificate {n m} (target : Bool) (R : Source.Formula (n+2)) (w z a b j N M Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (forcingSentence target R w z a b j N M Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact compiled_conjunction
    (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _)
    (OriginalAxiomCodeTest.test target) R w z a b j N M Q
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.InternalProofConjunction
