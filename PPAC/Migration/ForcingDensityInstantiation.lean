import PPAC.Migration.ForcingDensityCode
import PPAC.Migration.ForcingRawModalBody
import PPAC.Migration.NativeProofQuotation

/-! The outer ALL of the original force_of_dense premise is instantiated in
the actual target scope, at the selected condition term. The two guards and
existential tail are read from the same lifted query. -/
namespace PPAC.Migration.ForcingDensityInstantiation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofBackground (implication implication_rename)
open InternalProofConjunction (proved proved_rename)
open NativeProofQuotation (eliminate_objects)

set_option maxRecDepth 16384

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false


/-- Native instantiation and the two actual implication constructors in its
result, with all three subqueries made under the very same native table. -/
def pointData {m} (w z b U p G M O Tail I : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (successor (v 0) z).conj
    ((SyntaxTopFormulaSyntax.instantiateState w z b (v 0) p U (v 1) (v 2) (v 3)).conj
      ((ForcingRawModalBody.outputs w (v 2) (v 3) (v 0) b z b M O Tail I (v 1)).conj
        (implication test w z b G (v 1))))

theorem pointData_rename {m l} (w z b U p G M O Tail I : Fin m) (v : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (pointData w z b U p G M O Tail I v).rename ρ =
      pointData (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) (fun i => ρ (v i)) := by
  simp only [pointData, Formula.rename, successor_rename, SyntaxTopFormulaSyntax.instantiateState_rename,
    ForcingRawModalBody.outputs_rename, implication_rename]

def point {m} (w z b U p G M O Tail I : Fin m) : Formula m :=
  existsMany 4 (pointData (old 4 w) (old 4 z) (old 4 b) (old 4 U) (old 4 p) (old 4 G)
    (old 4 M) (old 4 O) (old 4 Tail) (old 4 I) (slot 4))

theorem point_rename {m l} (w z b U p G M O Tail I : Fin m) (ρ : Fin m → Fin l) :
    (point w z b U p G M O Tail I).rename ρ =
      point (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) := by
  simp only [point, existsMany_rename, pointData_rename, lift_old, lift_slot]

private theorem at_instance_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b U p G M O Tail I C N : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (binaryCode 2 w M I U)) (ho : Derives Γ (binaryCode 2 w O Tail I))
    (hC : Derives Γ (successor C z))
    (hInst : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b C p U N))
    (hp : Derives Γ (implication test w z b G N)) :
    Derives Γ (point w z b U p G M O Tail I) := by
  let out := point w z b U p G M O Tail I
  refine eliminate_objects hZ 2 (fun ρ v =>
    SyntaxTopFormulaSyntax.instantiateState (ρ w) (ρ z) (ρ b) (ρ C) (ρ p) (ρ U) (ρ N) (v 0) (v 1))
    ?_ out ?_
  · exact hInst
  intro l Δ ρ v hZ1 lift hSubst
  have hGuards := ForcingRawModalBody.from_query hZ1 (ρ w) (v 0) (v 1) (ρ C) (ρ b) (ρ z) (ρ b)
    (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ U) (ρ N)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hm))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift ho)) (.conjR hSubst)
  apply of_eq (point_rename w z b U p G M O Tail I ρ).symm
  let fields : Fin 4 → Fin l := Fin.cases (ρ C) (Fin.cases (ρ N) v)
  apply HornBinderRules.intro_many 4 _ fields
  have hd : Derives Δ (pointData (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G)
      (ρ M) (ρ O) (ρ Tail) (ρ I) fields) :=
    .conjI (of_eq (successor_rename _ _ _) (lift hC))
      (.conjI hSubst (.conjI hGuards (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp))))
  exact of_eq (by simp only [pointData_rename, assign_old, assign_slot]) hd

private theorem point_from_proof {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b U p G M O Tail I : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (binaryCode 2 w M I U)) (ho : Derives Γ (binaryCode 2 w O Tail I))
    (hInst : Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G)) :
    Derives Γ (point w z b U p G M O Tail I) := by
  let out := point w z b U p G M O Tail I
  refine eliminate_objects hZ 3 (fun ρ v =>
    (successor (v 0) (ρ z)).conj ((SyntaxTopFormulaSyntax.instantiated (ρ w) (ρ z) (ρ b)
      (v 0) (ρ p) (ρ U) (v 1)).conj ((SyntaxNodeSyntax.constructor 2 7 (ρ w)
        (SyntaxAtomSyntax.two (ρ G) (v 1)) (v 2)).conj (proved test (ρ w) (ρ z) (ρ b) (v 2)))))
    hInst out ?_
  intro l Δ ρ v hZ1 lift hv
  have hp : Derives Δ (implication test (ρ w) (ρ z) (ρ b) (ρ G) (v 1)) := by
    apply Derives.exI (v 2)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjR (.conjR hv))
  exact of_eq (point_rename w z b U p G M O Tail I ρ).symm
    (at_instance_tables hZ1 (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) (v 0) (v 1)
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hm))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift ho)) (.conjL hv) (.conjL (.conjR hv)) hp)

def pointGuardsData {m} (w z A f C b K H U p G M O Tail I : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (ForcingRawModalBody.data w K H A f C b M O Tail I U v).conj
    (point w z b U p G (v 1) (v 2) (v 3) (v 0))

theorem pointGuardsData_rename {m l} (w z A f C b K H U p G M O Tail I : Fin m) (v : Fin 4 → Fin m)
    (ρ : Fin m → Fin l) :
    (pointGuardsData w z A f C b K H U p G M O Tail I v).rename ρ =
      pointGuardsData (ρ w) (ρ z) (ρ A) (ρ f) (ρ C) (ρ b) (ρ K) (ρ H) (ρ U) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) (fun i => ρ (v i)) := by
  simp only [pointGuardsData, Formula.rename, ForcingRawModalBody.data_rename, point_rename]

def pointGuards {m} (w z A f C b K H U p G M O Tail I : Fin m) : Formula m :=
  existsMany 4 (pointGuardsData (old 4 w) (old 4 z) (old 4 A) (old 4 f) (old 4 C) (old 4 b)
    (old 4 K) (old 4 H) (old 4 U) (old 4 p) (old 4 G) (old 4 M) (old 4 O) (old 4 Tail) (old 4 I) (slot 4))

theorem pointGuards_rename {m l} (w z A f C b K H U p G M O Tail I : Fin m) (ρ : Fin m → Fin l) :
    (pointGuards w z A f C b K H U p G M O Tail I).rename ρ =
      pointGuards (ρ w) (ρ z) (ρ A) (ρ f) (ρ C) (ρ b) (ρ K) (ρ H) (ρ U) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) := by
  simp only [pointGuards, existsMany_rename, pointGuardsData_rename, lift_old, lift_slot]

private theorem point_guards {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A f C b K H U p G M O Tail I : Fin m) (hw : Derives Γ (omega w))
    (hInst : Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G))
    (hRaw : Derives Γ (ForcingRawModalBody.outputs w K H A f C b M O Tail I U)) :
    Derives Γ (pointGuards w z A f C b K H U p G M O Tail I) := by
  let out := pointGuards w z A f C b K H U p G M O Tail I
  refine eliminate_objects hZ 4 (fun ρ v => ForcingRawModalBody.data (ρ w) (ρ K) (ρ H) (ρ A)
    (ρ f) (ρ C) (ρ b) (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ U) v) hRaw out ?_
  intro l Δ ρ v hZ1 lift hv
  have hAt := point_from_proof hZ1 (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (v 1) (v 2) (v 3) (v 0)
    (of_eq (omega_rename _ _) (lift hw)) (.conjL (.conjL hv)) (.conjL (.conjR hv))
    (of_eq (InternalProofQuantifier.guardedInstance_rename _ _ _ _ _ _ _ _) (lift hInst))
  apply of_eq (pointGuards_rename w z A f C b K H U p G M O Tail I ρ).symm
  apply HornBinderRules.intro_many 4 _ v
  have hd : Derives Δ (pointGuardsData (ρ w) (ρ z) (ρ A) (ρ f) (ρ C) (ρ b) (ρ K) (ρ H) (ρ U)
      (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) v) := .conjI hv hAt
  exact of_eq (by simp only [pointGuardsData_rename, assign_old, assign_slot]) hd

/-- Actual target body, its two implications in the lifted environment, and
an instance proof under the very same background. -/
def openedData {m} (w z a f b L S E p G M O Tail I X : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (singleCode 9 w (v 0) E).conj
    ((SyntaxCodedMixedBinderSyntax.lifted w L S a f z b (v 1) (v 2) (v 3) (v 4)).conj
      ((substituted w (v 3) (v 4) (v 1) f (v 2) b X (v 0)).conj
        (pointGuards w z (v 1) f (v 2) b (v 3) (v 4) (v 0) p G M O Tail I)))

theorem openedData_rename {m l} (w z a f b L S E p G M O Tail I X : Fin m) (v : Fin 5 → Fin m)
    (ρ : Fin m → Fin l) :
    (openedData w z a f b L S E p G M O Tail I X v).rename ρ =
      openedData (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ L) (ρ S) (ρ E) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ X) (fun i => ρ (v i)) := by
  simp only [openedData, Formula.rename, singleCode_rename, SyntaxCodedMixedBinderSyntax.lifted_rename,
    substituted_rename, pointGuards_rename]

def opened {m} (w z a f b L S E p G M O Tail I X : Fin m) : Formula m :=
  existsMany 5 (openedData (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 b) (old 5 L) (old 5 S)
    (old 5 E) (old 5 p) (old 5 G) (old 5 M) (old 5 O) (old 5 Tail) (old 5 I) (old 5 X) (slot 5))

theorem opened_rename {m l} (w z a f b L S E p G M O Tail I X : Fin m) (ρ : Fin m → Fin l) :
    (opened w z a f b L S E p G M O Tail I X).rename ρ =
      opened (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ L) (ρ S) (ρ E) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ X) := by
  simp only [opened, existsMany_rename, openedData_rename, lift_old, lift_slot]

private theorem guarded_at_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b U E p G : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hE : Derives Γ (formulaCode w E z b)) (hU : Derives Γ (singleCode 9 w U E))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E)) :
    Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G) := by
  let B := (SyntaxNodeSyntax.constructor 2 7 w.castSucc
    (SyntaxAtomSyntax.two G.castSucc E.castSucc) (Fin.last m)).conj
      (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))
  apply Derives.exE (p := B) hp
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (InternalProofQuantifier.guardedInstance_rename test w z b U p G Fin.castSucc).symm
    (InternalProofQuantifier.guarded_instantiate (ZFContext.under hZ B) test w.castSucc z.castSucc b.castSucc
      U.castSucc p.castSucc E.castSucc G.castSucc (Fin.last m)
      (of_eq (omega_rename _ _) (under hw B)) (of_eq (empty_rename _ _) (under hz B))
      (of_eq (formulaCode_rename _ _ _ _ _) (under hE B))
      (of_eq (singleCode_rename _ _ _ _ _) (under hU B))
      (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (under ht B))
      (of_eq (formulaCode_rename _ _ _ _ _) (under hG B)) (.conjL hB) (.conjR hB))

private theorem at_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f b L S E p G M O Tail I X U : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (binaryCode 2 w M I X)) (ho : Derives Γ (binaryCode 2 w O Tail I))
    (hs : Derives Γ (singleCode 9 w U E))
    (hBody : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check true w X L S a f z b U))
    (hInst : Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G)) :
    Derives Γ (opened w z a f b L S E p G M O Tail I X) := by
  let out := opened w z a f b L S E p G M O Tail I X
  refine eliminate_objects hZ 4 (fun r v =>
    (SyntaxCodedMixedBinderSyntax.lifted (r w) (r L) (r S) (r a) (r f) (r z) (r b) (v 0) (v 1) (v 2) (v 3)).conj
      (substituted (r w) (v 2) (v 3) (v 0) (r f) (v 1) (r b) (r X) (r U))) ?_ out ?_
  · exact hBody
  intro l Δ r v hZ1 lift hLift
  have ho2 := ForcingRawModalBody.from_query hZ1 (r w) (v 2) (v 3) (v 0) (r f) (v 1) (r b)
    (r M) (r O) (r Tail) (r I) (r X) (r U) (of_eq (omega_rename _ _) (lift hw))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hm)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift ho))
    (.conjR hLift)
  have hPoint := point_guards hZ1 (r w) (r z) (v 0) (r f) (v 1) (r b) (v 2) (v 3) (r U)
    (r p) (r G) (r M) (r O) (r Tail) (r I) (of_eq (omega_rename _ _) (lift hw))
    (of_eq (InternalProofQuantifier.guardedInstance_rename _ _ _ _ _ _ _ _) (lift hInst)) ho2
  apply of_eq (opened_rename w z a f b L S E p G M O Tail I X r).symm
  let fields : Fin 5 → Fin l := Fin.cases (r U) v
  apply HornBinderRules.intro_many 5 _ fields
  have hd : Derives Δ (openedData (r w) (r z) (r a) (r f) (r b) (r L) (r S) (r E) (r p) (r G)
      (r M) (r O) (r Tail) (r I) (r X) fields) :=
    .conjI (of_eq (singleCode_rename _ _ _ _ _) (lift hs))
      (.conjI (.conjL hLift) (.conjI (.conjR hLift) hPoint))
  exact of_eq (by simp only [openedData_rename, assign_old, assign_slot]) hd

private theorem from_outer {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f b L S D E p G M O Tail I X : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E))
    (hOuter : Derives Γ (ForcingRawModalBody.shell w D M O Tail I X))
    (hQ : Derives Γ (substituted w L S a f z b D E)) :
    Derives Γ (opened w z a f b L S E p G M O Tail I X) := by
  let P := (singleCode 9 w.castSucc (Fin.last m) E.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check true w.castSucc X.castSucc L.castSucc S.castSucc
      a.castSucc f.castSucc z.castSucc b.castSucc (Fin.last m))
  apply Derives.exE (p := P) (ForcingMixedUnary.single_output hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩))
    w L S a f z b D X E hw (.conjL hOuter) hQ)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename _ _) (under hw P)
  have hZ1 := ZFContext.under hZ P
  have hType := SyntaxMixedFormulaJudgment.target_type w L S a f z b D E hQ
  have hI := guarded_at_body hZ1 w.castSucc z.castSucc b.castSucc (Fin.last m) E.castSucc p.castSucc G.castSucc
    hw1 (of_eq (empty_rename _ _) (under hz P)) (of_eq (formulaCode_rename _ _ _ _ _) (under hType P))
    (.conjL hP) (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (under ht P))
    (of_eq (formulaCode_rename _ _ _ _ _) (under hG P)) (of_eq (implication_rename _ _ _ _ _ _ _) (under hp P))
  exact of_eq (opened_rename w z a f b L S E p G M O Tail I X Fin.castSucc).symm
    (at_body hZ1 w.castSucc z.castSucc a.castSucc f.castSucc b.castSucc L.castSucc S.castSucc
      E.castSucc p.castSucc G.castSucc M.castSucc O.castSucc Tail.castSucc I.castSucc X.castSucc
      (Fin.last m) hw1
      (of_eq (binaryCode_rename _ _ _ _ _ _) (under (.conjL (.conjR hOuter)) P))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (under (.conjR (.conjR hOuter)) P))
      (.conjL hP) (.conjR hP) hI)


/-- The outer opened query tied to its actual five shell constructors. -/
def shellInstanceData {m} (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (u : Fin 5 → Fin m) : Formula m :=
  (ForcingDensityCode.shellData w a A B f M O rM rO N D u).conj
    (opened w z a f b L S E p G M O (u 2) (u 3) (u 4))

theorem shellInstanceData_rename {m l} (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (u : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (shellInstanceData w z a A B f b L S D E p G M O rM rO N u).rename ρ =
      shellInstanceData (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S) (ρ D) (ρ E)
        (ρ p) (ρ G) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) (fun i => ρ (u i)) := by
  simp only [shellInstanceData, Formula.rename, ForcingDensityCode.shellData_rename, opened_rename]

def shellInstance {m} (w z a A B f b L S D E p G M O rM rO N : Fin m) : Formula m :=
  existsMany 5 (shellInstanceData (old 5 w) (old 5 z) (old 5 a) (old 5 A) (old 5 B)
    (old 5 f) (old 5 b) (old 5 L) (old 5 S) (old 5 D) (old 5 E) (old 5 p) (old 5 G)
    (old 5 M) (old 5 O) (old 5 rM) (old 5 rO) (old 5 N) (slot 5))

theorem shellInstance_rename {m l} (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (ρ : Fin m → Fin l) :
    (shellInstance w z a A B f b L S D E p G M O rM rO N).rename ρ =
      shellInstance (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S) (ρ D) (ρ E)
        (ρ p) (ρ G) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) := by
  simp only [shellInstance, existsMany_rename, shellInstanceData_rename, lift_old, lift_slot]

private theorem from_shell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E))
    (hc : Derives Γ (ForcingDensityCode.shell w a A B f M O rM rO N D))
    (hq : Derives Γ (substituted w L S a f z b D E)) :
    Derives Γ (shellInstance w z a A B f b L S D E p G M O rM rO N) := by
  let out := shellInstance w z a A B f b L S D E p G M O rM rO N
  refine eliminate_objects hZ 5 (fun ρ u =>
    ForcingDensityCode.shellData (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) (ρ D) u)
    hc out ?_
  intro l Δ ρ u hZ1 lift hs
  have h4 := Derives.conjR (.conjR (.conjR hs))
  have h5 := Derives.conjR h4
  have hOuter : Derives Δ (ForcingRawModalBody.shell (ρ w) (ρ D) (ρ M) (ρ O) (u 2) (u 3) (u 4)) :=
    .conjI (.conjL (.conjR h5)) (.conjI (.conjL (.conjL h5)) (.conjL (.conjL h4)))
  have hOpen := from_outer hZ1 (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ L) (ρ S) (ρ D) (ρ E) (ρ p) (ρ G)
    (ρ M) (ρ O) (u 2) (u 3) (u 4)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp))
    hOuter (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hq))
  apply of_eq (shellInstance_rename w z a A B f b L S D E p G M O rM rO N ρ).symm
  apply HornBinderRules.intro_many 5 _ u
  have ho : Derives Δ (shellInstanceData (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S)
    (ρ D) (ρ E) (ρ p) (ρ G) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) u) := .conjI hs hOpen
  exact of_eq (by simp only [shellInstanceData_rename, assign_old, assign_slot]) ho

def instanceData {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m)
    (v : Fin 7 → Fin m) : Formula m :=
  (ForcingDensityCode.data Reln w a A B f j N D v).conj
    (shellInstance w z a A B f b L S D E p G (v 2) (v 3) (v 4) (v 5) (v 6))

theorem instanceData_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m)
    (v : Fin 7 → Fin m) (ρ : Fin m → Fin l) :
    (instanceData Reln w z a A B f j N b L S D E p G v).rename ρ =
      instanceData Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N)
        (ρ b) (ρ L) (ρ S) (ρ D) (ρ E) (ρ p) (ρ G) (fun i => ρ (v i)) := by
  simp only [instanceData, Formula.rename, ForcingDensityCode.data_rename, shellInstance_rename]

def instanceAt {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m) : Formula m :=
  existsMany 7 (instanceData Reln (old 7 w) (old 7 z) (old 7 a) (old 7 A) (old 7 B) (old 7 f)
    (old 7 j) (old 7 N) (old 7 b) (old 7 L) (old 7 S) (old 7 D) (old 7 E) (old 7 p) (old 7 G) (slot 7))

theorem instanceAt_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m)
    (ρ : Fin m → Fin l) :
    (instanceAt Reln w z a A B f j N b L S D E p G).rename ρ =
      instanceAt Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ L) (ρ S) (ρ D)
        (ρ E) (ρ p) (ρ G) := by
  simp only [instanceAt, existsMany_rename, instanceData_rename, lift_old, lift_slot]

/-- Open the actual density query and instantiate its proof under G. The
compiler, guard outputs and instance all refer to the same original query. -/
theorem from_query {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (n+2))
    (w z a A B f j N b L S D E p G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E))
    (hq : Derives Γ (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E)) :
    Derives Γ (instanceAt Reln w z a A B f j N b L S D E p G) := by
  let out := instanceAt Reln w z a A B f j N b L S D E p G
  refine eliminate_objects hZ 7 (fun ρ v => ForcingDensityCode.data Reln (ρ w) (ρ a) (ρ A) (ρ B)
    (ρ f) (ρ j) (ρ N) (ρ D) v) (.conjL hq) out ?_
  intro l Δ ρ v hZ1 lift hc
  have hShell := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hc)))))
  have hOpen := from_shell hZ1 (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S)
    (ρ D) (ρ E) (ρ p) (ρ G) (v 2) (v 3) (v 4) (v 5) (v 6)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp))
    hShell (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift (.conjR hq)))
  apply of_eq (instanceAt_rename Reln w z a A B f j N b L S D E p G ρ).symm
  apply HornBinderRules.intro_many 7 _ v
  have ho : Derives Δ (instanceData Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N)
    (ρ b) (ρ L) (ρ S) (ρ D) (ρ E) (ρ p) (ρ G) v) := .conjI hc hOpen
  exact of_eq (by simp only [instanceData_rename, assign_old, assign_slot]) ho


open StructuralListFieldSyntax (field field_rename)

def selectedData {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G p : Fin m) : Formula m :=
  (field w S j p).conj (instanceAt Reln w z a A B f j N b L S D E p G)

theorem selectedData_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G p : Fin m)
    (ρ : Fin m → Fin l) :
    (selectedData Reln w z a A B f j N b L S D E G p).rename ρ =
      selectedData Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ L)
        (ρ S) (ρ D) (ρ E) (ρ G) (ρ p) := by
  simp only [selectedData, Formula.rename, field_rename, instanceAt_rename]

def selected {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) : Formula m :=
  .ex (selectedData Reln w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc
    N.castSucc b.castSucc L.castSucc S.castSucc D.castSucc E.castSucc G.castSucc (Fin.last m))

theorem selected_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m)
    (ρ : Fin m → Fin l) :
    (selected Reln w z a A B f j N b L S D E G).rename ρ =
      selected Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ L) (ρ S)
        (ρ D) (ρ E) (ρ G) := by
  simp only [selected, Formula.rename, selectedData_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Use the actual condition image of slot j in the same mixed query. No
instance term, formula, guard result or proof output is supplied. -/
theorem from_condition_slot {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (n+2))
    (w z a A B f j N b L S D E G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hj : Derives Γ (.mem j f))
    (hG : Derives Γ (formulaCode w G z b)) (hp : Derives Γ (implication test w z b G E))
    (hq : Derives Γ (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E)) :
    Derives Γ (selected Reln w z a A B f j N b L S D E G) := by
  have hi := SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w L S a f z b D E hw (.conjR hq)
  have hf := Derives.conjR (Derives.conjL hi)
  have hjw := StructuralListTraceOrder.member_member hZ w j f hw (.conjL hf) hj
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc S.castSucc j.castSucc (Fin.last m))
  apply Derives.exE (p := P) (StructuralListFieldValues.exists_value hZ w S j hw hjw)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hf1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z b S Fin.castSucc) (under hf P)
  have ht := SyntaxMixedImageCodeFields.field_type w.castSucc f.castSucc z.castSucc b.castSucc S.castSucc
    j.castSucc (Fin.last m) hf1 (under hj P) (.conjR hP)
  have inst := from_query (ZFContext.under hZ P) Reln w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc
    f.castSucc j.castSucc N.castSucc b.castSucc L.castSucc S.castSucc D.castSucc E.castSucc (Fin.last m) G.castSucc
    (of_eq (omega_rename _ _) (under hw P)) (of_eq (empty_rename _ _) (under hz P)) ht
    (of_eq (formulaCode_rename _ _ _ _ _) (under hG P)) (of_eq (implication_rename _ _ _ _ _ _ _) (under hp P))
    (of_eq (ForcingDensityCode.queryData_rename Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _) (under hq P))
  simp only [Formula.raise, selected_rename]
  apply Derives.exI (Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, selectedData_rename, Fin.lastCases_last,
    Fin.lastCases_castSucc, id_eq]; rfl) (.conjI (.conjR hP) inst)

def input {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((Formula.mem j f).conj ((formulaCode w G z b).conj
    ((implication test w z b G E).conj (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E)))))

def sentence {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) : Source.Sentence :=
  ((input Reln w z a A B f j N b L S D E G).imp (selected Reln w z a A B f j N b L S D E G)).close

theorem kernel_certificate {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence
      (sentence Reln w z a A B f j N b L S D E G)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let P := input Reln w z a A B f j N b L S D E G
  have h : Derives (Context.add P (SetLanguage.ZF.at m)) P := .hyp (Or.inl rfl)
  have h2 := Derives.conjR h
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  have h5 := Derives.conjR h4
  exact from_condition_slot (ZFContext.add (ZFContext.source_ZF m) P) Reln w z a A B f j N b L S D E G
    (.conjL h) (.conjL h2) (.conjL h3) (.conjL h4) (.conjL h5) (.conjR h5)


/-- Read the complete point record of one actual density instance. Every
constructor, table, guard and tail remains an output of that instance. -/
theorem with_instance_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (w z a A B f j N b L S D E p G : Fin m)
    (hi : Derives Γ (instanceAt Reln w z a A B f j N b L S D E p G))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l)
      (d : Fin 7 → Fin l) (s o : Fin 5 → Fin l) (u v x : Fin 4 → Fin l),
      ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingDensityCode.data Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) d) →
      Derives Δ (ForcingDensityCode.shellData (r w) (r a) (r A) (r B) (r f)
        (d 2) (d 3) (d 4) (d 5) (d 6) (r D) s) →
      Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (r w) (r L) (r S) (r a) (r f) (r z) (r b)
        (o 1) (o 2) (o 3) (o 4)) →
      Derives Δ (ForcingRawModalBody.data (r w) (o 3) (o 4) (o 1) (r f) (o 2) (r b)
        (d 2) (d 3) (s 2) (s 3) (o 0) u) →
      Derives Δ (pointData (r w) (r z) (r b) (o 0) (r p) (r G) (u 1) (u 2) (u 3) (u 0) v) →
      Derives Δ (ForcingRawModalBody.data (r w) (v 2) (v 3) (v 0) (r b) (r z) (r b)
        (u 1) (u 2) (u 3) (u 0) (v 1) x) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  refine eliminate_objects hZ 7 (fun r d => instanceData Reln (r w) (r z) (r a) (r A) (r B) (r f)
    (r j) (r N) (r b) (r L) (r S) (r D) (r E) (r p) (r G) d) hi out ?_
  intro l Δ r d hZ1 lift hd
  refine eliminate_objects hZ1 5 (fun s u => shellInstanceData (s (r w)) (s (r z)) (s (r a)) (s (r A)) (s (r B))
    (s (r f)) (s (r b)) (s (r L)) (s (r S)) (s (r D)) (s (r E)) (s (r p)) (s (r G))
    (s (d 2)) (s (d 3)) (s (d 4)) (s (d 5)) (s (d 6)) u) (.conjR hd) (out.rename r) ?_
  intro l1 Δ1 s u hZ2 lift1 hs
  let R := s ∘ r
  let ds := s ∘ d
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hData := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ d s) (lift1 (.conjL hd))
  refine of_eq (SourceAlgebra.rename_comp out r s).symm ?_
  refine eliminate_objects hZ2 5 (fun t o => openedData (t (R w)) (t (R z)) (t (R a)) (t (R f)) (t (R b))
    (t (R L)) (t (R S)) (t (R E)) (t (R p)) (t (R G)) (t (ds 2)) (t (ds 3))
    (t (u 2)) (t (u 3)) (t (u 4)) o) (.conjR hs) (out.rename R) ?_
  intro l2 Δ2 t o hZ3 lift2 ho
  let Q := t ∘ R
  let dt := t ∘ ds
  let ut := t ∘ u
  have move2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename Q) :=
    of_eq (SourceAlgebra.rename_comp F R t) (lift2 (move h))
  have hData2 := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ ds t) (lift2 hData)
  have hShell := of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ u t) (lift2 (.conjL hs))
  have hLift := Derives.conjL (.conjR ho)
  refine of_eq (SourceAlgebra.rename_comp out R t).symm ?_
  refine eliminate_objects hZ3 4 (fun e y => pointGuardsData (e (Q w)) (e (Q z)) (e (o 1)) (e (Q f)) (e (o 2))
    (e (Q b)) (e (o 3)) (e (o 4)) (e (o 0)) (e (Q p)) (e (Q G)) (e (dt 2)) (e (dt 3)) (e (ut 2)) (e (ut 3)) y)
    (.conjR (.conjR (.conjR ho))) (out.rename Q) ?_
  intro l3 Δ3 e y hZ4 lift3 hy
  let T := e ∘ Q
  let de := e ∘ dt
  let ue := e ∘ ut
  let oe := e ∘ o
  have move3 {F : Formula m} (h : Derives Γ F) : Derives Δ3 (F.rename T) :=
    of_eq (SourceAlgebra.rename_comp F Q e) (lift3 (move2 h))
  have hData3 := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ dt e) (lift3 hData2)
  have hShell3 := of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ ut e) (lift3 hShell)
  have hLift3 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ e) (lift3 hLift)
  refine of_eq (SourceAlgebra.rename_comp out Q e).symm ?_
  refine eliminate_objects hZ4 4 (fun h v => pointData (h (T w)) (h (T z)) (h (T b)) (h (oe 0))
    (h (T p)) (h (T G)) (h (y 1)) (h (y 2)) (h (y 3)) (h (y 0)) v)
    (.conjR hy) (out.rename T) ?_
  intro l4 Δ4 h v hZ5 lift4 hv
  let P := h ∘ T
  let dh := h ∘ de
  let uh := h ∘ ue
  let oh := h ∘ oe
  let yh := h ∘ y
  have move4 {F : Formula m} (hp : Derives Γ F) : Derives Δ4 (F.rename P) :=
    of_eq (SourceAlgebra.rename_comp F T h) (lift4 (move3 hp))
  have hData4 := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ de h) (lift4 hData3)
  have hShell4 := of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ ue h) (lift4 hShell3)
  have hLift4 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ h) (lift4 hLift3)
  have hRaw4 := of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ y h) (lift4 (.conjL hy))
  refine of_eq (SourceAlgebra.rename_comp out T h).symm ?_
  refine eliminate_objects hZ5 4 (fun i x => ForcingRawModalBody.data (i (P w)) (i (v 2)) (i (v 3))
    (i (v 0)) (i (P b)) (i (P z)) (i (P b)) (i (yh 1)) (i (yh 2)) (i (yh 3)) (i (yh 0)) (i (v 1)) x)
    (.conjL (.conjR (.conjR hv))) (out.rename P) ?_
  intro l5 Δ5 i x hZ6 lift5 hx
  let F := i ∘ P
  have move5 {U : Formula m} (hp : Derives Γ U) : Derives Δ5 (U.rename F) :=
    of_eq (SourceAlgebra.rename_comp U P i) (lift5 (move4 hp))
  exact of_eq (SourceAlgebra.rename_comp out P i).symm
    (use F (i ∘ dh) (i ∘ uh) (i ∘ oh) (i ∘ yh) (i ∘ v) x hZ6 move5
      (of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ dh i) (lift5 hData4))
      (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ uh i) (lift5 hShell4))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ i) (lift5 hLift4))
      (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ yh i) (lift5 hRaw4))
      (of_eq (pointData_rename _ _ _ _ _ _ _ _ _ _ v i) (lift5 hv)) hx)

end PPAC.Migration.ForcingDensityInstantiation
