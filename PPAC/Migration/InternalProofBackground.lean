import PPAC.Migration.InternalProofTemplates
import PPAC.Migration.Internal.FormulaCodeConstructors

/-! A canonical common background B ∧ (x∈y), built by existing original
constructors. It depends only on B/x/y/scopes, not on the current formula.
Original rule13 produces actual internal proofs of its member projection;
neither the background nor the member proposition is assumed proved/true. -/
namespace PPAC.Migration.InternalProofBackground
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open FormulaCodeConstructSyntax (typedAt typedAt_rename)
open InternalProofConjunction (proved proved_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def data {m} (w z b x y B sym E G : Fin m) : Formula m :=
  (formulaCode w B z b).conj ((SyntaxAtomSyntax.zeroScalar w sym).conj
    ((typedAt 3 2 w (SyntaxAtomSyntax.three sym x y) E z b).conj
      (typedAt 2 5 w (SyntaxAtomSyntax.two B E) G z b)))
theorem data_rename {m l} (w z b x y B sym E G : Fin m) (ρ : Fin m → Fin l) :
    (data w z b x y B sym E G).rename ρ = data (ρ w) (ρ z) (ρ b) (ρ x) (ρ y) (ρ B) (ρ sym) (ρ E) (ρ G) := by
  simp only [data, Formula.rename, formulaCode_rename, SyntaxAtomSyntax.zeroScalar_rename,
    typedAt_rename, SyntaxAtomSyntax.three_map, SyntaxAtomSyntax.two_map]
def body {m} (w z b x y B : Fin m) : Formula (m+3) :=
  data (old 3 w) (old 3 z) (old 3 b) (old 3 x) (old 3 y) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2)
def background {m} (w z b x y B : Fin m) : Formula m := existsMany 3 (body w z b x y B)
theorem background_rename {m l} (w z b x y B : Fin m) (ρ : Fin m → Fin l) :
    (background w z b x y B).rename ρ = background (ρ w) (ρ z) (ρ b) (ρ x) (ρ y) (ρ B) := by
  simp only [background, existsMany_rename, body, data_rename, lift_old, lift_slot]

/-- The SAME member and conjunction codes are built entirely within ZF.
No guard/source formula or proof occurs among the constructor inputs. -/
theorem background_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b x y B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (formulaCode w B z b))
    (hx : Derives Γ (SyntaxTermSyntax.term w z b x)) (hy : Derives Γ (SyntaxTermSyntax.term w z b y)) :
    Derives Γ (background w z b x y B) := by
  have hs := FormulaCodeConstructors.membership hZ w z b x y hw hx hy
  let S := (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (FormulaCodeConstructSyntax.typedFiber 3 2 w.castSucc (SyntaxAtomSyntax.three (Fin.last m) x.castSucc y.castSucc) z.castSucc b.castSucc)
  let Δ1 := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) hs
  have hS : Derives Δ1 S := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hZ1 := ZFContext.under hZ S
  have he := FormulaCodeConstruct.exists_of_fiber 3 2 w.castSucc (SyntaxAtomSyntax.three (Fin.last m) x.castSucc y.castSucc) z.castSucc b.castSucc (.conjR hS)
  let E := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (typedAt 3 2 w.castSucc.castSucc (SyntaxAtomSyntax.three (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc)
      (Fin.last (m+1)) z.castSucc.castSucc b.castSucc.castSucc)
  let Δ2 := Context.add E (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E) he
  have hE : Derives Δ2 E := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 E
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 E)
  have hB2 : Derives Δ2 (formulaCode w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, formulaCode_rename]) (under (under hB S) E)
  have hET := Derives.conjR (.conjR hE)
  have hctx := Derives.conjR (FormulaCodeProperties.guards w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc hB2)
  have hg := FormulaCodeConstruct.exists_of_fiber 2 5 w.castSucc.castSucc (SyntaxAtomSyntax.two B.castSucc.castSucc (Fin.last (m+1))) z.castSucc.castSucc b.castSucc.castSucc
    (FormulaCodeConstructors.binary0 hZ2 w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjI hctx (.conjI hB2 hET)))
  let G := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (typedAt 2 5 w.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two B.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc)
      (Fin.last (m+2)) z.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc)
  let Δ3 := Context.add G (Context.image Formula.raise Δ2)
  apply Derives.exE (p := G) hg
  have hG : Derives Δ3 G := .hyp (Or.inl rfl)
  have hB3 : Derives Δ3 (formulaCode (old 3 w) (old 3 B) (old 3 z) (old 3 b)) :=
    of_eq (formulaCode_rename w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc Fin.castSucc) (under hB2 G)
  have hSym3 : Derives Δ3 (SyntaxAtomSyntax.zeroScalar (old 3 w) (slot 3 0)) :=
    of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.zeroScalar_rename]; rfl) (under (under (.conjL hS) E) G)
  have hMem3 : Derives Δ3 (typedAt 3 2 (old 3 w) (SyntaxAtomSyntax.three (slot 3 0) (old 3 x) (old 3 y)) (slot 3 1) (old 3 z) (old 3 b)) :=
    of_eq (by simp only [Formula.raise, typedAt_rename, SyntaxAtomSyntax.three_map]; rfl) (under (.conjR hE) G)
  have hout : Derives Δ3 (background (old 3 w) (old 3 z) (old 3 b) (old 3 x) (old 3 y) (old 3 B)) := by
    apply HornBinderRules.intro_many 3 _ (slot 3)
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl)
      (.conjI hB3 (.conjI hSym3 (.conjI hMem3 (.conjR hG))))
  exact of_eq (by simp only [Formula.raise, background_rename]; rfl) hout

/-- Canonical background uniqueness is independent of the current guard or
source formula. All candidate symbols/member/background codes are internal. -/
theorem background_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b x y B sym E G sym' E' G' : Fin m)
    (hw : Derives Γ (omega w)) (h : Derives Γ (data w z b x y B sym E G))
    (h' : Derives Γ (data w z b x y B sym' E' G')) : Derives Γ (.equal G G') := by
  have hm := Derives.conjL (.conjR (.conjR h))
  have hm' := Derives.conjL (.conjR (.conjR h'))
  have ht := Derives.impE (.conjL (FormulaCodeKnownAtomic.member_iff hZ w z b sym x y E hw (.conjL hm))) (.conjR hm)
  have ht' := Derives.impE (.conjL (FormulaCodeKnownAtomic.member_iff hZ w z b sym' x y E' hw (.conjL hm'))) (.conjR hm')
  have heq := SyntaxAtomUnique.member_same_inputs hZ w z b sym sym' x y E E' hw (.conjI ht (.conjL hm)) (.conjI ht' (.conjL hm'))
  have hc := SyntaxMixedFormulaLogicalSubst.binary_y 0 w B E G E' heq (.conjL (.conjR (.conjR (.conjR h))))
  exact SyntaxConstructors.unique hZ 2 5 w (SyntaxAtomSyntax.two B E') G G' hw hc (.conjL (.conjR (.conjR (.conjR h'))))

def implication {m} (test : Formula 1) (w z b G M : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc M.castSucc) (Fin.last m)).conj
    (proved test w.castSucc z.castSucc b.castSucc (Fin.last m)))
theorem implication_rename {m l} (test : Formula 1) (w z b G M : Fin m) (ρ : Fin m → Fin l) :
    (implication test w z b G M).rename ρ = implication test (ρ w) (ρ z) (ρ b) (ρ G) (ρ M) := by
  simp only [implication, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map,
    proved_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem at_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b x y B sym E G symM M I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (data w z b x y B sym E G))
    (hSymM : Derives Γ (SyntaxAtomSyntax.zeroScalar w symM))
    (hM : Derives Γ (SyntaxAtomSyntax.memberCode w symM x y M))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G M) I)) :
    Derives Γ (proved test w z b I) := by
  have hB := Derives.conjL hd
  have hMem := Derives.conjL (.conjR (.conjR hd))
  have hTypes := Derives.impE (.conjL (FormulaCodeKnownAtomic.member_iff hZ w z b sym x y E hw (.conjL hMem))) (.conjR hMem)
  have hActual : Derives Γ (SyntaxAtomSyntax.memberAt w z b symM x y M) :=
    .conjI (.conjI hSymM (.conjR hTypes)) hM
  have hEq := SyntaxAtomUnique.member_same_inputs hZ w z b symM sym x y M E hw hActual (.conjI hTypes (.conjL hMem))
  have hIE := SyntaxMixedFormulaLogicalSubst.binary_y 2 w G M I E hEq hI
  exact InternalProofTemplates.projection_axiom hZ test true w z b B E G I hw hz hB (.conjR hMem)
    (.conjL (.conjR (.conjR (.conjR hd)))) hIE

/-- Produce an ACTUAL original internal proof of G→M for the actual member
code M, independently of symbol/output candidates. Neither G nor M is proved
as a premise. Both the implication code and proof witness are internal. -/
theorem project_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b x y B sym E G symM M : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (data w z b x y B sym E G))
    (hSymM : Derives Γ (SyntaxAtomSyntax.zeroScalar w symM))
    (hM : Derives Γ (SyntaxAtomSyntax.memberCode w symM x y M)) :
    Derives Γ (implication test w z b G M) := by
  have hGT := Derives.conjR (.conjR (.conjR (.conjR hd)))
  have hGN := Derives.conjL (FormulaCodeProperties.guards w G z b hGT)
  have hMN := ProofTreeConstructorFacts.range hZ 3 2 w M (SyntaxAtomSyntax.three symM x y) hw hM
  have he := SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two G M) hw
    (.conjI hGN (.conjI hMN (.eqRefl w)))
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc M.castSucc) (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hout := at_implication (ZFContext.under hZ Q) test w.castSucc z.castSucc b.castSucc x.castSucc y.castSucc B.castSucc sym.castSucc E.castSucc G.castSucc symM.castSucc M.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (data_rename w z b x y B sym E G Fin.castSucc) (under hd Q))
    (of_eq (SyntaxAtomSyntax.zeroScalar_rename w symM Fin.castSucc) (under hSymM Q))
    (of_eq (SyntaxAtomSyntax.memberCode_rename w symM x y M Fin.castSucc) (under hM Q)) (.conjR hQ)
  have hi : Derives Δ (implication test w.castSucc z.castSucc b.castSucc G.castSucc M.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map,
      proved_rename, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hQ) hout)
  exact of_eq (implication_rename test w z b G M Fin.castSucc).symm hi

end PPAC.Migration.InternalProofBackground
