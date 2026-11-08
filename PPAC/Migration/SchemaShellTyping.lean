/- Type the exact ORIGINAL finite Separation/Collection shells over arbitrary
INTERNAL parameter counts. The finite proof schemes below build Source.Derives;
the external indices range only over the fixed shell, never over the input count. -/
import PPAC.Migration.SchemaClosureTyping
import PPAC.Migration.Internal.HornExprConstructor
import PPAC.Migration.Internal.NaturalOrderBasic

namespace PPAC.Migration.SchemaShellTyping
open Source SourceAlgebra SourceLogic OmegaSyntax
open PPAC.Migration.Internal
open PPAC.Migration.Internal.HornExprSyntax
open PPAC.Migration.Internal.SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def boundLaw {m} (k : Nat) (b : Fin m) : Source.Formula m := .all
  ((SyntaxNumeralSyntax.numeral k (Fin.last m)).imp (Source.Formula.mem (Fin.last m) b.castSucc))

private theorem boundLaw_rename {m l} (k : Nat) (b : Fin m) (r : Fin m → Fin l) :
    (boundLaw k b).rename r = boundLaw k (r b) := by
  simp only [boundLaw,Formula.rename,SyntaxNumeralSyntax.numeral_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

private theorem bound_at {m} {Γ : Context m} (k : Nat) (b i : Fin m)
    (h : Derives Γ (boundLaw k b)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) : Derives Γ (Source.Formula.mem i b) := by
  have hh := Derives.allE i h
  have hs : Derives Γ ((SyntaxNumeralSyntax.numeral k i).imp (Source.Formula.mem i b)) := of_eq
    (by simp only [Formula.instantiate,Formula.rename,SyntaxNumeralSyntax.numeral_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hh
  exact .impE hs hi

private def scopeLevels {m} (n : Fin m) (scopes : Fin 4 → Fin m) : Fin 5 → Fin m := Fin.cases n scopes

/-- Original Separation hole; Collection premise/image holes keep their exact scopes. -/
def matrixScope {m} (collection : Bool) (scopes : Fin 4 → Fin m) (i : Fin 3) : Fin m :=
  if collection then (if i.val = 0 then scopes 2 else scopes 3) else scopes 2

theorem matrixScope_map {m l} (collection : Bool) (scopes : Fin 4 → Fin m) (i : Fin 3) (r : Fin m → Fin l) :
    matrixScope collection (fun j => r (scopes j)) i = r (matrixScope collection scopes i) := by
  cases collection
  · rfl
  · by_cases hi : i.val = 0 <;> simp only [matrixScope,↓reduceIte,hi]

private def holeDepth (collection : Bool) (i : Fin 3) : Fin 5 := if collection then (if i.val = 0 then 3 else 4) else 3

/-- A finite bundle of ORIGINAL object premises, not new predicate axioms. -/
private structure Frame {m} (Γ : Context m) (collection : Bool) (w z : Fin m)
    (levels : Fin 5 → Fin m) (env : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (OmegaSyntax.omega w)
  zero : Derives Γ (empty z)
  natural : ∀ i, Derives Γ (Source.Formula.mem (levels i) w)
  successor : ∀ i : Fin 4, Derives Γ (OmegaSyntax.successor (levels i.succ) (levels i.castSucc))
  inputs : Derives Γ (environmentNat 3 w env)
  hole : ∀ i, Derives Γ (FormulaCodeSyntax.formulaCode w (env i) (levels (holeDepth collection i)) z)
  bound : ∀ (k : Fin 3) (d : Fin 5), k.val < d.val → Derives Γ (boundLaw k.val (levels d))

private theorem Frame.under {m} {Γ : Context m} {collection : Bool} {w z : Fin m}
    {levels : Fin 5 → Fin m} {env : Fin 3 → Fin m} (h : Frame Γ collection w z levels env) (P : Source.Formula (m+1)) :
    Frame (Context.add P (Context.image Formula.raise Γ)) collection w.castSucc z.castSucc
      (fun i => (levels i).castSucc) (fun i => (env i).castSucc) where
  zf := ZFContext.under h.zf P
  omega := of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.omega P)
  zero := of_eq (empty_rename z Fin.castSucc) (SourceLogic.under h.zero P)
  natural i := SourceLogic.under (h.natural i) P
  successor i := of_eq (successor_rename _ _ Fin.castSucc) (SourceLogic.under (h.successor i) P)
  inputs := of_eq (environmentNat_rename 3 w env Fin.castSucc) (SourceLogic.under h.inputs P)
  hole i := of_eq (FormulaCodeSyntax.formulaCode_rename _ _ _ _ Fin.castSucc) (SourceLogic.under (h.hole i) P)
  bound k d hlt := of_eq (boundLaw_rename _ _ Fin.castSucc) (SourceLogic.under (h.bound k d hlt) P)

private theorem Frame.contexts {m} {Γ : Context m} {collection : Bool} {w z : Fin m}
    {levels : Fin 5 → Fin m} {env : Fin 3 → Fin m} (h : Frame Γ collection w z levels env) (d : Fin 5) :
    Derives Γ (SyntaxTermSyntax.contexts w (levels d) z) :=
  .conjI (h.natural d) (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic h.zf).base.extensionality h.omega h.zero)

private def Typed (collection : Bool) (e : Expr 3) (d : Fin 5) : Prop :=
  ∀ {m} {Γ : Context m} (w z : Fin m) (levels : Fin 5 → Fin m) (env : Fin 3 → Fin m) (out : Fin m),
    Frame Γ collection w z levels env → Derives Γ (graph e w env out) →
      Derives Γ (FormulaCodeSyntax.formulaCode w out (levels d) z)

private def boundExpr (k : Nat) : Expr 3 := .node (.literal 0) [.node (.literal k) []]
private def memberExpr (i j : Nat) : Expr 3 := .node (.literal 2) [(.node (.literal 0) []),boundExpr i,boundExpr j]

private theorem leaf_scalar {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w i s : Fin m)
    (env : Fin 3 → Fin m) (hw : Derives Γ (omega w)) (henv : Derives Γ (environmentNat 3 w env))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hs : Derives Γ (graph (Expr.node (.literal k) []) w env s)) :
    Derives Γ (SyntaxNodeSyntax.scalar w i s) := by
  have hc : Derives Γ (SyntaxNodeSyntax.constructor 0 k w Fin.elim0 s) :=
    .impE (.conjL (HornExprConstructor.constructor_iff hZ 0 k Fin.elim0 w s env Fin.elim0 hw henv (fun j => Fin.elim0 j))) hs
  let C := SyntaxNodeSyntax.constructorBody 0 k w Fin.elim0 s
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_constructor 0 k w Fin.elim0 s _ hc
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := SyntaxNumerals.unique (ZFContext.under hZ C) k (Fin.last m) i.castSucc (.conjL hC)
    (of_eq (SyntaxNumeralSyntax.numeral_rename k i Fin.castSucc) (under hi C))
  have hn : Derives Δ (SyntaxNodeSyntax.node 0 w.castSucc (Fin.last m) Fin.elim0 s.castSucc) := by
    simpa only [SyntaxAtomSyntax.zero_map] using Derives.conjR hC
  have hout := SyntaxNodeSyntax.tag_subst 0 w.castSucc (Fin.last m) i.castSucc Fin.elim0 s.castSucc he hn
  exact of_eq (by simp only [Formula.raise,SyntaxNodeSyntax.scalar,SyntaxNodeSyntax.node_rename,SyntaxAtomSyntax.zero_map]) hout

private theorem term_typed {m} {Γ : Context m} (collection : Bool) (k : Fin 3) (d : Fin 5) (hlt : k.val < d.val)
    (w z : Fin m) (levels : Fin 5 → Fin m) (env : Fin 3 → Fin m) (out : Fin m)
    (hf : Frame Γ collection w z levels env) (hg : Derives Γ (graph (boundExpr k.val) w env out)) :
    Derives Γ (SyntaxTermSyntax.term w (levels d) z out) := by
  let I := (Source.Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral k.val (Fin.last m))
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) (SyntaxNumerals.exists_numeral hf.zf k.val w hf.omega)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hf1 := hf.under I
  let S := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (graph (Expr.node (.literal k.val) []) w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (Fin.last (m+1)))
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (HornExprExistence.exists_value hf1.zf (Expr.node (.literal k.val) []) w.castSucc
    (fun j => (env j).castSucc) hf1.omega hf1.inputs)
  have hf2 := hf1.under S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hi2 : Derives Ξ (SyntaxNumeralSyntax.numeral k.val (Fin.last m).castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (.conjR hI) S)
  have hg2 : Derives Ξ (graph (boundExpr k.val) w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) out.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,graph_rename]) (under (under hg I) S)
  have hs := leaf_scalar hf2.zf k.val w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (fun j => (env j).castSucc.castSucc) hf2.omega hf2.inputs hi2 (.conjR hS)
  have hc : Derives Ξ (SyntaxNodeSyntax.constructor 1 0 w.castSucc.castSucc (fun _ => Fin.last (m+1)) out.castSucc.castSucc) :=
    .impE (.conjL (HornExprConstructor.constructor_iff hf2.zf 1 0 (fun _ => Expr.node (.literal k.val) [])
      w.castSucc.castSucc out.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (fun _ => Fin.last (m+1))
      hf2.omega hf2.inputs (fun _ => .conjR hS))) hg2
  have hv := SyntaxVariableSyntax.intro_code true _ _ _ _ hs hc
  have ht := SyntaxTermSyntax.intro_term true w.castSucc.castSucc (levels d).castSucc.castSucc z.castSucc.castSucc out.castSucc.castSucc
    (Fin.last m).castSucc (.conjI (hf2.contexts d) (bound_at _ _ _ (hf2.bound k d hlt) hi2)) hv
  exact of_eq (by simp only [Formula.raise,SyntaxTermSyntax.term_rename]) ht

private theorem hole_typed (collection : Bool) (i : Fin 3) : Typed collection (.var i) (holeDepth collection i) := by
  intro m Γ w z levels env out hf hg
  exact FormulaCodeTransport.code_root w (env i) (levels (holeDepth collection i)) z out (eq_symm (.conjR hg)) (hf.hole i)

private theorem binary_typed (collection : Bool) (kind : Fin 4) (left right : Expr 3) (d : Fin 5)
    (hl : Typed collection left d) (hr : Typed collection right d) :
    Typed collection (.node (.literal (SyntaxLogicalSyntax.binaryTag kind)) [left,right]) d := by
  intro m Γ w z levels env out hf hg
  let X := (Source.Formula.mem (Fin.last m) w.castSucc).conj (graph left w.castSucc (fun j => (env j).castSucc) (Fin.last m))
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) (HornExprExistence.exists_value hf.zf left w env hf.omega hf.inputs)
  have hf1 := hf.under X
  let Y := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (graph right w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) (HornExprExistence.exists_value hf1.zf right w.castSucc (fun j => (env j).castSucc) hf1.omega hf1.inputs)
  have hf2 := hf1.under Y
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hleft : Derives Ξ (graph left w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (Fin.last m).castSucc) :=
    of_eq (graph_rename _ _ _ _ Fin.castSucc) (under (.conjR hX) Y)
  have hgraph : Derives Ξ (graph (.node (.literal (SyntaxLogicalSyntax.binaryTag kind)) [left,right])
      w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) out.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,graph_rename]) (under (under hg X) Y)
  let es : Fin 2 → Expr 3 := Fin.cases left (fun _ => right)
  let xs := Source.SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1))
  have hs (i : Fin 2) : Derives Ξ (graph (es i) w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (xs i)) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hleft
    · have hj : j = 0 := Fin.ext (by omega)
      subst j
      exact .conjR hY
  have hc : Derives Ξ (SyntaxNodeSyntax.constructor 2 (SyntaxLogicalSyntax.binaryTag kind) w.castSucc.castSucc xs out.castSucc.castSucc) :=
    .impE (.conjL (HornExprConstructor.constructor_iff hf2.zf 2 (SyntaxLogicalSyntax.binaryTag kind) es _ _ _ xs hf2.omega hf2.inputs hs)) hgraph
  have hlt := hl _ _ _ _ _ hf2 hleft
  have hrt := hr _ _ _ _ _ hf2 (.conjR hY)
  have law : Derives Ξ ((FormulaCodeSyntax.formulaCode w.castSucc.castSucc out.castSucc.castSucc (levels d).castSucc.castSucc z.castSucc.castSucc).iff
      (FormulaCodeBranchSyntax.binaryTypes w.castSucc.castSucc (levels d).castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))) := by
    have cases : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact FormulaCodeKnownLogical.binary0_iff hf2.zf _ _ _ _ _ _ hf2.omega hc
    · exact FormulaCodeKnownLogical.binary1_iff hf2.zf _ _ _ _ _ _ hf2.omega hc
    · exact FormulaCodeKnownLogical.binary2_iff hf2.zf _ _ _ _ _ _ hf2.omega hc
    · exact FormulaCodeKnownLogical.binary3_iff hf2.zf _ _ _ _ _ _ hf2.omega hc
  have ht := Derives.impE (.conjR law) (.conjI (hf2.contexts d) (.conjI hlt hrt))
  exact of_eq (by simp only [Formula.raise,FormulaCodeSyntax.formulaCode_rename]) ht

private theorem quantified_typed (collection : Bool) (universal : Bool) (e : Expr 3) (d : Fin 4)
    (he : Typed collection e d.succ) : Typed collection (.node (.literal (SyntaxLogicalSyntax.quantifierTag universal)) [e]) d.castSucc := by
  intro m Γ w z levels env out hf hg
  let X := (Source.Formula.mem (Fin.last m) w.castSucc).conj (graph e w.castSucc (fun j => (env j).castSucc) (Fin.last m))
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) (HornExprExistence.exists_value hf.zf e w env hf.omega hf.inputs)
  have hf1 := hf.under X
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hg1 : Derives Δ (graph (.node (.literal (SyntaxLogicalSyntax.quantifierTag universal)) [e]) w.castSucc
      (fun j => (env j).castSucc) out.castSucc) := of_eq (graph_rename _ _ _ _ Fin.castSucc) (under hg X)
  have hc : Derives Δ (SyntaxNodeSyntax.constructor 1 (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc (fun _ => Fin.last m) out.castSucc) :=
    .impE (.conjL (HornExprConstructor.constructor_iff hf1.zf 1 (SyntaxLogicalSyntax.quantifierTag universal) (fun _ => e)
      _ _ _ (fun _ => Fin.last m) hf1.omega hf1.inputs (fun _ => .conjR hX))) hg1
  have law := FormulaCodeKnownLogical.quantified_iff hf1.zf universal w.castSucc (levels d.castSucc).castSucc z.castSucc
    (Fin.last m) out.castSucc (levels d.succ).castSucc hf1.omega hc (hf1.successor d)
  have ht := Derives.impE (.conjR law) (.conjI (hf1.contexts d.castSucc) (he _ _ _ _ _ hf1 (.conjR hX)))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename _ _ _ _ Fin.castSucc).symm ht


private theorem member_typed (collection : Bool) (i j : Fin 3) (d : Fin 5) (hi : i.val < d.val) (hj : j.val < d.val) :
    Typed collection (memberExpr i.val j.val) d := by
  intro m Γ w z levels env out hf hg
  let S := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    (graph (Expr.node (.literal 0) []) w.castSucc (fun q => (env q).castSucc) (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (HornExprExistence.exists_value hf.zf (Expr.node (.literal 0) []) w env hf.omega hf.inputs)
  have hf1 := hf.under S
  let X := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (graph (boundExpr i.val) w.castSucc.castSucc (fun q => (env q).castSucc.castSucc) (Fin.last (m+1)))
  let Ξ := Context.add X (Context.image Formula.raise Δ)
  apply Derives.exE (p := X) (HornExprExistence.exists_value hf1.zf (boundExpr i.val) w.castSucc (fun q => (env q).castSucc) hf1.omega hf1.inputs)
  have hf2 := hf1.under X
  let Y := (Source.Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (graph (boundExpr j.val) w.castSucc.castSucc.castSucc (fun q => (env q).castSucc.castSucc.castSucc) (Fin.last (m+2)))
  let Ω := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) (HornExprExistence.exists_value hf2.zf (boundExpr j.val) w.castSucc.castSucc
    (fun q => (env q).castSucc.castSucc) hf2.omega hf2.inputs)
  have hf3 := hf2.under Y
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hY : Derives Ω Y := .hyp (Or.inl rfl)
  have hs3 : Derives Ω (graph (Expr.node (.literal 0) []) w.castSucc.castSucc.castSucc
      (fun q => (env q).castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,graph_rename]) (under (under (.conjR hS) X) Y)
  have hx3 : Derives Ω (graph (boundExpr i.val) w.castSucc.castSucc.castSucc
      (fun q => (env q).castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc) :=
    of_eq (graph_rename _ _ _ _ Fin.castSucc) (under (.conjR hX) Y)
  have hg3 : Derives Ω (graph (memberExpr i.val j.val) w.castSucc.castSucc.castSucc
      (fun q => (env q).castSucc.castSucc.castSucc) out.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,graph_rename]) (under (under (under hg S) X) Y)
  let es : Fin 3 → Expr 3 := Fin.cases (Expr.node (.literal 0) []) (Fin.cases (boundExpr i.val) (fun _ => boundExpr j.val))
  let xs := Source.SetLanguage.args3 (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
  have hfields (q : Fin 3) : Derives Ω (graph (es q) w.castSucc.castSucc.castSucc
      (fun q => (env q).castSucc.castSucc.castSucc) (xs q)) := by
    have hq : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hq with rfl | rfl | rfl
    · exact hs3
    · exact hx3
    · exact .conjR hY
  have hc : Derives Ω (SyntaxNodeSyntax.constructor 3 2 w.castSucc.castSucc.castSucc xs out.castSucc.castSucc.castSucc) :=
    .impE (.conjL (HornExprConstructor.constructor_iff hf3.zf 3 2 es _ _ _ xs hf3.omega hf3.inputs hfields)) hg3
  have hzero : Derives Ω (SyntaxNodeSyntax.constructor 0 0 w.castSucc.castSucc.castSucc Fin.elim0 (Fin.last m).castSucc.castSucc) :=
    .impE (.conjL (HornExprConstructor.constructor_iff hf3.zf 0 0 Fin.elim0 _ _ _ Fin.elim0 hf3.omega hf3.inputs (fun q => Fin.elim0 q))) hs3
  have hti := term_typed collection i d hi _ _ _ _ _ hf3 hx3
  have htj := term_typed collection j d hj _ _ _ _ _ hf3 (.conjR hY)
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.member_iff hf3.zf w.castSucc.castSucc.castSucc
    (levels d).castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
    (Fin.last (m+2)) out.castSucc.castSucc.castSucc hf3.omega hc)) (.conjI hzero (.conjI hti htj))
  exact of_eq (by simp only [Formula.raise,FormulaCodeSyntax.formulaCode_rename]) ht

private theorem bound_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (Source.Formula.mem a w)) (hb : Derives Γ (successor b a)) :
    Derives Γ (boundLaw 0 b) := by
  apply Derives.allI
  apply Derives.impI
  let Z := empty (Fin.last m)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ Z
  have hz : Derives Δ Z := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hb1 := of_eq (successor_rename b a Fin.castSucc) (under hb Z)
  have hiW := OmegaStructureAlgebra.zero_member w.castSucc (Fin.last m) (ZFContext.arithmetic hZ1).base.extensionality hw1 hz
  have ho := NaturalOrderBasic.ordinal hZ1 _ _ hw1 hiW
  have hao := NaturalOrderBasic.ordinal hZ1 _ _ hw1 (under ha Z)
  have hle := Derives.impE (.conjL (OrdinalComparison.subset_iff (Fin.last m) a.castSucc
    (ZFContext.arithmetic hZ1).base.extensionality (ZFContext.arithmetic hZ1).base.foundation
    (ZFContext.separation hZ1 OrdinalDifference.outsideMatrix) ho hao)) (OmegaElementary.empty_subset _ _ hz)
  exact NaturalOrderBasic.below_successor _ _ _ hb1 hle

private theorem bound_up {m} {Γ : Context m} (k : Nat) (a b : Fin m)
    (ha : Derives Γ (boundLaw k a)) (hb : Derives Γ (successor b a)) : Derives Γ (boundLaw k b) := by
  apply Derives.allI
  apply Derives.impI
  let P := SyntaxNumeralSyntax.numeral k (Fin.last m)
  have ha1 := of_eq (boundLaw_rename k a Fin.castSucc) (under ha P)
  have hb1 := of_eq (successor_rename b a Fin.castSucc) (under hb P)
  exact InsertLogic.old_member b.castSucc a.castSucc a.castSucc (Fin.last m) hb1 (bound_at _ _ _ ha1 (.hyp (Or.inl rfl)))

private theorem bound_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (haW : Derives Γ (Source.Formula.mem a w))
    (ha : Derives Γ (boundLaw k a)) (hb : Derives Γ (successor b a)) : Derives Γ (boundLaw (k+1) b) := by
  apply Derives.allI
  apply Derives.impI
  let N := SyntaxNumeralSyntax.numeral (k+1) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  let P := (SyntaxNumeralSyntax.numeral k (Fin.last (m+1))).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  apply SyntaxNumeralSyntax.eliminate_succ k (Fin.last m) _ hN
  have hZ2 := ZFContext.under (ZFContext.under hZ N) P
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw N) P)
  have hb2 : Derives Ξ (successor b.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise,successor_rename]) (under (under hb N) P)
  have ha2 : Derives Ξ (boundLaw k a.castSucc.castSucc) := of_eq (by simp only [Formula.raise,boundLaw_rename]) (under (under ha N) P)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hp := bound_at k a.castSucc.castSucc (Fin.last (m+1)) ha2 (.conjL hP)
  have hao := NaturalOrderBasic.ordinal hZ2 _ _ hw2 (under (under haW N) P)
  have hsub := OmegaElementary.successor_subset (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc (.conjR hP) hp
    (OrdinalTransitivity.subset_of_member a.castSucc.castSucc (Fin.last (m+1)) (.conjL hao) hp)
  have hiNum : Derives Ξ (SyntaxNumeralSyntax.numeral (k+1) (Fin.last m).castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hN P)
  have hiW := SyntaxNumerals.range hZ2 (k+1) w.castSucc.castSucc (Fin.last m).castSucc hw2 hiNum
  have hio := NaturalOrderBasic.ordinal hZ2 _ _ hw2 hiW
  have hle := Derives.impE (.conjL (OrdinalComparison.subset_iff (Fin.last m).castSucc a.castSucc.castSucc
    (ZFContext.arithmetic hZ2).base.extensionality (ZFContext.arithmetic hZ2).base.foundation
    (ZFContext.separation hZ2 OrdinalDifference.outsideMatrix) hio hao)) hsub
  exact of_eq (by simp only [Formula.raise,Formula.rename]) (NaturalOrderBasic.below_successor _ _ _ hb2 hle)

private theorem make_frame {m} {Γ : Context m} (collection : Bool) (hZ : ZFContext.Evidence Γ)
    (w n z : Fin m) (scopes : Fin 4 → Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SchemaIndexSyntax.chain n scopes))
    (ht : ∀ i, Derives Γ (FormulaCodeSyntax.formulaCode w (env i) ((scopeLevels n scopes) (holeDepth collection i)) z)) :
    Frame Γ collection w z (scopeLevels n scopes) env := by
  let levels := scopeLevels n scopes
  have hs0 := Derives.conjL hc
  have hs1 := Derives.conjL (.conjR hc)
  have hs2 := Derives.conjL (.conjR (.conjR hc))
  have hs3 := Derives.conjR (.conjR (.conjR hc))
  have h0 := OmegaStructureAlgebra.successor_member w (scopes 0) n (ZFContext.arithmetic hZ).base.extensionality hw hn hs0
  have h1 := OmegaStructureAlgebra.successor_member w (scopes 1) (scopes 0) (ZFContext.arithmetic hZ).base.extensionality hw h0 hs1
  have h2 := OmegaStructureAlgebra.successor_member w (scopes 2) (scopes 1) (ZFContext.arithmetic hZ).base.extensionality hw h1 hs2
  have h3 := OmegaStructureAlgebra.successor_member w (scopes 3) (scopes 2) (ZFContext.arithmetic hZ).base.extensionality hw h2 hs3
  have b01 := bound_zero hZ w n (scopes 0) hw hn hs0
  have b02 := bound_up 0 (scopes 0) (scopes 1) b01 hs1
  have b03 := bound_up 0 (scopes 1) (scopes 2) b02 hs2
  have b04 := bound_up 0 (scopes 2) (scopes 3) b03 hs3
  have b12 := bound_step hZ 0 w (scopes 0) (scopes 1) hw h0 b01 hs1
  have b13 := bound_up 1 (scopes 1) (scopes 2) b12 hs2
  have b14 := bound_up 1 (scopes 2) (scopes 3) b13 hs3
  have b23 := bound_step hZ 1 w (scopes 1) (scopes 2) hw h1 b12 hs2
  have b24 := bound_up 2 (scopes 2) (scopes 3) b23 hs3
  refine ⟨hZ,hw,hz,?_,?_,?_,ht,?_⟩
  · intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact hn
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3
  · change Derives Γ ((Source.Formula.mem (env 0) w).conj ((Source.Formula.mem (env 1) w).conj
      ((Source.Formula.mem (env 2) w).conj (Formula.bot.imp Formula.bot))))
    exact .conjI (.conjL (FormulaCodeProperties.guards _ _ _ _ (ht 0)))
      (.conjI (.conjL (FormulaCodeProperties.guards _ _ _ _ (ht 1)))
        (.conjI (.conjL (FormulaCodeProperties.guards _ _ _ _ (ht 2))) (.impI (.hyp (Or.inl rfl)))))
  · intro k d hlt
    have ks : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    have ds : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
    rcases ks with rfl | rfl | rfl <;> rcases ds with rfl | rfl | rfl | rfl | rfl <;> try omega
    · exact b01
    · exact b02
    · exact b03
    · exact b04
    · exact b12
    · exact b13
    · exact b14
    · exact b23
    · exact b24

private theorem separation_core_typed : Typed false (SchemaAxiomAssembly.coreProgram false) 0 := by
  exact quantified_typed false true _ 0 (quantified_typed false false _ 1 (quantified_typed false true _ 2
    (binary_typed false 3 _ _ 3 (member_typed false 0 1 3 (by decide) (by decide))
      (binary_typed false 0 _ _ 3 (member_typed false 0 2 3 (by decide) (by decide)) (hole_typed false 0)))))

private theorem collection_core_typed : Typed true (SchemaAxiomAssembly.coreProgram true) 0 := by
  exact quantified_typed true true _ 0 (binary_typed true 2 _ _ 1
    (quantified_typed true true _ 1 (binary_typed true 2 _ _ 2
      (member_typed true 0 1 2 (by decide) (by decide)) (quantified_typed true false _ 2 (hole_typed true 0))))
    (quantified_typed true false _ 1 (quantified_typed true true _ 2 (binary_typed true 2 _ _ 3
      (member_typed true 0 2 3 (by decide) (by decide)) (quantified_typed true false _ 3
        (binary_typed true 0 _ _ 4 (member_typed true 0 2 4 (by decide) (by decide)) (hole_typed true 1)))))))

/-- Exact unchanged original finite templates; the parameter count is INTERNAL. -/
theorem core_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z out : Fin m) (scopes : Fin 4 → Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SchemaIndexSyntax.chain n scopes))
    (ht : ∀ i, Derives Γ (FormulaCodeSyntax.formulaCode w (env i) (matrixScope collection scopes i) z))
    (hg : Derives Γ (graph (SchemaAxiomAssembly.coreProgram collection) w env out)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out n z) := by
  have hh (i : Fin 3) : scopeLevels n scopes (holeDepth collection i) = matrixScope collection scopes i := by
    cases collection
    · rfl
    · by_cases hi : i.val = 0 <;> simp only [holeDepth,matrixScope,↓reduceIte,hi] <;> rfl
  have hf := make_frame collection hZ w n z scopes env hw hn hz hc (fun i =>
    of_eq (congrArg (fun b => FormulaCodeSyntax.formulaCode w (env i) b z) (hh i).symm) (ht i))
  cases collection
  · exact separation_core_typed w z (scopeLevels n scopes) env out hf hg
  · exact collection_core_typed w z (scopeLevels n scopes) env out hf hg


/-- Type the actual whole original assembly, not only the finite core. -/
theorem assembled_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z out : Fin m) (scopes : Fin 4 → Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SchemaIndexSyntax.chain n scopes))
    (ht : ∀ i, Derives Γ (FormulaCodeSyntax.formulaCode w (env i) (matrixScope collection scopes i) z))
    (ha : Derives Γ (SchemaAxiomAssembly.assembled collection w n env out)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out z z) := by
  let B := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    ((graph (SchemaAxiomAssembly.coreProgram collection) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj
      (SyntaxUnaryIterationSyntax.forallClosure w.castSucc (Fin.last m) n.castSucc out.castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := under hn B
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have hc1 := of_eq (SchemaIndexSyntax.chain_rename n scopes Fin.castSucc) (under hc B)
  have ht1 (i : Fin 3) : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc (env i).castSucc
      (matrixScope collection (fun j => (scopes j).castSucc) i) z.castSucc) := by
    simpa only [Formula.raise,FormulaCodeSyntax.formulaCode_rename,matrixScope_map] using under (ht i) B
  have hcore := core_type (ZFContext.under hZ B) collection w.castSucc n.castSucc z.castSucc (Fin.last m)
    (fun i => (scopes i).castSucc) (fun i => (env i).castSucc) hw1 hn1 hz1 hc1 ht1 (.conjL (.conjR hB))
  have hout := SchemaClosureTyping.closed (ZFContext.under hZ B) w.castSucc n.castSucc (Fin.last m) z.castSucc out.castSucc
    hw1 hn1 hz1 hcore (.conjR (.conjR hB))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w out z z Fin.castSucc).symm hout

private theorem first_target {α : Type} (collection : Bool) (scopes : Fin 4 → α) :
    SchemaIndexSyntax.targetScope (SchemaAxiomCompilation.firstSite collection) scopes = scopes 2 := by
  cases collection <;> rfl

/-- EVERY result accepted by the raw original body pipeline is a closed code.
The finite shell, every matrix and whole closure are all actually consumed. -/
theorem result_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SchemaIndexSyntax.chain n scopes))
    (hr : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out scopes)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out z z) := by
  let B := SchemaAxiomCompilation.schemaBody collection w n z body out scopes
  let Δ := Context.add B (HornBinderSyntax.raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  let s := fun i => HornBinderSyntax.old 2 (scopes i)
  let x := HornBinderSyntax.slot 2 (m := m) 0
  let y := HornBinderSyntax.slot 2 (m := m) 1
  let ww := HornBinderSyntax.old 2 w
  let nn := HornBinderSyntax.old 2 n
  let zz := HornBinderSyntax.old 2 z
  have hx0 := SchemaAxiomCompilation.compiled_target_type (SchemaAxiomCompilation.firstSite collection) ww nn zz
    (HornBinderSyntax.old 2 body) x s (.conjL hB)
  have hx : Derives Δ (FormulaCodeSyntax.formulaCode ww x (s 2) zz) :=
    of_eq (congrArg (fun a => FormulaCodeSyntax.formulaCode ww x a zz) (first_target collection s)) hx0
  have hy : Derives Δ (FormulaCodeSyntax.formulaCode ww y (if collection then s 3 else s 2) zz) := by
    cases collection
    · have he : Derives Δ (.equal y x) := .conjL (.conjR hB)
      exact FormulaCodeTransport.code_root ww x (s 2) zz y (eq_symm he) hx
    · exact SchemaAxiomCompilation.compiled_target_type 2 ww nn zz (HornBinderSyntax.old 2 body) y s (.conjL (.conjR hB))
  let env : Fin 3 → Fin (m+2) := fun i => if i.val = 0 then x else y
  have htypes (i : Fin 3) : Derives Δ (FormulaCodeSyntax.formulaCode ww (env i) (matrixScope collection s i) zz) := by
    by_cases hi : i.val = 0
    · simpa only [env,matrixScope,hi,↓reduceIte,ite_self] using hx
    · simpa only [env,matrixScope,hi,↓reduceIte] using hy
  have hout := assembled_type (HornBinderRules.zf_body 2 hZ B) collection ww nn zz (HornBinderSyntax.old 2 out) s env
    (of_eq (omega_rename w (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hw B))
    (HornBinderRules.under_body 2 hn B)
    (of_eq (empty_rename z (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hz B))
    (of_eq (SchemaIndexSyntax.chain_rename n scopes (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hc B))
    htypes (.conjR (.conjR hB))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w out z z (HornBinderSyntax.old 2)).symm hout

def existsTyped {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m := .ex
  (((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SchemaAxiomCompilation.schemaResult collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))).conj
      (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) z.castSucc z.castSucc))

theorem existsTyped_rename {m l} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsTyped collection w n z body scopes).rename r = existsTyped collection (r w) (r n) (r z) (r body) (fun i => r (scopes i)) := by
  simp only [existsTyped,Formula.rename,SchemaAxiomCompilation.schemaResult_rename,
    FormulaCodeSyntax.formulaCode_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Raw valid source body -> actual typed complete original axiom formula.
No compiled/matrix/core/output/type/trace oracle is a premise. -/
theorem output_exists_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z body : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SchemaIndexSyntax.chain n scopes))
    (ha : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z)) :
    Derives Γ (existsTyped collection w n z body scopes) := by
  let O := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SchemaAxiomCompilation.schemaResult collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))
  let Δ := Context.add O (Context.image Formula.raise Γ)
  apply Derives.exE (p := O) (SchemaAxiomCompilation.schema_output_exists hZ collection w n z body scopes hw hn hz hc ha)
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  have ht := result_type (ZFContext.under hZ O) collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m)
    (fun i => (scopes i).castSucc) (of_eq (omega_rename w Fin.castSucc) (under hw O)) (under hn O)
    (of_eq (empty_rename z Fin.castSucc) (under hz O)) (of_eq (SchemaIndexSyntax.chain_rename n scopes Fin.castSucc) (under hc O)) (.conjR hO)
  have hout : Derives Δ (existsTyped collection w.castSucc n.castSucc z.castSucc body.castSucc (fun i => (scopes i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [O,Formula.instantiate,Formula.rename,SchemaAxiomCompilation.schemaResult_rename,
      FormulaCodeSyntax.formulaCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hO ht)
  exact of_eq (existsTyped_rename collection w n z body scopes Fin.castSucc).symm hout

def sentence {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem n w).imp ((empty z).imp ((SchemaIndexSyntax.chain n scopes).imp
    ((ProjectSourceCodeSyntax.sourceCode w body (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z).imp
      (existsTyped collection w n z body scopes)))))).close

theorem source_certificate {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence collection w n z body scopes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (ProjectSourceCodeSyntax.sourceCode w body (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z)
    (Context.add (SchemaIndexSyntax.chain n scopes) (Context.add (empty z) (Context.add (Source.Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _
  exact output_exists_typed hZ collection w n z body scopes (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence collection w n z body scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate collection w n z body scopes))

end PPAC.Migration.SchemaShellTyping
