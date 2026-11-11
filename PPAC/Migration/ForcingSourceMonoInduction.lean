import PPAC.Migration.ForcingSourceLogicalMono
import PPAC.Migration.BoundedInduction

/-! Original force_mono on all internal source formula codes. Induction uses
the actual lower-code fields and the original compiler history. -/
namespace PPAC.Migration.ForcingSourceMonoInduction
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open FormulaCodeCaseLogic (disj_imp)
open NativeProofQuotation (eliminate_objects)
open ForcingSourceMono (atSource atSource_rename apply_atSource)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false

private structure Frame (m : Nat) where
  w : Fin m
  z : Fin m
  a : Fin m
  f : Fin m
  j : Fin m
  b : Fin m
  B : Fin m
  R : Fin m
  S : Fin m
  T : Fin m
  SOld : Fin m
  SNew : Fin m
  A1 : Fin m
  A2 : Fin m
  A3 : Fin m
  K : Fin m
  Extra : Fin m
  α : Fin m
  β : Fin m
  γ : Fin m
  raw : Fin 16 → Fin m
  v : Fin 10 → Fin m
  C : Fin 2 → Fin m
  Refl : Fin 2 → Fin m
  Pre : Fin 2 → Fin m
  U0 : Fin 2 → Fin m
  P : Fin 2 → Fin 3 → Fin m
  rows : Fin 48 → Fin m
  layout : Fin 6 → Fin m

private def Frame.map {m l} (p : Frame m) (r : Fin m → Fin l) : Frame l :=
  ⟨r p.w, r p.z, r p.a, r p.f, r p.j, r p.b, r p.B, r p.R, r p.S, r p.T, r p.SOld, r p.SNew,
    r p.A1, r p.A2, r p.A3, r p.K, r p.Extra, r p.α, r p.β, r p.γ,
    (fun i => r (p.raw i)), (fun i => r (p.v i)), (fun i => r (p.C i)), (fun i => r (p.Refl i)),
    (fun i => r (p.Pre i)), (fun i => r (p.U0 i)), (fun i j => r (p.P i j)),
    (fun i => r (p.rows i)), (fun i => r (p.layout i))⟩

private theorem Frame.map_id {m} (p : Frame m) : p.map id = p := by cases p; rfl

private theorem Frame.map_comp {m l t} (p : Frame m) (r : Fin m → Fin l) (s : Fin l → Fin t) :
    (p.map r).map s = p.map (fun i => s (r i)) := by
  cases p
  rfl

private def Frame.runtime {k m} (p : Frame m) (Reln : Formula (k+2)) : Formula m :=
  ForcingRawModalBody.globalModalInput test Reln p.w p.z p.a p.f p.j p.b p.B p.R p.S p.T p.SOld p.SNew
    p.A1 p.A2 p.A3 p.K p.Extra p.raw p.v p.C p.Refl p.Pre p.U0 p.P p.rows p.layout

private theorem Frame.runtime_rename {k m l} (p : Frame m) (Reln : Formula (k+2)) (r : Fin m → Fin l) :
    (p.runtime Reln).rename r = (p.map r).runtime Reln :=
  ForcingRawModalBody.globalModalInput_rename test Reln p.w p.z p.a p.f p.j p.b p.B p.R p.S p.T p.SOld p.SNew
    p.A1 p.A2 p.A3 p.K p.Extra p.raw p.v p.C p.Refl p.Pre p.U0 p.P p.rows p.layout r

private abbrev Frame.G {m} (p : Frame m) : Fin m := p.layout 3
private abbrev Frame.bound {m} (p : Frame m) : Fin 2 → Fin m := fun _ => p.T
private abbrev Frame.free {m} (p : Frame m) : Fin 2 → Fin m := SyntaxAtomSyntax.two p.SOld p.SNew

private abbrev Frame.source {k m} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1)) (n : Fin m) : Formula m :=
  atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.bound p.free n

private abbrev Frame.transfer {m} (p : Frame m) (Q : Fin m) : Formula m :=
  ForcingConjunctionMono.transfer test p.w p.z p.a p.f p.b p.G p.bound p.free Q

private theorem Frame.transfer_rename {m l} (p : Frame m) (Q : Fin m) (r : Fin m → Fin l) :
    (p.transfer Q).rename r = (p.map r).transfer (r Q) := by
  simp only [Frame.transfer, ForcingConjunctionMono.transfer_rename, Frame.map, Frame.G, Frame.bound,
    Frame.free, SyntaxAtomSyntax.two_map]

private abbrev Frame.property {k m} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1)) (n : Fin m) : Formula m :=
  ForcingSourceLogicalMono.property test Reln Dom p.w p.z p.a p.f p.j p.b p.G n p.bound p.free

private theorem Frame.property_rename {k m l} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (n : Fin m) (r : Fin m → Fin l) : (p.property Reln Dom n).rename r = (p.map r).property Reln Dom (r n) := by
  simp only [Frame.property, ForcingSourceLogicalMono.property_rename, Frame.map, Frame.G, Frame.bound,
    Frame.free, SyntaxAtomSyntax.two_map]

private abbrev Frame.below {k m} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1)) (n : Fin m) : Formula m :=
  ForcingSourceLogicalMono.below test Reln Dom p.w p.z p.a p.f p.j p.b p.G n p.bound p.free

private theorem Frame.below_rename {k m l} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (n : Fin m) (r : Fin m → Fin l) : (p.below Reln Dom n).rename r = (p.map r).below Reln Dom (r n) := by
  simp only [Frame.below, ForcingSourceLogicalMono.below_rename, Frame.map, Frame.G, Frame.bound,
    Frame.free, SyntaxAtomSyntax.two_map]

private theorem Frame.below_eq {k m} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1)) (n : Fin m) :
    p.below Reln Dom n = .all ((Formula.mem (Fin.last m) p.w.castSucc).imp
      ((Formula.mem (Fin.last m) n.castSucc).imp ((p.map Fin.castSucc).property Reln Dom (Fin.last m)))) := by
  simp only [Frame.below, ForcingSourceLogicalMono.below, Frame.property, Frame.map, Frame.G, Frame.bound,
    Frame.free, SyntaxAtomSyntax.two_map]

private abbrev Frame.neg {k m} (p : Frame m) (Reln : Formula (k+2)) : Formula m :=
  ForcingSourceLogicalMono.negativeLaw test Reln p.w p.z p.a p.α p.f p.j p.b p.G p.bound p.free

private theorem Frame.neg_rename {k m l} (p : Frame m) (Reln : Formula (k+2)) (r : Fin m → Fin l) :
    (p.neg Reln).rename r = (p.map r).neg Reln := by
  simp only [Frame.neg, ForcingSourceLogicalMono.negativeLaw_rename, Frame.map, Frame.G, Frame.bound,
    Frame.free, SyntaxAtomSyntax.two_map]

private abbrev Frame.compiled {k m} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1)) (n Q : Fin m) : Formula m :=
  ForcingCodeRecursion.compiled Reln Dom p.w p.z p.f p.j p.a n Q

private structure Inputs {k m} (Γ : Context m) (Reln : Formula (k+2)) (p : Frame m) : Prop where
  zf : ZFContext.Evidence Γ
  row : Derives Γ (p.runtime Reln)
  omega : Derives Γ (OmegaSyntax.omega p.w)
  zero : Derives Γ (empty p.z)
  background : Derives Γ (formulaCode p.w p.G p.z p.b)
  first : Derives Γ (successor p.α p.a)
  second : Derives Γ (successor p.β p.α)
  third : Derives Γ (successor p.γ p.β)
  neg : Derives Γ (p.neg Reln)

private theorem Inputs.map {k m l} {Γ : Context m} {Δ : Context l} {Reln : Formula (k+2)} {p : Frame m}
    (h : Inputs Γ Reln p) (r : Fin m → Fin l) (hZ : ZFContext.Evidence Δ)
    (lift : ∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename r)) : Inputs Δ Reln (p.map r) :=
  ⟨hZ, of_eq (p.runtime_rename Reln r) (lift h.row),
    of_eq (omega_rename p.w r) (lift h.omega), of_eq (empty_rename p.z r) (lift h.zero),
    of_eq (formulaCode_rename p.w p.G p.z p.b r) (lift h.background),
    of_eq (successor_rename p.α p.a r) (lift h.first),
    of_eq (successor_rename p.β p.α r) (lift h.second),
    of_eq (successor_rename p.γ p.β r) (lift h.third),
    of_eq (p.neg_rename Reln r) (lift h.neg)⟩

private theorem Inputs.add {k m} {Γ : Context m} {Reln : Formula (k+2)} {p : Frame m}
    (h : Inputs Γ Reln p) (E : Formula m) : Inputs (Context.add E Γ) Reln p := by
  simpa only [p.map_id] using h.map id (ZFContext.add h.zf E)
    (fun hp => of_eq (Reverse.source_rename_id _).symm (SourceLogic.add hp E))

private theorem Frame.compiled_rename {k m l} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (n Q : Fin m) (r : Fin m → Fin l) : (p.compiled Reln Dom n Q).rename r = (p.map r).compiled Reln Dom (r n) (r Q) :=
  ForcingCodeRecursion.compiled_rename Reln Dom p.w p.z p.f p.j p.a n Q r

private theorem consume_source {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (n Q : Fin m) (ht : Derives Γ (p.source Reln Dom n)) (hc : Derives Γ (p.compiled Reln Dom n Q)) :
    Derives Γ (p.transfer Q) :=
  apply_atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.bound p.free n Q ht hc

private theorem typed_atom {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (equality : Bool) (n Q s x y : Fin m)
    (ht : Derives Γ (formulaCode p.w n p.a p.z))
    (hc : Derives Γ (p.compiled Reln Dom n Q))
    (hf : Derives Γ (ForcingSourceMono.atomAt equality p.w p.a p.z s x y n)) :
    Derives Γ (p.transfer Q) :=
  consume_source n Q
    (ForcingSourceMono.atomic h.zf equality Reln Dom p.w p.z p.a p.f p.j p.b p.B p.R p.S p.T p.SOld p.SNew
      p.A1 p.A2 p.A3 p.K p.Extra p.α p.β p.γ n s x y p.raw p.v p.C p.Refl p.Pre p.U0 p.P p.rows p.layout
      h.row ht h.first h.second h.third hf) hc

private theorem member_transfer {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (n Q : Fin m) (ht : Derives Γ (formulaCode p.w n p.a p.z))
    (hc : Derives Γ (p.compiled Reln Dom n Q)) (hm : Derives Γ (SyntaxAtomSyntax.membership p.w p.a p.z n)) :
    Derives Γ (p.transfer Q) := by
  apply eliminate_objects h.zf 3 (fun r v => SyntaxAtomSyntax.memberAt (r p.w) (r p.a) (r p.z)
    (v 0) (v 1) (v 2) (r n)) (.conjR hm) (p.transfer Q)
  intro l Δ r v hZ lift hf
  exact of_eq (p.transfer_rename Q r).symm
    (typed_atom (h.map r hZ lift) false (r n) (r Q) (v 0) (v 1) (v 2)
      (of_eq (formulaCode_rename p.w n p.a p.z r) (lift ht))
      (of_eq (p.compiled_rename Reln Dom n Q r) (lift hc)) hf)

private theorem equality_transfer {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (n Q : Fin m) (ht : Derives Γ (formulaCode p.w n p.a p.z))
    (hc : Derives Γ (p.compiled Reln Dom n Q)) (hm : Derives Γ (SyntaxAtomSyntax.equality p.w p.a p.z n)) :
    Derives Γ (p.transfer Q) := by
  apply eliminate_objects h.zf 2 (fun r v => SyntaxAtomSyntax.equalAt (r p.w) (r p.a) (r p.z)
    (v 0) (v 1) (r n)) (.conjR hm) (p.transfer Q)
  intro l Δ r v hZ lift hf
  exact of_eq (p.transfer_rename Q r).symm
    (typed_atom (h.map r hZ lift) true (r n) (r Q) (r p.z) (v 0) (v 1)
      (of_eq (formulaCode_rename p.w n p.a p.z r) (lift ht))
      (of_eq (p.compiled_rename Reln Dom n Q r) (lift hc)) hf)

private theorem atomic_step {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (n Q : Fin m) (ht : Derives Γ (formulaCode p.w n p.a p.z))
    (hc : Derives Γ (p.compiled Reln Dom n Q)) (ha : Derives Γ (SyntaxAtomSyntax.atomic p.w p.a p.z n)) :
    Derives Γ (p.transfer Q) := by
  have constant (truth : Bool) : Derives Γ ((SyntaxAtomSyntax.nullary truth p.w p.a p.z n).imp (p.transfer Q)) := by
    apply Derives.impI
    exact consume_source n Q (ForcingSourceMono.nullary (ZFContext.add h.zf _) test truth Reln Dom
      p.w p.z p.f p.j p.a p.α p.β p.γ p.b p.G n p.bound p.free
      (SourceLogic.add h.omega _) (SourceLogic.add ht _) (SourceLogic.add h.first _) (SourceLogic.add h.second _)
      (SourceLogic.add h.third _) (.conjR (.hyp (Or.inl rfl)))) (SourceLogic.add hc _)
  have member : Derives Γ ((SyntaxAtomSyntax.membership p.w p.a p.z n).imp (p.transfer Q)) := by
    apply Derives.impI
    exact member_transfer (h.add _) n Q (SourceLogic.add ht _) (SourceLogic.add hc _) (.hyp (Or.inl rfl))
  have equality : Derives Γ ((SyntaxAtomSyntax.equality p.w p.a p.z n).imp (p.transfer Q)) := by
    apply Derives.impI
    exact equality_transfer (h.add _) n Q (SourceLogic.add ht _) (SourceLogic.add hc _) (.hyp (Or.inl rfl))
  exact .impE (FormulaCodeCaseLogic.disj_imp (FormulaCodeCaseLogic.disj_imp (constant false) (constant true))
    (FormulaCodeCaseLogic.disj_imp member equality)) ha

private theorem existential_step {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (g n Q : Fin m)
    (hc : Derives Γ (ForcingCodeStep.existential Reln Dom p.w p.z p.f p.j p.a p.α p.β p.γ g n Q)) :
    Derives Γ (p.transfer Q) := by
  apply eliminate_objects h.zf 2 (fun r v =>
    (FormulaCodeRecursiveSyntax.singleFields 10 true (r p.w) (r p.a) (r p.z) (v 0) (r n)).conj
      ((ForcingCodeStep.read (r p.w) (r g) (v 0) (r p.α) (r p.f) (v 1)).conj
        (ForcingExistCode.compiled Reln Dom (r p.w) (r p.a) (r p.α) (r p.β) (r p.γ) (r p.f) (r p.j) (v 1) (r Q))))
    hc (p.transfer Q)
  intro l Δ r v hZ lift hf
  let p1 := p.map r
  have h1 := h.map r hZ lift
  have hx := ForcingCodeStep.read_type p1.w (r g) (v 0) p1.α p1.f (v 1) (.conjL (.conjR hf))
  exact of_eq (p.transfer_rename Q r).symm
    (ForcingRawModalBody.transfer_existential_global hZ test Reln Dom p1.w p1.z p1.a p1.f p1.j p1.b
      p1.B p1.R p1.S p1.T p1.SOld p1.SNew p1.A1 p1.A2 p1.A3 p1.K p1.Extra p1.raw p1.v p1.C
      p1.Refl p1.Pre p1.U0 p1.P p1.rows p1.layout p1.α p1.β p1.γ (v 1) (r Q)
      (.conjI h1.row (.conjI h1.first (.conjI h1.second (.conjI h1.third
        (.conjI hx (.conjR (.conjR hf))))))))

private theorem from_cases {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (g n Q : Fin m)
    (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (ForcingCodeRecursion.graph Reln Dom p.w p.z p.f p.j g n))
    (hi : Derives Γ (p.below Reln Dom n))
    (ht : Derives Γ (formulaCode p.w n p.a p.z)) (hQ : Derives Γ (p.compiled Reln Dom n Q))
    (hc : Derives Γ (ForcingCodeStep.cases Reln Dom p.w p.z p.f p.j p.a p.α p.β p.γ g n Q)) :
    Derives Γ (p.transfer Q) := by
  let binary := fun kind => ForcingCodeStep.binary kind Reln p.w p.z p.f p.j p.a p.α p.β p.γ g n Q
  have atom : Derives Γ (((SyntaxAtomSyntax.atomic p.w p.a p.z n).conj (ForcingAtomCode.compiled Reln p.w p.a p.z n Q)).imp
      (p.transfer Q)) := by
    apply Derives.impI
    exact atomic_step (h.add _) n Q (SourceLogic.add ht _) (SourceLogic.add hQ _) (.conjL (.hyp (Or.inl rfl)))
  have negative : Derives Γ ((ForcingCodeStep.negative Reln Dom p.w p.z p.f p.j p.a p.α p.β p.γ g n Q).imp
      (p.transfer Q)) := by
    apply Derives.impI
    exact ForcingSourceLogicalMono.negative_step (ZFContext.add h.zf _) test Reln Dom
      p.w p.z p.a p.α p.β p.γ p.f p.j p.b p.G g n Q p.bound p.free (SourceLogic.add h.neg _) (.hyp (Or.inl rfl))
  have conjunction : Derives Γ ((binary 0).imp (p.transfer Q)) := by
    apply Derives.impI
    exact ForcingSourceLogicalMono.conjunction_step (ZFContext.add h.zf _) test Reln Dom
      p.w p.z p.a p.α p.β p.γ p.f p.j p.b p.G g n Q p.bound p.free
      (SourceLogic.add h.omega _) (SourceLogic.add h.zero _) (SourceLogic.add h.background _)
      (SourceLogic.add ho _) (SourceLogic.add hg _) (SourceLogic.add hi _) (.hyp (Or.inl rfl))
  have normalized (kind : Fin 3) : Derives Γ ((binary kind.succ).imp (p.transfer Q)) := by
    apply Derives.impI
    exact ForcingSourceLogicalMono.binary_step (ZFContext.add h.zf _) kind test Reln
      p.w p.z p.a p.α p.β p.γ p.f p.j p.b p.G g n Q p.bound p.free
      (SourceLogic.add h.omega _) (SourceLogic.add h.zero _) (SourceLogic.add h.background _)
      (SourceLogic.add h.neg _) (.hyp (Or.inl rfl))
  have universal : Derives Γ ((ForcingCodeStep.universal Reln Dom p.w p.z p.f p.j p.a p.α p.β p.γ g n Q).imp
      (p.transfer Q)) := by
    apply Derives.impI
    exact ForcingSourceLogicalMono.universal_step (ZFContext.add h.zf _) test Reln Dom
      p.w p.z p.a p.α p.β p.γ p.f p.j p.b p.G g n Q p.bound p.free (SourceLogic.add h.neg _) (.hyp (Or.inl rfl))
  have existential : Derives Γ ((ForcingCodeStep.existential Reln Dom p.w p.z p.f p.j p.a p.α p.β p.γ g n Q).imp
      (p.transfer Q)) := by
    apply Derives.impI
    exact existential_step (h.add _) g n Q (.hyp (Or.inl rfl))
  exact .impE (disj_imp atom (disj_imp negative (disj_imp conjunction (disj_imp (normalized 0)
    (disj_imp (normalized 1) (disj_imp (normalized 2) (disj_imp universal existential))))))) hc

private theorem from_compiled {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (n Q : Fin m)
    (hi : Derives Γ (p.below Reln Dom n)) (ht : Derives Γ (formulaCode p.w n p.a p.z))
    (hq : Derives Γ (p.compiled Reln Dom n Q)) : Derives Γ (p.transfer Q) := by
  have ho := NaturalOrderBasic.ordinal h.zf p.w n h.omega (.conjL (FormulaCodeProperties.guards p.w n p.a p.z ht))
  have he := ForcingCodeRecursion.exists_graph h.zf Reln Dom p.w p.z p.f p.j n ho
  apply eliminate_objects h.zf 1 (fun r v => ForcingCodeRecursion.graph Reln Dom (r p.w) (r p.z) (r p.f) (r p.j) (v 0) (r n))
    he (p.transfer Q)
  intro l Δ r v hZ lift hg
  let p1 := p.map r
  have h1 := h.map r hZ lift
  have ho1 := of_eq (OrdinalSyntax.ordinal_rename n r) (lift ho)
  have hq1 := of_eq (p.compiled_rename Reln Dom n Q r) (lift hq)
  have step := ForcingCodeUnique.compiled_step hZ Reln Dom p1.w p1.z p1.f p1.j (r n) (v 0) p1.a p1.α p1.β p1.γ
    (r Q) h1.omega ho1 h1.first h1.second h1.third hg hq1
  exact of_eq (p.transfer_rename Q r).symm (from_cases h1 (v 0) (r n) (r Q) ho1 hg
    (of_eq (p.below_rename Reln Dom n r) (lift hi))
    (of_eq (formulaCode_rename p.w n p.a p.z r) (lift ht)) hq1 (.conjR step))

private theorem from_below {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) (n : Fin m) (hi : Derives Γ (p.below Reln Dom n)) :
    Derives Γ (p.property Reln Dom n) := by
  apply Derives.impI
  let E := formulaCode p.w n p.a p.z
  let Δ := Context.add E Γ
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  apply Derives.allI
  apply Derives.impI
  let r : Fin m → Fin (m+1) := Fin.castSucc
  let Q := Fin.last m
  let p1 := p.map r
  let H := p1.compiled Reln Dom (r n) Q
  let Ξ := Context.add H (Context.image Formula.raise Δ)
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have h1 := (h.add E).map r (ZFContext.under (ZFContext.add h.zf E) H) (fun hp => under hp H)
  have result := from_compiled h1 (r n) Q (of_eq (p.below_rename Reln Dom n r) (under (SourceLogic.add hi E) H))
    (of_eq (formulaCode_rename p.w n p.a p.z r) (under hE H)) hH
  exact of_eq (by simp only [Frame.transfer, Frame.map, Frame.free, SyntaxAtomSyntax.two_map] <;> rfl) result

private def matrix {k m} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1)) : Formula (m+1) :=
  (p.map Fin.castSucc).property Reln Dom (Fin.last m)

private theorem matrix_pred {k m l} (p : Frame m) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (r : Fin m → Fin l) (n : Fin l) :
    MinimalPredicates.pred (matrix p Reln Dom) r n = (p.map r).property Reln Dom n := by
  simp only [matrix, MinimalPredicates.pred, Frame.property_rename, Frame.map_comp,
    Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem progressive {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) : Derives Γ (BoundedInduction.progressive (matrix p Reln Dom) id p.w) := by
  let p1 := p.map Fin.castSucc
  let n := Fin.last m
  let E := Formula.mem n p1.w
  let I := p1.below Reln Dom n
  have he : BoundedInduction.progressive (matrix p Reln Dom) id p.w =
      .all (E.imp (I.imp (p1.property Reln Dom n))) := by
    simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred,
      Frame.below_eq, Frame.map_comp, p1, E, I, n] <;> rfl
  apply of_eq he.symm
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  exact from_below
    (h.map Fin.castSucc (ZFContext.add (ZFContext.under h.zf E) I) (fun hp => SourceLogic.add (under hp E) I))
    n (.hyp (Or.inl rfl))

private theorem all_properties {k m} {Γ : Context m} {Reln : Formula (k+2)} {Dom : Formula (k+1)} {p : Frame m}
    (h : Inputs Γ Reln p) : Derives Γ (BoundedInduction.holds (matrix p Reln Dom) id p.w) :=
  BoundedInduction.induction_on_set (matrix p Reln Dom) id p.w
    (ZFContext.separation h.zf (matrix p Reln Dom).neg) (ZFContext.arithmetic h.zf).base.foundation
    (progressive h)

private theorem at_scopes {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra α β γ n : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hα : Derives Γ (successor α a)) (hβ : Derives Γ (successor β α)) (hγ : Derives Γ (successor γ β))
    (hn : Derives Γ (formulaCode w n a z)) :
    Derives Γ (atSource test Reln Dom w z f j a b (layout 3) (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n) := by
  let p : Frame m := ⟨w,z,a,f,j,b,B,R,S,T,SOld,SNew,A1,A2,A3,K,Extra,α,β,γ,raw,v,C,Refl,Pre,U0,P,rows,layout⟩
  have hGlobal := Derives.conjL hr
  have hFresh := Derives.conjL (.conjL (.conjR hGlobal))
  have hw : Derives Γ (omega w) := .conjL (.conjL (.conjL (.conjR (.conjR hFresh))))
  have hz : Derives Γ (empty z) := .conjL hFresh
  have hLayout := Derives.conjR (.conjR (.conjR hGlobal))
  have hg : Derives Γ (formulaCode w (layout 3) z b) := .conjR (.conjL (.conjR (.conjR (.conjR hLayout))))
  have hNeg := ForcingSourceLogicalMono.negativeLaw_of_runtime hZ test Reln w z a f j b B R S T SOld SNew A1 A2 A3
    K Extra α raw v C Refl Pre U0 P rows layout hr hα
  have h : Inputs Γ Reln p := ⟨hZ,hr,hw,hz,hg,hα,hβ,hγ,hNeg⟩
  have hall : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp
      ((p.map Fin.castSucc).property Reln Dom (Fin.last m)))) :=
    of_eq (by simp only [BoundedInduction.holds, matrix_pred] <;> rfl)
      (all_properties h)
  have hp : Derives Γ ((Formula.mem n w).imp (p.property Reln Dom n)) :=
    of_eq (by
      simp only [Formula.instantiate, Formula.rename, Frame.property_rename, Frame.map_comp,
        Fin.lastCases_castSucc, Fin.lastCases_last, id_eq]
      exact congrArg (fun p' : Frame m => (Formula.mem n w).imp (p'.property Reln Dom n)) (p.map_id))
      (Derives.allE n hall)
  exact .impE (.impE hp (.conjL (FormulaCodeProperties.guards w n a z hn))) hn

/-- Original forcing monotonicity for all internally legal source formula
codes in the actual runtime. The three successor scopes are obtained in
object ZF and eliminated before closing the derivation. -/
theorem at_code {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra n : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hn : Derives Γ (formulaCode w n a z)) :
    Derives Γ (atSource test Reln Dom w z f j a b (layout 3) (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n) := by
  let bound : Fin 2 → Fin m := fun _ => T
  let free := SyntaxAtomSyntax.two SOld SNew
  let out := atSource test Reln Dom w z f j a b (layout 3) bound free n
  have hGlobal := Derives.conjL hr
  have hFresh := Derives.conjL (.conjL (.conjR hGlobal))
  have hw : Derives Γ (omega w) := .conjL (.conjL (.conjL (.conjR (.conjR hFresh))))
  have ha : Derives Γ (.mem a w) := .conjL (.conjR (FormulaCodeProperties.guards w n a z hn))
  apply InternalProofTemplates.eliminate_successor hZ w a hw ha out
  intro l Δ r α hZ1 lift1 hα
  have hw1 := of_eq (omega_rename w r) (lift1 hw)
  have ha1 : Derives Δ (.mem (r a) (r w)) := lift1 ha
  have hαw := OmegaStructureAlgebra.successor_member (r w) α (r a)
    (ZFContext.arithmetic hZ1).base.extensionality hw1 ha1 hα
  apply InternalProofTemplates.eliminate_successor hZ1 (r w) α hw1 hαw (out.rename r)
  intro l2 Δ2 s β hZ2 lift2 hβ
  have hw2 := of_eq (omega_rename (r w) s) (lift2 hw1)
  have hαw2 : Derives Δ2 (.mem (s α) (s (r w))) := lift2 hαw
  have hβw := OmegaStructureAlgebra.successor_member (s (r w)) β (s α)
    (ZFContext.arithmetic hZ2).base.extensionality hw2 hαw2 hβ
  apply InternalProofTemplates.eliminate_successor hZ2 (s (r w)) β hw2 hβw ((out.rename r).rename s)
  intro l3 Δ3 t γ hZ3 lift3 hγ
  let ρ : Fin m → Fin l3 := fun i => t (s (r i))
  have carry {φ : Formula m} (h : Derives Γ φ) : Derives Δ3 (φ.rename ρ) :=
    of_eq (by simp only [rename_comp, ρ]) (lift3 (lift2 (lift1 h)))
  have hα3 : Derives Δ3 (successor (t (s α)) (ρ a)) :=
    of_eq (by simp only [successor_rename, ρ]) (lift3 (lift2 hα))
  have hβ3 := of_eq (successor_rename β (s α) t) (lift3 hβ)
  have hr3 := of_eq (ForcingRawModalBody.globalModalInput_rename test Reln w z a f j b B R S T SOld SNew
    A1 A2 A3 K Extra raw v C Refl Pre U0 P rows layout ρ) (carry hr)
  have result := at_scopes hZ3 Reln Dom (ρ w) (ρ z) (ρ a) (ρ f) (ρ j) (ρ b)
    (ρ B) (ρ R) (ρ S) (ρ T) (ρ SOld) (ρ SNew) (ρ A1) (ρ A2) (ρ A3) (ρ K) (ρ Extra)
    (t (s α)) (t β) γ (ρ n) (fun i => ρ (raw i)) (fun i => ρ (v i))
    (fun i => ρ (C i)) (fun i => ρ (Refl i)) (fun i => ρ (Pre i)) (fun i => ρ (U0 i))
    (fun i u => ρ (P i u)) (fun i => ρ (rows i)) (fun i => ρ (layout i))
    hr3 hα3 hβ3 hγ (of_eq (formulaCode_rename w n a z ρ) (carry hn))
  have renameOut : (((out.rename r).rename s).rename t) = out.rename ρ := by
    simp only [rename_comp, ρ]
  exact of_eq renameOut.symm
    (of_eq (by simp only [out, atSource_rename, bound, free, SyntaxAtomSyntax.two_map]) result)

def sentence {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra n : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Source.Sentence :=
  ((ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra
    raw v C Refl Pre U0 P rows layout).imp
    ((formulaCode w n a z).imp
      (atSource test Reln Dom w z f j a b (layout 3) (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n))).close

theorem kernel_certificate {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra n : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence
      (sentence Reln Dom w z a f j b B R S T SOld SNew A1 A2 A3 K Extra n raw v C Refl Pre U0 P rows layout)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact at_code (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) Reln Dom
    w z a f j b B R S T SOld SNew A1 A2 A3 K Extra n raw v C Refl Pre U0 P rows layout
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingSourceMonoInduction
