import PPAC.Migration.SeparationReverse

/-! 原Collection公理的源语法呈现：收集见证界，不断言精确像集。 -/
namespace PPAC.Migration.CollectionSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

def firstIndex {n} : Fin (n+2) → Fin (n+3) :=
  Fin.lastCases (Fin.last (n+2)) (Fin.lastCases (Fin.last (n+1)).castSucc
    (fun i => i.castSucc.castSucc.castSucc))

def secondIndex {n} : Fin (n+2) → Fin (n+4) :=
  Fin.lastCases (Fin.last (n+3)) (Fin.lastCases (Fin.last (n+2)).castSucc
    (fun i => i.castSucc.castSucc.castSucc.castSucc))

def core {n} (p : Source.Formula (n+2)) : Source.Formula n :=
  .all ((Source.Formula.all ((Source.Formula.mem (Fin.last (n+1)) (Fin.last n).castSucc).imp
    (.ex (p.rename firstIndex)))).imp
    (.ex (.all ((Source.Formula.mem (Fin.last (n+2)) (Fin.last n).castSucc.castSucc).imp
      (.ex ((Source.Formula.mem (Fin.last (n+3)) (Fin.last (n+1)).castSucc.castSucc).conj
        (p.rename secondIndex)))))))

def collection {n} (p : Source.Formula (n+2)) : Source.Sentence := (core p).close

theorem first_index {n} :
    (fun i : Fin (n+2) => Fin.rev (firstIndex i)) =
      (fun i => BoundEmbedding.binaryUnderOne (Fin.rev i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [firstIndex, Fin.lastCases_last, Fin.rev_last, BoundEmbedding.binaryUnderOne,
      Fin.cases_zero]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [firstIndex, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.rev_castSucc,
        Fin.rev_last, BoundEmbedding.binaryUnderOne, Fin.cases_succ, Fin.cases_zero]
      rw [Fin.succ_zero_eq_one]
    · simp only [firstIndex, Fin.lastCases_castSucc, Fin.rev_castSucc,
        BoundEmbedding.binaryUnderOne, Fin.cases_succ]
      apply Fin.ext
      simp only [Fin.val_succ]

theorem second_index {n} :
    (fun i : Fin (n+2) => Fin.rev (secondIndex i)) =
      (fun i => BoundEmbedding.binaryUnderTwo (Fin.rev i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [secondIndex, Fin.lastCases_last, Fin.rev_last, BoundEmbedding.binaryUnderTwo,
      Fin.cases_zero]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [secondIndex, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.rev_castSucc,
        Fin.rev_last, BoundEmbedding.binaryUnderTwo, Fin.cases_succ, Fin.cases_zero]
      rw [Fin.succ_zero_eq_one]
    · simp only [secondIndex, Fin.lastCases_castSucc, Fin.rev_castSucc,
        BoundEmbedding.binaryUnderTwo, Fin.cases_succ]
      apply Fin.ext
      simp only [Fin.val_succ]

theorem encode_core {n} (p : Source.Formula (n+2)) :
    ProjectSyntax.formula (core p) = ProjectNormalization.formula
      (Axioms.Schema.collectionCore (ProjectSyntax.binary p)) := by
  simp only [core, ProjectSyntax.formula, ProjectSyntax.encode, ProjectSyntax.lift_reverse,
    ProjectSyntax.rename_source, first_index, second_index,
    Axioms.Schema.collectionCore, ProjectSyntax.binary,
    Definitional.Project.Formula.forallMem, Definitional.Project.Formula.existsMem,
    Definitional.Term.newest, Definitional.Term.weaken, Definitional.Term.rename,
    Definitional.Term.bind, Function.comp_def, ProjectSyntax.rename_project,
    ProjectNormalization.formula, ProjectNormalization.encode_fixed,
    Fin.rev_last, Fin.rev_castSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

theorem encode_collection {n} (p : Source.Formula (n+2)) :
    ProjectSyntax.formula (collection p) = ProjectNormalization.formula
      (Axioms.Schema.collection (ProjectSyntax.binary p)).formula := by
  rw [collection, ProjectSyntax.close_formula, encode_core]
  exact (ProjectNormalization.close_formula _).symm

theorem collection_ast {n} (p : Source.Formula (n+2)) :
    Translation.sentence (collection p) = Normalization.formula
      (Definitional.Project.fo_sentence (Axioms.Schema.collection (ProjectSyntax.binary p))) := by
  calc
    _ = Definitional.Project.fo_formula (ProjectSyntax.formula (collection p))
        (ProjectSyntax.freeClosed Fin.rev (collection p)) := (SeparationSyntax.fo_closed _).symm
    _ = Definitional.Project.fo_formula
        (ProjectNormalization.formula (Axioms.Schema.collection (ProjectSyntax.binary p)).formula)
        (ProjectNormalization.freeClosed _ (Axioms.Schema.collection (ProjectSyntax.binary p)).freeClosed) :=
      ProjectSyntax.fo_congr (encode_collection p)
    _ = _ := ProjectNormalization.fo_formula _ _

/-- 原Collection版ZF中的任意源矩阵收集实例，有实际原核推导。 -/
theorem source_collection {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (collection p)) :=
  ZFEquivalence.to_source (.collection (ProjectSyntax.binary p)) (collection_ast p)
theorem first_decode_index {n} :
    (fun i : Fin (n+2) => Fin.rev (BoundEmbedding.binaryUnderOne i)) =
      (fun i => firstIndex (Fin.rev i)) := by
  funext i
  have h := congrArg Fin.rev (congrFun (@first_index n) (Fin.rev i))
  simpa only [Fin.rev_rev] using h.symm

theorem second_decode_index {n} :
    (fun i : Fin (n+2) => Fin.rev (BoundEmbedding.binaryUnderTwo i)) =
      (fun i => secondIndex (Fin.rev i)) := by
  funext i
  have h := congrArg Fin.rev (congrFun (@second_index n) (Fin.rev i))
  simpa only [Fin.rev_rev] using h.symm

theorem rev_one {n} : Fin.rev (1 : Fin (n+2)) = (Fin.last n).castSucc := by
  rw [← Fin.succ_zero_eq_one, Fin.rev_succ, Fin.rev_zero]

/-- 原生全Collection矩阵也完整回译，不仅覆盖encode产生的矩阵。 -/
theorem decode_core {n} (s : Definitional.Project.BinarySchema n)
    (h : (Axioms.Schema.collectionCore s).FreeClosed) :
    ProjectDecode.reverse (Axioms.Schema.collectionCore s) h =
      core (ProjectDecode.reverse s.body s.freeClosed) := by
  have hfirst : (s.body.rename BoundEmbedding.binaryUnderOne).FreeClosed :=
    (Definitional.Formula.freeClosed_rename _ _).mpr s.freeClosed
  have hsecond : (s.body.rename BoundEmbedding.binaryUnderTwo).FreeClosed :=
    (Definitional.Formula.freeClosed_rename _ _).mpr s.freeClosed
  have he1 := ProjectDecode.rename_project Fin.rev BoundEmbedding.binaryUnderOne s.body s.freeClosed hfirst
  have he2 := ProjectDecode.rename_project Fin.rev BoundEmbedding.binaryUnderTwo s.body s.freeClosed hsecond
  simp only [ProjectDecode.reverse, Axioms.Schema.collectionCore,
    Definitional.Project.Formula.forallMem, Definitional.Project.Formula.existsMem,
    Definitional.Term.newest, Definitional.Term.weaken, Definitional.Term.rename,
    Definitional.Term.bind, Function.comp_def, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    ProjectDecode.formula, ProjectDecode.lift_reverse, core, he1, he2,
    ProjectDecode.rename_source, first_decode_index, second_decode_index,
    ProjectDecode.term, Fin.rev_zero, rev_one, SeparationReverse.rev_two]

theorem decode_collection {n} (s : Definitional.Project.BinarySchema n) :
    ProjectDecode.reverse (Axioms.Schema.collection s).formula
      (Axioms.Schema.collection s).freeClosed =
      collection (ProjectDecode.reverse s.body s.freeClosed) := by
  have hc : (Axioms.Schema.collectionCore s).FreeClosed := by
    simp [Axioms.Schema.collectionCore, Definitional.Formula.FreeClosed,
      Definitional.Project.Formula.forallMem, Definitional.Project.Formula.existsMem,
      Definitional.Term.newest, s.freeClosed]
  have hall : (Definitional.Project.Formula.forallClosure n (Axioms.Schema.collectionCore s)).FreeClosed :=
    (Definitional.Formula.freeClosed_forallClosure _).mpr hc
  calc
    _ = (ProjectDecode.reverse (Axioms.Schema.collectionCore s) hc).close := by
      simpa only [Axioms.Schema.collection, Definitional.Project.Sentence.forallClosure] using
        ProjectDecode.close_formula (Axioms.Schema.collectionCore s) hc hall
    _ = (core (ProjectDecode.reverse s.body s.freeClosed)).close :=
      congrArg Source.Formula.close (decode_core s hc)
    _ = _ := rfl

theorem native_collection_ast {n} (s : Definitional.Project.BinarySchema n) :
    Translation.sentence (collection (ProjectDecode.reverse s.body s.freeClosed)) =
      Normalization.formula (Definitional.Project.fo_sentence (Axioms.Schema.collection s)) := by
  rw [← decode_collection]
  exact ProjectDecode.closed_fo _

/-- 纯逻辑对象等价，不把Collection作为源Replacement版ZF的已知定理。 -/
theorem native_collection_equivalent {n} (s : Definitional.Project.BinarySchema n)
    {T : FirstOrder.Theory ℒ} {Γ : FirstOrder.Context ℒ []} :
    FirstOrder.Derives T Γ (.iff (Definitional.Project.fo_sentence (Axioms.Schema.collection s))
      (Translation.sentence (collection (ProjectDecode.reverse s.body s.freeClosed)))) := by
  rw [native_collection_ast]
  exact Normalization.equivalent _
end PPAC.Migration.CollectionSyntax
