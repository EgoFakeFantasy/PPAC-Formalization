import PPAC.Migration.Internal.ObjectProjectCompilerSourceValid

/-! Bounded affine cells used by the actual 128/256 Packet rules; all numeric fields are object values. -/
namespace PPAC.Migration.Internal.PacketAffineSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def equationBody {m} (w B d t n : Fin m) : Formula (m+1) :=
  (NaturalMultiplicationSyntax.product w.castSucc B.castSucc t.castSucc (Fin.last m)).conj
    (NaturalAdditionSyntax.sum w.castSucc d.castSucc (Fin.last m) n.castSucc)

def equation {m} (w B d t n : Fin m) : Formula m := .ex (equationBody w B d t n)

def affine {m} (w B d t n : Fin m) : Formula m :=
  (Formula.mem B w).conj ((Formula.mem d B).conj ((Formula.mem t w).conj ((Formula.mem n w).conj (equation w B d t n))))

def existsValue {m} (w B d t : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m)))

def uniqueOutput {m} (w B d t n : Fin m) : Formula m := .all
  ((affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m)).imp (.equal (Fin.last m) n.castSucc))

def fiber {m} (w B d t : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m))).conj
    (uniqueOutput w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m)))

def stepBody {m} (w B d s n : Fin m) : Formula (m+2) :=
  (successor (old 2 s) (slot 2 0)).conj
    ((affine (old 2 w) (old 2 B) (old 2 d) (slot 2 0) (slot 2 1)).conj
      (NaturalAdditionSyntax.sum (old 2 w) (slot 2 1) (old 2 B) (old 2 n)))

def stepCase {m} (w B d s n : Fin m) : Formula m := existsMany 2 (stepBody w B d s n)

def criterion {m} (w B d t n : Fin m) : Formula m :=
  ((empty t).conj ((Formula.mem d B).conj (.equal n d))).disj (stepCase w B d t n)

theorem equationBody_lift {m j} (w B d t n : Fin m) (σ : Fin m → Fin j) :
    (equationBody w B d t n).rename (Formula.liftRen σ) = equationBody (σ w) (σ B) (σ d) (σ t) (σ n) := by
  simp only [equationBody, Formula.rename, NaturalMultiplicationSyntax.product_rename, NaturalAdditionSyntax.sum_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equation_rename {m j} (w B d t n : Fin m) (σ : Fin m → Fin j) :
    (equation w B d t n).rename σ = equation (σ w) (σ B) (σ d) (σ t) (σ n) := by
  simp only [equation, Formula.rename, equationBody_lift]

theorem affine_rename {m j} (w B d t n : Fin m) (σ : Fin m → Fin j) :
    (affine w B d t n).rename σ = affine (σ w) (σ B) (σ d) (σ t) (σ n) := by
  simp only [affine, Formula.rename, equation_rename]

theorem existsValue_rename {m j} (w B d t : Fin m) (σ : Fin m → Fin j) :
    (existsValue w B d t).rename σ = existsValue (σ w) (σ B) (σ d) (σ t) := by
  simp only [existsValue, Formula.rename, affine_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m j} (w B d t n : Fin m) (σ : Fin m → Fin j) :
    (uniqueOutput w B d t n).rename σ = uniqueOutput (σ w) (σ B) (σ d) (σ t) (σ n) := by
  simp only [uniqueOutput, Formula.rename, affine_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m j} (w B d t : Fin m) (σ : Fin m → Fin j) :
    (fiber w B d t).rename σ = fiber (σ w) (σ B) (σ d) (σ t) := by
  simp only [fiber, Formula.rename, affine_rename, uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem stepBody_lift {m j} (w B d s n : Fin m) (σ : Fin m → Fin j) :
    (stepBody w B d s n).rename (lift 2 σ) = stepBody (σ w) (σ B) (σ d) (σ s) (σ n) := by
  simp only [stepBody, Formula.rename, successor_rename, affine_rename, NaturalAdditionSyntax.sum_rename, lift_old, lift_slot]

theorem stepCase_rename {m j} (w B d s n : Fin m) (σ : Fin m → Fin j) :
    (stepCase w B d s n).rename σ = stepCase (σ w) (σ B) (σ d) (σ s) (σ n) := by
  simp only [stepCase, existsMany_rename, stepBody_lift]

theorem criterion_rename {m j} (w B d t n : Fin m) (σ : Fin m → Fin j) :
    (criterion w B d t n).rename σ = criterion (σ w) (σ B) (σ d) (σ t) (σ n) := by
  simp only [criterion, Formula.rename, empty_rename, stepCase_rename]

theorem intro_equation {m} {Γ : Context m} (w B d t n p : Fin m)
    (hp : Derives Γ (NaturalMultiplicationSyntax.product w B t p))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d p n)) : Derives Γ (equation w B d t n) := by
  apply Derives.exI p
  exact of_eq (by simp only [equationBody, Formula.instantiate, Formula.rename, NaturalMultiplicationSyntax.product_rename,
    NaturalAdditionSyntax.sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.conjI hp hs)

theorem intro_affine {m} {Γ : Context m} (w B d t n p : Fin m)
    (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d B)) (ht : Derives Γ (.mem t w)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (NaturalMultiplicationSyntax.product w B t p)) (hs : Derives Γ (NaturalAdditionSyntax.sum w d p n)) :
    Derives Γ (affine w B d t n) := .conjI hB (.conjI hd (.conjI ht (.conjI hn (intro_equation w B d t n p hp hs))))

theorem intro_exists {m} {Γ : Context m} (w B d t n : Fin m) (hn : Derives Γ (.mem n w)) (ha : Derives Γ (affine w B d t n)) :
    Derives Γ (existsValue w B d t) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, affine_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.conjI hn ha)

theorem intro_step {m} {Γ : Context m} (w B d s n t a : Fin m) (hs : Derives Γ (successor s t))
    (ha : Derives Γ (affine w B d t a)) (hn : Derives Γ (NaturalAdditionSyntax.sum w a B n)) :
    Derives Γ (stepCase w B d s n) := by
  apply HornBinderRules.intro_many 2 (stepBody w B d s n) (SyntaxAtomSyntax.two t a)
  exact of_eq (by simp only [stepBody, Formula.rename, successor_rename, affine_rename, NaturalAdditionSyntax.sum_rename,
    assign_old, assign_slot]; rfl) (Derives.conjI hs (Derives.conjI ha hn))

end PPAC.Migration.Internal.PacketAffineSyntax
