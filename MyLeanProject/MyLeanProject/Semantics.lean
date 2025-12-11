import MyLeanProject.Basic

open PropForm

def PropAssignment := List (String × Bool)

namespace PropAssignment

def eval (v : PropAssignment) (s : String) : Bool :=
  match v.find? (fun p => p.1 == s) with
  | some (_, b) => b
  | none => false


def mk (l : List (String × Bool)) : PropAssignment := l

end PropAssignment

def PropForm.eval (v : PropAssignment) : PropForm → Bool
  | var s => v.eval s
  | tr => true
  | fls => false
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))

@[simp]
theorem negation_evaluation (v : PropAssignment) (A : PropForm) :
  eval v (neg A) = !(eval v A) := by
  rfl

@[simp]
theorem conjunction_evaluation (v : PropAssignment) (A B : PropForm) :
  (eval v (conj A B)) = ((eval v A) && (eval v B)) := by
  rfl

def allSublists : List α → List (List α)
  | [] => [[]]
  | (a :: as) =>
      let recval := allSublists as
      recval.map (a :: ·) ++ recval

def truthTable (A : PropForm) : List (List Bool × Bool) :=
  let vars := A.vars
  let assignments := (allSublists vars).map (fun l => PropAssignment.mk (l.map (·, true)))
  let evalLine := fun v : PropAssignment => (vars.map v.eval, A.eval v)
  assignments.map evalLine


def PropForm.isValid (A : PropForm) : Bool :=
  List.all (truthTable A) Prod.snd

def PropForm.isSat (A : PropForm) : Bool :=
  List.any (truthTable A) Prod.snd

notation "⊨" A => PropForm.isValid A
#check ⊨ var "p"

notation A "AND" B => PropForm.conj A B
#eval var "p" AND var "q"

notation A "OR" B => PropForm.disj A B
#eval var "p" OR var "q"


theorem reflexive_biImpl (A : PropForm) : ⊨ biImpl A A := by
 simp [PropForm.isValid]
 intro a
 by_contra h
 /-truthtable-/

 theorem negation_biImpl (A B : PropForm) : (⊨ biImpl A B) -> (⊨ biImpl (neg A) (neg B))
 theorem conjunction_biImpl (A1 A2 B1 B2 : PropForm) : (⊨ biImpl A1 B1) -> (⊨ biImpl A2 B2) -> (⊨ biImpl (conj A1 A2) (conj B1 B2))
 theorem disjunction_biImpl (A1 A2 B1 B2 : PropForm) : (⊨ biImpl A1 B1) -> (⊨ biImpl A2 B2) -> (⊨ biImpl (conj A1 A2) (conj B1 B2))
 theorem implication_biImpl (A1 A2 B1 B2 : PropForm) : (⊨ biImpl A1 B1) -> (⊨ biImpl A2 B2) -> (⊨ biImpl (impl A1 A2) (impl B1 B2))
 theorem biimplication_biImpl (A1 A2 B1 B2 : PropForm) : (⊨ biImpl A1 B1) -> (⊨ biImpl A2 B2) -> (⊨ biImpl (biImpl A1 A2) (biImpl B1 B2))

def testAssignment := PropAssignment.mk [("p", true), ("q", true), ("r", true)]

#eval propExample.eval testAssignment
#eval allSublists propExample.vars
#eval truthTable propExample
#eval propExample.isValid
#eval propExample.isSat



/-cases checkt alle mogelijkheden, volgens tactics hfst in boek-/
/-<;> zorgt ervoor dat rfl op beide onderdelen wordt toegepast-/
/-simp[auxiliary, PropForm.eval] =  aan de linkerkant wordt de auxiliary geevalueerd, aan de rechterkant de negatie hiervan -/
/- rw = rewrite -/
theorem auxiliary_theorem (A : PropForm) (v : PropAssignment) : (auxiliary A).eval v = (neg A).eval v := by
  induction A with
    | tr
    | fls
    | var s =>
      simp[auxiliary, PropForm.eval]
    | neg A ih =>
      simp[auxiliary, PropForm.eval]
      rw[ih]
      simp
    | conj A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp
    | disj A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp
    | impl A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp
    | biImpl A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp


/--dit nog uitwerken-/
/-intro is introduceren van iets nieuws.-/
/-bij var ook 2 cases?-/
theorem substitution_theorem (A B C : PropForm) (t : String) :
(⊨ (biImpl A B)) -> (⊨ (biImpl (substitution t A C) (substitution t B C))) := by
intro h
induction C with
 | tr =>
    simp[substitution]
    apply reflexive_biImpl tr
 | fls =>
   simp[substitution]
   apply reflexive_biImpl fls
 | var s => sorry
 | neg A t =>
   simp[substitution]
   apply negation_biImpl
 | conj A1 A2 t1 t2 =>
   simp[substitution]
   apply conjunction_biImpl
 | disj A1 A2 t1 t2 =>
   simp[substitution]
   apply disjunction_biImpl
 | impl A1 A2 t1 t2 =>
   simp[substitution]
   apply implication_biImpl
 | biImpl A1 A2 t1 t2 =>
   simp[substitution]
   apply biimplication_biImpl


theorem duality_theorem (A B : PropForm) : (⊨ (biImpl A B)) ↔ (⊨ (biImpl (duality2 A) (duality2 B))) := by sorry
