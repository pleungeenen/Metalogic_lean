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
/-zit een error in?-/
theorem auxiliary_theorem (A : PropForm) (v : PropAssignment) : (auxiliary A).eval v = (neg A).eval v := by induction
  | tr => simp[auxiliary, PropForm.eval] rfl
  | fls => simp[auxiliary,PropForm.eval] rfl
  | var s => simp[auxiliary,PropForm.eval] rfl
  | neg A t => simp[auxiliary, PropForm.eval]
              rw [t]
              simp[PropForm.eval]
              cases A.eval v <;> rfl
  | conj A1 A2 t1 t2 => simp[auxiliary, PropForm.eval]
              rw [t1, t2]
              simp[PropForm.eval]
              cases A1.eval v <;> cases A2.eval v <;> rfl
  | disj A1 A2 t1 t2 => simp[auxiliary, PropForm.eval]
              rw [t1, t2]
              simp[PropForm.eval]
              cases A1.eval v <;> cases A2.eval v <;> rfl
  | impl A1 A2 t1 t2 => simp[auxiliary, PropForm.eval]
              rw[t1, t2]
              simp[PropForm.eval]
              cases A1.eval v <;> cases A2.eval v <;> rfl
  |biImpl A1 A2 t1 t2 => simp[auxiliary, PropForm.eval]
              rw[t1, t2]
              simp[PropForm.eval]
              cases A1.eval v <;> cases A2.eval v <;> rfl

/--dit nog uitwerken-/
/-intro is introduceren van iets nieuws.-/
/-bij var ook 2 cases?-/
theorem substitution_theorem (A B C : PropForm) (t : String) : (⊨ (biImpl A B)) -> (⊨ (biImpl (substitution t A C) (substitution t B C))) := by
intro h
induction
 | tr => simp[substitution] rfl
 | fls => simp[substitution] rfl
 | var s => simp[substitution] rfl
 | neg A t => simp[substitution]
 | conj A1 A2 t1 t2 => sorry
 | disj A1 A2 t1 t2 =>  sorry
 | impl A1 A2 t1 t2 => sorry
 | biImpl A1 A2 t1 t2 => sorry


theorem duality_theorem (A B : PropForm) : (⊨ (biImpl A B)) ↔ (⊨ (biImpl (duality2 A) (duality2 B))) := by sorry
