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

theorem duality_theorem (A B : PropForm) : (⊨ (biImpl A B)) ↔ (⊨ (biImpl (duality2 A) (duality2 B))) := by sorry

def testAssignment := PropAssignment.mk [("p", true), ("q", true), ("r", true)]

#eval propExample.eval testAssignment
#eval allSublists propExample.vars
#eval truthTable propExample
#eval propExample.isValid
#eval propExample.isSat
