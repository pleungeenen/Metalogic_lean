import metalogica_lean_project.metalogica_functions

open PropForm

inductive Lit where
  | tr  : Lit
  | fls : Lit
  | pos : String → Lit
  | neg : String → Lit
  deriving Repr, DecidableEq

inductive NnfForm where
  | lit  (l : Lit)       : NnfForm
  | conj (p q : NnfForm) : NnfForm
  | disj (p q : NnfForm) : NnfForm
  deriving Repr

def Lit.negate : Lit → Lit
  | tr   => fls
  | fls  => tr
  | pos s => neg s
  | neg s => pos s

def NnfForm.neg : NnfForm → NnfForm
  | lit l    => lit l.negate
  | conj p q => disj (neg p) (neg q)
  | disj p q => conj (neg p) (neg q)

namespace PropForm

def toNnfForm : PropForm → NnfForm
  | tr         => NnfForm.lit Lit.tr
  | fls        => NnfForm.lit Lit.fls
  | var n      => NnfForm.lit (Lit.pos n)
  | neg p      => p.toNnfForm.neg
  | conj p q   => NnfForm.conj p.toNnfForm q.toNnfForm
  | disj p q   => NnfForm.disj p.toNnfForm q.toNnfForm
  | impl p q   => NnfForm.disj p.toNnfForm.neg q.toNnfForm
  | biImpl p q => NnfForm.conj (NnfForm.disj p.toNnfForm.neg q.toNnfForm)
                               (NnfForm.disj q.toNnfForm.neg p.toNnfForm)

end PropForm

def Clause := List Lit

def CnfForm := List Clause

def Lit.toString : Lit → String
  | tr => "⊤"
  | fls => "⊥"
  | pos s => s
  | neg s => "¬" ++ s

instance : ToString Lit where
  toString := Lit.toString

def Clause.toString (c : Clause) : String :=
  if c.isEmpty then "⊥"
  else "(" ++ String.intercalate " ∨ " (c.map Lit.toString) ++ ")"

instance : ToString Clause where
  toString := Clause.toString

def CnfForm.toString (cnf : CnfForm) : String :=
  if cnf.isEmpty then "⊤"
  else String.intercalate " ∧ " (cnf.map Clause.toString)

instance : ToString CnfForm where
  toString := CnfForm.toString

def NnfForm.toString : NnfForm → String
  | lit l => l.toString
  | conj p q => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
  | disj p q => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"

instance : ToString NnfForm where
  toString := NnfForm.toString

def unionClause (l1 l2 : List Lit) : List Lit :=
  l1 ++ (l2.filter (fun x => !l1.contains x))

def conjCnf (cnf1 cnf2 : List (List Lit)) : List (List Lit) :=
  cnf1 ++ cnf2

def disjCnf (cnf1 cnf2 : List (List Lit)) : List (List Lit) :=
  (cnf1.map (fun cls => cnf2.map (unionClause cls ·))).flatten

def NnfForm.toCnfForm : NnfForm → CnfForm
  | NnfForm.lit (Lit.pos s) => [ [Lit.pos s] ]
  | NnfForm.lit (Lit.neg s) => [ [Lit.neg s] ]
  | NnfForm.lit Lit.tr      => []
  | NnfForm.lit Lit.fls     => [ [] ]
  | NnfForm.conj A B        => conjCnf A.toCnfForm B.toCnfForm
  | NnfForm.disj A B        => disjCnf A.toCnfForm B.toCnfForm

def PropForm.toCnfForm (A : PropForm) : CnfForm :=
  A.toNnfForm.toCnfForm

#eval propExample.toNnfForm
#eval propExample.toNnfForm.toString
#eval propExample.toCnfForm
#eval propExample.toCnfForm.toString

def testFormula1 := conj (conj (var "p1") (var "p2")) (disj (var "q1") (var "q2"))
#eval testFormula1.toCnfForm.toString
 def testFormula2 := disj (disj (conj (var "p1") (var "p2")) (conj (var "q1") (var "q2")))
                         (disj (conj (var "r1") (var "r2")) (conj (var "s1") (var "s2")))
#eval testFormula2.toCnfForm.toString
