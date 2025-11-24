import MyLeanProject

def main : IO Unit := do
  IO.println "=== Propositional Logic Implementation ==="
  IO.println ""
  
  IO.println "--- Chapter 5.1: Syntax ---"
  IO.println s!"Example formula: {propExample}"
  IO.println s!"Complexity: {propExample.complexity}"
  IO.println s!"Depth: {propExample.depth}"
  IO.println s!"Variables: {propExample.vars}"
  IO.println ""
  
  IO.println "--- Chapter 5.2: Semantics ---"
  let testAssign := PropAssignment.mk [("p", true), ("q", true), ("r", true)]
  IO.println s!"Evaluation under assignment: {propExample.eval testAssign}"
  IO.println s!"Is valid: {propExample.isValid}"
  IO.println s!"Is satisfiable: {propExample.isSat}"
  IO.println ""
  
  IO.println "--- Chapter 5.3: Normal Forms ---"
  IO.println s!"NNF: {propExample.toNnfForm}"
  IO.println s!"CNF: {propExample.toCnfForm}"
