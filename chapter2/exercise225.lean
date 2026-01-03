def main : IO Unit := do
  let englishGreeting := IO.println "Hello!" -- no side effect yet
  IO.println "Bonjour!" -- side effect
  englishGreeting -- side effect
