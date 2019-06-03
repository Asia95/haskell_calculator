# haskell_calculator

## Calculator implemented in Haskell

  It can be used by providing the equation in the form of Tree
  ```
  evaluate [Fu "cos" (Op (Val 3) "+" (Val 4))]
  ```
  or in String, and the correct Tree structure will be build.
  ```
  evaluate' "cos ( 3 + 4 )"
  ```
