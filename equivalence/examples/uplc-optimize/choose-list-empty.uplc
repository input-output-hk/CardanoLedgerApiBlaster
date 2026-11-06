(program
  1.1.0
  (lam
    x-0
    [
      [
        [ (force (force (builtin chooseList))) (con (list integer) []) ]
        (con integer 7)
      ]
      [ [ (builtin divideInteger) (con integer 1) ] x-0 ]
    ]
  )
)