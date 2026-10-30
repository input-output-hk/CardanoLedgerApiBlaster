(program
  1.1.0
  (lam
    x-0
    [
      [
        [ (force (force (builtin chooseList))) (con (list integer) [1]) ]
        [ [ (builtin divideInteger) (con integer 1) ] x-0 ]
      ]
      (con integer 7)
    ]
  )
)