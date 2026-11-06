(program
  1.1.0
  (lam
    x-0
    [
      [
        [
          [
            [
              [ (force (builtin chooseData)) (con data (I 0)) ]
              [
                [ (builtin divideInteger) (con integer 1) ]
                [ [ (builtin subtractInteger) x-0 ] (con integer 42) ]
              ]
            ]
            [
              [ (builtin divideInteger) (con integer 1) ]
              [ [ (builtin subtractInteger) x-0 ] (con integer 42) ]
            ]
          ]
          [
            [ (builtin divideInteger) (con integer 1) ]
            [ [ (builtin subtractInteger) x-0 ] (con integer 42) ]
          ]
        ]
        (con integer 9)
      ]
      [
        [ (builtin divideInteger) (con integer 1) ]
        [ [ (builtin subtractInteger) x-0 ] (con integer 42) ]
      ]
    ]
  )
)