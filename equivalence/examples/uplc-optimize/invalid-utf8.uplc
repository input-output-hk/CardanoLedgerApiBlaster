(program
  1.1.0
  (lam
    x-0
    [
      [ [ (force (builtin ifThenElse)) (con bool True) ] (con integer 7) ]
      (force
        [
          [
            [
              (force (builtin ifThenElse))
              [ [ (builtin equalsInteger) x-0 ] (con integer 0) ]
            ]
            (delay
              [
                (builtin lengthOfByteString)
                [
                  (builtin encodeUtf8)
                  [ (builtin decodeUtf8) (con bytestring #ff) ]
                ]
              ]
            )
          ]
          (delay (con integer 1))
        ]
      )
    ]
  )
)