(program
  1.1.0
  (lam
    x-0
    [
      [ [ (force (builtin ifThenElse)) (con bool True) ] (con integer 7) ]
      [
        (builtin lengthOfByteString)
        [
          (builtin encodeUtf8)
          [
            (builtin decodeUtf8)
            [
              [
                [
                  (force (builtin ifThenElse))
                  [ [ (builtin equalsInteger) x-0 ] (con integer 0) ]
                ]
                (con bytestring #ff)
              ]
              (con bytestring #61)
            ]
          ]
        ]
      ]
    ]
  )
)