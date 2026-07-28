name: pair-closed
version: 1.0
description: Closed pair theory (bool+function+pair inlined; only base axioms remain)
author: ember
license: MIT
show: "Data.Bool"
show: "Data.Pair"
show: "Function"

b {
  package: bool-1.37
}

f {
  import: b
  package: function-1.55
}

main {
  import: b
  import: f
  package: pair-1.30
}
