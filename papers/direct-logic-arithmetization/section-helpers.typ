#let leaf = rgb("35634b")
#let moss = rgb("dce8dd")
#let rust = rgb("8c3f2f")
#let amber = rgb("f0e5bf")

#let callout(title, body, tone: leaf) = block(
  width: 100%,
  breakable: false,
  fill: if tone == rust { rgb("f3e2dc") } else if tone == amber { amber } else { moss },
  stroke: (left: 3pt + tone),
  inset: (x: 10pt, y: 8pt),
  radius: 2pt,
  above: 0.6em,
  below: 0.7em,
)[
  #text(weight: "bold", fill: tone)[#title]
  #h(0.5em)
  #body
]

#let theorem(name, body) = callout(
  [FORMAL ARTIFACT - #name],
  body,
)

#let boundary(body) = callout([BOUNDARY], body, tone: rust)
