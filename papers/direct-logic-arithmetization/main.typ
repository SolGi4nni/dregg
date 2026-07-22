#let ink = rgb("18211d")
#let muted = rgb("5f6b65")
#let leaf = rgb("1f6148")
#let leaf-dark = rgb("174a38")
#let rule = rgb("ccd8d1")
#let moss = rgb("e7f0eb")
#let cream = rgb("fbfaf6")
#let rust = rgb("873b31")
#let amber = rgb("f2e7bd")
#let body-face = "Charter"
#let display-face = "Avenir Next"
#let mono-face = "Fira Code"

#set document(
  title: "Direct Logic Arithmetization, Corrected",
  author: "DREGG research note",
  date: datetime(year: 2026, month: 7, day: 22),
)
#set page(
  paper: "us-letter",
  margin: (top: 0.78in, bottom: 0.74in, left: 0.86in, right: 0.82in),
  fill: cream,
  header: context {
    if counter(page).get().first() > 2 {
      set text(font: display-face, size: 7.1pt, weight: 600, tracking: 0.07em, fill: muted)
      grid(
        columns: (1fr, auto),
        [DREGG / RESEARCH NOTE],
        [DIRECT LOGIC ARITHMETIZATION],
      )
      v(3pt)
      line(length: 100%, stroke: 0.45pt + rule)
    }
  },
  footer: context {
    if counter(page).get().first() > 1 {
      set text(font: display-face, size: 7.2pt, weight: 500, fill: muted)
      align(center)[#counter(page).display("1")]
    }
  },
)
#set text(font: body-face, size: 9.85pt, fill: ink, lang: "en", hyphenate: false)
#set par(justify: false, leading: 0.72em, spacing: 0.52em)
#set heading(numbering: "1.1", outlined: true)
#set list(indent: 1.12em, body-indent: 0.55em, spacing: 0.32em)
#set enum(indent: 1.12em, body-indent: 0.55em, spacing: 0.32em)
#set table(
  stroke: 0.4pt + rule,
  inset: (x: 6pt, y: 5.5pt),
  align: left + top,
)

#show heading.where(level: 1): it => {
  block(above: 0.08in, below: 0.72em, breakable: false)[
    #text(font: display-face, size: 7.4pt, weight: 700, tracking: 0.11em, fill: leaf)[
      SECTION #context counter(heading).display("1")
    ]
    #v(4pt)
    #text(font: display-face, size: 19.5pt, weight: 600, fill: ink, hyphenate: false)[#it.body]
    #v(7pt)
    #line(length: 100%, stroke: 0.9pt + leaf)
  ]
}
#show heading.where(level: 2): it => {
  block(above: 1.05em, below: 0.35em, breakable: false)[
    #text(font: display-face, size: 8pt, weight: 700, fill: muted)[
      #context counter(heading).display("1.1")
    ]
    #h(0.6em)
    #text(font: display-face, size: 12.2pt, weight: 600, fill: leaf-dark, hyphenate: false)[#it.body]
  ]
}
#show heading.where(level: 3): it => {
  block(above: 0.88em, below: 0.28em, breakable: false)[
    #text(font: display-face, size: 7.7pt, weight: 700, fill: muted)[
      #context counter(heading).display("1.1.1")
    ]
    #h(0.52em)
    #text(font: display-face, size: 10.25pt, weight: 600, fill: ink, hyphenate: false)[#it.body]
  ]
}
#show raw: it => box(
  fill: rgb("edf1ee"),
  inset: (x: 2.7pt, y: 1.1pt),
  radius: 1.5pt,
  text(font: mono-face, size: 7.65pt, fill: rgb("253a31"), it),
)
#show link: it => text(fill: leaf-dark, it)
#show table: it => block(above: 0.5em, below: 0.68em, breakable: false, it)

#let callout(title, body, tone: leaf) = block(
  width: 100%,
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

#set align(left)
#v(0.08in)
#grid(
  columns: (1fr, auto),
  align: (left, right),
  text(font: display-face, size: 7.8pt, weight: 700, tracking: 0.11em, fill: leaf)[DREGG / RESEARCH NOTE 01],
  text(font: display-face, size: 7.8pt, weight: 600, tracking: 0.07em, fill: muted)[22 JULY 2026],
)
#v(0.72in)
#line(length: 42pt, stroke: 2.2pt + leaf)
#v(0.18in)
#block(width: 100%)[
  #set par(leading: 0.08em, spacing: 0pt)
  #text(font: display-face, size: 31pt, weight: 600, fill: ink, hyphenate: false)[
    Direct Logic\
    Arithmetization, Corrected
  ]
]
#v(0.24in)
#block(width: 84%)[
  #text(font: display-face, size: 13pt, weight: 450, fill: leaf-dark, hyphenate: false)[
    Sound finite-field compilation, finite higher-order polynomial semantics, and proof objects beyond polynomials
  ]
]
#v(0.58in)
#grid(
  columns: (0.88fr, 3.12fr),
  column-gutter: 15pt,
  row-gutter: 16pt,
  align: (left + top, left + top),
  [
    #text(font: display-face, size: 7.1pt, weight: 700, tracking: 0.11em, fill: leaf)[THE CLAIM]
  ],
  [
    #text(font: display-face, size: 11.2pt, weight: 600, fill: ink)[Direct first-order arithmetization promises an unusually short route from logic to polynomial constraints.]
  ],
  [
    #text(font: display-face, size: 7.1pt, weight: 700, tracking: 0.11em, fill: leaf)[THE RESULT]
  ],
  [
    #text(font: body-face, size: 10.3pt, fill: ink)[A formal construction suite for sound direct logic: corrected FOL, finite higher-order semantics, live DREGG descriptors, executable conformance, and encrypted evaluation.]
  ],
)
#v(0.62in)
#block(width: 100%, fill: moss, inset: (x: 15pt, y: 13pt), radius: 2pt)[
  #text(font: display-face, size: 7pt, weight: 700, tracking: 0.11em, fill: leaf)[EVIDENCE STANDARD]
  #v(4pt)
  #text(font: body-face, size: 9.2pt, fill: ink)[
    This report distinguishes proved mathematics, checked executable models, theorem interfaces, implementation evidence, and future work. Performance claims are not inferred from algebra alone.
  ]
]
#v(1fr)
#line(length: 100%, stroke: 0.5pt + rule)
#v(8pt)
#grid(
  columns: (1fr, auto),
  text(font: display-face, size: 7.2pt, weight: 600, fill: muted)[FORMALIZATION-BACKED REPORT],
  text(font: display-face, size: 7.2pt, weight: 600, fill: muted)[DREGG],
)

#pagebreak()
#v(0.12in)
#text(font: display-face, size: 7.3pt, weight: 700, tracking: 0.11em, fill: leaf)[REPORT MAP]
#v(3pt)
#text(font: display-face, size: 22pt, weight: 600, fill: ink)[Contents]
#v(7pt)
#line(length: 100%, stroke: 0.8pt + leaf)
#v(0.24in)
#block[
  #set text(font: display-face, size: 8.45pt, fill: ink, hyphenate: false)
  #set par(leading: 0.48em, spacing: 0.17em)
  #outline(title: none, depth: 2, indent: 1.1em)
]

#pagebreak()
#include "sections/01-findings.typ"
#pagebreak()
#include "sections/02-gabbay-bitlogic.typ"
#pagebreak()
#include "sections/03-corrected-constructions.typ"
#include "sections/04-hol-ccc-limits.typ"
#pagebreak()
#include "sections/05-proofobjects-topos.typ"
#pagebreak()
#include "sections/06-pipeline-fhe-dregg.typ"
#pagebreak()
#include "sections/07-conclusion.typ"
#include "sections/08-references.typ"
