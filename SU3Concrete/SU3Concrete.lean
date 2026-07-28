/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import SU3Concrete.GellMann
public import SU3Concrete.LieAlgebra
public import SU3Concrete.StructureConstants
public import SU3Concrete.Commutator
public import SU3Concrete.Representation

/-!
# Concrete `su(3)`: Gell-Mann matrices, adjoint, Killing form and Casimirs

This is the root module for the standalone `SU3Concrete` package.  It packages
the concrete `su(3)` material around Gell-Mann matrices: the anti-Hermitian
generators, the matrix commutator Lie algebra, explicit structure constants, the
Gell-Mann commutator table, the adjoint representation, the Killing form, the
Cartan pair, and the fundamental Casimir.

## Main results

- `Physics.YangMills.gellMannGenerator_antiHermitian`.
- `Physics.YangMills.generator_commutator_matrix`.
- `Physics.YangMills.structureConstant_jacobi`.
- `Physics.YangMills.adjointCasimir_diagonal`.
- `Physics.YangMills.killingFormBasis_diagonal`.
- `Physics.YangMills.fundamentalCasimir_diagonal`.

## Tags

su(3), Gell-Mann matrices, Lie algebra, Yang-Mills
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The diagram shows the `A₂` root hexagon of `su(3)` in the Cartan
plane, together with the formal identities certified by the package.
-/

namespace SU3ConcreteGraph

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  grid : String := "#d1d5db"
  root : String := "#0f766e"
  rootAlt : String := "#1f5fd1"
  critical : String := "#b91c1c"
  muted : String := "#475569"
  pale : String := "#f0fdf4"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1800.0
def height : Float := 1400.0

def cx : Float := 900.0
def cy : Float := 690.0
def radius : Float := 330.0

def localOutputPath : System.FilePath :=
  "SU3Concrete.svg"

def repositoryOutputDir : System.FilePath :=
  "M4TH/SU3Concrete"

def repositoryOutputPath : System.FilePath :=
  "M4TH/SU3Concrete/SU3Concrete.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String :=
  toString x

def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

def attrs (xs : List (String × String)) : String :=
  xs.foldl (fun acc (k, v) => acc ++ " " ++ k ++ "=\"" ++ esc v ++ "\"") ""

def tag (name : String) (xs : List (String × String)) (body : String := "") : String :=
  if body.isEmpty then
    s!"  <{name}{attrs xs}/>\n"
  else
    s!"  <{name}{attrs xs}>{esc body}</{name}>\n"

def line (x1 y1 x2 y2 : Float) (color : String) (w : Float)
    (dash : Option String := none) (extra : List (String × String) := []) : String :=
  let base := [
    ("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
    ("stroke", color), ("stroke-width", fstr w), ("fill", "none")
  ]
  let dashed := match dash with
    | none => base
    | some d => base ++ [("stroke-dasharray", d)]
  tag "line" (dashed ++ extra)

def rect (x y w h : Float) (fill stroke : String) (sw : Float)
    (opacity : Option Float := none) : String :=
  let base := [
    ("x", fstr x), ("y", fstr y), ("width", fstr w), ("height", fstr h),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]
  let extra := match opacity with
    | none => base
    | some a => base ++ [("opacity", fstr a)]
  tag "rect" extra

def circle (x y r : Float) (fill stroke : String) (sw : Float := 0.0) : String :=
  tag "circle" [
    ("cx", fstr x), ("cy", fstr y), ("r", fstr r),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]

def polyline (points color : String) (w : Float) : String :=
  tag "polyline" [
    ("points", points), ("stroke", color), ("stroke-width", fstr w),
    ("fill", "none"), ("stroke-linejoin", "round"), ("stroke-linecap", "round")
  ]

def textAt (x y : Float) (content : String) (size : Nat) (color : String)
    (anchor : String := "middle") (extra : List (String × String) := []) : String :=
  tag "text" ([
    ("x", fstr x), ("y", fstr y), ("font-size", toString size),
    ("fill", color), ("text-anchor", anchor), ("font-family", "DejaVu Serif, Georgia, serif")
  ] ++ extra) (esc content)

def arrowDefs : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow-root\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"8\" markerHeight=\"8\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#0f766e\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def tx (x : Float) : Float :=
  cx + radius * x

def ty (y : Float) : Float :=
  cy - radius * y

def rootPoints : List (Float × Float × String) := [
  (cx + radius, cy, "α₁"),
  (cx + radius / 2.0, cy - 285.8, "α₁+α₂"),
  (cx - radius / 2.0, cy - 285.8, "α₂"),
  (cx - radius, cy, "-α₁"),
  (cx - radius / 2.0, cy + 285.8, "-α₁-α₂"),
  (cx + radius / 2.0, cy + 285.8, "-α₂")
]

def pointString (p : Float × Float × String) : String :=
  let (x, y, _) := p
  s!"{fstr x},{fstr y}"

def hexagon : String :=
  let pts := String.intercalate " " ((rootPoints.map pointString) ++ [pointString rootPoints.head!])
  polyline pts style.root 4.0

def radialLines : String :=
  rootPoints.foldl (fun out p =>
    let (x, y, _) := p
    out ++ line cx cy x y style.grid 1.3 (some "8 8")
  ) ""

def roots : String :=
  rootPoints.foldl (fun out p =>
    let (x, y, label) := p
    out ++ circle x y 10.0 style.root style.white 2.0 ++
      textAt x (y - 22.0) label 25 style.axis
  ) ""

def cartanAxes : String :=
  line (tx (-1.2)) (ty 0.0) (tx 1.2) (ty 0.0) style.axis 2.0 ++
  line (tx 0.0) (ty (-1.2)) (tx 0.0) (ty 1.2) style.axis 2.0 ++
  textAt (tx 1.18) (ty 0.0 + 8.0) "T₃" 27 style.axis "start" ++
  textAt (tx 0.0 - 25.0) (ty 1.16) "T₈" 27 style.axis "end" ++
  textAt cx (cy + 48.0) "Cartan plane" 24 style.muted

def rootLines : String :=
  -- Positive and negative roots in the `(T₃,T₈)` plane.
  -- No residual dashed center-to-right line: the visible ray is exactly `I₊`.
  line (tx 0.0) (ty 0.0) (tx 1.0) (ty 0.0) style.root 3.5 none
    [("marker-end", "url(#arrow-root)")] ++
  line (tx 0.0) (ty 0.0) (tx 0.5) (ty 0.866) style.root 3.5 none
    [("marker-end", "url(#arrow-root)")] ++
  line (tx 0.0) (ty 0.0) (tx (-0.5)) (ty 0.866) style.root 3.5 none
    [("marker-end", "url(#arrow-root)")] ++
  line (tx 0.0) (ty 0.0) (tx (-1.0)) (ty 0.0) style.root 3.5 none
    [("marker-end", "url(#arrow-root)")] ++
  line (tx 0.0) (ty 0.0) (tx (-0.5)) (ty (-0.866)) style.root 3.5 none
    [("marker-end", "url(#arrow-root)")] ++
  line (tx 0.0) (ty 0.0) (tx 0.5) (ty (-0.866)) style.root 3.5 none
    [("marker-end", "url(#arrow-root)")]

def labels : String :=
  textAt (tx 1.0 + 25.0) (ty 0.0 + 8.0) "I₊" 24 style.root "start" ++
  textAt (tx (-1.0) - 25.0) (ty 0.0 + 8.0) "I₋" 24 style.root "end" ++
  textAt (tx 0.5 + 22.0) (ty 0.866 - 18.0) "V₊" 24 style.root "start" ++
  textAt (tx (-0.5) - 28.0) (ty 0.866 - 16.0) "U₊" 24 style.root "end" ++
  textAt (tx (-0.5) - 26.0) (ty (-0.866) + 28.0) "V₋" 24 style.root "end" ++
  textAt (tx 0.5 + 30.0) (ty (-0.866) + 28.0) "U₋" 24 style.root "start"

def leftPanel : String :=
  let x := 145.0
  let y := 295.0
  rect x y 455.0 154.0 style.white "#cbd5e1" 1.5 (some 0.96) ++
  textAt (x + 26.0) (y + 40.0) "anti-Hermitian generators" 21 style.axis "start" ++
  textAt (x + 26.0) (y + 76.0) "Tᵃ = i λₐ" 23 style.critical "start" ++
  textAt (x + 26.0) (y + 112.0) "[Tᵃ,Tᵇ] = -2 f^{abc} Tᶜ" 21 style.muted "start"

def rightPanel : String :=
  let x := 1200.0
  let y := 295.0
  rect x y 455.0 154.0 style.white "#cbd5e1" 1.5 (some 0.96) ++
  textAt (x + 26.0) (y + 40.0) "certified invariants" 21 style.axis "start" ++
  textAt (x + 26.0) (y + 76.0) "κ(Tᵃ,Tᵇ) = -3 δᵃᵇ" 22 style.root "start" ++
  textAt (x + 26.0) (y + 112.0) "∑ₐ TᵃTᵃ = -(16/3) I₃" 21 style.muted "start"

def bottomPanel : String :=
  let x := 615.0
  let y := 1088.0
  rect x y 570.0 92.0 style.white "#cbd5e1" 1.5 (some 0.96) ++
  textAt (x + 285.0) (y + 38.0) "structureConstant_jacobi" 22 style.axis ++
  textAt (x + 285.0) (y + 68.0) "finite certificate over Fin 8" 20 style.muted

def titleBlock : String :=
  textAt (width / 2.0) 66.0 "SU3Concrete" 54 style.axis ++
  textAt (width / 2.0) 100.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0 "Concrete su(3), Gell-Mann generators, structure constants, and Casimirs" 32 style.muted

def footer : String :=
  textAt (width / 2.0) 1348.0
    "Illustration of formal objects in SU3Concrete: gellMannGenerator, structureConstant, adjointCasimir, killingFormBasis, fundamentalCasimir."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowDefs ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  circle cx cy 405.0 style.pale "none" 0.0 ++
  cartanAxes ++
  rootLines ++
  labels ++
  circle cx cy 8.0 style.axis style.white 2.0 ++
  leftPanel ++
  rightPanel ++
  bottomPanel ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end SU3ConcreteGraph

#eval SU3ConcreteGraph.writeDefault
