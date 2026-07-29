/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import ZetaZeroCounting.Xi
public import ZetaZeroCounting.ZeroCounting
public import ZetaZeroCounting.SafeHeights
public import ZetaZeroCounting.MainTerm

/-!
# Zero-counting infrastructure for the Riemann zeta function

This file collects the `ZetaZeroCounting` package: the entire Xi function,
nontrivial zeros, zero-counting with multiplicities, safe heights, and the
von Mangoldt main term.
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The code is intentionally separate from the mathematical namespace:
it illustrates `criticalBox T`, `zerosUpToIm T`, and `IsSafeHeight T`, but it
does not add mathematical assumptions or alter the API of the formal package.
-/

namespace ZetaZeroCountingGraph

structure ZeroPoint where
  re : Float
  im : Float
  deriving Repr

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  strip : String := "#eaf2fb"
  box : String := "#1f5fd1"
  criticalLine : String := "#475569"
  safeHeight : String := "#b91c1c"
  zero : String := "#111827"
  muted : String := "#475569"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1900.0
def height : Float := 1400.0

def plotLeft : Float := 150.0
def plotRight : Float := 1770.0
def plotTop : Float := 240.0
def plotBottom : Float := 1130.0

def xMin : Float := -0.08
def xMax : Float := 1.08
def yMin : Float := 0.0
def yMax : Float := 40.0

def safeHeightT : Float := 31.8

def zeroPoints : List ZeroPoint := [
  ⟨0.46, 14.134725141734693⟩,
  ⟨0.53, 21.022039638771554⟩,
  ⟨0.49, 25.010857580145688⟩,
  ⟨0.52, 30.424876125859513⟩,
  ⟨0.50, 32.935061587739189⟩,
  ⟨0.55, 37.586178158825671⟩
]

def localOutputPath : System.FilePath :=
  "ZetaZeroCounting.svg"

def repositoryOutputDir : System.FilePath :=
  "ZetaZeroCounting"

def repositoryOutputPath : System.FilePath :=
  "ZetaZeroCounting/ZetaZeroCounting.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String :=
  toString x

def px (re : Float) : Float :=
  plotLeft + ((re - xMin) / (xMax - xMin)) * (plotRight - plotLeft)

def py (im : Float) : Float :=
  plotBottom - ((im - yMin) / (yMax - yMin)) * (plotBottom - plotTop)

def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

def attrs (xs : List (String × String)) : String :=
  xs.foldl (fun acc (k, v) => acc ++ " " ++ k ++ "=\"" ++ esc v ++ "\"") ""

def tag (name : String) (xs : List (String × String)) (body : String := "") : String :=
  if body.isEmpty then
    s!"  <{name}{attrs xs}/>\n"
  else
    s!"  <{name}{attrs xs}>{body}</{name}>\n"

def line (x1 y1 x2 y2 : Float) (color : String) (w : Float)
    (dash : Option String := none) : String :=
  let base := [
    ("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
    ("stroke", color), ("stroke-width", fstr w), ("fill", "none")
  ]
  let extra := match dash with
    | none => base
    | some d => base ++ [("stroke-dasharray", d)]
  tag "line" extra

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

def circle (cx cy r : Float) (fill stroke : String) (sw : Float := 0.0) : String :=
  tag "circle" [
    ("cx", fstr cx), ("cy", fstr cy), ("r", fstr r),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]

def textAt (x y : Float) (content : String) (size : Nat) (color : String)
    (anchor : String := "middle") (extra : List (String × String) := []) : String :=
  tag "text" ([
    ("x", fstr x), ("y", fstr y), ("font-size", toString size),
    ("fill", color), ("text-anchor", anchor), ("font-family", "DejaVu Serif, Georgia, serif")
  ] ++ extra) (esc content)

def horizontalGrid : String :=
  [0.0, 10.0, 20.0, 30.0].foldl (fun out t =>
    out ++ line plotLeft (py t) plotRight (py t) "#d1d5db" 0.7 (some "4 6") ++
    textAt (plotLeft - 28.0) (py t + 7.0) (toString t.toUInt64) 24 style.axis "end"
  ) ""

def verticalGrid : String :=
  [0.0, 0.5, 1.0].foldl (fun out x =>
    out ++ line (px x) plotTop (px x) plotBottom "#e5e7eb" 0.65 (some "4 6")
  ) ""

def axesAndTicks : String :=
  horizontalGrid ++ verticalGrid ++
  line plotLeft plotBottom plotRight plotBottom style.axis 2.2 ++
  line plotLeft plotTop plotLeft plotBottom style.axis 2.2 ++
  textAt (px 0.0) (plotBottom + 42.0) "0" 26 style.axis ++
  textAt (px 0.5) (plotBottom + 42.0) "1/2" 26 style.axis ++
  textAt (px 1.0) (plotBottom + 42.0) "1" 26 style.axis ++
  textAt ((plotLeft + plotRight) / 2.0) (plotBottom + 95.0) "Re(s)" 30 style.axis ++
  textAt (plotLeft - 90.0) ((plotTop + plotBottom) / 2.0) "Im(s)" 30 style.axis "middle"
    [("transform", s!"rotate(-90 {fstr (plotLeft - 90.0)} {fstr ((plotTop + plotBottom) / 2.0)})")] ++
  textAt (plotLeft - 28.0) (py safeHeightT + 8.0) "T_safe" 26 style.axis "end"

def criticalBoxSvg : String :=
  let x0 := px 0.0
  let x1 := px 1.0
  let y0 := py safeHeightT
  let y1 := py 0.0
  rect x0 y0 (x1 - x0) (y1 - y0) "none" style.box 4.2 ++
  line plotLeft y0 plotRight y0 style.safeHeight 4.0 (some "34 16") ++
  line (px 0.5) plotTop (px 0.5) plotBottom style.criticalLine 2.6 (some "12 12")

def zeroMarkersAux : List ZeroPoint → Nat → String
  | [], _ => ""
  | z :: zs, i =>
    let cx := px z.re
    let cy := py z.im
    let here :=
      if z.im <= safeHeightT then
        circle cx cy 9.5 style.zero style.white 1.6 ++
        textAt (cx + 24.0) (cy - 5.0) s!"rho_{i + 1}" 21 style.muted "start"
      else
        circle cx cy 9.0 "none" style.muted 3.0
    here ++ zeroMarkersAux zs (i + 1)

def zeroMarkers : String :=
  zeroMarkersAux zeroPoints 0

def annotations : String :=
  textAt (px 0.03) (py safeHeightT - 24.0)
    "safe height: no rho in nontrivialZeros has Im(rho) = T" 25 style.safeHeight "start" ++
  textAt (px 0.03) (py 2.4) "criticalBox(T)" 28 style.box "start" ++
  textAt (px 0.03) (py 0.8)
    "bottom edge in criticalBox(T); counted zeros require Im(s) > 0" 21 style.muted "start" ++
  textAt (px 0.58) (py 18.0) "sample zeros in zerosUpToIm(T)" 23 style.axis "start" ++
  textAt (px 0.56) (py 33.6) "above T, not counted" 22 style.muted "start" ++
  textAt (px 0.5 + 70.0) (py 8.5) "critical line Re(s) = 1/2" 22 style.criticalLine "middle"
    [("transform", s!"rotate(-90 {fstr (px 0.5 + 70.0)} {fstr (py 8.5)})")]

def titleBlock : String :=
  textAt (width / 2.0) 62.0 "ZetaZeroCounting" 54 style.axis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0 "Critical box, counted zeros, and a safe height" 34 style.muted

def footer : String :=
  textAt (width / 2.0) 1350.0
    "Illustration of formal objects in ZetaZeroCounting: criticalBox T, zerosUpToIm T, IsSafeHeight T."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) "none" style.axis 2.4 ++
  rect (px 0.0) plotTop (px 1.0 - px 0.0) (plotBottom - plotTop) style.strip "none" 0.0 (some 0.74) ++
  axesAndTicks ++
  criticalBoxSvg ++
  zeroMarkers ++
  annotations ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end ZetaZeroCountingGraph

#eval ZetaZeroCountingGraph.writeDefault
