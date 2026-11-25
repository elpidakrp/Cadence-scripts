#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
tia_tb_gen.py - generate a complete TIA characterisation testbench
(open-loop + closed-loop schematics and an ADE Maestro view) in Cadence
Virtuoso from one plain-text configuration file (tia_specs.txt).

Run it from the directory where you normally start Virtuoso (the one that
holds cds.lib):

    python3 tia_tb_gen.py                          # reads ./tia_specs.txt
    python3 tia_tb_gen.py my_specs.txt
    python3 tia_tb_gen.py my_specs.txt --inspect   # report pins/devices/variables only
    python3 tia_tb_gen.py my_specs.txt --dry-run   # write the build SKILL, change nothing
    python3 tia_tb_gen.py my_specs.txt --overwrite # rebuild an existing testbench cell

Created in <tb_library>/<tb_cell>:

  schematic       open loop: DC feedback through very large inductors, AC drive
                  on the inputs -> open-loop gain, UGF, phase margin, bias point
  schematic_w_fb  closed loop: current-source input with source R/C, RF||CF
                  feedback, load capacitors, loop-gain (stb) probes
  maestro         tests OL_DC_AC, FB_AC, FB_NOISE, FB_STB_*, FB_TRAN with their
                  outputs, specs, global variables and corners, plus one output
                  per transistor and per metric (region, vsat_marg, gmoverid,
                  ...) for every MOSFET found in the TIA hierarchy

Loop stability: FB_STB_DM / FB_STB_CM run stb in differential / common mode on
a diffstbprobe placed between the outputs and the feedback network;
FB_STB_CMFB runs single-ended stb on an iprobe that the user places inside the
CMFB loop of the TIA (see cmfb_probe); single-ended TIAs get FB_STB on an iprobe.
Noise: FB_NOISE uses the input current source as the input-referred noise port.

Nothing technology specific is built in: transistors are recognised by their
terminals (D G S [B]), sources and passives come from analogLib, and model
files, variables and corners come from the configuration file.

Requires Python >= 3.6 and `virtuoso` on PATH. No simulation is started.
"""
from __future__ import print_function

import argparse
import configparser
import fnmatch
import itertools
import os
import re
import shutil
import subprocess
import sys
import tempfile

VERSION = '1.0'
DUT = 'I0'                     # instance name of the TIA in both schematics


class ConfigError(Exception):
    pass


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------
_SI = {'T': 1e12, 'G': 1e9, 'M': 1e6, 'K': 1e3, 'k': 1e3, '': 1.0,
       'm': 1e-3, 'u': 1e-6, 'n': 1e-9, 'p': 1e-12, 'f': 1e-15, 'a': 1e-18}
_NUM = re.compile(r'^([+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?)([TGMKkmunpfa]?)$')
_IDENT = re.compile(r'(?<![\w.$])([A-Za-z_][A-Za-z0-9_]*)(?![\w(])(?!\s*\()')
_EXPR_BUILTINS = {'t', 'nil', 'pi', 'temp', 'tnom', 'freq', 'time', 'true', 'false'}


def si(text):
    """'1k' -> 1000.0, '2u' -> 2e-06, '45M' -> 4.5e7; None if not a number."""
    m = _NUM.match(str(text).strip())
    return float(m.group(1)) * _SI[m.group(2)] if m else None


def num(x):
    return format(x, '.12g')


def eng(x):
    """4.5e7 -> '45M' (for output and corner names)."""
    for scale, suffix in ((1e9, 'G'), (1e6, 'M'), (1e3, 'k'), (1.0, '')):
        if abs(x) >= scale:
            return format(x / scale, '.6g') + suffix
    return format(x, '.6g')


def fname(f):
    """Frequency -> name fragment: 1e6 -> '1MHz', 1.5e6 -> '1p5MHz'."""
    return eng(f).replace('.', 'p') + 'Hz'


def identifiers(expr):
    """Design-variable candidates inside a value/expression string."""
    expr = re.sub(r'"[^"]*"', '', expr)
    return {m.group(1) for m in _IDENT.finditer(expr)} - _EXPR_BUILTINS


def q(s):
    """Escape a Python string for a double-quoted SKILL string literal."""
    return (str(s).replace('\\', '\\\\').replace('"', '\\"')
            .replace('\n', '\\n').replace('\r', ''))


def sk(v):
    """Python value -> SKILL literal (lists become list(...))."""
    if v is True:
        return 't'
    if v is False or v is None:
        return 'nil'
    if isinstance(v, (int, float)):
        return num(v)
    if isinstance(v, (list, tuple)):
        return 'list(' + ' '.join(sk(x) for x in v) + ')'
    return '"' + q(v) + '"'


def yes(value, where):
    v = str(value).strip().lower()
    if v in ('yes', 'y', 'true', 'on', '1'):
        return True
    if v in ('no', 'n', 'false', 'off', '0'):
        return False
    raise ConfigError('{}: expected yes/no, got {!r}'.format(where, value))


def bus_width(term):
    m = re.search(r'<(\d+):(\d+)(?::\d+)?>$', term)
    return abs(int(m.group(1)) - int(m.group(2))) + 1 if m else 1


def expand_iterated(path):
    """'/X1/M3<0:2>' -> ['/X1/M3<0>', '/X1/M3<1>', '/X1/M3<2>']."""
    m = re.match(r'^(.*)<(\d+):(\d+)>$', path)
    if not m:
        return [path]
    a, b = int(m.group(2)), int(m.group(3))
    step = 1 if b >= a else -1
    return ['{}<{}>'.format(m.group(1), i) for i in range(a, b + step, step)]


def parse_spec(text, where):
    """Spec syntax -> None | ('gt', v) | ('lt', v) | ('range', lo, hi) | ('tol', target, pct)."""
    parts = str(text).split()
    if not parts or parts[0].lower() in ('none', 'off', '-'):
        return None
    kind = {'>': 'gt', '<': 'lt'}.get(parts[0], parts[0].lower())
    nargs = {'gt': 1, 'lt': 1, 'range': 2, 'tol': 2}.get(kind)
    if nargs is None or len(parts) != nargs + 1:
        raise ConfigError('{}: spec must be one of: none | gt V | lt V | range MIN MAX | '
                          'tol TARGET PERCENT (got {!r})'.format(where, text))
    vals = parts[1:]
    for v in vals:
        if si(v) is None:
            raise ConfigError('{}: {!r} is not a number'.format(where, v))
    if kind == 'range' and si(vals[0]) > si(vals[1]):
        raise ConfigError('{}: range MIN is larger than MAX'.format(where))
    if kind == 'tol' and si(vals[1]) < 0:
        raise ConfigError('{}: tolerance percent cannot be negative'.format(where))
    return tuple([kind] + vals)


def spec_text(spec):
    return 'none' if not spec else ' '.join(spec)


# ---------------------------------------------------------------------------
# configuration file
# ---------------------------------------------------------------------------
class Config(object):
    """Thin case-insensitive wrapper around configparser (values keep case)."""

    def __init__(self, path):
        cp = configparser.ConfigParser(interpolation=None, strict=True,
                                       inline_comment_prefixes=('#',),
                                       empty_lines_in_values=False)
        cp.optionxform = str
        with open(path, 'r') as f:
            cp.read_file(f)
        self.cp = cp
        self.path = path
        self.names = {s.lower(): s for s in cp.sections()}

    def items(self, section):
        s = self.names.get(section.lower())
        return [(k, v.strip()) for k, v in self.cp.items(s)] if s else []

    def get(self, section, key, default=None):
        for k, v in self.items(section):
            if k.lower() == key.lower():
                return v
        return default

    def need(self, section, key):
        v = self.get(section, key)
        if v is None or v == '':
            raise ConfigError('[{}] {} is required'.format(section, key))
        return v

    def flag(self, section, key, default):
        v = self.get(section, key)
        return default if v in (None, '') else yes(v, '[{}] {}'.format(section, key))

    def freq(self, section, key, default):
        v = self.get(section, key, default)
        f = si(v)
        if f is None or f <= 0:
            raise ConfigError('[{}] {}: {!r} is not a positive number'.format(section, key, v))
        return f

    def freqs(self, section, key, default):
        out = []
        for v in self.get(section, key, default).split():
            f = si(v)
            if f is None or f <= 0:
                raise ConfigError('[{}] {}: {!r} is not a positive number'.format(section, key, v))
            out.append(f)
        return out

    def prefixed(self, prefix):
        """[prefix:NAME] sections -> [(NAME, items)] in file order."""
        out = []
        for s in self.cp.sections():
            if s.lower().startswith(prefix.lower() + ':'):
                out.append((s.split(':', 1)[1].strip(), self.items(s)))
        return out


# ---------------------------------------------------------------------------
# SKILL: inspection pass (read only)
# ---------------------------------------------------------------------------
SKILL_COMMON = r'''
procedure(tbgOut(key @rest fields)
  printf("TBI|%s" key)
  foreach(f fields printf("|%s" if(stringp(f) f sprintf(nil "%L" f))))
  printf("\n"))
'''

SKILL_INSPECT = r'''
; tia_tb_gen.py inspection pass - reads the TIA, changes nothing.
tbgSeen = makeTable("tbgSeen" nil)
tbgMaxDepth = __DEPTH__
tbgCellRe = __CELLRE__
tbgExclRe = __EXCLRE__

; a transistor is a leaf whose terminals are exactly {D G S} or {D G S B}
; (any case), unless the user gave an explicit cell-name regex
procedure(tbgIsMos(master cellName)
  let((names)
    cond(
      (and(tbgExclRe pcreMatchp(tbgExclRe cellName)) nil)
      (tbgCellRe pcreMatchp(tbgCellRe cellName))
      (t
        names = sort(mapcar(lambda((n) lowerCase(n)) master~>terminals~>name) 'alphalessp)
        or(equal(names list("d" "g" "s")) equal(names list("b" "d" "g" "s")))))))

procedure(tbgGateNet(inst)
  let((it)
    it = car(setof(x inst~>instTerms equal(lowerCase(x~>name) "g")))
    if(and(it it~>net) it~>net~>name "")))

procedure(tbgYes(v) or(eq(v t) equal(v "yes")))

; report numeric, expression-valued CDF parameters (to find design variables)
procedure(tbgCel(inst)
  let((cdf)
    cdf = car(errset(cdfGetInstCDF(inst)))
    when(cdf
      foreach(p cdf~>parameters
        when(and(stringp(p~>value) nequal(p~>value "")
                 tbgYes(p~>parseAsCEL) tbgYes(p~>parseAsNumber)
                 member(p~>paramType list("string" "float" "int"))
                 !arrayref(tbgSeen p~>value))
          setarray(tbgSeen p~>value t)
          tbgOut("EXPR" p~>name p~>value))))))

procedure(tbgWalk(lib cell view prefix depth ancestors)
  let((cv key found master path sub)
    found = nil
    key = strcat(lib "/" cell)
    cond(
      (member(key ancestors) nil)
      (greaterp(depth tbgMaxDepth)
        tbgOut("WARN" sprintf(nil "hierarchy below %s is deeper than max_depth=%d and was not searched" prefix tbgMaxDepth)))
      ((cv = dbOpenCellViewByType(lib cell view nil "r"))
        foreach(inst cv~>instances
          master = inst~>master
          when(master
            path = strcat(prefix "/" inst~>name)
            tbgCel(inst)
            when(zerop(depth) tbgOut("INST" inst~>name inst~>libName inst~>cellName))
            sub = nil
            when(ddGetObj(inst~>libName inst~>cellName view)
              sub = tbgWalk(inst~>libName inst~>cellName view path add1(depth) cons(key ancestors)))
            cond(
              (sub found = t)
              (tbgIsMos(master inst~>cellName)
                found = t
                tbgOut("MOS" path inst~>libName inst~>cellName)
                when(zerop(depth) tbgOut("TOPMOS" inst~>name tbgGateNet(inst)))))))
        dbClose(cv)))
    found))

procedure(tbgLocked(lib cell view file)
  let((obj)
    obj = ddGetObj(lib cell view)
    and(obj isFile(strcat(obj~>readPath "/" file ".cdslck")))))

procedure(tbgInspect(tiaLib tiaCell symView schView tbLib tbCell tbViews)
  let((sym libObj)
    tbgOut("TIALIB" if(ddGetObj(tiaLib) "yes" "no"))
    libObj = ddGetObj(tbLib)
    tbgOut("TBLIB" if(libObj "yes" "no"))
    when(libObj
      tbgOut("TBWRITE" if(isWritable(libObj~>readPath) "yes" "no"))
      foreach(v tbViews
        when(ddGetObj(tbLib tbCell car(v))
          tbgOut("TBVIEW" car(v) if(tbgLocked(tbLib tbCell car(v) cadr(v)) "locked" "free")))))
    sym = and(ddGetObj(tiaLib) dbOpenCellViewByType(tiaLib tiaCell symView nil "r"))
    if(sym then
      foreach(term sym~>terminals tbgOut("TERM" term~>name term~>direction))
    else
      tbgOut("NOSYM" ""))
    if(and(ddGetObj(tiaLib) ddGetObj(tiaLib tiaCell schView)) then
      tbgWalk(tiaLib tiaCell schView "" 0 nil)
    else
      tbgOut("NOSCH" ""))
    tbgOut("DONE" "")))

unless(errset(tbgInspect(__ARGS__) t)
  tbgOut("ERR" "SKILL error during inspection (see the *Error* line above)"))
'''

# ---------------------------------------------------------------------------
# SKILL: build pass (schematics + maestro)
# ---------------------------------------------------------------------------
SKILL_BUILD = r'''
; tia_tb_gen.py build pass
tbgGrid = 0.0625
tbgStub = 0.125
tbgGapX = 1.0
tbgGapY = 0.75

procedure(tbgSnap(v) tbgGrid * round(v / tbgGrid))

procedure(tbgCenter(box)
  list(quotient(plus(xCoord(car(box)) xCoord(cadr(box))) 2.0)
       quotient(plus(yCoord(car(box)) yCoord(cadr(box))) 2.0)))

procedure(tbgPinPoints(master)
  let((pts)
    foreach(term master~>terminals
      foreach(pin term~>pins
        when(pin~>fig pts = cons(list(term~>name tbgCenter(pin~>fig~>bBox)) pts))))
    pts))

; direction (dx dy) in which a wire stub leaves a pin, in symbol coordinates:
; pins on the left/right/top/bottom extreme of the pin cloud point outwards,
; anything else points to the nearest edge of the symbol bounding box
procedure(tbgStubDir(pt pts box)
  let((x y xs ys xmin xmax ymin ymax eps dl dr dt db m)
    eps = 0.0001
    x = xCoord(pt)
    y = yCoord(pt)
    xs = mapcar(lambda((p) xCoord(cadr(p))) pts)
    ys = mapcar(lambda((p) yCoord(cadr(p))) pts)
    xmin = apply('min xs)
    xmax = apply('max xs)
    ymin = apply('min ys)
    ymax = apply('max ys)
    cond(
      (and(greaterp(difference(xmax xmin) eps) lessp(abs(difference(x xmin)) eps)) list(minus(1) 0))
      (and(greaterp(difference(xmax xmin) eps) lessp(abs(difference(x xmax)) eps)) list(1 0))
      (and(greaterp(difference(ymax ymin) eps) lessp(abs(difference(y ymax)) eps)) list(0 1))
      (and(greaterp(difference(ymax ymin) eps) lessp(abs(difference(y ymin)) eps)) list(0 minus(1)))
      (t
        dl = difference(x xCoord(car(box)))
        dr = difference(xCoord(cadr(box)) x)
        db = difference(y yCoord(car(box)))
        dt = difference(yCoord(cadr(box)) y)
        m = min(dl dr db dt)
        cond((equal(m dt) list(0 1))
             (equal(m db) list(0 minus(1)))
             (equal(m dl) list(minus(1) 0))
             (t list(1 0)))))))

; short wire stub + net label on every pin listed in pinNets ((term net) ...)
procedure(tbgConnect(cv inst pinNets)
  let((pts box c d x1 y1 p0 p1 wires just nerr)
    nerr = 0
    pts = tbgPinPoints(inst~>master)
    box = inst~>master~>bBox
    foreach(pn pinNets
      c = cadr(assoc(car(pn) pts))
      if(c then
        d = tbgStubDir(c pts box)
        x1 = plus(xCoord(c) times(tbgStub car(d)))
        y1 = plus(yCoord(c) times(tbgStub cadr(d)))
        p0 = dbTransformPoint(c inst~>transform)
        p1 = dbTransformPoint(list(x1 y1) inst~>transform)
        wires = schCreateWire(cv "draw" "full" list(p0 p1) tbgGrid tbgGrid 0.0)
        just = cond(
          (lessp(xCoord(p1) difference(xCoord(p0) 0.0001)) "lowerRight")
          (greaterp(xCoord(p1) plus(xCoord(p0) 0.0001)) "lowerLeft")
          (lessp(yCoord(p1) yCoord(p0)) "upperCenter")
          (t "lowerCenter"))
        if(wires then
          schCreateWireLabel(cv car(wires) p1 cadr(pn) just "R0" "stick" 0.0625 nil)
        else
          nerr = add1(nerr)
          tbgOut("ERR" sprintf(nil "could not draw a wire on %s/%s" inst~>name car(pn))))
      else
        nerr = add1(nerr)
        tbgOut("ERR" sprintf(nil "instance %s has no pin %s" inst~>name car(pn)))))
    nerr))

procedure(tbgSetParams(inst params)
  let((cdf p)
    cdf = cdfGetInstCDF(inst)
    foreach(pv params
      p = and(cdf cdfFindParamByName(cdf car(pv)))
      if(p then
        p~>value = cadr(pv)
      else
        dbReplaceProp(inst car(pv) "string" cadr(pv))))))

; rows: list of rows; row: list of (name lib cell params pinNets)
procedure(tbgMakeSchematic(lib cell view rows)
  let((cv master inst x yTop rowBottom mb nerr chk)
    nerr = 0
    cv = dbOpenCellViewByType(lib cell view "schematic" "w")
    unless(cv
      error("cannot open %s/%s/%s for writing (open in another session or no write permission)" lib cell view))
    yTop = 0.0
    foreach(row rows
      x = 0.0
      rowBottom = yTop
      foreach(spec row
        master = dbOpenCellViewByType(nth(1 spec) nth(2 spec) "symbol" nil "r")
        unless(master error("symbol view of %s/%s not found" nth(1 spec) nth(2 spec)))
        mb = master~>bBox
        inst = schCreateInst(cv master car(spec)
                 list(tbgSnap(difference(x xCoord(car(mb)))) tbgSnap(difference(yTop yCoord(cadr(mb)))))
                 "R0")
        unless(inst error("could not place instance %s" car(spec)))
        tbgSetParams(inst nth(3 spec))
        nerr = plus(nerr tbgConnect(cv inst nth(4 spec)))
        x = plus(xCoord(cadr(inst~>bBox)) tbgGapX)
        rowBottom = min(rowBottom yCoord(car(inst~>bBox))))
      yTop = difference(rowBottom tbgGapY))
    chk = schCheck(cv)
    tbgOut("SCH" view sprintf(nil "%L" chk))
    unless(dbSave(cv) nerr = add1(nerr) tbgOut("ERR" sprintf(nil "could not save %s" view)))
    dbClose(cv)
    nerr))

procedure(tbgSpec(sdb test out spec)
  let((kind)
    kind = car(spec)
    cond(
      (equal(kind "gt") axlAddSpecToOutput(sdb test out ?gt cadr(spec)))
      (equal(kind "lt") axlAddSpecToOutput(sdb test out ?lt cadr(spec)))
      (equal(kind "range") axlAddSpecToOutput(sdb test out ?range list(cadr(spec) caddr(spec))))
      (equal(kind "tol") axlAddSpecToOutput(sdb test out ?tol list(cadr(spec) caddr(spec))))
      (t sprintf(nil "unknown spec type %s" kind)))))

; tests: list of (name view enabled analyses outputs)
;   analyses: list of (analysisName ((option value) ...))
;   outputs:  list of (name expression plot spec)
procedure(tbgBuildMaestro(lib cell view sim tests vars corners models)
  let((sess sdb tname nerr res name)
    nerr = 0
    sess = maeOpenSetup(lib cell view ?mode "a")
    unless(sess error("maeOpenSetup failed for %s/%s/%s" lib cell view))
    sdb = axlGetMainSetupDB(sess)
    foreach(v vars
      unless(maeSetVar(car(v) cadr(v) ?session sess)
        nerr = add1(nerr)
        tbgOut("ERR" sprintf(nil "could not set global variable %s" car(v)))))
    foreach(tst tests
      tname = nth(0 tst)
      unless(maeCreateTest(tname ?lib lib ?cell cell ?view nth(1 tst) ?simulator sim ?session sess)
        error("could not create test %s" tname))
      when(models
        unless(maeSetEnvOption(tname ?options list(list("modelFiles" models)) ?session sess)
          nerr = add1(nerr)
          tbgOut("ERR" sprintf(nil "%s: could not set the model files" tname))))
      foreach(ana maeGetEnabledAnalysis(tname ?session sess)
        name = if(symbolp(ana) get_pname(ana) ana)
        unless(assoc(name nth(3 tst)) maeSetAnalysis(tname name ?enable nil ?session sess)))
      foreach(a nth(3 tst)
        unless(maeSetAnalysis(tname car(a) ?enable t ?options cadr(a) ?session sess)
          nerr = add1(nerr)
          tbgOut("ERR" sprintf(nil "%s: could not set up analysis %s" tname car(a)))))
      foreach(o nth(4 tst)
        if(maeAddOutput(car(o) tname ?outputType "point" ?expr cadr(o) ?plot caddr(o) ?save nil ?session sess) then
          when(cadddr(o)
            res = tbgSpec(sdb tname car(o) cadddr(o))
            unless(eq(res t)
              nerr = add1(nerr)
              tbgOut("ERR" sprintf(nil "%s: could not set the spec of %s: %L" tname car(o) res))))
        else
          nerr = add1(nerr)
          tbgOut("ERR" sprintf(nil "%s: could not add output %s" tname car(o)))))
      tbgOut("TEST" tname sprintf(nil "%d" length(nth(4 tst)))))
    foreach(c corners
      if(maeSetCorner(car(c) ?session sess) then
        foreach(v cadr(c)
          unless(maeSetVar(car(v) cadr(v) ?typeName "corner" ?typeValue list(car(c)) ?session sess)
            nerr = add1(nerr)
            tbgOut("ERR" sprintf(nil "corner %s: could not set %s" car(c) car(v)))))
      else
        nerr = add1(nerr)
        tbgOut("ERR" sprintf(nil "could not create corner %s" car(c)))))
    foreach(tst tests
      unless(nth(2 tst) maeEnableTests(?testNames list(nth(0 tst)) ?enable nil ?session sess)))
    unless(maeSaveSetup(?session sess)
      nerr = add1(nerr)
      tbgOut("ERR" "maeSaveSetup failed"))
    maeCloseSession(?session sess ?forceClose t)
    tbgOut("MAESTRO" view sprintf(nil "%d" length(corners)))
    nerr))

procedure(tbgBuild()
  let((nerr obj)
    nerr = 0
    obj = ddGetObj(tbgLib tbgCell tbgMaestroView)
    when(obj
      if(tbgOverwrite then
        unless(ddDeleteObj(obj) error("could not delete the existing %s view" tbgMaestroView))
        tbgOut("INFO" sprintf(nil "deleted existing %s/%s/%s" tbgLib tbgCell tbgMaestroView))
      else
        error("%s/%s/%s already exists (set overwrite = yes)" tbgLib tbgCell tbgMaestroView)))
    foreach(s tbgSchematics
      nerr = plus(nerr tbgMakeSchematic(tbgLib tbgCell car(s) cadr(s))))
    nerr = plus(nerr tbgBuildMaestro(tbgLib tbgCell tbgMaestroView tbgSimulator tbgTests tbgVars tbgCorners tbgModels))
    tbgOut("RESULT" if(zerop(nerr) "ok" sprintf(nil "%d problem(s)" nerr)))))

unless(errset(tbgBuild() t)
  tbgOut("ERR" "SKILL error during the build (see the *Error* line above)"))
'''


# ---------------------------------------------------------------------------
# running Virtuoso
# ---------------------------------------------------------------------------
def run_virtuoso(body, args, tag):
    """Run SKILL in a batch Virtuoso; return the parsed TBI records and raw output."""
    tmp = tempfile.mkdtemp(prefix='tia_tb_gen_')
    body_il = os.path.join(tmp, tag + '.il')
    main_il = os.path.join(tmp, tag + '_main.il')
    log = os.path.join(tmp, 'CDS.log')
    with open(body_il, 'w') as f:
        f.write(SKILL_COMMON + body)
    # the wrapper always reaches exit(): a SKILL error must never leave a
    # batch Virtuoso waiting at its prompt
    with open(main_il, 'w') as f:
        f.write('unless(errset(load("{0}") t) printf("TBI|ERR|could not load {0}\\n"))\n'
                'exit(0)\n'.format(q(body_il)))
    cmd = [args.virtuoso, '-nograph', '-log', log, '-restore', main_il]
    try:
        p = subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=args.timeout)
        out, rc = p.stdout, p.returncode
    except subprocess.TimeoutExpired as e:
        out, rc = (e.output or b''), 'timeout'
    except OSError as e:
        shutil.rmtree(tmp, ignore_errors=True)
        raise ConfigError('cannot start {!r}: {}'.format(args.virtuoso, e))
    text = out.decode('utf-8', 'replace')
    if args.keep:
        print('  kept SKILL/log in', tmp)
    else:
        shutil.rmtree(tmp, ignore_errors=True)
    if args.verbose:
        print(text)
    recs = []
    for line in text.splitlines():
        if line.startswith('TBI|'):
            recs.append(line.split('|', 3)[1:] if line.startswith('TBI|EXPR|')
                        else line.split('|')[1:])
    errors = [r[1] if len(r) > 1 else '' for r in recs if r[0] == 'ERR']
    skill_errs = [l.strip() for l in text.splitlines() if l.lstrip().startswith('*Error*')]
    if rc == 'timeout':
        errors.append('Virtuoso did not finish within {} s (use --timeout)'.format(args.timeout))
    elif not recs:
        errors.append('no answer from Virtuoso (exit code {}); rerun with --verbose'.format(rc))
    return recs, errors, skill_errs


# ---------------------------------------------------------------------------
# phase 1: inspect the TIA
# ---------------------------------------------------------------------------
def inspect(cfg, args, tb):
    def cre(key):
        v = cfg.get('mos', key, '')
        return '"(?i)' + q(v) + '"' if v else 'nil'

    views = [[tb['ol_view'], 'sch.oa'], [tb['fb_view'], 'sch.oa'],
             [tb['maestro_view'], 'maestro.sdb']]
    call = ' '.join(sk(x) for x in (tb['tia_lib'], tb['tia_cell'], tb['tia_symbol'],
                                    tb['tia_schematic'], tb['tb_lib'], tb['tb_cell'], views))
    depth = cfg.get('mos', 'max_depth', '12')
    if not depth.isdigit():
        raise ConfigError('[mos] max_depth must be a whole number')
    body = (SKILL_INSPECT.replace('__DEPTH__', depth).replace('__CELLRE__', cre('cell_regex'))
            .replace('__EXCLRE__', cre('exclude_regex')).replace('__ARGS__', call))
    recs, errors, skill_errs = run_virtuoso(body, args, 'inspect')
    info = {'terms': [], 'tb_views': {}, 'mos': [], 'topmos': [], 'insts': [], 'exprs': [],
            'warn': [], 'tia_lib': False, 'tb_lib': False, 'tb_write': False,
            'sym': True, 'sch': True, 'done': False}
    for r in recs:
        k = r[0]
        if k == 'TERM':
            info['terms'].append(r[1])
        elif k == 'TBVIEW':
            info['tb_views'][r[1]] = r[2]
        elif k == 'MOS':
            info['mos'].extend((p, r[2], r[3]) for p in expand_iterated(r[1]))
        elif k == 'TOPMOS':
            info['topmos'].append((r[1], r[2]))
        elif k == 'INST':
            info['insts'].append((r[1], r[2], r[3]))
        elif k == 'EXPR':
            info['exprs'].append((r[1], r[2] if len(r) > 2 else ''))
        elif k == 'WARN':
            info['warn'].append(r[1])
        elif k == 'TIALIB':
            info['tia_lib'] = r[1] == 'yes'
        elif k == 'TBLIB':
            info['tb_lib'] = r[1] == 'yes'
        elif k == 'TBWRITE':
            info['tb_write'] = r[1] == 'yes'
        elif k == 'NOSYM':
            info['sym'] = False
        elif k == 'NOSCH':
            info['sch'] = False
        elif k == 'DONE':
            info['done'] = True
    if errors or not info['done']:
        msg = '\n  '.join(errors + skill_errs) or 'inspection did not complete'
        raise ConfigError('Virtuoso inspection failed:\n  ' + msg)
    return info


# ---------------------------------------------------------------------------
# configuration -> testbench plan
# ---------------------------------------------------------------------------
PIN_KEYS = ('VDD', 'VSS', 'pos_in', 'neg_in', 'pos_out', 'neg_out')
DIFF_TESTS = ['OL_DC_AC', 'FB_AC', 'FB_NOISE', 'FB_STB_DM', 'FB_STB_CM', 'FB_STB_CMFB', 'FB_TRAN']
SE_TESTS = ['OL_DC_AC', 'FB_AC', 'FB_NOISE', 'FB_STB', 'FB_TRAN']
TB_VARS = ['avdd', 'CL', 'RFR', 'CFR', 'Rs', 'Cs', 'iamp', 'fin']


def read_testbench(cfg, args):
    s = 'testbench'
    tb = {
        'tb_lib': cfg.need(s, 'tb_library'),
        'tb_cell': cfg.need(s, 'tb_cell'),
        'tia_cell': cfg.need(s, 'tia_cell'),
        'tia_symbol': cfg.get(s, 'tia_symbol_view', 'symbol'),
        'tia_schematic': cfg.get(s, 'tia_schematic_view', 'schematic'),
        'diff': cfg.flag(s, 'differential', True),
        'overwrite': args.overwrite or cfg.flag(s, 'overwrite', False),
        'src_lib': cfg.get(s, 'source_library', 'analogLib'),
        'simulator': cfg.get(s, 'simulator', 'spectre'),
        'ol_view': cfg.get(s, 'ol_view', 'schematic'),
        'fb_view': cfg.get(s, 'fb_view', 'schematic_w_fb'),
        'maestro_view': cfg.get(s, 'maestro_view', 'maestro'),
        'cmfb_probe': cfg.get(s, 'cmfb_probe', 'IPRB_CMFB'),
        'l_dc': cfg.get(s, 'ol_dc_inductor', '1M'),
        'c_ac': cfg.get(s, 'ol_ac_capacitor', '1'),
        'ignore_vars': set(cfg.get(s, 'ignore_vars', '').replace(',', ' ').split()),
    }
    tb['tia_lib'] = cfg.get(s, 'tia_library', '') or tb['tb_lib']
    models = []
    for chunk in cfg.get(s, 'model_files', '').split(';'):
        parts = chunk.split()
        if len(parts) > 2:
            raise ConfigError('[testbench] model_files: use "path [section]; path [section]"')
        if parts:
            models.append(parts)
    tb['models'] = models
    for key in ('tb_lib', 'tb_cell', 'tia_lib', 'tia_cell'):
        if not re.match(r'^[A-Za-z0-9_.+-]+$', tb[key]):
            raise ConfigError('[testbench] invalid name {!r}'.format(tb[key]))
    return tb


def read_pins(cfg, tb):
    pins = {}
    for key in PIN_KEYS:
        v = cfg.get('pins', key, '')
        pins[key] = None if v.lower() in ('', 'none', '-') else v
    for k, _ in cfg.items('pins'):
        if k.lower() not in [p.lower() for p in PIN_KEYS]:
            raise ConfigError('[pins] unknown key {!r}; allowed: {}'.format(k, ', '.join(PIN_KEYS)))
    required = PIN_KEYS if tb['diff'] else ('VDD', 'VSS', 'neg_in', 'pos_out')
    missing = [k for k in required if not pins[k]]
    if missing:
        raise ConfigError('[pins] missing for a {} TIA: {}'.format(
            'differential' if tb['diff'] else 'single-ended', ', '.join(missing)))
    if not tb['diff'] and pins['neg_out']:
        raise ConfigError('[pins] neg_out must be "none" for a single-ended TIA')
    used = [v for v in pins.values() if v]
    dup = sorted({v for v in used if used.count(v) > 1})
    if dup:
        raise ConfigError('[pins] TIA pin(s) mapped twice: ' + ', '.join(dup))
    return pins


def check_pins(cfg, tb, pins, info):
    """Map every TIA terminal to a testbench net; returns (dut_pins, extra_insts, extra_vars)."""
    terms = info['terms']
    net_of = {'VDD': 'VDD', 'VSS': 'VSS'}
    if tb['diff']:
        net_of.update(pos_in='INP', neg_in='INN', pos_out='OP', neg_out='ON')
    else:
        net_of.update(pos_in='REF', neg_in='IN', pos_out='OUT')
    dut, unknown = [], []
    for key in PIN_KEYS:
        if pins[key]:
            if pins[key] not in terms:
                unknown.append('{} = {}'.format(key, pins[key]))
            elif bus_width(pins[key]) != 1:
                raise ConfigError('[pins] {} = {} is a bus; use a scalar pin'.format(key, pins[key]))
            else:
                dut.append((pins[key], net_of[key]))
    if unknown:
        raise ConfigError('[pins] not pins of {}/{}: {}\n  TIA pins are: {}'.format(
            tb['tia_lib'], tb['tia_cell'], '; '.join(unknown), ' '.join(terms)))
    extra_insts, extra_vars = [], set()
    mapped = {p for p, _ in dut}
    for term, how in cfg.items('extra_pins'):
        if term not in terms:
            raise ConfigError('[extra_pins] {} is not a pin of the TIA (pins: {})'.format(term, ' '.join(terms)))
        if term in mapped:
            raise ConfigError('[extra_pins] {} is already connected in [pins]'.format(term))
        mapped.add(term)
        w = bus_width(term)
        words = how.split(None, 1)
        kind = words[0].lower() if words else ''
        arg = words[1].strip() if len(words) > 1 else ''
        safe = re.sub(r'\W', '_', term).strip('_')
        if kind in ('vdd', 'vss', 'gnd') and not arg:
            net = {'vdd': 'VDD', 'vss': 'VSS', 'gnd': 'gnd!'}[kind]
        elif kind == 'net' and re.match(r'^[A-Za-z_][\w!]*$', arg):
            net = arg
        elif kind in ('noconn', 'open') and not arg:
            net = 'NC_' + safe
        elif kind in ('vdc', 'idc_in', 'idc_out') and arg:
            if w != 1:
                raise ConfigError('[extra_pins] {}: sources are only supported on scalar pins'.format(term))
            net = 'X_' + safe
            extra_vars |= identifiers(arg)
            if kind == 'vdc':
                extra_insts.append(('V_' + safe, 'vdc', [('vdc', arg)], [('PLUS', net), ('MINUS', 'VSS')]))
            elif kind == 'idc_in':      # current flows into the TIA pin
                extra_insts.append(('I_' + safe, 'idc', [('idc', arg)], [('PLUS', 'VSS'), ('MINUS', net)]))
            else:                       # current flows out of the TIA pin
                extra_insts.append(('I_' + safe, 'idc', [('idc', arg)], [('PLUS', net), ('MINUS', 'VSS')]))
        else:
            raise ConfigError('[extra_pins] {} = {!r}: use VDD | VSS | gnd | net NAME | vdc VALUE | '
                              'idc_in VALUE | idc_out VALUE | noconn'.format(term, how))
        dut.append((term, '<*{}>{}'.format(w, net) if w > 1 else net))
    left = [t for t in terms if t not in mapped]
    if left:
        raise ConfigError('TIA pin(s) not connected: {}\n  map them in [pins] or [extra_pins] '
                          '(e.g. "{} = vdc 0.5" or "{} = VDD")'.format(' '.join(left), left[0], left[0]))
    return dut, extra_insts, extra_vars


def read_variables(cfg):
    out = []
    for k, v in cfg.items('variables'):
        if not re.match(r'^[A-Za-z_]\w*$', k):
            raise ConfigError('[variables] invalid variable name {!r}'.format(k))
        if v == '':
            raise ConfigError('[variables] {} has no value'.format(k))
        out.append((k, v))
    return out


def tia_variables(info, tb):
    """Design-variable names used in the TIA hierarchy -> {name: first parameter that uses it}."""
    found = {}
    for param, value in info['exprs']:
        if '=' in value:           # display-only strings such as "m/nf=..."
            continue
        for name in identifiers(value):
            found.setdefault(name, param)
    for name in tb['ignore_vars']:
        found.pop(name, None)
    return found


def read_mos_metrics(cfg):
    metrics = []
    for name, items in cfg.prefixed('mos_metric'):
        if not re.match(r'^[A-Za-z]\w*$', name):
            raise ConfigError('[mos_metric:{}] invalid metric name'.format(name))
        d = {'name': name, 'enabled': True, 'plot': True, 'expr': '', 'spec': None, 'override': []}
        where = '[mos_metric:{}]'.format(name)
        for k, v in items:
            kl = k.lower()
            if kl == 'enabled':
                d['enabled'] = yes(v, where + ' enabled')
            elif kl == 'plot':
                d['plot'] = yes(v, where + ' plot')
            elif kl == 'expression':
                d['expr'] = v
            elif kl == 'spec':
                d['spec'] = parse_spec(v, where + ' spec')
            elif kl.startswith('spec.'):
                pat = k[5:].strip().lstrip('/')
                d['override'].append((pat, 'skip' if v.lower() == 'skip'
                                      else parse_spec(v, '{} {}'.format(where, k))))
            else:
                raise ConfigError('{} unknown key {!r}'.format(where, k))
        if d['enabled']:
            if '{device}' not in d['expr']:
                raise ConfigError(where + ' expression must contain {device}')
            rest = d['expr'].replace('{device}', '').replace('{op}', '')
            if '{' in rest or '}' in rest:
                raise ConfigError(where + ' only {device} and {op} are allowed as placeholders')
        metrics.append(d)
    return metrics


def freq_sweep(a, b, ppd):
    return [('sweep', 'Frequency'), ('rangeType', 'Start-Stop'), ('start', num(a)),
            ('stop', num(b)), ('incrType', 'Logarithmic'),
            ('stepTypeLog', 'Points Per Decade'), ('dec', str(ppd))]


def build_plan(cfg, tb, pins, info):
    notes = []
    diff = tb['diff']
    S = tb['src_lib']
    dut_pins, extra_insts, extra_vars = check_pins(cfg, tb, pins, info)
    variables = read_variables(cfg)
    defined = {k for k, _ in variables}

    # ---------- design variables -------------------------------------------
    need = set(TB_VARS) | extra_vars
    if not diff and pins['pos_in']:
        need.add('vcmin')
    tia_vars = tia_variables(info, tb)
    missing_tb = sorted(need - defined)
    missing_tia = sorted(set(tia_vars) - defined)
    if missing_tb or missing_tia:
        msg = []
        if missing_tb:
            msg.append('testbench variables without a value: ' + ', '.join(missing_tb))
        if missing_tia:
            msg.append('variables used inside the TIA without a value: ' + ', '.join(
                '{} (parameter {})'.format(v, tia_vars[v]) for v in missing_tia))
            msg.append('if one of these is not a design variable, add it to '
                       '[testbench] ignore_vars')
        raise ConfigError('add these to [variables]:\n  ' + '\n  '.join(msg))

    # ---------- analyses settings ------------------------------------------
    A = 'analyses'
    f_dc = cfg.freq(A, 'dc_freq', '1k')
    ac = (cfg.freq(A, 'ac_start', '1k'), cfg.freq(A, 'ac_stop', '10G'), cfg.get(A, 'ac_ppd', '20'))
    nz = (cfg.freq(A, 'noise_start', '1k'), cfg.freq(A, 'noise_stop', '1G'), cfg.get(A, 'noise_ppd', '20'))
    st = (cfg.freq(A, 'stb_start', '1k'), cfg.freq(A, 'stb_stop', '10G'), cfg.get(A, 'stb_ppd', '20'))
    zin_f = cfg.freqs(A, 'zin_freqs', '100k 1M 50M')
    nz_f = cfg.freqs(A, 'noise_freqs', '100k 1M 10M')
    vn_f = cfg.freqs(A, 'vout_noise_freqs', '1M')
    band = cfg.freqs(A, 'noise_rms_band', '10k 50M')
    t_stop = cfg.get(A, 'tran_stop', '2u')
    t_meas = cfg.get(A, 'tran_meas_start', '1u')
    t_max = cfg.get(A, 'tran_maxstep', '1n')
    t_err = cfg.get(A, 'tran_errpreset', 'conservative')
    nfft = cfg.get(A, 'tran_fft_points', '1024')
    for v in (ac[2], nz[2], st[2], nfft):
        if not v.isdigit():
            raise ConfigError('[analyses] points per decade / fft points must be whole numbers')
    if len(band) != 2 or band[0] >= band[1]:
        raise ConfigError('[analyses] noise_rms_band needs two frequencies: LOW HIGH')
    if si(t_stop) is None or si(t_meas) is None or si(t_meas) >= si(t_stop):
        raise ConfigError('[analyses] need tran_meas_start < tran_stop (both numbers)')
    if not ac[0] <= f_dc <= ac[1]:
        raise ConfigError('[analyses] dc_freq must lie inside the ac sweep')
    t1, t2 = num(si(t_meas)), num(si(t_stop))

    # ---------- schematics --------------------------------------------------
    def I(name, cell, params, pinnets, lib=None):
        return [name, lib or S, cell, [list(p) for p in params], [list(p) for p in pinnets]]

    dut = I(DUT, tb['tia_cell'], [], dut_pins, lib=tb['tia_lib'])
    supplies = [I('VDD0', 'vdc', [('vdc', 'avdd')], [('PLUS', 'VDD'), ('MINUS', 'VSS')]),
                I('V0', 'vdc', [('vdc', '0')], [('PLUS', 'VSS'), ('MINUS', 'gnd!')]),
                I('GND0', 'gnd', [], [('gnd!', 'gnd!')])]
    supplies += [I(n, c, p, pn) for n, c, p, pn in extra_insts]
    if not diff and pins['pos_in']:
        supplies.append(I('VREF', 'vdc', [('vdc', 'vcmin')], [('PLUS', 'REF'), ('MINUS', 'VSS')]))
    L, C = tb['l_dc'], tb['c_ac']
    if diff:
        ol_rows = [[dut], supplies,
                   [I('VINP', 'vdc', [('vdc', '0'), ('acm', '0.5'), ('acp', '0')], [('PLUS', 'INP'), ('MINUS', 'BP')]),
                    I('VINN', 'vdc', [('vdc', '0'), ('acm', '0.5'), ('acp', '180')], [('PLUS', 'INN'), ('MINUS', 'BN')]),
                    I('LDCP', 'ind', [('l', L)], [('PLUS', 'ON'), ('MINUS', 'BP')]),
                    I('LDCN', 'ind', [('l', L)], [('PLUS', 'OP'), ('MINUS', 'BN')]),
                    I('CDCP', 'cap', [('c', C)], [('PLUS', 'BP'), ('MINUS', 'VSS')]),
                    I('CDCN', 'cap', [('c', C)], [('PLUS', 'BN'), ('MINUS', 'VSS')])],
                   [I('CLP', 'cap', [('c', 'CL')], [('PLUS', 'OP'), ('MINUS', 'VSS')]),
                    I('CLN', 'cap', [('c', 'CL')], [('PLUS', 'ON'), ('MINUS', 'VSS')])]]
        fb_rows = [[dut], supplies,
                   [I('IDIF', 'isin', [('io', '0'), ('acm', '1'), ('freq', 'fin'), ('ia', 'iamp')],
                      [('PLUS', 'INN'), ('MINUS', 'INP')]),
                    I('RSP', 'res', [('r', 'Rs')], [('PLUS', 'INP'), ('MINUS', 'VSS')]),
                    I('RSN', 'res', [('r', 'Rs')], [('PLUS', 'INN'), ('MINUS', 'VSS')]),
                    I('CSP', 'cap', [('c', 'Cs')], [('PLUS', 'INP'), ('MINUS', 'VSS')]),
                    I('CSN', 'cap', [('c', 'Cs')], [('PLUS', 'INN'), ('MINUS', 'VSS')])],
                   [I('RFP', 'res', [('r', 'RFR')], [('PLUS', 'ONY'), ('MINUS', 'INP')]),
                    I('CFP', 'cap', [('c', 'CFR')], [('PLUS', 'ONY'), ('MINUS', 'INP')]),
                    I('RFN', 'res', [('r', 'RFR')], [('PLUS', 'OPY'), ('MINUS', 'INN')]),
                    I('CFN', 'cap', [('c', 'CFR')], [('PLUS', 'OPY'), ('MINUS', 'INN')])],
                   [I('CLP', 'cap', [('c', 'CL')], [('PLUS', 'OP'), ('MINUS', 'VSS')]),
                    I('CLN', 'cap', [('c', 'CL')], [('PLUS', 'ON'), ('MINUS', 'VSS')]),
                    # one differential stb probe, used in differential mode by
                    # FB_STB_DM and in common mode by FB_STB_CM
                    I('PRB_DIFF', 'diffstbprobe', [],
                      [('IN1', 'ON'), ('IN2', 'OP'), ('OUT1', 'ONY'), ('OUT2', 'OPY')])]]
    else:
        ol_rows = [[dut], supplies,
                   [I('VIN', 'vdc', [('vdc', '0'), ('acm', '1')], [('PLUS', 'IN'), ('MINUS', 'B')]),
                    I('LDC', 'ind', [('l', L)], [('PLUS', 'OUT'), ('MINUS', 'B')]),
                    I('CDC', 'cap', [('c', C)], [('PLUS', 'B'), ('MINUS', 'VSS')])],
                   [I('CLO', 'cap', [('c', 'CL')], [('PLUS', 'OUT'), ('MINUS', 'VSS')])]]
        fb_rows = [[dut], supplies,
                   [I('IIN', 'isin', [('io', '0'), ('acm', '1'), ('freq', 'fin'), ('ia', 'iamp')],
                      [('PLUS', 'VSS'), ('MINUS', 'IN')]),
                    I('RS', 'res', [('r', 'Rs')], [('PLUS', 'IN'), ('MINUS', 'VSS')]),
                    I('CS', 'cap', [('c', 'Cs')], [('PLUS', 'IN'), ('MINUS', 'VSS')])],
                   [I('RF', 'res', [('r', 'RFR')], [('PLUS', 'OUTY'), ('MINUS', 'IN')]),
                    I('CF', 'cap', [('c', 'CFR')], [('PLUS', 'OUTY'), ('MINUS', 'IN')])],
                   [I('CLO', 'cap', [('c', 'CL')], [('PLUS', 'OUT'), ('MINUS', 'VSS')]),
                    I('PRB_LOOP', 'iprobe', [], [('PLUS', 'OUT'), ('MINUS', 'OUTY')])]]
    schematics = [[tb['ol_view'], ol_rows], [tb['fb_view'], fb_rows]]

    # ---------- input devices (gate on the signal input pin) ---------------
    in_pin = pins['pos_in'] if diff else pins['neg_in']
    in_devs = ['/{}/{}'.format(DUT, n) for n, g in info['topmos'] if g == in_pin]
    gm = '(' + ' + '.join('OS("{}" "gm")'.format(d) for d in in_devs) + ')' if in_devs else None
    if not in_devs:
        notes.append('no transistor gate is wired directly to TIA pin {} at the top level; the '
                     'gm/inv_Gm/Id_branch outputs were skipped (add them with [output:...] '
                     'sections if needed)'.format(in_pin))

    # ---------- tests and outputs -------------------------------------------
    sweep_ac = freq_sweep(*ac)
    dc = ('dc', [('saveOppoint', True)])
    tests = []

    def test(name, view, analyses):
        t = {'name': name, 'view': view, 'enabled': True, 'analyses': analyses, 'outputs': []}
        tests.append(t)
        return t

    def out(t, name, expr, plot=True):
        t['outputs'].append([name, expr, plot, None])

    if diff:
        g_ol = '(VF("/OP") - VF("/ON"))'
        zt, zin = '(VF("/OP") - VF("/ON"))', '(VF("/INP") - VF("/INN"))'
        vt = '(VT("/OP") - VT("/ON"))'
        zin_name, gm_name, igm_name, igm_k = 'Zin_diff', 'gm_OTA', 'inv_Gm_diff', '2'
    else:
        g_ol = '(-1 * VF("/OUT"))'       # inverting stage: flip sign -> 0 deg at DC
        zt, zin = 'VF("/OUT")', 'VF("/IN")'
        vt = 'VT("/OUT")'
        zin_name, gm_name, igm_name, igm_k = 'Zin', 'gm_in', 'inv_Gm', '1'
    fdc = num(f_dc)

    t = test('OL_DC_AC', tb['ol_view'], [dc, ('ac', sweep_ac)])
    out(t, 'Av0_dB', 'value(dB20({}) {})'.format(g_ol, fdc))
    out(t, 'UGF_OL', 'cross(dB20({}) 0 1 "falling")'.format(g_ol))
    out(t, 'PM_OL', '(180 + value(phaseDegUnwrapped({0}) cross(dB20({0}) 0 1 "falling")))'.format(g_ol))
    if gm:
        out(t, gm_name, gm)
        out(t, igm_name, '({} / {})'.format(igm_k, gm))
    if diff:
        out(t, 'VOUT_CM', '((VDC("/OP") + VDC("/ON")) / 2)')
    else:
        out(t, 'VOUT_DC', 'VDC("/OUT")')

    t = test('FB_AC', tb['fb_view'], [dc, ('ac', sweep_ac)])
    out(t, 'Zt_DC_ohm', 'value(mag({}) {})'.format(zt, fdc))
    out(t, 'Zt_DC_dBohm', 'value(dB20({}) {})'.format(zt, fdc))
    out(t, 'BW_3dB', 'bandwidth(mag({}) 3 "low")'.format(zt))
    out(t, 'Peaking_dB', '(ymax(dB20({0})) - value(dB20({0}) {1}))'.format(zt, fdc))
    for f in zin_f:
        out(t, '{}_{}'.format(zin_name, fname(f)), 'value(mag({}) {})'.format(zin, num(f)))
    if gm:
        out(t, igm_name, '({} / {})'.format(igm_k, gm))
        out(t, gm_name, gm)
        out(t, 'Id_branch', 'abs(OS("{}" "ids"))'.format(in_devs[0]))
    out(t, 'I_VDD', 'abs(OP("/VDD0" "i"))')
    out(t, 'Power', 'abs((OP("/VDD0" "i") * VAR("avdd")))')
    if diff:
        out(t, 'VOUT_CM', '((VDC("/OP") + VDC("/ON")) / 2)')
        out(t, 'VIN_CM', '((VDC("/INP") + VDC("/INN")) / 2)')
    else:
        out(t, 'VOUT_DC', 'VDC("/OUT")')
        out(t, 'VIN_DC', 'VDC("/IN")')
    out(t, 'Zt', 'mag({})'.format(zt))
    out(t, zin_name, 'mag({})'.format(zin))

    noise_opts = freq_sweep(*nz) + [('outType', 'voltage'),
                                    ('p', '/OP' if diff else '/OUT'), ('n', '/ON' if diff else ''),
                                    ('inType', 'port'), ('iprobe', '/IDIF' if diff else '/IIN')]
    t = test('FB_NOISE', tb['fb_view'], [('noise', noise_opts)])
    for f in nz_f:
        out(t, 'in_' + fname(f), 'value(getData("in" ?result "noise") {})'.format(num(f)))
    out(t, 'in_rms_{}_{}'.format(eng(band[0]), eng(band[1])).replace('.', 'p'),
        'sqrt(integ((getData("in" ?result "noise")**2) {} {}))'.format(num(band[0]), num(band[1])))
    for f in vn_f:
        out(t, 'vout_n_' + fname(f), 'value(getData("out" ?result "noise") {})'.format(num(f)))
    out(t, 'in_spectrum', 'getData("in" ?result "noise")')

    def stb(name, mode, probe, suffix):
        # mode = ADE stb "Mode Type": 'single-ended' with an iprobe, or
        # 'differential' / 'common' with a diffstbprobe (netlisted as
        # probe=<inst>.IPRB_DM / <inst>.IPRB_CM)
        opts = freq_sweep(*st) + [('stbProbeMode', mode), ('probeType', 'Probe Instance'),
                                  ('probe', probe)]
        t = test(name, tb['fb_view'], [('stb', opts)])
        sfx = '_' + suffix if suffix else ''
        out(t, 'LG0{}_dB'.format(sfx), 'value(dB20(getData("loopGain" ?result "stb")) {})'.format(fdc))
        out(t, 'PM' + sfx, 'getData("phaseMargin" ?result "stb_margin")')
        out(t, 'GM' + sfx, 'getData("gainMargin" ?result "stb_margin")')
        out(t, 'UGF' + sfx, 'getData("phaseMarginFreq" ?result "stb_margin")')
        return t

    cmfb_found = None
    if diff:
        stb('FB_STB_DM', 'differential', '/PRB_DIFF', 'DM')
        stb('FB_STB_CM', 'common', '/PRB_DIFF', 'CM')
        t_cmfb = stb('FB_STB_CMFB', 'single-ended', '/{}/{}'.format(DUT, tb['cmfb_probe']), 'CMFB')
        cmfb_found = [i for i in info['insts'] if i[0] == tb['cmfb_probe']]
        if not cmfb_found:
            t_cmfb['enabled'] = False
    else:
        stb('FB_STB', 'single-ended', '/PRB_LOOP', '')

    tran = [('stop', t_stop), ('errpreset', t_err), ('maxstep', t_max)]
    t = test('FB_TRAN', tb['fb_view'], [('tran', tran)])
    if diff:
        out(t, 'Vout_diff_pp', 'peakToPeak(clip({} {} {}))'.format(vt, t1, t2))
        out(t, 'VOUT_CM_avg', 'average(clip(((VT("/OP") + VT("/ON")) / 2) {} {}))'.format(t1, t2))
        out(t, 'Vout_diff', vt)
    else:
        out(t, 'Vout_pp', 'peakToPeak(clip({} {} {}))'.format(vt, t1, t2))
        out(t, 'VOUT_DC_avg', 'average(clip({} {} {}))'.format(vt, t1, t2))
        out(t, 'Vout', vt)
    out(t, 'THD_pct', 'thd({} {} {} {} VAR("fin"))'.format(vt, t1, t2, nfft))
    dft = 'dB20(dft({} {} {} {} "Rectangular"))'.format(vt, t1, t2, nfft)
    out(t, 'HD3_dBc', '(value({0} (3 * VAR("fin"))) - value({0} VAR("fin")))'.format(dft))

    by_name = {t['name']: t for t in tests}

    # ---------- per-transistor outputs ---------------------------------------
    op_fn = cfg.get('mos', 'op_function', 'OS')
    if op_fn not in ('OS', 'OP'):
        raise ConfigError('[mos] op_function must be OS or OP')
    mos_tests = cfg.get('mos', 'tests', 'OL_DC_AC').split()
    for name in mos_tests:
        if name not in ('OL_DC_AC', 'FB_AC'):
            raise ConfigError('[mos] tests: only OL_DC_AC and FB_AC have a DC operating point')
    metrics = read_mos_metrics(cfg)
    n_mos_out = 0
    for name in mos_tests:
        t = by_name[name]
        for path, _, _ in info['mos']:
            rel = path.lstrip('/')
            flat = re.sub(r'\W', '_', '{}/{}'.format(DUT, rel)).strip('_')
            for m in metrics:
                if not m['enabled']:
                    continue
                spec = m['spec']
                for pat, ov in m['override']:
                    if fnmatch.fnmatchcase(rel, pat):
                        spec = ov
                if spec == 'skip':
                    continue
                expr = m['expr'].replace('{op}', op_fn).replace('{device}', '/{}/{}'.format(DUT, rel))
                t['outputs'].append(['{}_{}'.format(m['name'], flat), expr, m['plot'], spec])
                n_mos_out += 1

    # ---------- [tests] enable / disable -------------------------------------
    valid = DIFF_TESTS if diff else SE_TESTS
    for k, v in cfg.items('tests'):
        if k in by_name:
            on = yes(v, '[tests] ' + k)
            if not on:
                by_name[k]['enabled'] = False
            elif k == 'FB_STB_CMFB' and not cmfb_found:
                pass                     # stays disabled until the probe exists
        elif k in DIFF_TESTS + SE_TESTS:
            pass                         # test of the other (SE/diff) bench type
        else:
            raise ConfigError('[tests] unknown test {!r}; tests are: {}'.format(k, ', '.join(valid)))

    # ---------- custom outputs ------------------------------------------------
    for oname, items in cfg.prefixed('output'):
        where = '[output:{}]'.format(oname)
        d = dict((k.lower(), v) for k, v in items)
        extra = set(d) - {'test', 'expression', 'spec', 'plot', 'enabled'}
        if extra:
            raise ConfigError('{} unknown key(s): {}'.format(where, ', '.join(sorted(extra))))
        names = d.get('test', '').split()
        if not names:
            raise ConfigError(where + ' test = TESTNAME is required')
        for tn in names:
            if tn not in by_name:
                raise ConfigError('{} unknown test {!r} (tests: {})'.format(where, tn, ', '.join(by_name)))
            t = by_name[tn]
            cur = [o for o in t['outputs'] if o[0] == oname]
            if not yes(d.get('enabled', 'yes'), where + ' enabled'):
                t['outputs'] = [o for o in t['outputs'] if o[0] != oname]
                continue
            expr = d.get('expression', '')
            if not expr and not cur:
                raise ConfigError(where + ' expression is required for a new output')
            row = cur[0] if cur else [oname, expr, True, None]
            if expr:
                row[1] = expr
            if 'plot' in d:
                row[2] = yes(d['plot'], where + ' plot')
            if 'spec' in d:
                row[3] = parse_spec(d['spec'], where + ' spec')
            if not cur:
                t['outputs'].append(row)

    # ---------- [specs] TEST.OUTPUT = spec -----------------------------------
    for k, v in cfg.items('specs'):
        if '.' not in k:
            raise ConfigError('[specs] {!r}: use TEST.OUTPUT = spec'.format(k))
        tn, on = k.split('.', 1)
        if tn not in by_name:
            if tn in DIFF_TESTS + SE_TESTS:
                continue                 # spec for the other (SE/diff) bench type
            raise ConfigError('[specs] unknown test in {!r}'.format(k))
        rows = [o for o in by_name[tn]['outputs'] if o[0] == on]
        if not rows:
            raise ConfigError('[specs] {}: test {} has no output {!r}\n  outputs: {}'.format(
                k, tn, on, ', '.join(o[0] for o in by_name[tn]['outputs'] if not o[0].startswith(
                    tuple(m['name'] + '_' for m in metrics)))))
        rows[0][3] = parse_spec(v, '[specs] ' + k)

    # ---------- corners -------------------------------------------------------
    corners = []
    CS = 'corners'
    if cfg.flag(CS, 'enabled', True):
        nominal = dict(variables)
        nominal['temperature'] = cfg.get(CS, 'nominal_temperature', '27')
        axes = []
        for k, v in cfg.items(CS):
            if k.lower() in ('enabled', 'skip_nominal', 'nominal_temperature'):
                continue
            if k != 'temperature' and k not in defined:
                raise ConfigError('[corners] {} is not a variable from [variables]'.format(k))
            vals = v.split()
            if not vals:
                raise ConfigError('[corners] {} has no values'.format(k))
            axes.append((k, vals))
        skip_nom = cfg.flag(CS, 'skip_nominal', True)
        for combo in itertools.product(*[[(k, x) for x in vals] for k, vals in axes]) if axes else []:
            if skip_nom and all(si(x) is not None and si(x) == si(nominal.get(k, '')) or x == nominal.get(k)
                                for k, x in combo):
                continue
            parts = []
            for k, x in combo:
                prefix = {'temperature': 'T', 'avdd': 'V'}.get(k, k)
                parts.append(prefix + re.sub(r'\W', '', x.replace('-', 'm').replace('.', 'p')))
            corners.append(['_'.join(parts), [[k, x] for k, x in combo]])

    plan = {'schematics': schematics, 'tests': tests, 'variables': variables, 'corners': corners,
            'models': tb['models'], 'in_devs': in_devs, 'tia_vars': tia_vars,
            'n_mos_out': n_mos_out, 'cmfb_found': cmfb_found, 'notes': notes}
    return plan


def build_skill(tb, plan):
    tests = [[t['name'], t['view'], t['enabled'],
              [[a, [[k, v] for k, v in opts]] for a, opts in t['analyses']],
              [[o[0], o[1], o[2], list(o[3]) if o[3] else None] for o in t['outputs']]]
             for t in plan['tests']]
    head = '\n'.join([
        '; generated by tia_tb_gen.py {}'.format(VERSION),
        'tbgLib = ' + sk(tb['tb_lib']),
        'tbgCell = ' + sk(tb['tb_cell']),
        'tbgMaestroView = ' + sk(tb['maestro_view']),
        'tbgSimulator = ' + sk(tb['simulator']),
        'tbgOverwrite = ' + sk(tb['overwrite']),
        'tbgSchematics = ' + sk(plan['schematics']),
        'tbgTests = ' + sk(tests),
        'tbgVars = ' + sk([list(v) for v in plan['variables']]),
        'tbgCorners = ' + sk(plan['corners']),
        'tbgModels = ' + sk(plan['models']),
        ''])
    return head + SKILL_BUILD


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------
def report_inspection(tb, pins, info, cfg):
    print('\nTIA {}/{}'.format(tb['tia_lib'], tb['tia_cell']))
    print('  pins            : ' + ' '.join(info['terms']))
    print('  transistors     : {}'.format(len(info['mos'])))
    for path, lib, cell in info['mos']:
        print('      /{}{}   ({}/{})'.format(DUT, path, lib, cell))
    in_pin = pins['pos_in'] if tb['diff'] else pins['neg_in']
    ins = [n for n, g in info['topmos'] if g == in_pin]
    print('  input devices   : {} (gate on {})'.format(' '.join(ins) or '-', in_pin))
    tv = tia_variables(info, tb)
    defined = {k for k, _ in cfg.items('variables')}
    print('  design variables: ' + (' '.join('{}{}'.format(v, '' if v in defined else '(!)')
                                              for v in sorted(tv)) or '-'))
    if any(v not in defined for v in tv):
        print('                    (!) = no value in [variables] yet')
    if tb['diff']:
        hit = [i for i in info['insts'] if i[0] == tb['cmfb_probe']]
        print('  CMFB probe      : {}'.format(
            '{} found ({}/{})'.format(hit[0][0], hit[0][1], hit[0][2]) if hit
            else '{} not found in the TIA top level'.format(tb['cmfb_probe'])))
    for w in info['warn']:
        print('  WARNING: ' + w)


def cmfb_message(tb, plan):
    probe = tb['cmfb_probe']
    path = '/{}/{}'.format(DUT, probe)
    lines = ['', '=' * 78, 'ACTION NEEDED - common-mode feedback loop probe (iprobe_cmfb)', '=' * 78]
    if plan['cmfb_found']:
        lines += ['Found instance "{}" in {}/{}. Test FB_STB_CMFB runs stb with probe {}.'.format(
            probe, tb['tia_lib'], tb['tia_cell'], path),
            'Check that it sits inside the CMFB loop (it must break that loop and only it).']
    else:
        lines += [
            'Test FB_STB_CMFB needs a loop-gain probe inside the CMFB loop of the TIA, which',
            'only you can place. Open {}/{} (schematic) and:'.format(tb['tia_lib'], tb['tia_cell']),
            '  1. add an analogLib "iprobe" and name the instance  {}'.format(probe),
            '  2. put it in series in the CMFB loop, e.g. between the CMFB error-amplifier',
            '     output and the node it controls, so that it breaks the CM loop only',
            '  3. check and save, then enable FB_STB_CMFB in the Maestro view',
            '     (it was created DISABLED because the probe does not exist yet).',
            'The test already points to probe {} (change cmfb_probe in [testbench] to'.format(path),
            'use another instance name).']
    lines.append('=' * 78)
    return '\n'.join(lines)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('specs', nargs='?', default=None,
                    help='configuration file (default: ./tia_specs.txt, else the one next to this script)')
    ap.add_argument('--inspect', action='store_true', help='only report TIA pins, transistors and variables')
    ap.add_argument('--dry-run', action='store_true', help='write the build SKILL file and stop')
    ap.add_argument('--overwrite', action='store_true', help='replace existing testbench views')
    ap.add_argument('--virtuoso', default='virtuoso', help='Virtuoso executable (default: virtuoso)')
    ap.add_argument('--timeout', type=int, default=900, help='seconds per Virtuoso run (default 900)')
    ap.add_argument('--keep', action='store_true', help='keep the generated SKILL and CDS.log')
    ap.add_argument('--verbose', action='store_true', help='print the full Virtuoso output')
    ap.add_argument('--version', action='version', version='%(prog)s ' + VERSION)
    args = ap.parse_args(argv)

    path = args.specs
    if path is None:
        here = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tia_specs.txt')
        path = 'tia_specs.txt' if os.path.exists('tia_specs.txt') else here
    if not os.path.exists(path):
        print('ERROR: configuration file not found: ' + path, file=sys.stderr)
        return 2
    if not os.path.exists('cds.lib'):
        print('WARNING: no cds.lib in {} - run this from your Cadence start-up directory'.format(os.getcwd()))
    if not args.dry_run and shutil.which(args.virtuoso) is None:
        print('ERROR: {!r} is not on PATH; load your Cadence environment first'.format(args.virtuoso),
              file=sys.stderr)
        return 2

    try:
        cfg = Config(path)
        tb = read_testbench(cfg, args)
        pins = read_pins(cfg, tb)
        read_mos_metrics(cfg)                       # validate early
        print('tia_tb_gen {}: {} TIA {}/{} -> testbench {}/{}'.format(
            VERSION, 'differential' if tb['diff'] else 'single-ended',
            tb['tia_lib'], tb['tia_cell'], tb['tb_lib'], tb['tb_cell']))
        print('[1/2] reading the TIA (batch Virtuoso, read-only) ...', flush=True)
        info = inspect(cfg, args, tb)
        if not info['tia_lib']:
            raise ConfigError('library {} is not defined in cds.lib'.format(tb['tia_lib']))
        if not info['sym']:
            raise ConfigError('{}/{}/{} does not exist'.format(tb['tia_lib'], tb['tia_cell'], tb['tia_symbol']))
        if args.inspect:
            report_inspection(tb, pins, info, cfg)
            return 0
        if not info['tb_lib']:
            raise ConfigError('testbench library {} is not defined in cds.lib (create it first)'.format(tb['tb_lib']))
        if not info['tb_write']:
            raise ConfigError('no write permission on library {}'.format(tb['tb_lib']))
        if not info['sch']:
            print('WARNING: {}/{} has no {} view - no per-transistor outputs'.format(
                tb['tia_lib'], tb['tia_cell'], tb['tia_schematic']))
        locked = [v for v, s in info['tb_views'].items() if s == 'locked']
        if locked:
            raise ConfigError('{}/{}: view(s) {} are open in another Virtuoso session - close them first'.format(
                tb['tb_lib'], tb['tb_cell'], ', '.join(locked)))
        if info['tb_views'] and not tb['overwrite']:
            raise ConfigError('{}/{} already has view(s) {}; choose another tb_cell or use --overwrite'.format(
                tb['tb_lib'], tb['tb_cell'], ', '.join(sorted(info['tb_views']))))
        plan = build_plan(cfg, tb, pins, info)
    except (ConfigError, configparser.Error, OSError) as e:
        print('ERROR: {}'.format(e), file=sys.stderr)
        return 1

    for w in info['warn']:
        print('WARNING: ' + w)
    n_out = sum(len(t['outputs']) for t in plan['tests'])
    print('  {} transistors, input devices: {}'.format(
        len(info['mos']), ' '.join(d.split('/')[-1] for d in plan['in_devs']) or '-'))
    print('  {} tests, {} outputs ({} per-transistor), {} global variables, {} corners'.format(
        len(plan['tests']), n_out, plan['n_mos_out'], len(plan['variables']), len(plan['corners'])))

    skill = build_skill(tb, plan)
    if args.dry_run:
        out = 'tia_tb_gen_{}.il'.format(tb['tb_cell'])
        with open(out, 'w') as f:
            f.write(SKILL_COMMON + skill)
        print('dry run: build SKILL written to ' + os.path.abspath(out))
        return 0

    print('[2/2] creating schematics and Maestro view ...', flush=True)
    try:
        recs, errors, skill_errs = run_virtuoso(skill, args, 'build')
    except ConfigError as e:
        print('ERROR: {}'.format(e), file=sys.stderr)
        return 1
    result = [r for r in recs if r[0] == 'RESULT']
    for r in recs:
        if r[0] == 'SCH':
            print('  {}/{}/{}: created (schCheck errors/warnings: {})'.format(
                tb['tb_lib'], tb['tb_cell'], r[1], r[2]))
        elif r[0] == 'TEST':
            t = [x for x in plan['tests'] if x['name'] == r[1]][0]
            print('  test {:<12} {:>4} outputs{}'.format(
                r[1], r[2], '' if t['enabled'] else '   (disabled)'))
        elif r[0] == 'MAESTRO':
            print('  {}/{}/{}: created with {} corner(s)'.format(tb['tb_lib'], tb['tb_cell'], r[1], r[2]))
        elif r[0] == 'INFO':
            print('  ' + r[1])
    if errors or skill_errs or not result or result[0][1] != 'ok':
        for e in errors + skill_errs:
            print('ERROR: ' + e, file=sys.stderr)
        print('ERROR: the testbench is incomplete (rerun with --verbose --keep for details)', file=sys.stderr)
        return 1
    for n in plan['notes']:
        print('NOTE: ' + n)
    if not plan['models']:
        print('NOTE: no model_files given - the tests use the default model setup of your environment')
    print('\nTestbench {}/{} is complete.'.format(tb['tb_lib'], tb['tb_cell']))
    if tb['diff']:
        print(cmfb_message(tb, plan))
    return 0


if __name__ == '__main__':
    sys.exit(main())
