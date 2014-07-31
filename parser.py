# Copyright 2014 The ALIVe authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import collections, sys
from language import *
from precondition import *
from pyparsing.pyparsing import *

ParserElement.enablePackrat()

class Phase:
  Source, Target, Pre = range(3);

  names = {
    Source: "Source",
    Target: "Target",
    Pre: "Precondition",
  }

class Expr(object):
  def __init__(self, pstr, loc, toks):
    self.str = pstr
    self.loc = loc
    self.toks = toks

  def __repr__(self):
    return "%s('', %s, %s)" % (self.__class__.__name__, self.loc, self.toks)

  def _fatal(self, msg):
    if isinstance(msg, list):
      msg = '\n'.join(msg)
    raise ParseFatalException(self.str, self.loc, msg)


class TypeExpr(Expr):
  @staticmethod
  def _indirect(ty, n):
    for i in range(n):
      ty = PtrType(ty)
    return ty

  def evalInt(self, ids, phase):
    try:
      return self.eval(ids, phase).ensureIntType()
    except ParseError, e:
      self._fatal(e.msgs)

  def evalPtr(self, ids, phase):
    try:
      return self.eval(ids, phase).ensurePtrType()
    except ParseError, e:
      self._fatal(e.msgs)

  def evalIntPtrOrVector(self, ids, phase):
    try:
      return self.eval(ids, phase).ensureIntPtrOrVector()
    except ParseError, e:
      self._fatal(e.msgs)

class IntTypeExpr(TypeExpr):
  def eval(self, ids, phase):
    ty = IntType(self.toks[1])
    return self._indirect(ty, len(self.toks) - 2)

class ArrayTypeExpr(TypeExpr):
  def eval(self, ids, phase):
    elems = self.toks[1].getValue(IntType(), ids, phase)
    elemty = self.toks[3].eval(ids, phase)
    return self._indirect(ArrayType(elems, elemty), len(self.toks) - 5)

class NamedTypeExpr(TypeExpr):
  def eval(self, ids, phase):
    ty = NamedType(self.toks[0])
    return self._indirect(ty, len(self.toks) - 1)

class OptionalTypeExpr(TypeExpr):
  def eval(self, ids, phase):
    if self.toks:
      self.loc = self.toks[0].loc  # is this ever needed?
      return self.toks[0].eval(ids, phase)

    return UnknownType()

class ValExpr(Expr):
  pass

class OperandExpr(ValExpr):
  '''Emulates the behavior of the old parser.

  Insert any operand into the list of identifiers, but not sub-expressions.
  '''

  def getValue(self, ty, ids, phase):
    v = self.toks[0].getValue(ty, ids, phase)

    ids[v.getUniqueName()] = v # test whether needed?

    return v

class Lit(ValExpr):
  def getValue(self, ty, ids, phase):
    try:
      return ConstantVal(int(self.toks[0]), ty.ensureIntType())
    except ParseError, e:
      self._fatal(e.msgs)

class LitWordExpr(ValExpr):
  def getValue(self, ty, ids, phase):
    v = self.toks[0]
    try:
      if v == 'undef':
        c = UndefVal(ty)
      elif v == 'true':
        c = ConstantVal(1, ty.ensureIntType(1))
      elif v == 'false':
        c = ConstantVal(0, ty.ensureIntType(1))
      elif v == 'null':
        c = ConstantVal(0, ty.ensurePtrType())
      else:
        assert False
    except ParseError, e:
      self._fatal(e.msgs)

    ids[c.getUniqueName()] = c
    return c

class Name(ValExpr):
  def __init__(self, pstr, loc, tok):
    self.id = tok[0]
    self.loc = loc
    self.str = pstr

  def __str__(self): return self.id

  def __repr__(self):
    return "%s(%s,%d)" % (self.__class__.__name__, self.id, self.loc)

  def getValue(self, ty, ids, phase):
    if self.id in ids:
      return ids[self.id]

    if phase == Phase.Source:
      ids[self.id] = Input(self.id, ty)
      return ids[self.id]

    # FIXME: hack to get same error messages as old parser
    if phase == Phase.Target:
      self._fatal('Cannot declare new input variables or constants in Target')
    self._fatal('Identifier used in precondition was not defined')
    #self._fatal('Input %s not in source' % self.id)

class Register(Name): pass
class ConstName(Name): pass

def yieldPairs(toks):
  it = iter(toks)
  while True:
    try:
      a = it.next()
      b = it.next()
      yield a,b
    except StopIteration:
      break


class UnaryExpr(ValExpr):
  def getValue(self, ty, ids, phase):
    if phase == Phase.Source:
      self._fatal('Expressions not permitted in source')

    op = CnstUnaryOp.getOpId(self.toks[0][0])
    return CnstUnaryOp(op, self.toks[0][1].getValue(ty, ids, phase))

class BinaryExpr(ValExpr):
  def getValue(self, ty, ids, phase):
    if phase == Phase.Source:
      self._fatal('Expressions not permitted in source')

    x = self.toks[0][0].getValue(ty, ids, phase)
    for op, v in yieldPairs(self.toks[0][1:]):
      y = v.getValue(ty, ids, phase)
      x = CnstBinaryOp(CnstBinaryOp.getOpId(op), x, y)

    return x


class PreconditionExpr(Expr):
  pass

class TrueExpr(PreconditionExpr):
  def getPred(self, ids):
    return TruePred()

class CmpExpr(PreconditionExpr):
  def getPred(self, ids):
    x = self.toks[0].getValue(IntType(), ids, Phase.Pre)
    conds = []
    for opname,rhs in yieldPairs(self.toks[1:]):
      op = BinaryBoolPred.getOpId(opname)
      y = rhs.getValue(IntType(), ids, Phase.Pre)
      conds.append(BinaryBoolPred(op,x,y))
      x = y
    if len(conds) == 1:
      return conds[0]
    else:
      return PredAnd(*conds)

class NotExpr(PreconditionExpr):
  def getPred(self, ids):
    return PredNot(self.toks[0][0].getPred(ids))

class AndExpr(PreconditionExpr):
  def getPred(self, ids):
    return PredAnd(*(p.getPred(ids) for p in self.toks[0]))

class OrExpr(PreconditionExpr):
  def getPred(self, ids):
    return PredOr(*(p.getPred(ids) for p in self.toks[0]))

class FunExpr(ValExpr, PreconditionExpr):
  'Common expression type for <name>(<args>). Supports getValue and getPred.'

  def getPred(self, ids):
    name = self.toks[0]

    if name not in LLVMBoolPred.opids:
      self._fatal('Unknown predicate: ' + name)

    op = LLVMBoolPred.opids[name]
    #args = [arg.getValue(UnknownType(), ids, Phase.Pre) for arg in self.toks[1:]]

    args = []
    i = 1
    for t in self.toks[1:]:
      a = t.getValue(UnknownType(), ids, Phase.Pre)
      (ok,msg) = LLVMBoolPred.argAccepts(op, i, a)
      if not ok:
        t._fatal('Expected ' + msg)
      args.append(a)
      i += 1

    try:
      return LLVMBoolPred(op, args)
    except ParseError, e:
      self._fatal(e.msgs)


  def getValue(self, ty, ids, phase):
    if phase == Phase.Source:
      self._fatal('Expressions not permitted in source')

    # determine if this is a valid function
    name = self.toks[0]

    if not name in CnstFunction.opids:
      self._fatal('Unknown function: ' + name)

    op = CnstFunction.opids[name]
    args = [arg.getValue(UnknownType(), ids, phase) for arg in self.toks[1:]]
    ## TODO: check arity/arg kinds?

    try:
      return CnstFunction(op, args, ty)
    except ParseError, e:
      self._fatal(e.msgs)


class OpInstrExpr(Expr):
  def eval(self, ids, phase):
    r = self.toks.lhs.id

    op = self.toks.op.getOp(r, ids, phase)
    if r in ids:
      self._fatal('Redefinition of ' + r)

    op.setName(r)  #FIXME: names should be set in the op constructor
    ids[r] = op


class InstrExpr(Expr):
  pass

class CopyOpExpr(InstrExpr):
  def getOp(self, name, ids, phase):
    ty = self.toks.ty.eval(ids, phase)
    return CopyOperand(self.toks.x.getValue(ty, ids, phase), ty)

class BinOpExpr(InstrExpr):
  def getOp(self, name, ids, phase):
    ty = self.toks.ty.evalInt(ids, phase)

    v1 = self.toks.x.getValue(IntType(), ids, phase)
    v2 = self.toks.y.getValue(IntType(), ids, phase)
    flags = [tok.value for tok in self.toks.flags]
    try:
      return BinOp(self.toks.code, ty, v1, v2, flags)
    except ParseError, e:
      ## TODO: find better way to detect unsupported flags
      for tok in self.toks.flags:
        if tok.value == e.token:
          raise ParseFatalException(self.str, tok.locn_start, '\n'.join(e.msgs))

      self._fatal(e.msgs)

class ConvOpExpr(InstrExpr):
  def getOp(self, name, ids, phase):
    op = self.toks.code
    if ConversionOp.enforceIntSrc(op):
      sty = self.toks.sty.evalInt(ids, phase)
    elif ConversionOp.enforcePtrSrc(op):
      sty = self.toks.sty.evalPtr(ids, phase)
    else:
      sty = self.toks.sty.eval(ids, phase)

    if ConversionOp.enforceIntTgt(op):
      rty = self.toks.rty.evalInt(ids, phase)
    elif ConversionOp.enforcePtrTgt(op):
      rty = self.toks.rty.evalPtr(ids, phase)
    else:
      rty = self.toks.rty.eval(ids, phase)

    v1 = self.toks.x.getValue(sty, ids, phase)

    try:
      return ConversionOp(op, sty, v1, rty)
    except AssertionError:
      self._fatal('AssertionError')

class ICmpExpr(InstrExpr):
  def getOp(self, name, ids, phase):
# FIXME: calling ensureIntPtrOrVector twice crashes
#     ty = self.toks.ty.evalIntPtrOrVector(ids, phase)
    ty = self.toks.ty.eval(ids, phase)
    x = self.toks.x.getValue(ty, ids, phase)
    y = self.toks.y.getValue(ty, ids, phase)
    try:
      return Icmp(self.toks.cmp, ty, x, y)
    except ParseError, e:
      if 'type' in ' '.join(e.msgs):
        # assume this is only raised by having the wrong type
        self.toks.ty._fatal('int/ptr/vector expected')
      self._fatal(e.msgs)


class SelectExpr(InstrExpr):
  def getOp(self, name, ids, phase):
    toks = self.toks

    pty = toks.ty.evalInt(ids, phase)
    if pty.defined and pty.size != 1:
      toks.ty._fatal('Only i1 permitted')
    pty = pty.ensureIntType(1)

    try:
      ty = getMostSpecificType(toks.tty.eval(ids,phase), toks.fty.eval(ids,phase))
    except ParseError, e:
      toks.fty._fatal(e.msgs)

    return Select(ty, toks.pred.getValue(pty, ids, phase),
      toks.tval.getValue(ty, ids, phase),
      toks.fval.getValue(ty, ids, phase))

class AllocaExpr(InstrExpr):
  def getOp(self, name, ids, phase):
#     print 'AllocaExpr.getOp', self.toks.dump()
    if 'num' in self.toks:
      num_ty = self.toks.num_ty.evalInt(ids, phase)
      num = self.toks.num.getValue(num_ty, ids, phase)
    else:
      num_ty = IntType()
      num = ConstantVal(1, num_ty)
      ids[num.getUniqueName()] = num

    align = self.toks.align if 'align' in self.toks else 0
    ty = self.toks.ty.eval(ids, phase)

    try:
      return Alloca(self.toks.ty.eval(ids, phase), num_ty, num, align)
    except AssertionError, e:
      self._fatal(str(e))

class GEPExpr(InstrExpr):
  def getOp(self, name, ids, phase):
    ty = self.toks.ptr_t.evalPtr(ids,phase)
    ptr = self.toks.ptr.getValue(ty, ids, phase)
    flds = []
    for te, ve in yieldPairs(self.toks.flds):
      t = te.evalInt(ids,phase)
      v = ve.getValue(ty,ids,phase)
      flds += [t,v]

    return GEP(ty, ptr, flds, 'inbounds' in self.toks)

class LoadExpr(InstrExpr):
  def getOp(self, name, ids, phase):
    ty = self.toks.ty.evalPtr(ids, phase)
    x = self.toks.x.getValue(ty, ids, phase)
    align = self.toks.get('align', defaultValue = 0)

    return Load(ty, x, align)

class StoreExpr(Expr):
  def eval(self, ids, phase):
    val_t = self.toks.val_t.eval(ids, phase)
    val   = self.toks.val.getValue(val_t, ids, phase)
    ptr_t = self.toks.ptr_t.evalPtr(ids, phase)
    ptr   = self.toks.ptr.getValue(ptr_t, ids, phase)
    align = self.toks.get('align', defaultValue = 0)

    s = Store(val_t, val, ptr_t, ptr, align)
    ids[s.getUniqueName()] = s

cexpr = Forward()

reg = Regex(r"%[a-zA-Z0-9_.]+").setName("Register").setParseAction(Register)

cname = Regex(r"C\d*").setName("ConstName").setParseAction(ConstName)

posnum = Word(nums).setParseAction(lambda s,l,t: int(t[0]))


stars = ZeroOrMore(Literal('*').leaveWhitespace())
ty = Forward()
ty << ((Literal('i') + posnum + stars).setParseAction(IntTypeExpr)
  | ('[' + cexpr + 'x' + ty + ']' + ZeroOrMore(Literal('*'))).setParseAction(ArrayTypeExpr)
  | (Regex(r'Ty[0-9]*') + stars).setParseAction(NamedTypeExpr)
  )
ty.setName('type')

opt_ty = Optional(ty).setParseAction(OptionalTypeExpr)


lit = Regex("(?:-\s*)?\d+").setName("Literal").setParseAction(Lit)

ident = Word(srange("[a-zA-Z]"), srange(r"[a-zA-Z0-9_.]")).setName("Identifier")

arg = reg | cexpr # | ty

args = delimitedList(arg)




cfunc = ident + Suppress('(') + args + Suppress(')')
cfunc.setParseAction(FunExpr)

catom = cname | lit | cfunc
catom.setName('const, literal, or function')

cexpr << infixNotation(catom,
      [(Regex(r'~|-(?!\s*\d)'), 1, opAssoc.RIGHT, UnaryExpr),
       (Regex(r'\*|/|%(?= )'), 2, opAssoc.LEFT, BinaryExpr),  # require space after % to avoid matching registers
       (oneOf('+ -'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('>>'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('<<'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('&'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('^'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('|'), 2, opAssoc.LEFT, BinaryExpr),
      ])
cexpr.setName('ConstExpr')

#cexpr.setWhitespaceChars(' ')


pre_comp_op = oneOf('== != < <= > >=').setName('comparison operator')

pre_lit = Literal("true").setParseAction(TrueExpr)
pre_comp = (cexpr + OneOrMore(pre_comp_op - cexpr)).setParseAction(CmpExpr)
pre_comp.setName('comparison')

#pre_pred_name = opCode(LLVMBoolPred.opids).setName('pred name')
#pre_pred = (pre_pred_name + Suppress('(') + args + Suppress(')')).setParseAction(PredExpr)
pre_pred = (ident + Suppress('(') + args + Suppress(')')).setParseAction(FunExpr)
pre_pred.setName('predicate')

pre_atom = pre_lit | pre_comp | cfunc

pre = infixNotation(pre_atom,
      [(Suppress('!'), 1, opAssoc.RIGHT, NotExpr),
       (Suppress('&&'), 2, opAssoc.LEFT, AndExpr),
       (Suppress('||'), 2, opAssoc.LEFT, OrExpr),
      ])
pre.setName('precondition')

special_lit = oneOf('true false undef null').setParseAction(LitWordExpr)
operand = (reg | special_lit | cexpr).setName("Operand")
operand.setParseAction(OperandExpr)

comma = Suppress(',')
equals = Suppress('=')

copyOp = opt_ty('ty') + operand('x')
copyOp.setParseAction(CopyOpExpr)

def opCode(codes):
  def pa(s,l,t):
    if t[0] in codes:
      return codes[t[0]]
    else:
      raise ParseException(s,l,"Not an appropriate code")

#   return oneOf(' '.join(codes))('code').setParseAction(traceParseAction(pa)).setDebug()
  return ident('code').setParseAction(pa, callDuringTry=True)

flags = Group(ZeroOrMore(locatedExpr(oneOf('nsw nuw exact'))))

binOp = (opCode(BinOp.opids) - flags('flags') - opt_ty('ty') - operand('x') - comma
      - operand('y')).setParseAction(BinOpExpr)

opt_rty = (Suppress('to') - ty | FollowedBy(LineEnd())).setParseAction(OptionalTypeExpr)

convOp = (opCode(ConversionOp.opids) - opt_ty('sty') - operand('x') - opt_rty('rty')).setParseAction(ConvOpExpr)

cmpOp = Optional(ident, '')

## FIXME: "icmp i8 %x, %y" parses the "i8" as the comparison operator
icmp = Literal('icmp') - cmpOp('cmp') - opt_ty('ty') - operand('x') - comma - operand('y')
icmp.setParseAction(ICmpExpr)

select = Literal('select') - opt_ty('ty') + operand('pred') \
  + comma + opt_ty('tty') + operand('tval') + comma + opt_ty('fty') + operand('fval')
select.setParseAction(SelectExpr)

# Ending with an optional segment consumes the newline
alloca = Suppress('alloca') - (ty | FollowedBy(comma|LineEnd()))('ty').setParseAction(OptionalTypeExpr) \
  + (comma + opt_ty('num_ty') + operand('num') | FollowedBy(comma|LineEnd())) \
  + (comma + Suppress('align') + posnum('align') | FollowedBy(LineEnd()))
alloca.setName('alloca')
alloca.setParseAction(AllocaExpr)

# alloca = Suppress('alloca') + opt_ty('ty') + Optional(comma + opt_ty('num_ty') + operand('num')) \
#     + comma + Suppress('align') + posnum('align') \
#   | Suppress('alloca') + opt_ty('ty') + comma + opt_ty('num_ty') + operand('num') \
#   | Suppress('alloca') + (ty | FollowedBy(LineEnd()))('ty').setParseAction(OptionalTypeExpr)


gep = Suppress('getelementptr') + Optional('inbounds') + opt_ty('ptr_t') + operand('ptr') + Group(
  comma + ZeroOrMore(opt_ty + operand + comma) + opt_ty + operand
  | FollowedBy(LineEnd()))('flds')

gep.setParseAction(GEPExpr)

load = Suppress('load') + opt_ty('ty') + operand('x') + (comma + Suppress('align') + posnum('align')|FollowedBy(LineEnd()))
load.setParseAction(LoadExpr)

op = binOp | convOp | icmp | select | alloca | gep | load | copyOp
op.setName('operator')


opInstr = reg('lhs') + Suppress('=') + op('op')
opInstr.setParseAction(OpInstrExpr)

store = Suppress('store') - opt_ty('val_t') - operand('val') - comma - opt_ty('ptr_t') - operand('ptr') - \
  (comma - Suppress('align') - posnum('align') | FollowedBy(LineEnd()))
store.setParseAction(StoreExpr)

instr = opInstr | store
instr.setName('Instruction')

instrs = OneOrMore(instr - LineEnd().suppress())

def parseTransform(s,l,t):
#   print t.dump()
  try:
    src = collections.OrderedDict()
    for i in t.src: i.eval(src, Phase.Source)

    if t.pre[0]:
      pre = t.pre[0].getPred(src)
    else:
      pre = TruePred()

    # copy inputs to target
    tgt = collections.OrderedDict(
      [(k,v) for k,v in src.iteritems() if isinstance(v, Input)])

    for i in t.tgt: i.eval(tgt, Phase.Target)

    return t.name[0] if t.name else '', pre, src, tgt
  except ParseBaseException:
    raise
  except Exception, e:
    print e
    raise


comment = Literal(';') + restOfLine()

transform = (Optional(Suppress("Name:") - SkipTo(LineEnd())).setResultsName("name") \
  + Optional(Suppress("Pre:") - pre - LineEnd().suppress(), None).setResultsName("pre") \
  + Group(OneOrMore(instr - LineEnd().suppress())).setResultsName("src") \
  - Suppress("=>") \
  - Group(OneOrMore(instr - LineEnd().suppress())).setResultsName("tgt"))
transform.setName('transform')
transform.setParseAction(parseTransform)
transform.ignore(comment)

transforms = OneOrMore(transform)

str1 = """
Name: Test1
Pre: width(%a) == -C

%a = mul %x, C
%r = add %a, %x
=>
%r = mul %x, C+1
"""

# comma.setDebug()
# cfunc.setDebug()
# arg.setDebug()
# reg.setDebug()
# ty.setDebug()
# opt_ty.setDebug()
# cexpr.setDebug()
# pre.setDebug()
# pre_atom.setDebug()
# pre_pred.setDebug()
# pre_comp.setDebug()
# pre_lit.setDebug()
# binOp.setDebug()
# convOp.setDebug()
# select.setDebug()
# alloca.setDebug()
# op.setDebug(True)
# instr.setDebug()
# instrs.setDebug()
# cexpr.setDebug()
# reg.setDebug()
# operand.setDebug()
# transform.setDebug()

def test(s = '%a = add i8 %b, %c', t = None):
  try:
    op = instr.parseString(s)[0]
    src = collections.OrderedDict()
    op.eval(src, Phase.Source)

    if t:
      top = instr.parseString(t)[0]
      tgt = collections.OrderedDict([(k,v) for k,v in src.iteritems() if isinstance(v,Input)])

      #for x in src:
      # if isinstance(src[x], Input):
      #   tgt[x] = src[x]
      top.eval(tgt, Phase.Target)
    else: tgt = {}
    return src, tgt
  except ParseBaseException, e:
    print e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'

def parse_opt_file(s):
  'Wrapper for transforms.parseString which exits program on exceptions.'
  try:
    return transforms.parseString(s, True)
  except ParseBaseException, e:
    print 'ERROR:', e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'
    exit(-1)



def parse_opts(s):
  # transforms.setDebug()
  try:
    for name,pre,src,tgt in transforms.parseString(s, True):
      print '---------'
      print 'Name:', name
      print 'Pre:', repr(pre)
      print
      print_prog(src)
      print '  =>'
      print_prog(tgt)
  except ParseBaseException, e:
    print e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'

if __name__ == "__main__":
  opts = parse_opts(sys.stdin.read())
